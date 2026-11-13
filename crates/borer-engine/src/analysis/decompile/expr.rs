//! Symbolic expressions for the decompiler: text variables ([`Key`]), access
//! types ([`Ty`]), their construction, and constant folding. Rendering them
//! as C text lives in [`super::expr_render`].
//!
//! Every `Var` refers to the *current text value* of a variable in the emitted
//! pseudo-C, never to a machine register at some earlier time. That invariant
//! is what lets the lifter keep expressions symbolic until they are needed.

use crate::isa::a64;
use crate::isa::x86::{ConditionCode, Register};

use super::fcmp::FPred;
use super::helper::Helper;
use super::opaque::Evidence;
use crate::num::{lo16, lo32};

mod reach;

pub(super) use super::expr_render::{
    Names, TEB_FIELDS, a64_code, a64_reg, bare, compact_literal, negative_magnitude, render_const,
};

/// A text variable: something the emitted pseudo-C can name and assign.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Key {
    /// Canonical (full-width) register.
    Reg(Register),
    /// Stack slot at this byte offset from the rsp value at function entry
    /// (negative: local; positive: caller frame).
    Slot(i64),
    /// Absolute data address, accessed with this width in bits.
    Global(u64, u8),
    /// Branch condition materialized into a named temporary.
    Tmp(u32),
    /// The function's incoming argument at this position of the calling
    /// convention (`a1` is the first argument register). Never written, so
    /// copies of it stay symbolic across calls.
    Param(u8),
    /// An arm64 register: `x0`..`x30`, the stack pointer while it is no
    /// tracked offset, or `v0`..`v31`. Last, so the order and hash of every
    /// other variable stay as they were.
    A64(a64::Reg),
    /// An ARM32 register: `r0`..`r14`, the stack pointer while it is no
    /// tracked offset, a single `s0`..`s31` or a double `d0`..`d31`.
    A32(crate::isa::a32::Reg),
    /// A RISC-V register: `x1`..`x31`, the stack pointer while it is no
    /// tracked offset, or `f0`..`f31`.
    Rv(crate::isa::rv::Reg),
}

impl Key {
    /// Tells whether the variable is an x87 stack register, `st0` to `st7`.
    ///
    /// Those are positions, not places: every push and pop moves each one's
    /// value to its neighbour, a read and a write the instruction's own
    /// register operands do not list.
    pub(super) fn is_x87(self) -> bool {
        matches!(self, Key::Reg(r) if r >= Register::ST0 && r <= Register::ST7)
    }
}

/// Access width and interpretation of a memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Ty {
    /// One byte.
    U8,
    /// Two bytes.
    U16,
    /// Four bytes, integer.
    U32,
    /// Eight bytes, integer.
    U64,
    /// Sixteen bytes (vector registers, or any wider blob).
    U128,
    /// Four bytes, IEEE-754 single.
    F32,
    /// Eight bytes, IEEE-754 double.
    F64,
}

impl Ty {
    /// Picks the type for an access of `bytes` bytes.
    ///
    /// Anything wider than 16 bytes (ymm/zmm) is an opaque 128-bit blob; odd
    /// sizes such as the 10-byte x87 format count as 64 bits.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Operand size in bytes.
    /// * `float` - The operand is a floating-point value (4 or 8 bytes).
    pub(super) fn from_size(bytes: usize, float: bool) -> Ty {
        match (bytes, float) {
            (1, _) => Ty::U8,
            (2, _) => Ty::U16,
            (4, true) => Ty::F32,
            (4, false) => Ty::U32,
            (8, true) => Ty::F64,
            (8, false) => Ty::U64,
            (16, _) => Ty::U128,
            (n, _) if n > 16 => Ty::U128,
            _ => Ty::U64,
        }
    }

    /// Returns the width in bits.
    pub(super) fn bits(self) -> u8 {
        match self {
            Ty::U8 => 8,
            Ty::U16 => 16,
            Ty::U32 | Ty::F32 => 32,
            Ty::U64 | Ty::F64 => 64,
            Ty::U128 => 128,
        }
    }

    /// Picks the smallest integer type holding `bits` bits.
    ///
    /// # Arguments
    ///
    /// * `bits` - Width in bits; more than 64 gives [`Ty::U128`].
    pub(super) fn from_bits(bits: u8) -> Ty {
        match bits {
            0..=8 => Ty::U8,
            9..=16 => Ty::U16,
            17..=32 => Ty::U32,
            33..=64 => Ty::U64,
            _ => Ty::U128,
        }
    }

    /// Returns the C type name (`uint32_t`, `double`, ...).
    pub(super) fn name(self) -> &'static str {
        match self {
            Ty::U8 => "uint8_t",
            Ty::U16 => "uint16_t",
            Ty::U32 => "uint32_t",
            Ty::U64 => "uint64_t",
            Ty::U128 => "uint128_t",
            Ty::F32 => "float",
            Ty::F64 => "double",
        }
    }
}

/// Binary operator of an [`Expr::Bin`] node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Op {
    /// Wrapping addition.
    Add,
    /// Wrapping subtraction.
    Sub,
    /// Wrapping multiplication (low half).
    Mul,
    /// Unsigned division.
    Div,
    /// Unsigned remainder.
    Rem,
    /// Signed division.
    SDiv,
    /// Signed remainder.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise exclusive or.
    Xor,
    /// Shift left.
    Shl,
    /// Logical shift right.
    Shr,
    /// Arithmetic shift right.
    Sar,
    /// Rotate left within this many bits.
    Rol(u8),
    /// Rotate right within this many bits.
    Ror(u8),
    /// High half of the unsigned product at this width.
    MulHi(u8),
    /// High half of the signed product at this width.
    SMulHi(u8),
    /// 1 when the signed product at this width overflows, else 0.
    SMulO(u8),
    /// 1 when the unsigned sum at this width carries out, else 0.
    UAddO(u8),
    /// 1 when the unsigned difference at this width borrows, else 0.
    USubO(u8),
    /// IEEE-754 addition.
    FAdd,
    /// IEEE-754 subtraction.
    FSub,
    /// IEEE-754 multiplication.
    FMul,
    /// IEEE-754 division.
    FDiv,
    /// The smaller operand when the ordered `<` holds, otherwise the right one.
    ///
    /// A NaN comparison fails, and so does an equal pair, so `minss` and the
    /// emulator's `fmin` keep the right operand's bits, including a NaN and
    /// the other zero. C's `fmin` returns the number and prefers `-0`.
    FMin,
    /// The larger operand when the ordered `>` holds, otherwise the right one.
    ///
    /// The same failure rule as [`Op::FMin`]: `maxss` and the emulator's
    /// `fmax` keep the right operand when the compare does not hold.
    FMax,
}

impl Op {
    /// Returns the C precedence level (higher binds tighter; [`ATOM`] for calls).
    pub(super) fn prec(self) -> u8 {
        match self {
            Op::Or => 3,
            Op::Xor => 4,
            Op::And => 5,
            Op::Shl | Op::Shr | Op::Sar => 8,
            Op::Add | Op::Sub | Op::FAdd | Op::FSub => 9,
            Op::Mul | Op::Div | Op::Rem | Op::SDiv | Op::SRem | Op::FMul | Op::FDiv => 10,
            Op::Rol(_)
            | Op::Ror(_)
            | Op::MulHi(_)
            | Op::SMulHi(_)
            | Op::SMulO(_)
            | Op::UAddO(_)
            | Op::USubO(_)
            | Op::FMin
            | Op::FMax => ATOM,
        }
    }

    /// Tells whether the operator works on IEEE-754 values (never constant-folded as integers).
    pub(super) fn is_float(self) -> bool {
        matches!(
            self,
            Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FMin | Op::FMax
        )
    }

    /// Returns the C operator symbol; empty for the function-style operators.
    pub(super) fn sym(self) -> &'static str {
        match self {
            Op::Add | Op::FAdd => "+",
            Op::Sub | Op::FSub => "-",
            Op::Mul | Op::FMul => "*",
            Op::Div | Op::SDiv | Op::FDiv => "/",
            Op::Rem | Op::SRem => "%",
            Op::And => "&",
            Op::Or => "|",
            Op::Xor => "^",
            Op::Shl => "<<",
            Op::Shr | Op::Sar => ">>",
            Op::Rol(_)
            | Op::Ror(_)
            | Op::MulHi(_)
            | Op::SMulHi(_)
            | Op::SMulO(_)
            | Op::UAddO(_)
            | Op::USubO(_)
            | Op::FMin
            | Op::FMax => "",
        }
    }

    /// Tells whether `a op b == b op a`.
    pub(super) fn commutative(self) -> bool {
        matches!(
            self,
            Op::Add | Op::Mul | Op::And | Op::Or | Op::Xor | Op::FAdd | Op::FMul
        )
    }

    /// Returns the compound-assignment spelling: `x = x op y` reads as `x op= y`.
    ///
    /// # Returns
    ///
    /// The operator text, or `None` for operators C has no compound form for
    /// here (division, arithmetic shift, rotates, wide multiplies).
    pub(super) fn compound(self) -> Option<&'static str> {
        match self {
            Op::Add | Op::FAdd => Some("+="),
            Op::Sub | Op::FSub => Some("-="),
            Op::Mul | Op::FMul => Some("*="),
            Op::FDiv => Some("/="),
            Op::And => Some("&="),
            Op::Or => Some("|="),
            Op::Xor => Some("^="),
            Op::Shl => Some("<<="),
            Op::Shr => Some(">>="),
            Op::Div
            | Op::Rem
            | Op::SDiv
            | Op::SRem
            | Op::Sar
            | Op::Rol(_)
            | Op::Ror(_)
            | Op::MulHi(_)
            | Op::SMulHi(_)
            | Op::SMulO(_)
            | Op::UAddO(_)
            | Op::USubO(_)
            | Op::FMin
            | Op::FMax => None,
        }
    }

    /// Returns the helper a function-style operator prints as.
    ///
    /// # Returns
    ///
    /// The helper, or `None` for an operator C spells (`+`) and for
    /// [`Op::FMin`] and [`Op::FMax`], which print as a select.
    pub(super) fn helper(self) -> Option<Helper> {
        match self {
            Op::Rol(w) => Some(Helper::Rotl(w)),
            Op::Ror(w) => Some(Helper::Rotr(w)),
            Op::MulHi(w) => Some(Helper::MulHi(w)),
            Op::SMulHi(w) => Some(Helper::SMulHi(w)),
            Op::SMulO(w) => Some(Helper::SMulO(w)),
            Op::UAddO(w) => Some(Helper::UAddO(w)),
            Op::USubO(w) => Some(Helper::USubO(w)),
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Rem
            | Op::SDiv
            | Op::SRem
            | Op::And
            | Op::Or
            | Op::Xor
            | Op::Shl
            | Op::Shr
            | Op::Sar
            | Op::FAdd
            | Op::FSub
            | Op::FMul
            | Op::FDiv
            | Op::FMin
            | Op::FMax => None,
        }
    }

    /// Tells whether `a op b == b op a` (the public form of [`Op::commutative`]).
    pub(super) fn is_commutative(self) -> bool {
        self.commutative()
    }

    /// Tells whether constant operands read better in hex (bitwise masks).
    pub(super) fn hex_operands(self) -> bool {
        matches!(self, Op::And | Op::Or | Op::Xor)
    }

    /// Returns the operator family; mixing families gets explicit parentheses
    /// even when C precedence would not need them (`a & b | c`, `a + b << 2`).
    pub(super) fn family(self) -> u8 {
        match self {
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Rem
            | Op::SDiv
            | Op::SRem
            | Op::FAdd
            | Op::FSub
            | Op::FMul
            | Op::FDiv => 0,
            Op::Shl | Op::Shr | Op::Sar => 1,
            Op::And | Op::Or | Op::Xor => 2,
            Op::Rol(_)
            | Op::Ror(_)
            | Op::MulHi(_)
            | Op::SMulHi(_)
            | Op::SMulO(_)
            | Op::UAddO(_)
            | Op::USubO(_)
            | Op::FMin
            | Op::FMax => 3,
        }
    }
}

/// Unary operator of an [`Expr::Un`] node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum UnOp {
    /// Two's-complement negation.
    Neg,
    /// Bitwise not.
    Not,
    /// Byte swap at the operand width.
    Bswap,
    /// Trailing zero count (operand width when zero).
    Tzcnt,
    /// Leading zero count.
    Lzcnt,
    /// Population count.
    Popcnt,
    /// IEEE-754 square root.
    Sqrt,
    /// IEEE-754 absolute value.
    Fabs,
    /// Bit scan forward (index of the lowest set bit).
    Bsf,
    /// Bit scan reverse (index of the highest set bit).
    Bsr,
}

impl UnOp {
    /// Returns the helper the operator prints as, or `None` for the prefix
    /// operators.
    pub(super) fn helper(self) -> Option<Helper> {
        match self {
            UnOp::Neg | UnOp::Not => None,
            UnOp::Bswap => Some(Helper::Bswap),
            UnOp::Tzcnt => Some(Helper::Tzcnt),
            UnOp::Lzcnt => Some(Helper::Lzcnt),
            UnOp::Popcnt => Some(Helper::Popcnt),
            UnOp::Sqrt => Some(Helper::Sqrt),
            UnOp::Fabs => Some(Helper::Fabs),
            UnOp::Bsf => Some(Helper::Bsf),
            UnOp::Bsr => Some(Helper::Bsr),
        }
    }
}

/// x86 condition code, kept in iced's vocabulary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Cc(pub ConditionCode);

impl Cc {
    /// Returns the negated condition (`e` to `ne`, `l` to `ge`, ...).
    pub(super) fn invert(self) -> Cc {
        use ConditionCode as C;
        Cc(match self.0 {
            C::None => C::None,
            C::o => C::no,
            C::no => C::o,
            C::b => C::ae,
            C::ae => C::b,
            C::e => C::ne,
            C::ne => C::e,
            C::be => C::a,
            C::a => C::be,
            C::s => C::ns,
            C::ns => C::s,
            C::p => C::np,
            C::np => C::p,
            C::l => C::ge,
            C::ge => C::l,
            C::le => C::g,
            C::g => C::le,
        })
    }

    /// Tells whether the condition compares as signed integers.
    pub(super) fn signed(self) -> bool {
        use ConditionCode as C;
        matches!(self.0, C::l | C::ge | C::le | C::g)
    }

    /// Returns the C relational operator for a compare.
    ///
    /// # Returns
    ///
    /// `==`, `!=`, `<`, `>=`, `<=` or `>`; `None` for flag tests that are not
    /// comparisons (overflow, parity, no condition).
    pub(super) fn rel(self) -> Option<&'static str> {
        use ConditionCode as C;
        Some(match self.0 {
            C::e => "==",
            C::ne => "!=",
            C::b | C::l => "<",
            C::ae | C::ge => ">=",
            C::be | C::le => "<=",
            C::a | C::g => ">",
            C::s => "<",
            C::ns => ">=",
            C::None | C::o | C::no | C::p | C::np => return None,
        })
    }
}

/// What the flags register holds symbolically at a conditional instruction.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Flags {
    /// `cmp l, r` at this operand width.
    Cmp(Expr, Expr, u8),
    /// A floating-point compare of the two values at this width: the same
    /// records an integer compare keeps, with the order the flags answer
    /// the floating-point one, an unordered pair apart from every ordered
    /// one.
    ///
    /// The compare's being floating-point is a fact of the instruction
    /// that set the flags, which the values alone no longer say once a
    /// store protects its operands into temporaries.
    Float(Expr, Expr, u8),
    /// A floating-point compare of the two values at this width, asked one
    /// predicate: the code `ne` holds where the predicate does and `e`
    /// where it does not, so inverting the condition negates the predicate.
    ///
    /// It names the predicates no code over [`Flags::Float`] asks, such as
    /// the ordered equality arm64's `eq` and the lane `cmpsd` writes test.
    FCmp(FPred, Expr, Expr, u8),
    /// `test l, r` at this operand width.
    Test(Expr, Expr, u8),
    /// Flags set by an arithmetic result of this width (`dec`, `shl`, ...).
    Result(Expr, u8),
    /// `add l, r` at this width (carry and overflow are recoverable).
    Add(Expr, Expr, u8),
    /// CF = OF = (expr != 0): `bt`, the overflow of `mul`/`imul`, and the
    /// carry out of `adc`/`sbb` (whose OF is not modeled).
    Carry(Expr),
    /// A shift by a constant: the result (for ZF/SF conditions, as
    /// [`Flags::Result`]) and the bit shifted out last (CF, as
    /// [`Flags::Carry`]).
    Shift(Expr, u8, Expr),
    /// The condition code holds exactly when the value is nonzero: the
    /// truth a join's predecessors each computed into one shared temporary.
    Truth(Expr, Cc),
    /// Set in another block or by an unmodeled instruction.
    Unknown,
}

impl Flags {
    /// Tells whether any operand reads a text variable satisfying `pred`.
    ///
    /// # Arguments
    ///
    /// * `pred` - Predicate over the variables read.
    pub(super) fn any_var(&self, pred: &dyn Fn(Key) -> bool) -> bool {
        match self {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => l.any_var(pred) || r.any_var(pred),
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.any_var(pred),
            Flags::Shift(e, _, c) => e.any_var(pred) || c.any_var(pred),
            Flags::Unknown => false,
        }
    }

    /// Returns the float compare predicate a condition code asks of these
    /// flags.
    ///
    /// # Arguments
    ///
    /// * `cc` - The code: any [`FPred::of_flags`] decides over
    ///   [`Flags::Float`], `ne` (the predicate) or `e` (its negation) over
    ///   [`Flags::FCmp`].
    ///
    /// # Returns
    ///
    /// The predicate, or `None` for other flags or a code that asks them
    /// nothing.
    pub(super) fn fpred(&self, cc: Cc) -> Option<FPred> {
        match self {
            Flags::Float(..) => FPred::of_flags(cc.0),
            Flags::FCmp(p, ..) => match cc.0 {
                ConditionCode::ne => Some(*p),
                ConditionCode::e => Some(p.negate()),
                ConditionCode::None
                | ConditionCode::o
                | ConditionCode::no
                | ConditionCode::b
                | ConditionCode::ae
                | ConditionCode::be
                | ConditionCode::a
                | ConditionCode::s
                | ConditionCode::ns
                | ConditionCode::p
                | ConditionCode::np
                | ConditionCode::l
                | ConditionCode::ge
                | ConditionCode::le
                | ConditionCode::g => None,
            },
            Flags::Cmp(..)
            | Flags::Test(..)
            | Flags::Result(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Shift(..)
            | Flags::Truth(..)
            | Flags::Unknown => None,
        }
    }

    /// Tells whether any operand reads text variable `k`.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    pub(super) fn mentions(&self, k: Key) -> bool {
        self.any_var(&|v| v == k)
    }
}

/// A branch condition: a condition code applied to symbolic flags.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Cond {
    /// The condition code of the `jcc`/`setcc`/`cmovcc`.
    pub cc: Cc,
    /// What set the flags.
    pub flags: Flags,
}

/// The truth of a condition code on two floating-point values.
///
/// The code a float compare leaves (`e`, `ne`, `b`, `ae`, `a`, `be`, `p`,
/// `np`) answers the pair's order and unordered test, and no other code
/// does.
///
/// # Arguments
///
/// * `cc` - The condition code.
/// * `a` - The left value.
/// * `b` - The right value.
///
/// # Returns
///
/// The truth, or `None` for a code a float compare does not decide.
pub(super) fn float_cc(cc: ConditionCode, a: f64, b: f64) -> Option<bool> {
    FPred::of_flags(cc).map(|p| p.holds(a, b))
}

/// A symbolic value.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Expr {
    /// A 64-bit constant (narrower results are stored masked).
    Const(u64),
    /// The current text value of a variable.
    Var(Key),
    /// Quoted string literal found at a resolved address (capped, sanitized).
    Str(String),
    /// Stack address relative to the entry rsp.
    Sp(i64),
    /// A binary operation.
    Bin(Op, Box<Expr>, Box<Expr>),
    /// A unary operation.
    Un(UnOp, Box<Expr>),
    /// A memory read of the given type at the given address.
    Deref(Box<Expr>, Ty),
    /// 0/1 truth value of a condition (`setcc`).
    Cond(Box<Cond>),
    /// `cond ? a : b` (`cmovcc`).
    Ternary(Box<Cond>, Box<Expr>, Box<Expr>),
    /// Sign-extend the low `bits` of the operand to 64 bits.
    Sext(Box<Expr>, u8),
    /// Convert the value to another type (`(float)x`, `(int32_t)x`).
    Cast(Box<Expr>, Ty),
    /// The same bits read as another type of the same width: `movd eax,
    /// xmm0`, or a float stored and loaded back as an integer.
    Bitcast(Box<Expr>, Ty),
    /// A packed vector operation by the instruction's name, which
    /// [`super::vector`] spells as C; constant arguments render in hex
    /// (shuffle and blend masks).
    Call(String, Vec<Expr>),
    /// A helper call: an operation C has no operator for, from the closed
    /// vocabulary of [`Helper`].
    Helper(Helper, Vec<Expr>),
    /// An IEEE-754 constant: its bit pattern and type.
    FConst(u64, Ty),
}

/// Precedence of an atom (name, constant, call): never parenthesized.
pub(super) const ATOM: u8 = 13;
/// Precedence of the prefix operators (`-`, `~`, `*`, casts).
pub(super) const UNARY: u8 = 12;
/// Precedence of a `&&` or `||` chain: below every operator a value takes
/// part in, so any operand position parenthesizes it.
pub(super) const LOGICAL: u8 = 1;

/// Returns the mask of the low `bits` bits (all ones for 64 or more).
///
/// # Arguments
///
/// * `bits` - Width in bits.
pub(super) fn mask_bits(bits: u8) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// Sign-extends the low `bits` bits of `v` to 64 bits.
///
/// # Arguments
///
/// * `v` - The value; higher bits are ignored.
/// * `bits` - Width of the signed field.
pub(super) fn sext(v: u64, bits: u8) -> u64 {
    if bits >= 64 {
        return v;
    }
    let shift = 64 - u32::from(bits);
    ((v << shift).cast_signed() >> shift).cast_unsigned()
}

/// The low 64 bits of a double-width product.
///
/// # Arguments
///
/// * `v` - The product.
#[expect(
    clippy::cast_possible_truncation,
    reason = "the low bits are the point"
)]
const fn lo64(v: u128) -> u64 {
    v as u64
}

impl Expr {
    /// Whether this is a logical shift right by a constant, the shape of a
    /// signed quotient's sign-bit fix.
    fn is_shift_fix(&self) -> bool {
        matches!(self, Expr::Bin(Op::Shr, _, amount) if const_of(amount).is_some())
    }

    /// Tells whether the expression is the constant zero.
    pub(super) fn is_zero(&self) -> bool {
        matches!(self, Expr::Const(0))
    }

    /// Tells whether the expression reads exactly text variable `key`.
    ///
    /// # Arguments
    ///
    /// * `key` - A register, or a slot through its unknown-value form
    ///   (`Deref(Sp(k))` names slot `k`).
    pub(super) fn is_var(&self, key: Key) -> bool {
        match (self, key) {
            (Expr::Var(v), k) => *v == k,
            (Expr::Deref(a, _), Key::Slot(o)) => matches!(**a, Expr::Sp(k) if k == o),
            _ => false,
        }
    }

    /// Returns the node count, which drives when a value is written out to a named variable.
    pub(super) fn size(&self) -> usize {
        match self {
            Expr::Const(_) | Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => 1,
            Expr::Bin(_, l, r) => 1 + l.size() + r.size(),
            Expr::Un(_, e)
            | Expr::Deref(e, _)
            | Expr::Sext(e, _)
            | Expr::Cast(e, _)
            | Expr::Bitcast(e, _) => 1 + e.size(),
            Expr::Call(_, args) | Expr::Helper(_, args) => {
                1 + args.iter().map(Expr::size).sum::<usize>()
            }
            Expr::Cond(c) => 1 + c.size(),
            Expr::Ternary(c, a, b) => 1 + c.size() + a.size() + b.size(),
        }
    }

    /// Tells whether the expression reads text variable `k`.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    pub(super) fn mentions(&self, k: Key) -> bool {
        self.any_var(&|v| v == k)
    }

    /// Tells whether the expression reads a text variable satisfying `pred`.
    ///
    /// An unknown slot value (`Deref(Sp(k))`) counts as reading slot `k`.
    ///
    /// # Arguments
    ///
    /// * `pred` - Predicate over the variables read.
    pub(super) fn any_var(&self, pred: &dyn Fn(Key) -> bool) -> bool {
        match self {
            Expr::Var(v) => pred(*v),
            Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => false,
            Expr::Bin(_, l, r) => l.any_var(pred) || r.any_var(pred),
            Expr::Deref(a, _) if matches!(**a, Expr::Sp(_)) => match **a {
                Expr::Sp(k) => pred(Key::Slot(k)),
                _ => false,
            },
            Expr::Un(_, e)
            | Expr::Deref(e, _)
            | Expr::Sext(e, _)
            | Expr::Cast(e, _)
            | Expr::Bitcast(e, _) => e.any_var(pred),
            Expr::Call(_, args) | Expr::Helper(_, args) => args.iter().any(|a| a.any_var(pred)),
            Expr::Cond(c) => c.any_var(pred),
            Expr::Ternary(c, a, b) => c.any_var(pred) || a.any_var(pred) || b.any_var(pred),
        }
    }

    /// Tells whether the expression holds a high multiply.
    ///
    /// Such a value is half of a division idiom: on its own it means
    /// nothing, and only folding it with the shift and sign fix that
    /// follow recovers the `x / d` it stands for, so it must stay
    /// symbolic until those arrive.
    pub(super) fn partial_idiom(&self) -> bool {
        match self {
            Expr::Bin(Op::MulHi(_) | Op::SMulHi(_), ..) => true,
            Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Var(_) | Expr::FConst(..) => false,
            Expr::Bin(_, l, r) => l.partial_idiom() || r.partial_idiom(),
            Expr::Un(_, e)
            | Expr::Deref(e, _)
            | Expr::Sext(e, _)
            | Expr::Cast(e, _)
            | Expr::Bitcast(e, _) => e.partial_idiom(),
            Expr::Call(_, args) | Expr::Helper(_, args) => args.iter().any(Expr::partial_idiom),
            Expr::Cond(_) => false,
            Expr::Ternary(_, a, b) => a.partial_idiom() || b.partial_idiom(),
        }
    }

    /// Tells whether the expression reads memory a store or a call could change.
    ///
    /// Stack slots are locals, not aliasable memory, so a slot read
    /// does not count.
    pub(super) fn mem_dependent(&self) -> bool {
        match self {
            Expr::Deref(a, _) => !matches!(**a, Expr::Sp(_)),
            Expr::Var(Key::Global(..)) => true,
            Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Var(_) | Expr::FConst(..) => false,
            Expr::Bin(_, l, r) => l.mem_dependent() || r.mem_dependent(),
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) | Expr::Bitcast(e, _) => {
                e.mem_dependent()
            }
            Expr::Call(_, args) | Expr::Helper(_, args) => args.iter().any(Expr::mem_dependent),
            Expr::Cond(c) => c.mem_dependent(),
            Expr::Ternary(c, a, b) => c.mem_dependent() || a.mem_dependent() || b.mem_dependent(),
        }
    }

    /// Returns the lowest stack offset whose address appears in the expression.
    pub(super) fn min_sp(&self) -> Option<i64> {
        match self {
            Expr::Sp(k) => Some(*k),
            Expr::Const(_) | Expr::Str(_) | Expr::Var(_) | Expr::FConst(..) => None,
            Expr::Bin(_, l, r) => min_opt(l.min_sp(), r.min_sp()),
            Expr::Un(_, e)
            | Expr::Deref(e, _)
            | Expr::Sext(e, _)
            | Expr::Cast(e, _)
            | Expr::Bitcast(e, _) => e.min_sp(),
            Expr::Call(_, args) | Expr::Helper(_, args) => {
                args.iter().filter_map(Expr::min_sp).min()
            }
            Expr::Cond(c) => c.min_sp(),
            Expr::Ternary(c, a, b) => min_opt(c.min_sp(), min_opt(a.min_sp(), b.min_sp())),
        }
    }

    /// Replaces every subtree equal to `from` with `to`.
    ///
    /// # Arguments
    ///
    /// * `from` - The subtree to find (compared structurally).
    /// * `to` - Its replacement.
    pub(super) fn subst(&self, from: &Expr, to: &Expr) -> Expr {
        if self == from {
            return to.clone();
        }
        match self {
            Expr::Const(_) | Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => {
                self.clone()
            }
            Expr::Bin(op, l, r) => Expr::Bin(
                *op,
                Box::new(l.subst(from, to)),
                Box::new(r.subst(from, to)),
            ),
            Expr::Un(op, e) => Expr::Un(*op, Box::new(e.subst(from, to))),
            Expr::Deref(e, t) => Expr::Deref(Box::new(e.subst(from, to)), *t),
            Expr::Sext(e, b) => Expr::Sext(Box::new(e.subst(from, to)), *b),
            Expr::Cast(e, t) => Expr::Cast(Box::new(e.subst(from, to)), *t),
            Expr::Bitcast(e, t) => Expr::Bitcast(Box::new(e.subst(from, to)), *t),
            Expr::Call(f, args) => {
                Expr::Call(f.clone(), args.iter().map(|a| a.subst(from, to)).collect())
            }
            Expr::Helper(h, args) => {
                Expr::Helper(*h, args.iter().map(|a| a.subst(from, to)).collect())
            }
            Expr::Cond(c) => Expr::Cond(Box::new(c.subst(from, to))),
            Expr::Ternary(c, a, b) => Expr::Ternary(
                Box::new(c.subst(from, to)),
                Box::new(a.subst(from, to)),
                Box::new(b.subst(from, to)),
            ),
        }
    }

    /// Builds a memory read of `ty` at `addr`.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address expression.
    /// * `ty` - The access type.
    pub(super) fn deref(addr: Expr, ty: Ty) -> Expr {
        Expr::Deref(Box::new(addr), ty)
    }

    /// Tells whether the value is floating point by its own shape: a float
    /// constant, load or conversion, a float operation, a C library call
    /// returning a float, or a vector or x87 register.
    ///
    /// A comparison of such a value is a floating-point one, whose
    /// unordered outcome (a NaN operand) sets the flags `comiss` and
    /// `fcomi` leave apart from any ordered one.
    pub(super) fn is_float(&self) -> bool {
        match self {
            Expr::FConst(..) => true,
            Expr::Deref(_, ty) | Expr::Cast(_, ty) | Expr::Bitcast(_, ty) => {
                matches!(ty, Ty::F32 | Ty::F64)
            }
            Expr::Bin(op, ..) => op.is_float(),
            Expr::Un(UnOp::Sqrt | UnOp::Fabs, _) => true,
            Expr::Un(UnOp::Neg, inner) => inner.is_float(),
            Expr::Var(Key::Reg(r)) => {
                r.is_vector_register() || (*r >= Register::ST0 && *r <= Register::ST7)
            }
            Expr::Call(f, _) => {
                matches!(f.as_str(), "__lane_f32" | "__lane_f64")
                    || super::lift_a64::mem::libm_width(f).is_some()
            }
            Expr::Helper(h, _) => *h == Helper::Fabs,
            Expr::Ternary(_, a, b) => a.is_float() || b.is_float(),
            Expr::Const(_)
            | Expr::Var(_)
            | Expr::Str(_)
            | Expr::Sp(_)
            | Expr::Un(..)
            | Expr::Cond(_)
            | Expr::Sext(..) => false,
        }
    }
}

/// The width a select carries when either arm has one.
///
/// Both arms sized: the wider. One sized: that width, so a bare register
/// next to a float does not drop the select's width. Neither sized: none,
/// and a select of two bare registers stays an integer the write cuts.
///
/// # Arguments
///
/// * `a` - One arm's width.
/// * `b` - The other's.
pub(super) fn either_width(a: Option<u8>, b: Option<u8>) -> Option<u8> {
    match (a, b) {
        (Some(l), Some(r)) => Some(l.max(r)),
        (Some(w), None) | (None, Some(w)) => Some(w),
        (None, None) => None,
    }
}

/// Returns the smaller of two optional offsets, ignoring `None`.
///
/// # Arguments
///
/// * `a` - First offset.
/// * `b` - Second offset.
fn min_opt(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, None) => a,
        (None, b) => b,
    }
}

impl Cond {
    /// The lowest frame offset the flags operands read through a computed
    /// address from ([`Expr::frame_read_base`]).
    fn frame_read_base(&self) -> Option<i64> {
        match &self.flags {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => min_opt(l.frame_read_base(), r.frame_read_base()),
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.frame_read_base(),
            Flags::Shift(e, _, c) => min_opt(e.frame_read_base(), c.frame_read_base()),
            Flags::Unknown => None,
        }
    }

    /// Returns the lowest stack offset whose address appears in the flags operands.
    fn min_sp(&self) -> Option<i64> {
        match &self.flags {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => min_opt(l.min_sp(), r.min_sp()),
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.min_sp(),
            Flags::Shift(e, _, c) => min_opt(e.min_sp(), c.min_sp()),
            Flags::Unknown => None,
        }
    }

    /// Returns the float compare predicate the condition asks, with its
    /// operands and width.
    ///
    /// # Returns
    ///
    /// The predicate, the left and right values and the width, or `None`
    /// when the flags are no float compare or the code asks a float
    /// compare nothing ([`FPred::of_flags`]).
    pub(super) fn fcmp(&self) -> Option<(FPred, &Expr, &Expr, u8)> {
        match &self.flags {
            Flags::Float(l, r, w) | Flags::FCmp(_, l, r, w) => {
                Some((self.flags.fpred(self.cc)?, l, r, *w))
            }
            Flags::Cmp(..)
            | Flags::Test(..)
            | Flags::Result(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Shift(..)
            | Flags::Truth(..)
            | Flags::Unknown => None,
        }
    }

    /// Returns the negated condition over the same flags.
    pub(super) fn invert(&self) -> Cond {
        Cond {
            cc: self.cc.invert(),
            flags: self.flags.clone(),
        }
    }

    /// Folds an equality test of `x - c1` or `x + c1` against a constant onto
    /// `x` (`a - 1 == 1` is `a == 2`, `test` of `a - 3` against itself is
    /// `a == 3`, and the zero flag `dec` leaves on `a - 3` is `a == 3`), the
    /// shape `dec`/`sub` compare ladders leave.
    ///
    /// # Returns
    ///
    /// The folded condition, or `None` when the condition is not an equality
    /// (ordered comparisons depend on the wrapped value) or has no such
    /// operand.
    pub(super) fn simplify(&self) -> Option<Cond> {
        use ConditionCode as C;
        if !matches!(self.cc.0, C::e | C::ne) {
            return None;
        }
        let (l, c2, bits) = match &self.flags {
            Flags::Cmp(l, Expr::Const(c2), bits) => (l, *c2, *bits),
            Flags::Test(l, r, bits) if l == r => (l, 0, *bits),
            Flags::Result(e, bits) => (e, 0, *bits),
            Flags::Add(x, Expr::Const(c1), bits) if !matches!(x, Expr::Const(_)) => {
                return Some(Cond {
                    cc: self.cc,
                    flags: Flags::Cmp(
                        x.clone(),
                        Expr::Const(c1.wrapping_neg() & mask_bits(*bits)),
                        *bits,
                    ),
                });
            }
            _ => return None,
        };
        let Expr::Bin(op @ (Op::Sub | Op::Add), x, c1) = l else {
            return None;
        };
        let Expr::Const(c1) = **c1 else {
            return None;
        };
        let target = if *op == Op::Sub {
            c1.wrapping_add(c2)
        } else {
            c2.wrapping_sub(c1)
        };
        Some(Cond {
            cc: self.cc,
            flags: Flags::Cmp((**x).clone(), Expr::Const(target & mask_bits(bits)), bits),
        })
    }

    /// Finds the boolean an `e`/`ne` test of these flags is really about.
    ///
    /// # Returns
    ///
    /// The inner condition when the flags come from testing a 0/1 value
    /// (`test al, al` after `setcc`, `cmp al, 0`, or the result itself), else
    /// `None`.
    pub(super) fn bool_operand(&self) -> Option<&Cond> {
        match self.tested()? {
            Expr::Cond(c) => Some(c),
            _ => None,
        }
    }

    /// Returns the value an `e`/`ne` test of these flags compares with
    /// zero: what `test x, x`, `test x, 1` or `cmp x, 0` reads, or the
    /// result an operation set the flags from.
    ///
    /// # Returns
    ///
    /// The value, or `None` for flags that compare anything else.
    pub(super) fn tested(&self) -> Option<&Expr> {
        match &self.flags {
            Flags::Test(l, r, _) if l == r || matches!(r, Expr::Const(1)) => Some(l),
            Flags::Result(e, _) | Flags::Shift(e, _, _) => Some(e),
            Flags::Cmp(l, Expr::Const(0), _) => Some(l),
            Flags::Cmp(..)
            | Flags::Float(..)
            | Flags::FCmp(..)
            | Flags::Test(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Truth(..)
            | Flags::Unknown => None,
        }
    }

    /// Returns the node count of the flags operands.
    pub(super) fn size(&self) -> usize {
        match &self.flags {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => l.size() + r.size(),
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.size(),
            Flags::Shift(e, _, c) => e.size() + c.size(),
            Flags::Unknown => 1,
        }
    }

    /// Tells whether any flags operand reads a text variable satisfying `pred`.
    ///
    /// # Arguments
    ///
    /// * `pred` - Predicate over the variables read.
    pub(super) fn any_var(&self, pred: &dyn Fn(Key) -> bool) -> bool {
        self.flags.any_var(pred)
    }

    /// Tells whether any flags operand reads aliasable memory.
    fn mem_dependent(&self) -> bool {
        match &self.flags {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => l.mem_dependent() || r.mem_dependent(),
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.mem_dependent(),
            Flags::Shift(e, _, c) => e.mem_dependent() || c.mem_dependent(),
            Flags::Unknown => false,
        }
    }

    /// Replaces every subtree equal to `from` with `to` in the flags operands.
    ///
    /// # Arguments
    ///
    /// * `from` - The subtree to find.
    /// * `to` - Its replacement.
    pub(super) fn subst(&self, from: &Expr, to: &Expr) -> Cond {
        let flags = match &self.flags {
            Flags::Cmp(l, r, b) => Flags::Cmp(l.subst(from, to), r.subst(from, to), *b),
            Flags::Float(l, r, b) => Flags::Float(l.subst(from, to), r.subst(from, to), *b),
            Flags::FCmp(p, l, r, b) => Flags::FCmp(*p, l.subst(from, to), r.subst(from, to), *b),
            Flags::Test(l, r, b) => Flags::Test(l.subst(from, to), r.subst(from, to), *b),
            Flags::Result(e, b) => Flags::Result(e.subst(from, to), *b),
            Flags::Add(l, r, b) => Flags::Add(l.subst(from, to), r.subst(from, to), *b),
            Flags::Carry(e) => Flags::Carry(e.subst(from, to)),
            Flags::Shift(e, b, c) => Flags::Shift(e.subst(from, to), *b, c.subst(from, to)),
            Flags::Truth(e, cc) => Flags::Truth(e.subst(from, to), *cc),
            Flags::Unknown => Flags::Unknown,
        };
        Cond { cc: self.cc, flags }
    }

    /// Evaluates the condition when every operand is a constant.
    ///
    /// # Returns
    ///
    /// The truth value, or `None` when an operand is symbolic or the
    /// condition code is not decidable from the recorded flags.
    pub(super) fn eval(&self) -> Option<bool> {
        if let Some(s) = self.simplify() {
            return s.eval();
        }
        let (l, r, bits) = match &self.flags {
            Flags::Cmp(Expr::Const(l), Expr::Const(r), bits) => (*l, *r, *bits),
            Flags::Float(Expr::Const(l), Expr::Const(r), bits)
            | Flags::FCmp(_, Expr::Const(l), Expr::Const(r), bits) => {
                let of = |v: u64| {
                    if *bits == 32 {
                        f64::from(f32::from_bits(lo32(v)))
                    } else {
                        f64::from_bits(v)
                    }
                };
                return Some(self.fcmp()?.0.holds(of(*l), of(*r)));
            }
            Flags::Test(Expr::Const(l), Expr::Const(r), bits) => (l & r, 0, *bits),
            Flags::Result(Expr::Const(e), bits) => (*e, 0, *bits),
            Flags::Shift(e, bits, c) => {
                use ConditionCode as C;
                match (self.cc.0, e, c) {
                    (C::b, _, Expr::Const(c)) => return Some(*c != 0),
                    (C::ae, _, Expr::Const(c)) => return Some(*c == 0),
                    (C::be, Expr::Const(e), Expr::Const(c)) => {
                        return Some(*c != 0 || e & mask_bits(*bits) == 0);
                    }
                    (C::a, Expr::Const(e), Expr::Const(c)) => {
                        return Some(*c == 0 && e & mask_bits(*bits) != 0);
                    }
                    (C::b | C::o | C::ae | C::no | C::be | C::a, _, _) => return None,
                    (_, Expr::Const(e), _) => (*e, 0, *bits),
                    _ => return None,
                }
            }
            Flags::Carry(Expr::Const(c)) => {
                use ConditionCode as C;
                return match self.cc.0 {
                    C::b | C::o => Some(*c != 0),
                    C::ae | C::no => Some(*c == 0),
                    _ => None,
                };
            }
            Flags::Add(Expr::Const(l), Expr::Const(r), bits) => {
                use ConditionCode as C;
                let m = mask_bits(*bits);
                let (lu, ru) = (l & m, r & m);
                let sum = lu.wrapping_add(ru) & m;
                let (ls, rs) = (sext(lu, *bits).cast_signed(), sext(ru, *bits).cast_signed());
                let ss = sext(sum, *bits).cast_signed();
                let signed_ovf = (ls < 0) == (rs < 0) && (ss < 0) != (ls < 0);
                let true_sum = i128::from(ls) + i128::from(rs);
                return match self.cc.0 {
                    C::e => Some(sum == 0),
                    C::ne => Some(sum != 0),
                    C::s => Some(ss < 0),
                    C::ns => Some(ss >= 0),
                    C::l => Some(true_sum < 0),
                    C::ge => Some(true_sum >= 0),
                    C::le => Some(true_sum <= 0),
                    C::g => Some(true_sum > 0),
                    C::b => Some(lu.checked_add(ru).is_none_or(|s| s > m)),
                    C::ae => Some(lu.checked_add(ru).is_some_and(|s| s <= m)),
                    C::o => Some(signed_ovf),
                    C::no => Some(!signed_ovf),
                    C::None | C::be | C::a | C::p | C::np => None,
                };
            }
            Flags::Truth(Expr::Const(c), tcc) => {
                return if self.cc == *tcc {
                    Some(*c != 0)
                } else if self.cc == tcc.invert() {
                    Some(*c == 0)
                } else {
                    None
                };
            }
            Flags::Cmp(..)
            | Flags::Float(..)
            | Flags::FCmp(..)
            | Flags::Test(..)
            | Flags::Result(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Truth(..)
            | Flags::Unknown => return None,
        };
        let m = mask_bits(bits);
        let (lu, ru) = (l & m, r & m);
        let (ls, rs) = (sext(lu, bits).cast_signed(), sext(ru, bits).cast_signed());
        use ConditionCode as C;
        Some(match self.cc.0 {
            C::e => lu == ru,
            C::ne => lu != ru,
            C::b => lu < ru,
            C::ae => lu >= ru,
            C::be => lu <= ru,
            C::a => lu > ru,
            C::l => ls < rs,
            C::ge => ls >= rs,
            C::le => ls <= rs,
            C::g => ls > rs,
            C::s | C::ns => {
                let top = lu.wrapping_sub(ru) & m & (1u64 << (bits.clamp(1, 64) - 1)) != 0;
                (self.cc.0 == C::s) == top
            }
            C::None | C::o | C::no | C::p | C::np => return None,
        })
    }
}

/// Returns the C signed integer type of `bits` bits.
///
/// # Arguments
///
/// * `bits` - Width in bits; rounded up to the next C type.
pub(super) fn signed_ty(bits: u8) -> &'static str {
    match bits {
        0..=8 => "int8_t",
        9..=16 => "int16_t",
        17..=32 => "int32_t",
        _ => "int64_t",
    }
}

/// Splits `x`, `x * c` or `x << k` into `(x, factor)`.
///
/// # Arguments
///
/// * `e` - The expression.
pub(super) fn term_of(e: &Expr) -> (&Expr, u64) {
    match e {
        Expr::Bin(Op::Mul, a, b) => match (const_of(a), const_of(b)) {
            (None, Some(c)) => (a, c),
            (Some(c), None) => (b, c),
            _ => (e, 1),
        },
        Expr::Bin(Op::Shl, a, k) => match const_of(k) {
            Some(k) if k < 64 => (a, 1u64 << k),
            _ => (e, 1),
        },
        _ => (e, 1),
    }
}

/// Combines like terms: `x + x`, `x + x * c`, `x * a + x * b` and
/// `x * a - x * b` into one product, and `(x * a) * b` into `x * (a * b)`.
///
/// Wrapping arithmetic makes every one exact at any width. This is how
/// `lea` chains (`x + x * 4`) read as the multiply they are.
///
/// # Arguments
///
/// * `op` - The operator being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Operand width.
///
/// # Returns
///
/// The combined product, or `None` when the operands share no term.
fn like_terms(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    let m = mask_bits(bits);
    let product = |x: &Expr, c: u64| -> Expr {
        match c & m {
            0 => Expr::Const(0),
            1 => x.clone(),
            c => Expr::Bin(Op::Mul, Box::new(x.clone()), Box::new(Expr::Const(c))),
        }
    };
    match op {
        Op::Add | Op::Sub => {
            let (x, a) = term_of(l);
            let (y, b) = term_of(r);
            if x != y || matches!(x, Expr::Const(_)) || (a == 1 && b == 1 && op == Op::Sub) {
                return None;
            }
            let c = if op == Op::Add {
                a.wrapping_add(b)
            } else {
                a.wrapping_sub(b)
            };
            Some(product(x, c))
        }
        Op::Mul => {
            let (x, a) = term_of(l);
            let b = const_of(r)?;
            (a != 1).then(|| product(x, a.wrapping_mul(b)))
        }
        _ => None,
    }
}

/// The constant an expression is, if it is one.
///
/// # Arguments
///
/// * `e` - The expression.
fn const_of(e: &Expr) -> Option<u64> {
    match e {
        Expr::Const(c) => Some(*c),
        _ => None,
    }
}

/// Splits a high multiply into `(width, magic, other operand)` when one side
/// is a constant.
///
/// An unsigned division's magic multiply is `mul`'s and a signed one's is
/// `imul`'s, so each idiom asks for its own.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `signed` - Match the signed high half rather than the unsigned.
fn mulhi_of(e: &Expr, signed: bool) -> Option<(u8, u64, &Expr)> {
    let Expr::Bin(Op::MulHi(w) | Op::SMulHi(w), a, b) = e else {
        return None;
    };
    if signed != matches!(e, Expr::Bin(Op::SMulHi(_), ..)) {
        return None;
    }
    match (const_of(a), const_of(b)) {
        (Some(m), None) => Some((*w, m, b)),
        (None, Some(m)) => Some((*w, m, a)),
        _ => None,
    }
}

/// The divisor whose magic multiplier and shift these are.
///
/// A compiler replaces `x / d` with the high half of `x * M` shifted right
/// by `s` more bits, where `M` is `2^(w + s) / d` rounded up (or rounded
/// down plus one). Given `M` and `s`, `d` is that quotient rounded, and it
/// counts only when recomputing the magic from it gives `M` back and the
/// product stands in for the quotient on every `w`-bit dividend
/// ([`exact_below`]): a shift too short for the divisor leaves the right
/// magic off by one just below the multiples of `d` near the top, the
/// shift a compiler never picks.
///
/// # Arguments
///
/// * `w` - Operand width in bits.
/// * `m` - The magic multiplier.
/// * `s` - The shift after the high half.
fn magic_divisor(w: u8, m: u64, s: u64) -> Option<u64> {
    wide_magic_divisor(w, u128::from(m & mask_bits(w)), s)
}

/// [`magic_divisor`] for a magic that may carry one bit more than the width.
///
/// # Arguments
///
/// * `w` - Operand width in bits.
/// * `m` - The magic multiplier, at most `w + 1` bits.
/// * `s` - The shift after the high half.
fn wide_magic_divisor(w: u8, m: u128, s: u64) -> Option<u64> {
    let (d, total) = magic_candidate(w, m, s)?;
    exact_below(m, d, total, (1u128 << w) - 1, false).then(|| u64::try_from(d).ok())?
}

/// The divisor a signed quotient's magic multiplier and shift stand for.
///
/// The quotient is the high half of the signed product with `M`, plus the
/// dividend when the compiler stored `M` negative (the multiplier is then
/// `M + 2^w`), shifted right by `s`, plus one for a negative dividend. That
/// is `x / d` rounded toward zero on every `w`-bit dividend only when `M`
/// has the sign its shape expects (the other sign multiplies by something
/// else entirely), the product never reaches the next quotient on a
/// nonnegative dividend, and on a negative one it overshoots by more than
/// nothing and at most one ([`exact_below`]): an exact multiple rounded
/// down and then raised by one comes out one too large.
///
/// # Arguments
///
/// * `w` - Operand width in bits.
/// * `m` - The magic multiplier as stored.
/// * `s` - The shift after the high half.
/// * `negative` - The shape adds the dividend back, as a negative magic's
///   does.
fn signed_magic_divisor(w: u8, m: u64, s: u64, negative: bool) -> Option<u64> {
    let m = u128::from(m & mask_bits(w));
    let (d, total) = magic_candidate(w, m, s).filter(|_| negative == (m >> (w - 1) == 1))?;
    let half = 1u128 << (w - 1);
    let exact = m * d > 1u128 << total
        && exact_below(m, d, total, half - 1, false)
        && exact_below(m, d, total, half, true);
    exact.then(|| u64::try_from(d).ok())?
}

/// The divisor a magic multiplier and shift were computed from, and the
/// total shift: `2^(w + s) / M` rounded, when the magic recomputed from it
/// is `M` again.
///
/// # Arguments
///
/// * `w` - Operand width in bits.
/// * `m` - The magic multiplier, at most `w + 1` bits.
/// * `s` - The shift after the high half.
fn magic_candidate(w: u8, m: u128, s: u64) -> Option<(u128, u32)> {
    let total = u32::from(w).checked_add(u32::try_from(s).ok()?)?;
    if total >= 128 || w == 0 || m >> (w + 1) != 0 {
        return None;
    }
    let pow: u128 = 1u128 << total;
    if m < 2 {
        return None;
    }
    let d = (pow + m / 2) / m;
    if d < 2 || d >= (1u128 << (w - 1)) {
        return None;
    }
    let ceil = pow.div_ceil(d);
    let floor_plus = pow / d + 1;
    (m == ceil || m == floor_plus).then_some((d, total))
}

/// Tells whether `m / 2^p` stands in for `1 / d` on every `n` up to `top`.
///
/// It does when `floor(m * n / 2^p)` is `floor(n / d)`, or, `closed`, when
/// the product rounded up is at most one more, the rounding a negative
/// dividend takes. With `e = m * d - 2^p`, never negative, the product overshoots `n / d`
/// by `e * n / (d * 2^p)`, and the quotient holds while that and the
/// remainder's `r / d` stay below one (at most one, `closed`). The
/// overshoot grows with `n` within each remainder, so the largest `n` of
/// each decides, and of those `top` and the largest `n` of remainder
/// `d - 1` cover the rest.
///
/// # Arguments
///
/// * `m` - The multiplier.
/// * `d` - The divisor, at least 2.
/// * `p` - The total shift, below 128.
/// * `top` - The largest dividend.
/// * `closed` - Allow the overshoot to reach the next quotient exactly.
fn exact_below(m: u128, d: u128, p: u32, top: u128, closed: bool) -> bool {
    let Some(e) = m.checked_mul(d).and_then(|md| md.checked_sub(1u128 << p)) else {
        return false;
    };
    let holds = |n: u128| {
        let over = e.checked_mul(n);
        let room = (d - n % d).checked_mul(1u128 << p);
        match (over, room) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(o), Some(r)) => o < r || (closed && o == r),
        }
    };
    holds(top) && (top < d || holds(top / d * d - 1))
}

/// Reverses a signed division by a power of two.
///
/// Rounding toward zero adds `2^k - 1` to a negative dividend before the
/// arithmetic shift, and the sign supplies it: MSVC divides by two as
/// `(x - (x >> 31)) >> 1` (the sign is `0` or `-1`) and by `2^k` as
/// `(x + ((x >> 31) & (2^k - 1))) >> k`; other compilers add the sign bit
/// alone, `(x + ((uint32_t)x >> 31)) >> 1`. A 32-bit dividend is read
/// through its sign extension, as `cdq` reads it, so the quotient is
/// `(int32_t)x / 2`. The sign has the shift's own width: a 64-bit sign
/// fixed into a 32-bit shift, or a 32-bit one into a 64-bit shift, rounds
/// a value the shift does not hold, and the result is no quotient. The
/// divisor `2^k` is a positive number at that width only below its sign
/// bit: a 32-bit shift by 31 divides by `INT_MIN` if anything.
///
/// # Arguments
///
/// * `l` - The shifted expression.
/// * `k` - The shift.
/// * `bits` - The width of the shift.
///
/// # Returns
///
/// `x / 2^k`, or `None` when `l` is not that shape.
fn signed_power_quotient(l: &Expr, k: u64, bits: u8) -> Option<Expr> {
    /// The width and operand of a sign, `x >> 31` or `x >> 63`, the 32-bit
    /// operand read through its sign extension.
    fn sign_of(e: &Expr) -> Option<(u64, &Expr)> {
        let Expr::Bin(Op::Sar, s, amount) = e else {
            return None;
        };
        match (const_of(amount)?, s.as_ref()) {
            (31, Expr::Sext(x, 32)) => Some((32, x.as_ref())),
            (63, x) => Some((64, x)),
            _ => None,
        }
    }
    if k == 0 || k >= 32 {
        return None;
    }
    let found = match l {
        Expr::Bin(Op::Sub, x, sign) if k == 1 => sign_of(sign)
            .filter(|(_, s)| *s == x.as_ref())
            .map(|(w, _)| (w, x.as_ref())),
        Expr::Bin(Op::Add, a, b) => [(a.as_ref(), b.as_ref()), (b.as_ref(), a.as_ref())]
            .into_iter()
            .find_map(|(x, fix)| {
                let (w, s) = match fix {
                    Expr::Bin(Op::And, sign, m) if const_of(m) == Some((1u64 << k) - 1) => {
                        sign_of(sign)?
                    }
                    Expr::Bin(Op::Shr, s, amount) if k == 1 && const_of(amount) == Some(31) => {
                        (32, s.as_ref())
                    }
                    Expr::Bin(Op::Shr, s, amount) if k == 1 && const_of(amount) == Some(63) => {
                        (64, s.as_ref())
                    }
                    _ => return None,
                };
                (s == x).then_some((w, x))
            }),
        _ => None,
    };
    let (w, x) = found.filter(|(w, _)| *w == u64::from(bits) && k + 1 < *w)?;
    let dividend = if w == 32 {
        Expr::Sext(Box::new(x.clone()), 32)
    } else {
        x.clone()
    };
    Some(Expr::Bin(
        Op::SDiv,
        Box::new(dividend),
        Box::new(Expr::Const(1u64 << k)),
    ))
}

/// The `(width, magic, dividend, shift, negative magic)` of a signed
/// quotient before its sign fix.
///
/// The shapes are `mulhi(M, x) >> s` (arithmetic), `mulhi(M, x)` alone, and,
/// for a magic the compiler stored negative, `(mulhi(M, x) + x) >> s` or
/// `mulhi(M, x) + x`. A 32-bit `sar` in 64-bit code shifts the high half
/// sign-extended from its lane, so the shift may reach it through that
/// extension.
///
/// # Arguments
///
/// * `q` - The quotient expression.
fn signed_quotient_of(q: &Expr) -> Option<(u8, u64, &Expr, u64, bool)> {
    let (inner, s) = match q {
        Expr::Bin(Op::Sar, inner, shift) => (inner.as_ref(), const_of(shift)?),
        other => (other, 0),
    };
    let (inner, lane) = match inner {
        Expr::Sext(e, bits) => (e.as_ref(), Some(*bits)),
        other => (other, None),
    };
    let found = mulhi_of(inner, true)
        .map(|(w, m, x)| (w, m, x, s, false))
        .or_else(|| {
            let Expr::Bin(Op::Add, a, b) = inner else {
                return None;
            };
            [(a.as_ref(), b.as_ref()), (b.as_ref(), a.as_ref())]
                .into_iter()
                .find_map(|(mul, x2)| {
                    mulhi_of(mul, true)
                        .filter(|(_, _, x)| *x == x2)
                        .map(|(w, m, x)| (w, m, x, s, true))
                })
        })?;
    lane.is_none_or(|bits| bits == found.0).then_some(found)
}

/// Reverses an unsigned division whose magic needs one bit more than the
/// width.
///
/// When `2^(w + s) / d` rounded up does not fit in `w` bits, a compiler
/// multiplies by the low `w` bits `M'` of it and adds the missing top bit
/// through the dividend: `((x - mulhi(M', x)) >> 1) + mulhi(M', x)`, then
/// shifts by `s - 1`. The magic is `M' + 2^w` and the shift `s`.
///
/// # Arguments
///
/// * `l` - The value being shifted.
/// * `s` - The shift.
///
/// # Returns
///
/// The division, or `None` when the operands are not that shape.
fn overflow_division(l: &Expr, s: u64) -> Option<Expr> {
    let Expr::Bin(Op::Add, p, q) = l else {
        return None;
    };
    for (half, high) in [(p.as_ref(), q.as_ref()), (q.as_ref(), p.as_ref())] {
        let Expr::Bin(Op::Shr, diff, one) = half else {
            continue;
        };
        let Some((w, m, x)) = mulhi_of(high, false) else {
            continue;
        };
        if const_of(one) != Some(1) {
            continue;
        }
        let dividend = match diff.as_ref() {
            Expr::Bin(Op::Sub, y, m2) if m2.as_ref() == high => (**y).clone(),
            Expr::Bin(Op::Add, inner, k) if matches!(**k, Expr::Const(_)) => match inner.as_ref() {
                Expr::Bin(Op::Sub, y, m2) if m2.as_ref() == high => {
                    fold(Op::Add, (**y).clone(), (**k).clone(), w)
                }
                _ => continue,
            },
            _ => continue,
        };
        if &dividend != x {
            continue;
        }
        let d = wide_magic_divisor(w, u128::from(m) + (1u128 << w), s + 1)?;
        return Some(Expr::Bin(
            Op::Div,
            Box::new(mask(dividend, mask_bits(w))),
            Box::new(Expr::Const(d)),
        ));
    }
    None
}

/// Reads a shift of the whole product of two 32-bit values as the high
/// multiply it shifts.
///
/// `smull` and `umull`, and an `imul` of a sign-extended word, form the
/// 64-bit product of two words; shifted right by 32 or more it is the
/// product's high word shifted by the rest, which is the shape
/// [`division_idiom`] reads a quotient's magic multiply in: `(sext(x) *
/// M) >> 34` is `smulhi32(x, M) >> 2`. A logical shift reads the high word
/// as it is, an arithmetic one through its sign extension.
///
/// # Arguments
///
/// * `op` - The shift, [`Op::Shr`] or [`Op::Sar`].
/// * `l` - The product: a sign-extended word times a constant that fits a
///   signed word, or a word cut to its low 32 bits times one that fits an
///   unsigned word.
/// * `r` - The shift, 32 to 63.
///
/// # Returns
///
/// The shift of the high multiply, or `None` when the operands are not
/// that shape.
fn wide_high(op: Op, l: &Expr, r: &Expr) -> Option<Expr> {
    /// The mask of a word's bits.
    const WORD: u64 = 0xffff_ffff;
    if !matches!(op, Op::Shr | Op::Sar) {
        return None;
    }
    let k = const_of(r).filter(|k| (32..64).contains(k))?;
    let Expr::Bin(Op::Mul, a, b) = l else {
        return None;
    };
    let (x, c, signed) = [(a, b), (b, a)].into_iter().find_map(|(v, c)| {
        let c = const_of(c)?;
        match v.as_ref() {
            Expr::Sext(x, 32) if sext(c & WORD, 32) == c => Some((x.as_ref(), c & WORD, true)),
            other if known_bits(other) <= WORD && c <= WORD => Some((other, c, false)),
            _ => None,
        }
    })?;
    let high = |hi: Op| fold(hi, x.clone(), Expr::Const(c), 32);
    let rest = Expr::Const(k - 32);
    match (op, signed) {
        (Op::Shr, true) if k == 32 => Some(high(Op::SMulHi(32))),
        (Op::Shr, true) => Some(Expr::Bin(
            Op::Shr,
            Box::new(high(Op::SMulHi(32))),
            Box::new(rest),
        )),
        (Op::Shr, false) => Some(fold(Op::Shr, high(Op::MulHi(32)), rest, 64)),
        (Op::Sar, true) => Some(fold(
            Op::Sar,
            Expr::Sext(Box::new(high(Op::SMulHi(32))), 32),
            rest,
            64,
        )),
        _ => None,
    }
}

/// The value a signed quotient shifts arithmetically, its lane's sign
/// extension taken off: the high multiply, or its sum with the dividend.
///
/// Its sign is the quotient's, since an arithmetic shift keeps the sign.
///
/// # Arguments
///
/// * `q` - The quotient, as [`signed_quotient_of`] reads it.
fn quotient_operand(q: &Expr) -> &Expr {
    let inner = match q {
        Expr::Bin(Op::Sar, inner, _) => inner.as_ref(),
        other => other,
    };
    match inner {
        Expr::Sext(e, _) => e.as_ref(),
        other => other,
    }
}

/// `e` with its outer cut to the low word taken off: a sign extension of
/// it or a mask of it (a cast stays, which from a float converts).
///
/// Two values the same below that cut agree in every bit an operation of
/// 32 bits or fewer reads.
///
/// # Arguments
///
/// * `e` - The value.
fn low_word(e: &Expr) -> &Expr {
    match e {
        Expr::Sext(x, 32) => x.as_ref(),
        Expr::Bin(Op::And, x, m) if const_of(m) == Some(0xffff_ffff) => x.as_ref(),
        other => other,
    }
}

/// Reverses the strength reduction of a division or remainder by a constant.
///
/// Unsigned `x / d` comes back as `mulhi(M, x) >> s`, or `mulhi(M, x)`
/// alone when no shift is needed (a quotient shifted further is a larger
/// divisor's), or the shape of [`overflow_division`] when the magic needs a
/// bit more; signed as the quotient of [`signed_quotient_of`] plus its own
/// sign bit (`q + (q >>> (w - 1))`), the sign read off the quotient, the
/// dividend or the value the quotient shifts, a 32-bit lane's through its
/// 64-bit extension; `x % d` as `x - (x / d) * d` or `x + (x / d) * -d` once
/// the division is back, and `x - (x / y) * y` by a divisor that is no
/// constant (`sdiv; msub`), the dividend at 32 bits or fewer matched through
/// its cut to the low word ([`low_word`]). Each is rendered as the operator
/// it was, the divisor recovered by [`magic_divisor`] or
/// [`signed_magic_divisor`], a dividend the multiply read at fewer bits
/// than the register holds cut to those bits. The sign bit of such a quotient on its own,
/// that is `q >>> (w - 1)` for a quotient the compiler kept in a register and
/// fixed up elsewhere, is the sign bit of the dividend, since the divisor is
/// positive; the fix-up then matches either spelling.
///
/// # Arguments
///
/// * `op` - The operator being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Operation width.
///
/// # Returns
///
/// The division or remainder, or `None` when the operands are not that shape.
fn division_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    match op {
        Op::Sar => {
            let k = const_of(r)?;
            match l {
                Expr::Sext(inner, 32) => signed_power_quotient(inner, k, 32),
                _ => None,
            }
            .or_else(|| signed_power_quotient(l, k, bits))
        }
        Op::MulHi(w) => {
            let (m, x) = match (const_of(l), const_of(r)) {
                (Some(m), None) => (m, r),
                (None, Some(m)) => (m, l),
                _ => return None,
            };
            let d = magic_divisor(w, m, 0).filter(|d| !d.is_power_of_two())?;
            Some(Expr::Bin(
                Op::Div,
                Box::new(mask(x.clone(), mask_bits(w))),
                Box::new(Expr::Const(d)),
            ))
        }
        Op::Shr => {
            let s = const_of(r)?;
            if let Expr::Bin(Op::Div, x, d) = l
                && let Some(d) = const_of(d).filter(|d| *d > 0)
                && let Some(wider) = d.checked_shl(u32::try_from(s).ok()?)
                && wider >> s == d
                && wider <= mask_bits(bits)
                && known_bits(x) <= mask_bits(bits)
            {
                return Some(Expr::Bin(Op::Div, x.clone(), Box::new(Expr::Const(wider))));
            }
            if let Some((w, m, x)) = mulhi_of(l, false)
                && let Some(d) = magic_divisor(w, m, s)
            {
                return Some(Expr::Bin(
                    Op::Div,
                    Box::new(mask(x.clone(), mask_bits(w))),
                    Box::new(Expr::Const(d)),
                ));
            }
            if let Some((w, m, x, s2, negative)) = signed_quotient_of(l)
                && s == u64::from(w) - 1
                && signed_magic_divisor(w, m, s2, negative).is_some()
            {
                return Some(Expr::Bin(
                    Op::Shr,
                    Box::new(mask(x.clone(), mask_bits(w))),
                    Box::new(Expr::Const(s)),
                ));
            }
            overflow_division(l, s)
        }
        Op::Add if l.is_shift_fix() || r.is_shift_fix() => {
            for (q, fix) in [(l, r), (r, l)] {
                let Expr::Bin(Op::Shr, sign_of, amount) = fix else {
                    continue;
                };
                let Some((w, m, x, s, negative)) = signed_quotient_of(q) else {
                    continue;
                };
                let top = u64::from(w) - 1;
                let sign_of = match (const_of(amount), sign_of.as_ref()) {
                    (Some(a), Expr::Bin(Op::And, v, k))
                        if a == top && const_of(k) == Some(mask_bits(w)) =>
                    {
                        v.as_ref()
                    }
                    (Some(63), Expr::Sext(v, b)) if *b == w => v.as_ref(),
                    (Some(a), other) if a == top => other,
                    _ => continue,
                };
                if sign_of != q && sign_of != x && sign_of != quotient_operand(q) {
                    continue;
                }
                let d = signed_magic_divisor(w, m, s, negative)?;
                let dividend = if w == 32 {
                    Expr::Sext(Box::new(x.clone()), 32)
                } else {
                    x.clone()
                };
                return Some(Expr::Bin(
                    Op::SDiv,
                    Box::new(dividend),
                    Box::new(Expr::Const(d)),
                ));
            }
            None
        }
        Op::Sub | Op::Add => {
            let negated = op == Op::Add;
            let lane = mask_bits(bits);
            let same = |a: &Expr, b: &Expr| a == b || (bits <= 32 && low_word(a) == low_word(b));
            let orders: &[(&Expr, &Expr)] = if negated {
                &[(l, r), (r, l)]
            } else {
                &[(l, r)]
            };
            for &(x, product) in orders {
                let Expr::Bin(Op::Mul, a, b) = product else {
                    continue;
                };
                for (quot, d) in [(a.as_ref(), b.as_ref()), (b.as_ref(), a.as_ref())] {
                    let Expr::Bin(div, x2, d2) = quot else {
                        continue;
                    };
                    let rem = match div {
                        Op::Div => Op::Rem,
                        Op::SDiv => Op::SRem,
                        _ => continue,
                    };
                    let divides = match const_of(d2) {
                        Some(dc) => {
                            let factor = if negated { dc.wrapping_neg() } else { dc };
                            const_of(d).is_some_and(|c| (c ^ factor) & lane == 0)
                        }
                        None => !negated && same(d, d2),
                    };
                    if divides && same(x2, x) {
                        return Some(Expr::Bin(rem, x2.clone(), d2.clone()));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Reverses a branchless select.
///
/// A compiler spells `c ? x : 0` as `(-(c)) & x`: the condition from a
/// `setcc` or `sbb`, negated into a mask of all ones or none. The `and` of
/// such a mask with anything is the select.
///
/// # Arguments
///
/// * `op` - The operator being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
///
/// # Returns
///
/// The ternary, or `None` when the operands are not that shape.
fn select_idiom(op: Op, l: &Expr, r: &Expr) -> Option<Expr> {
    if op != Op::And {
        return None;
    }
    for (mask, x) in [(l, r), (r, l)] {
        let negated = match mask {
            Expr::Un(UnOp::Neg, c) => c.as_ref(),
            Expr::Bin(Op::Sub, z, c) if matches!(**z, Expr::Const(0)) => c.as_ref(),
            _ => continue,
        };
        if let Expr::Cond(cond) = negated {
            return Some(Expr::Ternary(
                cond.clone(),
                Box::new(x.clone()),
                Box::new(Expr::Const(0)),
            ));
        }
    }
    None
}

/// Reverses a value masked by its own complemented sign.
///
/// `x & ~(x >> (bits - 1))` keeps `x` where its sign at `bits` is clear
/// and is zero where it is set: `x >= 0 ? x : 0`, the clamp a compiler
/// writes for a loop's trip count (`bic w9, w9, w9, asr #31`). The
/// complement is a `not` or an `xor` with all ones at the width, and the
/// shift reads the sign of the same `x`. Only the low `bits` bits of the
/// result are claimed, as every fold claims.
///
/// # Arguments
///
/// * `op` - The operator being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// The ternary, or `None` when the operands are not that shape.
fn clamp_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if op != Op::And || !(8..=64).contains(&bits) {
        return None;
    }
    let m = mask_bits(bits);
    for (mask, x) in [(l, r), (r, l)] {
        let sign = match mask {
            Expr::Un(UnOp::Not, s) => s.as_ref(),
            Expr::Bin(Op::Xor, s, c) if matches!(**c, Expr::Const(k) if k & m == m) => s.as_ref(),
            _ => continue,
        };
        let Expr::Bin(Op::Sar, v, by) = sign else {
            continue;
        };
        let same = match v.as_ref() {
            Expr::Sext(z, b) if *b == bits => **z == *x || **z == low_bits_read(x.clone(), bits),
            other => bits == 64 && other == x,
        };
        if same && const_of(by) == Some(u64::from(bits - 1)) {
            let cond = Cond {
                cc: Cc(ConditionCode::ge),
                flags: Flags::Cmp(x.clone(), Expr::Const(0), bits),
            };
            return Some(Expr::Ternary(
                Box::new(cond),
                Box::new(x.clone()),
                Box::new(Expr::Const(0)),
            ));
        }
    }
    None
}

/// The note for a condition whose outcome never varied.
///
/// A proven outcome names the dead branch: a condition that is always true
/// makes its `else` unreachable, and a reader can stop following the half of
/// the function that never runs. A sampled one only says how many inputs
/// agreed, since a real check failing one input in thousands agrees on all
/// of them. The condition itself is kept either way.
///
/// # Arguments
///
/// * `outcome` - What the condition evaluated to on every input tried.
/// * `inverted` - Whether the condition is being rendered negated.
/// * `evidence` - What the verdict rests on.
///
/// # Returns
///
/// The comment to append.
pub(super) fn opaque_note(outcome: bool, inverted: bool, evidence: Evidence) -> String {
    let taken = outcome != inverted;
    let dead = if taken { "else" } else { "body" };
    match evidence {
        Evidence::Proven => format!("/* opaque: always {taken}, so the {dead} never runs */"),
        Evidence::Sampled(n) => format!("/* {taken} on all {n} sampled inputs, not proven */"),
    }
}

/// A 64-bit absolute value written with the sign splat.
///
/// `(x ^ (x >> 63)) - (x >> 63)` and `(x + (x >> 63)) ^ (x >> 63)` are
/// `abs(x)`, including the minimum value, whose negation wraps. The shift
/// has to be by 63 and the surrounding operation at least 64 bits wide: a
/// shift by 31 is a 32-bit sign, and folding it would take the absolute
/// value of bits the 32-bit operation does not own. `cqo` is that shift
/// into `rdx`.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// `abs` of the operand, or `None` when this is not that shape.
fn sign_absolute(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if bits < 64 {
        return None;
    }
    /// `x >> 63`, the 64-bit sign splat, or `None`.
    fn splat(e: &Expr) -> Option<&Expr> {
        match e {
            Expr::Bin(Op::Sar, x, n) if const_of(n) == Some(63) => Some(x.as_ref()),
            _ => None,
        }
    }
    let call = |x: &Expr| Expr::Helper(Helper::Llabs, vec![x.clone()]);
    match op {
        Op::Sub => {
            let x = splat(r)?;
            let Expr::Bin(Op::Xor, a, b) = l else {
                return None;
            };
            let same = (a.as_ref() == x && b.as_ref() == r) || (b.as_ref() == x && a.as_ref() == r);
            same.then(|| call(x))
        }
        Op::Xor => {
            let (sign, sum) = if splat(l).is_some() { (l, r) } else { (r, l) };
            let x = splat(sign)?;
            let Expr::Bin(Op::Add, a, b) = sum else {
                return None;
            };
            let same =
                (a.as_ref() == x && b.as_ref() == sign) || (b.as_ref() == x && a.as_ref() == sign);
            same.then(|| call(x))
        }
        _ => None,
    }
}

/// Whether `e` evaluates a call.
///
/// A spelling that names the value once must not replace a tree that
/// evaluates the call twice, and a tree that evaluates it once may become
/// a call of that value.
///
/// # Arguments
///
/// * `e` - The expression.
fn invokes(e: &Expr) -> bool {
    match e {
        Expr::Call(..) | Expr::Helper(..) => true,
        Expr::Bin(_, a, b) | Expr::Ternary(_, a, b) => invokes(a) || invokes(b),
        Expr::Un(_, a)
        | Expr::Deref(a, _)
        | Expr::Sext(a, _)
        | Expr::Cast(a, _)
        | Expr::Bitcast(a, _) => invokes(a),
        Expr::Cond(c) => match &c.flags {
            Flags::Cmp(l, r, _)
            | Flags::Float(l, r, _)
            | Flags::FCmp(_, l, r, _)
            | Flags::Test(l, r, _)
            | Flags::Add(l, r, _) => invokes(l) || invokes(r),
            Flags::Result(v, _) | Flags::Carry(v) | Flags::Truth(v, _) => invokes(v),
            Flags::Shift(v, _, bit) => invokes(v) || invokes(bit),
            Flags::Unknown => false,
        },
        Expr::Const(_) | Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => false,
    }
}

/// `(x << n) | (x >> (width - n))` as a rotate.
///
/// The shifts are logical, of one value, by constants that add to the
/// operation width. The width is one `rotl` and `rotr` already name (8,
/// 16, 32, or 64). The printed count is the smaller of the two, and
/// `rotl` on a tie. An arithmetic shift is not a rotate: it fills with
/// the sign. A value that calls stays an or, so the text does not claim
/// the call ran once. A double shift of a register with itself (`shld rax,
/// rax, n`) is this shape; two different registers are not. A variable
/// count is the same rotate when it is masked to a 32-bit or 64-bit
/// width, which is the form `shld x, x, cl` lifts. The printed count is
/// the value under that mask. An 8-bit or 16-bit variable count can be
/// past the operand width, so it stays the shifts.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// The rotate, or `None` when this is not that shape.
fn rotate_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if op != Op::Or || !matches!(bits, 8 | 16 | 32 | 64) {
        return None;
    }
    /// `(left, value, count)` of a logical shift, or `None`.
    fn shift(e: &Expr) -> Option<(bool, &Expr, u64)> {
        match e {
            Expr::Bin(Op::Shl, v, n) => Some((true, v.as_ref(), const_of(n)?)),
            Expr::Bin(Op::Shr, v, n) => Some((false, v.as_ref(), const_of(n)?)),
            _ => None,
        }
    }
    if let (Some(a), Some(b)) = (shift(l), shift(r)) {
        if a.1 != b.1 || a.0 == b.0 || invokes(a.1) {
            return None;
        }
        let (left, right) = if a.0 { (a.2, b.2) } else { (b.2, a.2) };
        let width = u64::from(bits);
        if left == 0 || right == 0 || left >= width || right >= width || left + right != width {
            return None;
        }
        let (op, n) = if left <= right {
            (Op::Rol(bits), left)
        } else {
            (Op::Ror(bits), right)
        };
        return Some(Expr::Bin(
            op,
            Box::new(a.1.clone()),
            Box::new(Expr::Const(n)),
        ));
    }
    variable_rotate(l, r, bits)
}

/// `shld` or `shrd` of one value by a count masked to the width.
///
/// The lifter writes `shld x, x, n` as the or of `x << (n & (w - 1))` and
/// `(x >> 1) >> ((w - 1) - (n & (w - 1)))`, and `shrd` with the shifts
/// swapped.
/// That is a rotate by `n` at 32 and 64 bits, where the mask keeps the
/// count inside the width. A rotate reduces its count the same way, so
/// the printed count is `n`. An unmasked count is not this shape. A call
/// in the value or the count stays the shifts.
///
/// # Arguments
///
/// * `l` - Left operand of the or.
/// * `r` - Right operand of the or.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// The rotate, or `None` when this is not that shape.
fn variable_rotate(l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let mask = u64::from(bits) - 1;
    /// `(op, value, count)` of a logical shift, or `None`.
    fn shift(e: &Expr) -> Option<(Op, &Expr, &Expr)> {
        match e {
            Expr::Bin(op @ (Op::Shl | Op::Shr), v, n) => Some((*op, v.as_ref(), n.as_ref())),
            _ => None,
        }
    }
    /// The value under `& mask`, or `None`.
    fn under_mask(e: &Expr, mask: u64) -> Option<&Expr> {
        match e {
            Expr::Bin(Op::And, n, m) if const_of(m) == Some(mask) => Some(n.as_ref()),
            Expr::Bin(Op::And, m, n) if const_of(m) == Some(mask) => Some(n.as_ref()),
            _ => None,
        }
    }
    /// `(value, rest)` of a shift by one then by `rest`, or `None`.
    fn doubled(e: &Expr, op: Op) -> Option<(&Expr, &Expr)> {
        let (which, inner, rest) = shift(e)?;
        if which != op {
            return None;
        }
        let (which, base, one) = shift(inner)?;
        (which == op && const_of(one) == Some(1)).then_some((base, rest))
    }
    /// Whether `rest` is `(width - 1) - cnt`.
    fn complement(rest: &Expr, cnt: &Expr, mask: u64) -> bool {
        match rest {
            Expr::Bin(Op::Sub, top, c) => const_of(top) == Some(mask) && c.as_ref() == cnt,
            _ => false,
        }
    }
    for (near, far) in [(l, r), (r, l)] {
        let Some((near_op, base, cnt)) = shift(near) else {
            continue;
        };
        let Some(count) = under_mask(cnt, mask) else {
            continue;
        };
        let far_op = if near_op == Op::Shl { Op::Shr } else { Op::Shl };
        let Some((other, rest)) = doubled(far, far_op) else {
            continue;
        };
        if other != base || !complement(rest, cnt, mask) || invokes(base) || invokes(count) {
            continue;
        }
        let op = if near_op == Op::Shl {
            Op::Rol(bits)
        } else {
            Op::Ror(bits)
        };
        return Some(Expr::Bin(
            op,
            Box::new(base.clone()),
            Box::new(count.clone()),
        ));
    }
    None
}

/// The floor of the unsigned sum of `a` and `b`, half of it, at `bits`.
///
/// This is `(a & b) + ((a ^ b) >> 1)`, which does not drop the carry a
/// bare `(a + b) >> 1` drops. A width of 0 or above 64 is `None`.
///
/// # Arguments
///
/// * `a` - The first operand.
/// * `b` - The second operand.
/// * `bits` - The width.
pub(super) fn midpoint_bits(a: u64, b: u64, bits: u8) -> Option<u64> {
    if bits == 0 || bits > 64 {
        return None;
    }
    let m = mask_bits(bits);
    let (a, b) = (a & m, b & m);
    Some((a & b).wrapping_add((a ^ b) >> 1) & m)
}

/// `(x & y) + ((x ^ y) >> 1)` as `midpoint`.
///
/// The shift is logical and by one, and the operation is at least 64
/// bits: a 32-bit average is not the average of the zero-extended values.
/// The arguments stay in the and's order. A call in either value stays
/// the arithmetic. `(x + y) >> 1` is a different value when the sum wraps
/// and is not this shape.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// `midpoint` of the two values, or `None` when this is not that shape.
fn midpoint_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if bits < 64 || op != Op::Add {
        return None;
    }
    /// The value a logical shift by one shifts, or `None`.
    fn halved(e: &Expr) -> Option<&Expr> {
        match e {
            Expr::Bin(Op::Shr, v, n) if const_of(n) == Some(1) => Some(v.as_ref()),
            _ => None,
        }
    }
    /// The operands of `want`, or `None`.
    fn pair(e: &Expr, want: Op) -> Option<(&Expr, &Expr)> {
        match e {
            Expr::Bin(o, a, b) if *o == want => Some((a.as_ref(), b.as_ref())),
            _ => None,
        }
    }
    for (mask, shifted) in [(l, r), (r, l)] {
        let Some((x, y)) = pair(mask, Op::And) else {
            continue;
        };
        let Some(inner) = halved(shifted) else {
            continue;
        };
        let Some((p, q)) = pair(inner, Op::Xor) else {
            continue;
        };
        let same = (p == x && q == y) || (p == y && q == x);
        if same && !invokes(x) && !invokes(y) {
            return Some(Expr::Helper(Helper::Midpoint, vec![x.clone(), y.clone()]));
        }
    }
    None
}

/// `x` rounded up to a multiple of `align`, at `bits`.
///
/// `align` is a power of two. The rounding is `(x + align - 1) &
/// ~(align - 1)` and wraps the way that add does. Anything else, or a
/// width of 0 or above 64, is `None`.
///
/// # Arguments
///
/// * `x` - The value.
/// * `align` - The alignment, a power of two.
/// * `bits` - The width.
pub(super) fn align_up_bits(x: u64, align: u64, bits: u8) -> Option<u64> {
    if bits == 0 || bits > 64 || align < 2 || !align.is_power_of_two() {
        return None;
    }
    let m = mask_bits(bits);
    let low = align - 1;
    Some(x.wrapping_add(low) & m & !low)
}

/// `(x + (a - 1)) & ~(a - 1)` as `align_up`.
///
/// `a` is a power of two at least 4, and the mask is all ones above those
/// low zeros at a width of at least 64 bits. A 32-bit mask also clears
/// the top half of a 64-bit register, which is not an alignment of that
/// register. `x & ~m` is not rounded up. An alignment of two stays the
/// mask.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operation.
///
/// # Returns
///
/// `align_up` of the value, or `None` when this is not that shape.
fn align_up_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    if bits < 64 || op != Op::And {
        return None;
    }
    let (sum, mask) = match (l, r) {
        (sum, Expr::Const(m)) => (sum, *m),
        (Expr::Const(m), sum) => (sum, *m),
        _ => return None,
    };
    let width = mask_bits(bits);
    let low = (!mask) & width;
    let align = low
        .checked_add(1)
        .filter(|a| *a >= 4 && a.is_power_of_two())?;
    if mask & width != width & !low {
        return None;
    }
    let Expr::Bin(Op::Add, a, b) = sum else {
        return None;
    };
    let x = if const_of(b) == Some(low) {
        a.as_ref()
    } else if const_of(a) == Some(low) {
        b.as_ref()
    } else {
        return None;
    };
    Some(Expr::Helper(
        Helper::AlignUp,
        vec![x.clone(), Expr::Const(align)],
    ))
}

/// Reads a logical shift of the top bit after a shift left as the bit it
/// keeps, tested.
///
/// `(x << a) >> (w - 1)` at width `w` is bit `w - 1 - a` of `x`, `0` or `1`:
/// RISC-V, which has no bit test, writes `c & 0x40` as a truth value
/// `slli a0, a0, 57; srli a0, a0, 63`, which is `(x & 0x40) != 0`, the
/// flag the source tested. Only a shift left the expression holds bare is
/// read, at the width of the shift right: a narrower shift left is cut or
/// extended first, and then it is no such shape.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operands.
///
/// # Returns
///
/// The bit test, or `None` when this is not that shape.
fn bit_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    let top = u64::from(bits).checked_sub(1)?;
    let (Op::Shr, Expr::Bin(Op::Shl, x, a)) = (op, l) else {
        return None;
    };
    if const_of(r)? != top {
        return None;
    }
    let bit = 1u64.checked_shl(u32::try_from(top.checked_sub(const_of(a)?)?).ok()?)?;
    Some(Expr::Cond(Box::new(Cond {
        cc: Cc(ConditionCode::ne),
        flags: Flags::Cmp(
            fold(Op::And, (**x).clone(), Expr::Const(bit), bits),
            Expr::Const(0),
            bits,
        ),
    })))
}

/// Reads the count-leading-zeros idiom a compiler writes with a bit scan.
///
/// There is no `clz` instruction before `lzcnt`, so a compiler computes it as
/// `(width - 1) - bsr(x)`, and writes the subtraction as an exclusive or
/// because the bit scan's result cannot exceed the width. `bsr(x) ^ 63` is
/// the number of leading zeros, and on the target it appears sixteen times
/// as the index arithmetic of a container.
///
/// The rewrite is exact wherever the original is defined: a bit scan of zero
/// leaves its destination unspecified, so an expression built on it says
/// nothing about zero either, and `lzcnt` is the name for what it computes
/// everywhere else.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Width of the operands.
///
/// # Returns
///
/// The leading-zero count, or `None` when this is not that shape.
fn leading_zeros_idiom(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    /// Reads `bsr(x)` and returns `x`.
    fn scan(e: &Expr) -> Option<&Expr> {
        match e {
            Expr::Un(UnOp::Bsr, x) => Some(x.as_ref()),
            _ => None,
        }
    }
    let top = Expr::Const(u64::from(bits).saturating_sub(1));
    let count = |x: &Expr| Expr::Un(UnOp::Lzcnt, Box::new(x.clone()));
    match op {
        Op::Xor => {
            for (a, b) in [(l, r), (r, l)] {
                if *b == top
                    && let Some(x) = scan(a)
                {
                    return Some(count(x));
                }
            }
            None
        }
        Op::Sub if *l == top => scan(r).map(count),
        _ => None,
    }
}

/// Rewrites a mixed boolean-arithmetic identity back to what it computes.
///
/// An obfuscator replaces `x + y` with an expression that mixes arithmetic
/// and bitwise operations over the same two values. The result is equal for
/// every input, which is what makes it safe to emit and what makes it
/// unreadable: `(x ^ y) + 2 * (x & y)` is an addition, and nothing about its
/// shape says so.
///
/// These are the identities a rewriter can apply without a solver, each true
/// for all inputs by the bit-level argument in its comment. A test checks
/// every one of them numerically over random values, because an identity
/// that is merely believed would silently change what the code does.
///
/// # Arguments
///
/// * `op` - The operation being folded.
/// * `l` - Left operand.
/// * `r` - Right operand.
///
/// # Returns
///
/// The simplified expression, or `None` when nothing matches.
fn mba_idiom(op: Op, l: &Expr, r: &Expr) -> Option<Expr> {
    /// Reads a binary operation, either way round, returning its operands.
    fn binary(e: &Expr, want: Op) -> Option<(&Expr, &Expr)> {
        match e {
            Expr::Bin(o, a, b) if *o == want => Some((a.as_ref(), b.as_ref())),
            _ => None,
        }
    }
    /// Reads `x & y` or `x | y` as an unordered pair.
    fn pair(e: &Expr, want: Op) -> Option<(&Expr, &Expr)> {
        binary(e, want)
    }
    /// Whether two unordered pairs are the same pair.
    fn same_pair(one: (&Expr, &Expr), two: (&Expr, &Expr)) -> bool {
        (one.0 == two.0 && one.1 == two.1) || (one.0 == two.1 && one.1 == two.0)
    }
    /// Reads `2 * e` or `e << 1`, the doubling an MBA form uses.
    fn doubled(e: &Expr) -> Option<&Expr> {
        if let Some((a, b)) = binary(e, Op::Mul) {
            if *b == Expr::Const(2) {
                return Some(a);
            }
            if *a == Expr::Const(2) {
                return Some(b);
            }
        }
        if let Some((a, b)) = binary(e, Op::Shl)
            && *b == Expr::Const(1)
        {
            return Some(a);
        }
        None
    }
    let sum = |x: &Expr, y: &Expr| Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(y.clone()));
    let bits = |o: Op, x: &Expr, y: &Expr| Expr::Bin(o, Box::new(x.clone()), Box::new(y.clone()));
    match op {
        Op::Add => {
            for (first, second) in [(l, r), (r, l)] {
                if let Some(x) = pair(first, Op::Xor)
                    && let Some(d) = doubled(second)
                    && let Some(y) = pair(d, Op::And)
                    && same_pair(x, y)
                {
                    return Some(sum(x.0, x.1));
                }
                if let Some(x) = pair(first, Op::And)
                    && let Some(y) = pair(second, Op::Or)
                    && same_pair(x, y)
                {
                    return Some(sum(x.0, x.1));
                }
                if let Some(x) = pair(first, Op::Xor)
                    && let Some(y) = pair(second, Op::And)
                    && same_pair(x, y)
                {
                    return Some(bits(Op::Or, x.0, x.1));
                }
            }
            None
        }
        Op::Sub => {
            if let Some(x) = pair(l, Op::Or)
                && let Some(y) = pair(r, Op::And)
                && same_pair(x, y)
            {
                return Some(bits(Op::Xor, x.0, x.1));
            }
            if let Some(x) = pair(l, Op::Or)
                && let Some(y) = pair(r, Op::Xor)
                && same_pair(x, y)
            {
                return Some(bits(Op::And, x.0, x.1));
            }
            None
        }
        _ => None,
    }
}

/// Most nodes the general MBA collapse walks.
const MBA_NODES_MAX: usize = 32;

/// Collapses any two-variable linear mixed Boolean-arithmetic expression
/// to the plain operation it computes, by measuring it on the Boolean
/// lattice.
///
/// A linear MBA is a sum of constants times products of the variables'
/// bits: over two variables every such expression is `c0 + c1*(x & ~y) +
/// c2*(~x & y) + c3*(x & y)`, so evaluating it on the four classes of
/// `(x, y)` - both zero, one all-ones and the other zero, both all-ones -
/// gives the coefficients (the all-ones mask is odd, so it divides). The
/// coefficients then name the plain form, read in the basis `1, x, y,
/// x & y`: `x + y` is `(0, 1, 1, 0)`, the or is `(0, 1, 1, -1)`, a
/// difference keeps its zero. The collapsed form
/// is checked against the original on the four class vectors and two
/// mixed ones before it answers, so a shape this misread - a product, a
/// variable shift - never survives to say so; only a strictly smaller
/// node count is returned, so a form already plain stays.
///
/// # Arguments
///
/// * `op` - The outermost operator of the expression.
/// * `l` - Its left operand.
/// * `r` - Its right operand.
/// * `bits` - The width every value is masked to.
///
/// # Returns
///
/// The plain expression the MBA computes, or `None` when the expression
/// has more than two variables, more than [`MBA_NODES_MAX`] nodes, no
/// bitwise operation to collapse, or no plainly smaller form.
fn mba_linear(op: Op, l: &Expr, r: &Expr, bits: u8) -> Option<Expr> {
    /// Collects the distinct non-constant leaves, bailing on memory,
    /// conditions, calls and floats, which no plain form names.
    fn leaves(e: &Expr, out: &mut Vec<Expr>) -> bool {
        let ok = match e {
            Expr::Const(_) => true,
            Expr::Var(_) | Expr::Sp(_) => {
                if !out.contains(e) {
                    out.push(e.clone());
                }
                out.len() <= 2
            }
            Expr::Un(_, a) | Expr::Sext(a, _) | Expr::Cast(a, _) | Expr::Bitcast(a, _) => {
                leaves(a, out)
            }
            Expr::Bin(_, a, b) => leaves(a, out) && leaves(b, out),
            Expr::Str(_)
            | Expr::Deref(..)
            | Expr::Cond(_)
            | Expr::Ternary(..)
            | Expr::Call(..)
            | Expr::Helper(..)
            | Expr::FConst(..) => false,
        };
        ok && out.len() <= 2
    }
    /// Whether the tree holds a bitwise operation worth collapsing.
    fn bitwise(e: &Expr) -> bool {
        match e {
            Expr::Bin(Op::And | Op::Or | Op::Xor, ..) => true,
            Expr::Bin(_, a, b) => bitwise(a) || bitwise(b),
            Expr::Un(UnOp::Not, _) => true,
            Expr::Un(_, a) | Expr::Sext(a, _) | Expr::Cast(a, _) | Expr::Bitcast(a, _) => {
                bitwise(a)
            }
            _ => false,
        }
    }
    /// Counts the nodes, so only small shapes pay the walk.
    fn nodes(e: &Expr) -> usize {
        match e {
            Expr::Bin(_, a, b) => 1 + nodes(a) + nodes(b),
            Expr::Un(_, a) | Expr::Sext(a, _) | Expr::Cast(a, _) | Expr::Bitcast(a, _) => {
                1 + nodes(a)
            }
            Expr::Ternary(_, a, b) => 1 + nodes(a) + nodes(b),
            _ => 1,
        }
    }
    /// Evaluates an arithmetic expression with the leaves substituted,
    /// bailing on anything this cannot compute.
    fn eval(e: &Expr, bits: u8, x: &Expr, y: Option<&Expr>, vx: u64, vy: u64) -> Option<u64> {
        let m = mask_bits(bits);
        let v = match e {
            Expr::Const(c) => *c & m,
            leaf if leaf == x => vx,
            leaf if y.is_some_and(|y| leaf == y) => vy,
            Expr::Un(UnOp::Neg, a) => eval(a, bits, x, y, vx, vy)?.wrapping_neg(),
            Expr::Un(UnOp::Not, a) => eval(a, bits, x, y, vx, vy)? ^ m,
            Expr::Sext(a, from) => sext(eval(a, bits, x, y, vx, vy)? & mask_bits(*from), *from),
            Expr::Bin(op, a, b) => {
                let (a, b) = (eval(a, bits, x, y, vx, vy)?, eval(b, bits, x, y, vx, vy)?);
                match op {
                    Op::Add => a.wrapping_add(b),
                    Op::Sub => a.wrapping_sub(b),
                    Op::Mul => a.wrapping_mul(b),
                    Op::And => a & b,
                    Op::Or => a | b,
                    Op::Xor => a ^ b,
                    Op::Shl => a.wrapping_shl(lo32(b) & 63),
                    Op::Shr => a.wrapping_shr(lo32(b) & 63),
                    Op::Sar => sext(a, bits)
                        .cast_signed()
                        .wrapping_shr(lo32(b) & 63)
                        .cast_unsigned(),
                    _ => return None,
                }
            }
            _ => return None,
        };
        Some(v & m)
    }
    /// The inverse of the odd all-ones mask modulo `2^bits`, by Newton
    /// iteration: each round doubles the correct low bits.
    fn inverse_of_ones(bits: u8) -> u64 {
        let m = mask_bits(bits);
        let mut x = 1u64;
        for _ in 0..6 {
            x = x.wrapping_mul(2u64.wrapping_sub(m.wrapping_mul(x)));
        }
        x
    }
    /// Builds `c0 + form`, the constant folded away when zero.
    fn plus(base: Expr, c0: u64, bits: u8) -> Expr {
        if c0 & mask_bits(bits) == 0 {
            return base;
        }
        Expr::Bin(
            Op::Add,
            Box::new(base),
            Box::new(Expr::Const(c0 & mask_bits(bits))),
        )
    }
    /// Whether the tree mentions either collected leaf.
    fn mentions(e: &Expr, x: &Expr, y: Option<&Expr>) -> bool {
        if e == x || y.is_some_and(|y| e == y) {
            return true;
        }
        match e {
            Expr::Bin(_, a, b) | Expr::Ternary(_, a, b) => mentions(a, x, y) || mentions(b, x, y),
            Expr::Un(_, a) | Expr::Sext(a, _) | Expr::Cast(a, _) | Expr::Bitcast(a, _) => {
                mentions(a, x, y)
            }
            _ => false,
        }
    }
    /// Whether the tree is selector-linear in its leaves.
    ///
    /// No shift by a leaf, no shift right at all (a constant one loses
    /// bits the lattice does not carry), no product or quotient of two
    /// leaves, and no and, or or xor over an operand that is not a
    /// bitwise function of the leaves' own bits - a negation or a sum
    /// inside one carries between bit positions, which the lattice the
    /// coefficients are read on does not model.
    fn linear(e: &Expr, x: &Expr, y: Option<&Expr>) -> bool {
        /// Whether the tree is a bitwise function of the leaves' bits:
        /// each of its bits depends only on the leaves' bits at that
        /// position.
        fn bitwise(e: &Expr, x: &Expr, y: Option<&Expr>) -> bool {
            match e {
                Expr::Const(_) => true,
                leaf if leaf == x || y.is_some_and(|y| leaf == y) => true,
                Expr::Un(UnOp::Not, a) => bitwise(a, x, y),
                Expr::Bin(Op::And | Op::Or | Op::Xor, a, b) => bitwise(a, x, y) && bitwise(b, x, y),
                _ => false,
            }
        }
        match e {
            Expr::Bin(Op::Shl, a, count) => !mentions(count, x, y) && linear(a, x, y),
            Expr::Bin(Op::Shr | Op::Sar, ..) => false,
            Expr::Bin(Op::Mul | Op::Div | Op::Rem | Op::SDiv | Op::SRem, a, b) => {
                !(mentions(a, x, y) && mentions(b, x, y)) && linear(a, x, y) && linear(b, x, y)
            }
            Expr::Bin(Op::And | Op::Or | Op::Xor, a, b) => bitwise(a, x, y) && bitwise(b, x, y),
            Expr::Bin(_, a, b) | Expr::Ternary(_, a, b) => linear(a, x, y) && linear(b, x, y),
            Expr::Un(_, a) | Expr::Sext(a, _) | Expr::Cast(a, _) | Expr::Bitcast(a, _) => {
                linear(a, x, y)
            }
            _ => true,
        }
    }
    let whole = Expr::Bin(op, Box::new(l.clone()), Box::new(r.clone()));
    if nodes(&whole) > MBA_NODES_MAX || !bitwise(&whole) {
        return None;
    }
    let mut vars: Vec<Expr> = Vec::new();
    if !leaves(&whole, &mut vars) || vars.is_empty() {
        return None;
    }
    let (x, y) = (vars[0].clone(), vars.get(1).cloned());
    if !linear(&whole, &x, y.as_ref()) {
        return None;
    }
    let m = mask_bits(bits);
    let sign = m & !m.wrapping_shr(1);
    let low = m >> 1;
    let probes: [(u64, u64); 12] = [
        (0, 0),
        (m, 0),
        (0, m),
        (m, m),
        (m & 0xaaaa_aaaa_aaaa_aaaa, m & 0x5555_5555_5555_5555),
        (m & 0x5555_5555_5555_5555, m & 0xaaaa_aaaa_aaaa_aaaa),
        (sign, low),
        (low, sign),
        (m & 0x8000_0000, 0),
        (0, m & 0x8000_0000),
        (m & 0xdead_beef_cafe_f00d, m & 0xfeed_face_dead_beef),
        (m & 0x0f0f_0f0f_0f0f_0f0f, m & 0xf0f0_f0f0_f0f0_f0f0),
    ];
    let at = |e: &Expr, (vx, vy): (u64, u64)| eval(e, bits, &x, y.as_ref(), vx, vy);
    let values: Vec<u64> = probes
        .iter()
        .map(|&p| at(&whole, p))
        .collect::<Option<_>>()?;
    let inv = inverse_of_ones(bits);
    let k = values[0];
    let c1 = values[1].wrapping_sub(k).wrapping_mul(inv) & m;
    let c2 = values[2].wrapping_sub(k).wrapping_mul(inv) & m;
    let c3 = values[3]
        .wrapping_sub(values[1])
        .wrapping_sub(values[2])
        .wrapping_add(k)
        .wrapping_mul(inv)
        & m;
    let one = 1 & m;
    let neg = m;
    let neg_two = m.wrapping_sub(1);
    let y = || y.clone();
    let plain = match (c1, c2, c3) {
        (0, 0, 0) => Some(Expr::Const(k)),
        (a, 0, 0) if a == one => Some(plus(x.clone(), k, bits)),
        (a, 0, 0) if a == neg => Some(plus(Expr::Un(UnOp::Neg, Box::new(x.clone())), k, bits)),
        (0, a, 0) if a == one => Some(plus(y()?, k, bits)),
        (0, a, 0) if a == neg => Some(plus(Expr::Un(UnOp::Neg, Box::new(y()?)), k, bits)),
        (a, b, 0) if a == one && b == neg => Some(plus(
            Expr::Bin(Op::Sub, Box::new(x.clone()), Box::new(y()?)),
            k,
            bits,
        )),
        (a, b, 0) if a == neg && b == one => Some(plus(
            Expr::Bin(Op::Sub, Box::new(y()?), Box::new(x.clone())),
            k,
            bits,
        )),
        (a, b, c) if a == one && b == one => {
            let form = match c {
                0 => Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(y()?)),
                _ if c == neg => Expr::Bin(Op::Or, Box::new(x.clone()), Box::new(y()?)),
                _ if c == neg_two => Expr::Bin(Op::Xor, Box::new(x.clone()), Box::new(y()?)),
                _ => return None,
            };
            Some(plus(form, k, bits))
        }
        (0, 0, c) if c == one => Some(plus(
            Expr::Bin(Op::And, Box::new(x.clone()), Box::new(y()?)),
            k,
            bits,
        )),
        (a, 0, c) if a == one && c == neg => Some(plus(
            Expr::Bin(
                Op::And,
                Box::new(x.clone()),
                Box::new(Expr::Un(UnOp::Not, Box::new(y()?))),
            ),
            k,
            bits,
        )),
        (0, a, c) if a == one && c == neg => Some(plus(
            Expr::Bin(
                Op::And,
                Box::new(Expr::Un(UnOp::Not, Box::new(x.clone()))),
                Box::new(y()?),
            ),
            k,
            bits,
        )),
        _ => None,
    }?;
    if nodes(&plain) >= nodes(&whole) {
        return None;
    }
    probes
        .iter()
        .enumerate()
        .all(|(i, &p)| at(&plain, p).is_some_and(|v| v == values[i]))
        .then_some(plain)
}

/// The `(base, index)` of an address that reads an array element.
///
/// `base + index * size`, with `size` the width of the access, is element
/// `index` of an array of that type at `base`; a constant offset on the
/// sum stays with the base. A plain sum of two terms is not an index.
///
/// # Arguments
///
/// * `addr` - The address expression.
/// * `ty` - The access type.
pub(super) fn indexed(addr: &Expr, ty: Ty) -> Option<(Expr, Expr)> {
    let size = u64::from(ty.bits()) / 8;
    if size < 2 {
        return None;
    }
    let (sum, offset) = match addr {
        Expr::Bin(Op::Add, inner, k)
            if matches!(**k, Expr::Const(_)) && matches!(**inner, Expr::Bin(Op::Add, ..)) =>
        {
            (inner.as_ref(), const_of(k))
        }
        other => (other, None),
    };
    let Expr::Bin(Op::Add, p, q) = sum else {
        return None;
    };
    for (base, term) in [(p.as_ref(), q.as_ref()), (q.as_ref(), p.as_ref())] {
        let (index, factor) = term_of(term);
        if factor != size || matches!(index, Expr::Const(_)) {
            continue;
        }
        let base = match offset {
            Some(k) => Expr::Bin(Op::Add, Box::new(base.clone()), Box::new(Expr::Const(k))),
            None => base.clone(),
        };
        return Some((base, index.clone()));
    }
    None
}

/// Applies `op` with constant folding and the identities that keep output readable.
///
/// Constant results are truncated to `bits`. Identities: `x ^ x`, `x - x`
/// and `x & 0` are `0`; `x op 0` for additive and shift operators, and
/// `x * 1`, are `x`; `&` with a constant goes through [`mask`]; stack
/// addresses absorb constant offsets; `(x + c1) + c2` becomes `x + (c1 + c2)`;
/// `x - c` becomes `x + (-c)`; `(x + c) - y` becomes `(x - y) + c` so the
/// constant stays outermost. A complementary logical shift is a rotate,
/// an unsigned average of the and/xor form is `midpoint`, and an added
/// power-of-two mask is `align_up`. Division by a constant that is zero
/// in its low `bits` is left symbolic.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `bits` - Operation width; constant results are masked to it.
///
/// # Returns
///
/// The folded expression.
pub(super) fn fold(op: Op, l: Expr, r: Expr, bits: u8) -> Expr {
    let m = mask_bits(bits);
    if op.is_float() {
        return Expr::Bin(op, Box::new(l), Box::new(r));
    }
    if let Some(e) = wide_high(op, &l, &r) {
        return e;
    }
    if let Some(e) = division_idiom(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = select_idiom(op, &l, &r).or_else(|| clamp_idiom(op, &l, &r, bits)) {
        return e;
    }
    if let Some(e) = sign_absolute(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = rotate_idiom(op, &l, &r, bits).or_else(|| bit_idiom(op, &l, &r, bits)) {
        return e;
    }
    if let Some(e) = midpoint_idiom(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = align_up_idiom(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = mba_idiom(op, &l, &r) {
        return e;
    }
    if let Some(e) = mba_linear(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = leading_zeros_idiom(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = like_terms(op, &l, &r, bits) {
        return e;
    }
    if let (Expr::Const(a), Expr::Const(b)) = (&l, &r) {
        let (a, b) = (*a, *b);
        let v = match op {
            Op::Add => a.wrapping_add(b),
            Op::Sub => a.wrapping_sub(b),
            Op::Mul => a.wrapping_mul(b),
            Op::Div => {
                if b & m == 0 {
                    return Expr::Bin(op, Box::new(l), Box::new(r));
                }
                (a & m) / (b & m)
            }
            Op::Rem => {
                if b & m == 0 {
                    return Expr::Bin(op, Box::new(l), Box::new(r));
                }
                (a & m) % (b & m)
            }
            Op::SDiv | Op::SRem => {
                let (sa, sb) = (
                    sext(a & m, bits).cast_signed(),
                    sext(b & m, bits).cast_signed(),
                );
                if sb == 0 {
                    return Expr::Bin(op, Box::new(l), Box::new(r));
                }
                if op == Op::SDiv {
                    sa.wrapping_div(sb).cast_unsigned()
                } else {
                    sa.wrapping_rem(sb).cast_unsigned()
                }
            }
            Op::And => a & b,
            Op::Or => a | b,
            Op::Xor => a ^ b,
            Op::Shl => (a & m).wrapping_shl(lo32(b) & 63),
            Op::Shr => (a & m).wrapping_shr(lo32(b) & 63),
            Op::Sar => sext(a & m, bits)
                .cast_signed()
                .wrapping_shr(lo32(b) & 63)
                .cast_unsigned(),
            Op::Rol(w) => rotl(a & mask_bits(w), lo32(b), w),
            Op::Ror(w) => rotl(a & mask_bits(w), (u32::from(w)).wrapping_sub(lo32(b)), w),
            Op::MulHi(w) => {
                let wm = mask_bits(w);
                let prod = u128::from(a & wm) * u128::from(b & wm);
                lo64(prod >> w) & wm
            }
            Op::SMulHi(w) => {
                let wm = mask_bits(w);
                let prod = i128::from(sext(a & wm, w).cast_signed())
                    * i128::from(sext(b & wm, w).cast_signed());
                lo64((prod >> w).cast_unsigned()) & wm
            }
            Op::SMulO(w) => {
                let wm = mask_bits(w);
                let prod = i128::from(sext(a & wm, w).cast_signed())
                    * i128::from(sext(b & wm, w).cast_signed());
                let half = 1i128 << (w - 1);
                u64::from(prod < -half || prod >= half)
            }
            Op::UAddO(w) => {
                let wm = mask_bits(w);
                u64::from(u128::from(a & wm) + u128::from(b & wm) > u128::from(wm))
            }
            Op::USubO(w) => {
                let wm = mask_bits(w);
                u64::from((a & wm) < (b & wm))
            }
            Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FMin | Op::FMax => {
                return Expr::Bin(op, Box::new(l), Box::new(r));
            }
        };
        return Expr::Const(v & m);
    }
    match (op, &l, &r) {
        (Op::Xor | Op::Sub, a, b) if a == b => return Expr::Const(0),
        (Op::Add | Op::Sub | Op::Or | Op::Xor | Op::Shl | Op::Shr | Op::Sar, _, Expr::Const(0)) => {
            return l;
        }
        (Op::Mul | Op::Div | Op::SDiv, _, Expr::Const(1)) => return l,
        (Op::UAddO(_) | Op::USubO(_), _, Expr::Const(0)) => return Expr::Const(0),
        (Op::And | Op::Mul, _, Expr::Const(0)) | (Op::And | Op::Mul, Expr::Const(0), _) => {
            return Expr::Const(0);
        }
        (Op::Add | Op::Or | Op::Xor, Expr::Const(0), _) => return r,
        (Op::And, _, Expr::Const(c)) if *c == m => return l,
        (Op::Or, _, Expr::Const(c)) | (Op::Or, Expr::Const(c), _) if *c & m == m => {
            return Expr::Const(m);
        }
        (Op::And, _, Expr::Const(c)) => return mask(l, *c),
        (Op::Add, Expr::Sp(k), Expr::Const(c)) | (Op::Add, Expr::Const(c), Expr::Sp(k)) => {
            return super::frame::moved(k.checked_add(sext(*c, bits).cast_signed()), op, l, r);
        }
        (Op::Sub, Expr::Sp(k), Expr::Const(c)) => {
            return super::frame::moved(k.checked_sub(sext(*c, bits).cast_signed()), op, l, r);
        }
        (Op::Add, Expr::Bin(Op::Add, x, c1), Expr::Const(c2)) => {
            if let Expr::Const(c1) = **c1 {
                return fold(
                    Op::Add,
                    (**x).clone(),
                    Expr::Const(c1.wrapping_add(*c2)),
                    bits,
                );
            }
        }
        (Op::Sub, Expr::Const(0), _) => return unary(UnOp::Neg, r, bits),
        (Op::Sub, _, Expr::Const(c)) => {
            return fold(Op::Add, l, Expr::Const(c.wrapping_neg()), bits);
        }
        (Op::Sub, Expr::Bin(Op::Add, x, c1), _) => {
            if let Expr::Const(c1) = **c1 {
                let inner = fold(Op::Sub, (**x).clone(), r, bits);
                return fold(Op::Add, inner, Expr::Const(c1), bits);
            }
        }
        _ => {}
    }
    Expr::Bin(op, Box::new(l), Box::new(r))
}

/// `sum` with one addend equal to `term` taken out, when its tree of
/// additions holds one.
///
/// A backward `rep movsb` of `r8` bytes after `lea rdi, [rcx+r8-1]` starts
/// at `rdi + 1 - r8`; taking `r8` out of the sum, rather than subtracting
/// it, is what reads as `rcx`.
///
/// # Arguments
///
/// * `sum` - The expression, searched through `+` only.
/// * `term` - The addend to take out.
/// * `bits` - Operation width for the rebuilt sum.
///
/// # Returns
///
/// The rest of the sum, or `None` when no addend equals `term`.
pub(super) fn without_addend(sum: &Expr, term: &Expr, bits: u8) -> Option<Expr> {
    if sum == term {
        return Some(Expr::Const(0));
    }
    let Expr::Bin(Op::Add, a, b) = sum else {
        return None;
    };
    if let Some(rest) = without_addend(a, term, bits) {
        return Some(fold(Op::Add, rest, (**b).clone(), bits));
    }
    without_addend(b, term, bits).map(|rest| fold(Op::Add, (**a).clone(), rest, bits))
}

/// Rotates `v` left by `n` within a `bits`-wide field.
///
/// # Arguments
///
/// * `v` - The value, already masked to `bits`.
/// * `n` - Rotation count (reduced modulo `bits`).
/// * `bits` - Field width.
fn rotl(v: u64, n: u32, bits: u8) -> u64 {
    let w = u32::from(bits);
    let n = n % w;
    if n == 0 {
        return v & mask_bits(bits);
    }
    ((v << n) | (v >> (w - n))) & mask_bits(bits)
}

/// Finds the index expression inside a jump-table address.
///
/// The table is a constant address, or one the lift reads as a string
/// literal because the table's first bytes print (`65 00 94 ff` is "e").
///
/// # Arguments
///
/// * `e` - An address expression, searched anywhere for `table + x * 4` or `* 8`
///   (or `x << 2`, `<< 3`, as a RISC-V `slli` builds it).
///
/// # Returns
///
/// The `x`, or `None` when no scaled index appears.
pub(super) fn table_index(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Bin(Op::Add, a, b) => {
            let scaled = |side: &Expr| match side {
                Expr::Bin(Op::Mul, x, c) if matches!(**c, Expr::Const(4 | 8)) => {
                    Some((**x).clone())
                }
                Expr::Bin(Op::Shl, x, c) if matches!(**c, Expr::Const(2 | 3)) => {
                    Some((**x).clone())
                }
                _ => None,
            };
            if matches!(**a, Expr::Const(_) | Expr::Str(_))
                && let Some(x) = scaled(b)
            {
                return Some(x);
            }
            if matches!(**b, Expr::Const(_) | Expr::Str(_))
                && let Some(x) = scaled(a)
            {
                return Some(x);
            }
            table_index(a).or_else(|| table_index(b))
        }
        Expr::Bin(_, a, b) => table_index(a).or_else(|| table_index(b)),
        Expr::Un(_, x)
        | Expr::Deref(x, _)
        | Expr::Sext(x, _)
        | Expr::Cast(x, _)
        | Expr::Bitcast(x, _) => table_index(x),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Cond(_)
        | Expr::Call(..)
        | Expr::Helper(..)
        | Expr::FConst(..) => None,
        Expr::Ternary(_, a, b) => table_index(a).or_else(|| table_index(b)),
    }
}

/// Over-approximates the bits that may be set in the value of `e`.
///
/// # Arguments
///
/// * `e` - Any expression; unknown shapes yield all ones.
pub(super) fn known_bits(e: &Expr) -> u64 {
    match e {
        Expr::Const(c) => *c,
        Expr::Cond(_) => 1,
        Expr::Deref(_, ty) | Expr::Bitcast(_, ty) => mask_bits(ty.bits().min(64)),
        Expr::Bin(Op::And, a, b) => known_bits(a) & known_bits(b),
        Expr::Bin(Op::Or | Op::Xor, a, b) => known_bits(a) | known_bits(b),
        Expr::Bin(Op::Shl, a, s) => match **s {
            Expr::Const(s) if s < 64 => known_bits(a) << s,
            _ => u64::MAX,
        },
        Expr::Bin(Op::Shr, a, s) => match **s {
            Expr::Const(s) if s < 64 => known_bits(a) >> s,
            _ => u64::MAX,
        },
        Expr::Ternary(_, a, b) => known_bits(a) | known_bits(b),
        Expr::Bin(Op::MulHi(w) | Op::Rol(w) | Op::Ror(w), ..) => mask_bits(*w),
        Expr::Un(UnOp::Bswap, x) => match x.as_ref() {
            Expr::Cast(_, ty) | Expr::Bitcast(_, ty) | Expr::Deref(_, ty) if ty.bits() < 64 => {
                mask_bits(ty.bits())
            }
            _ => u64::MAX,
        },
        Expr::Helper(Helper::Cls, _) => 0x3f,
        Expr::Helper(Helper::RoundToInt(round), _) if round.bits() == 32 => 0xffff_ffff,
        Expr::Helper(Helper::Rbit | Helper::Rev16 | Helper::Rev32, args) => match args.first() {
            Some(Expr::Cast(_, ty) | Expr::Bitcast(_, ty) | Expr::Deref(_, ty))
                if ty.bits() <= 64 =>
            {
                mask_bits(ty.bits())
            }
            _ => u64::MAX,
        },
        Expr::Var(Key::Reg(r)) if r.size() == 4 => 0xffff_ffff,
        Expr::Var(Key::Global(_, bits)) => mask_bits(*bits),
        Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Sext(..)
        | Expr::Cast(..)
        | Expr::Call(..)
        | Expr::Helper(..)
        | Expr::FConst(..) => u64::MAX,
    }
}

/// Reverses a saturating multiply or add.
///
/// `mul` sets the carry when the high half of the product is not zero and
/// `add` when the sum wraps; a `cmov` of all ones on that carry over the
/// low product or the sum is C++26's `mul_sat` or `add_sat`, the shape a
/// standard library's allocation-size guard compiles to.
///
/// # Arguments
///
/// * `cond` - The select's condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
///
/// # Returns
///
/// The call, or `None` when the select is not that shape.
fn saturating(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    use ConditionCode as C;
    let (taken, other) = match cond.cc.0 {
        C::b | C::o => (a, b),
        C::ae | C::no => (b, a),
        _ => return None,
    };
    let (helper, l, r, bits) = match &cond.flags {
        Flags::Carry(Expr::Bin(Op::MulHi(w), l, r)) => {
            (Helper::MulSat(*w), l.as_ref(), r.as_ref(), *w)
        }
        Flags::Add(l, r, w) if matches!(cond.cc.0, C::b | C::ae) => (Helper::AddSat(*w), l, r, *w),
        _ => return None,
    };
    if !matches!(taken, Expr::Const(c) if *c == mask_bits(bits)) {
        return None;
    }
    let (x, y) = match other {
        Expr::Bin(Op::Mul, x, y) if matches!(helper, Helper::MulSat(_)) => (x.as_ref(), y.as_ref()),
        Expr::Bin(Op::Add, x, y) if matches!(helper, Helper::AddSat(_)) => (x.as_ref(), y.as_ref()),
        _ => return None,
    };
    let same = (x == l && y == r) || (x == r && y == l);
    same.then(|| Expr::Helper(helper, vec![l.clone(), r.clone()]))
}

/// The leading sign bits of `v` within `bits`, not counting the sign.
///
/// This is arm64 `cls`. Zero and all-ones count `bits - 1`. A width other
/// than 32 or 64 is `None`: those are the widths the instruction has. The
/// count is at most 63.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width.
pub(super) fn cls_bits(v: u64, bits: u8) -> Option<u64> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let v = v & mask_bits(bits);
    let runs = ((v ^ v.wrapping_shl(1)) & mask_bits(bits)) | 1;
    Some(u64::from(
        runs.leading_zeros().saturating_sub(64 - u32::from(bits)),
    ))
}

/// The bits of `v` reversed within `bits`.
///
/// This is arm64 `rbit`. The low `bits` are reversed and the rest are
/// zero. A width other than 32 or 64 is `None`: those are the widths the
/// instruction has.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width.
pub(super) fn rbit_bits(v: u64, bits: u8) -> Option<u64> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let v = v & mask_bits(bits);
    Some(v.reverse_bits() >> (64 - bits))
}

/// The bytes of each 16-bit half of `v` swapped, within `bits`.
///
/// This is arm64 `rev16`. A width other than 32 or 64 is `None`: those
/// are the widths the instruction has. Bits above `bits` stay zero.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width.
pub(super) fn rev16_bits(v: u64, bits: u8) -> Option<u64> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let v = v & mask_bits(bits);
    let low = 0x00ff_00ff_00ff_00ff;
    Some((((v & low) << 8) | ((v >> 8) & low)) & mask_bits(bits))
}

/// The bytes of each 32-bit word of `v` swapped.
///
/// This is arm64 `rev32`, which has a 64-bit form only. Any other width
/// is `None`.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width.
pub(super) fn rev32_bits(v: u64, bits: u8) -> Option<u64> {
    if bits != 64 {
        return None;
    }
    let swap = |x: u64| u64::from(lo32(x).swap_bytes());
    Some((swap(v >> 32) << 32) | swap(v))
}

/// The float of `fb` bits held in `v`.
///
/// A width other than 32 or 64 is `None`.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width.
pub(super) fn as_float(v: u64, fb: u8) -> Option<f64> {
    match fb {
        32 => Some(f64::from(f32::from_bits(lo32(v)))),
        64 => Some(f64::from_bits(v)),
        _ => None,
    }
}

/// `v` rounded to the nearest integer, ties to even, still a float of `fb` bits.
///
/// This is `frndint`, and the rounding `fist` and `fistp` do before the
/// integer store. A NaN stays a NaN, and the sign of zero stays. A width
/// other than 32 or 64 is `None`. Rounding a single in a wider type would
/// be a different value once the magnitude no longer has a half to spare.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width.
pub(super) fn rint_bits(v: u64, fb: u8) -> Option<u64> {
    match fb {
        32 => Some(u64::from(
            f32::from_bits(lo32(v)).round_ties_even().to_bits(),
        )),
        64 => Some(f64::from_bits(v).round_ties_even().to_bits()),
        _ => None,
    }
}

/// `a - b` clamped at zero, at `bits`.
///
/// This is the unsigned saturating subtract: below `b` the result is 0,
/// and otherwise it is the difference. A width of 0 or above 64 is `None`.
///
/// # Arguments
///
/// * `a` - The minuend.
/// * `b` - The subtrahend.
/// * `bits` - The width.
pub(super) fn sub_sat_bits(a: u64, b: u64, bits: u8) -> Option<u64> {
    if bits == 0 || bits > 64 {
        return None;
    }
    let m = mask_bits(bits);
    let (a, b) = (a & m, b & m);
    Some(a.saturating_sub(b))
}

/// An unsigned compare-select of zero and that compare's difference, as
/// `sub_sat`.
///
/// `a < b ? 0 : a - b` clamps the subtract at zero, and so does
/// `a <= b ? 0 : a - b`: the arms meet at zero when the two values are
/// equal. The same value with the arms swapped is `a >= b ? a - b : 0`
/// or `a > b ? a - b : 0`. The compare is unsigned and at least 64 bits.
/// A signed compare is not this clamp, and a 32-bit subtract does not
/// clamp the rest of the register. The difference has to be that same
/// pair, in subtract order.
///
/// # Arguments
///
/// * `cond` - The select's condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
///
/// # Returns
///
/// `sub_sat` of the two values, or `None` when this is not that shape.
fn saturating_sub(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    use ConditionCode as C;
    let Flags::Cmp(l, r, bits) = &cond.flags else {
        return None;
    };
    if *bits < 64 {
        return None;
    }
    let zero_on_true = match cond.cc.0 {
        C::b | C::be => true,
        C::a | C::ae => false,
        _ => return None,
    };
    let (taken, other) = if zero_on_true { (a, b) } else { (b, a) };
    let diff = Expr::Bin(Op::Sub, Box::new(l.clone()), Box::new(r.clone()));
    if !matches!(taken, Expr::Const(0)) || other != &diff {
        return None;
    }
    Some(Expr::Helper(Helper::SubSat, vec![l.clone(), r.clone()]))
}

/// A compare-select of its own operands, as `min` or `max`.
///
/// `l <= r ? l : r` is the minimum and `l <= r ? r : l` the maximum, and
/// the same with the test reversed. Signed condition codes (`l`, `le`,
/// `g`, `ge`) spell `min` and `max`; unsigned ones (`b`, `be`, `a`, `ae`)
/// spell `umin` and `umax`. A float compare is not one of those: `fcmovb`
/// is below or unordered, which is neither `umax` nor `fmax`. The arguments stay in compare order. A compare
/// narrower than the machine word stays a ternary: a 32-bit signed minimum is not
/// the signed minimum of the zero-extended values. An equality test, or a
/// value that is not one of the two operands, stays a ternary. `test x, x`
/// under a signed code compares `x` with zero, so `test eax, eax; cmovg
/// edx, eax` over a zeroed `edx` is `max(x, 0)`.
///
/// # Arguments
///
/// * `cond` - The select's condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
/// * `word` - The machine word in bits, the width the helpers compute at.
///
/// # Returns
///
/// The call, or `None` when the select is not that shape.
pub(super) fn extremum(cond: &Cond, a: &Expr, b: &Expr, word: u8) -> Option<Expr> {
    use ConditionCode as C;
    let zero = Expr::Const(0);
    let (l, r, bits) = match &cond.flags {
        Flags::Cmp(l, r, bits) => (l, r, bits),
        Flags::Test(x, y, bits) if x == y && matches!(cond.cc.0, C::l | C::le | C::g | C::ge) => {
            (x, &zero, bits)
        }
        _ => return None,
    };
    if *bits != word || l.is_float() || r.is_float() {
        return None;
    }
    let lesser = match cond.cc.0 {
        C::l | C::le | C::b | C::be => true,
        C::g | C::ge | C::a | C::ae => false,
        _ => return None,
    };
    let pick_min = if a == l && b == r {
        lesser
    } else if a == r && b == l {
        !lesser
    } else {
        return None;
    };
    let signed = matches!(cond.cc.0, C::l | C::le | C::g | C::ge);
    let helper = match (signed, pick_min) {
        (true, true) => Helper::Min,
        (true, false) => Helper::Max,
        (false, true) => Helper::UMin,
        (false, false) => Helper::UMax,
    };
    Some(Expr::Helper(helper, vec![l.clone(), r.clone()]))
}

/// The two's-complement absolute value of `v` at `bits`.
///
/// The minimum signed value keeps its bits: negating it wraps, which is
/// what `neg` then `cmovs` leaves in the register. A width of 0 or above
/// 64 is `None`.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width.
pub(super) fn abs_bits(v: u64, bits: u8) -> Option<u64> {
    if bits == 0 || bits > 64 {
        return None;
    }
    let v = v & mask_bits(bits);
    let signed = sext(v, bits).cast_signed();
    let magnitude = signed.checked_abs().unwrap_or(signed);
    Some(magnitude.cast_unsigned() & mask_bits(bits))
}

/// A compare-select of a value and its negation, as `abs`.
///
/// `x < 0 ? -x : x` is `abs(x)`, and so is `neg` then `cmovs` of the
/// original: the sign flag of `0 - x`. The opposite arm order is `-abs(x)`.
/// The compare has to be against zero, signed (`l`, `le`, `g`, `ge`) or
/// the sign flag (`s`, `ns`), at 64 bits. A narrower select stays a
/// ternary. A 32-bit absolute value is not the absolute value of the
/// zero-extended bits: a negative 32-bit lane would change sign.
///
/// # Arguments
///
/// * `cond` - The select's condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
///
/// # Returns
///
/// `abs` of the operand, or its negation, or `None` when the select is
/// not that shape.
fn absolute(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    use ConditionCode as C;
    let (src, neg_on_true) = match (a, b) {
        (Expr::Un(UnOp::Neg, n), other) if other == n.as_ref() => (n.as_ref(), true),
        (other, Expr::Un(UnOp::Neg, n)) if other == n.as_ref() => (n.as_ref(), false),
        _ => return None,
    };
    let Flags::Cmp(l, r, bits) = &cond.flags else {
        return None;
    };
    if *bits < 64 {
        return None;
    }
    let src_on_left = match (l, r) {
        (s, Expr::Const(0)) if s == src => true,
        (Expr::Const(0), s) if s == src => false,
        _ => return None,
    };
    let neg_when_abs = match (src_on_left, cond.cc.0) {
        (true, C::l | C::le | C::s) | (false, C::g | C::ge | C::ns) => true,
        (true, C::g | C::ge | C::ns) | (false, C::l | C::le | C::s) => false,
        _ => return None,
    };
    let call = Expr::Helper(Helper::Llabs, vec![src.clone()]);
    if neg_on_true == neg_when_abs {
        Some(call)
    } else {
        Some(Expr::Un(UnOp::Neg, Box::new(call)))
    }
}

/// Builds `cond ? a : b` with the boolean idioms folded.
///
/// A decidable condition, or one [`super::opaque::constant_outcome`] proves
/// never varies, picks its side; equal sides collapse; `c ? 1 : 0`
/// is `c` and `c ? 0 : 1` is `!c`; all ones on a carry over the product or
/// sum that set it is the saturating operation ([`saturating`]); a
/// full-width compare that selects one of its own operands is `min`,
/// `max`, `umin`, or `umax` ([`extremum`]); a full-width select of a
/// value and its negation is `abs` ([`absolute`]); an unsigned
/// full-width compare that selects zero over its own difference is
/// `sub_sat` ([`saturating_sub`]).
///
/// # Arguments
///
/// * `cond` - The condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
pub(super) fn ternary(cond: Cond, a: Expr, b: Expr) -> Expr {
    if let Some(outcome) = cond.eval().or_else(|| {
        super::opaque::constant_outcome(&cond)
            .filter(|(_, ev)| *ev == Evidence::Proven)
            .map(|(o, _)| o)
    }) {
        return if outcome { a } else { b };
    }
    if a == b {
        return a;
    }
    if let Some(e) = saturating(&cond, &a, &b)
        .or_else(|| extremum(&cond, &a, &b, 64))
        .or_else(|| absolute(&cond, &a, &b))
        .or_else(|| saturating_sub(&cond, &a, &b))
    {
        return e;
    }
    match (&a, &b) {
        (Expr::Const(1), Expr::Const(0)) => Expr::Cond(Box::new(cond)),
        (Expr::Const(0), Expr::Const(1)) => Expr::Cond(Box::new(cond.invert())),
        _ => Expr::Ternary(Box::new(cond), Box::new(a), Box::new(b)),
    }
}

/// Reads the bits of a value as another type of the same width.
///
/// Bits read back as the type they came from are the value itself, a
/// constant's bits are the constant at the other type, and
/// the bits of a float with the sign bit flipped or cleared, read back as
/// the float, are its negation or its magnitude: `movq rax, xmm0; xor
/// rax, rcx; movq xmm0, rax` with `rcx` the sign bit is `-x`, exactly, NaN
/// included.
///
/// # Arguments
///
/// * `e` - The value.
/// * `ty` - The type its bits are read as.
///
/// # Returns
///
/// The value at `ty`.
pub(super) fn bitcast(e: Expr, ty: Ty) -> Expr {
    let bits = ty.bits();
    let sign = 1u64 << (bits.clamp(1, 64) - 1);
    if matches!(ty, Ty::F32 | Ty::F64)
        && let Expr::Bin(op @ (Op::Xor | Op::And), l, r) = &e
        && let (Expr::Bitcast(f, t), Expr::Const(c)) | (Expr::Const(c), Expr::Bitcast(f, t)) =
            (l.as_ref(), r.as_ref())
        && t.bits() == bits
    {
        if *op == Op::Xor && *c == sign {
            return Expr::Un(UnOp::Neg, f.clone());
        }
        if *op == Op::And && *c == sign - 1 {
            return Expr::Un(UnOp::Fabs, f.clone());
        }
    }
    match e {
        Expr::Bitcast(inner, t) if t.bits() == bits => *inner,
        Expr::FConst(c, t) if t.bits() == bits && !matches!(ty, Ty::F32 | Ty::F64) => {
            Expr::Const(c)
        }
        Expr::Const(c) if matches!(ty, Ty::F32 | Ty::F64) => Expr::FConst(c & mask_bits(bits), ty),
        other => Expr::Bitcast(Box::new(other), ty),
    }
}

/// Builds `e & m` simplified.
///
/// The mask is dropped when `e` provably fits in it, the result is `0` when no
/// bit of `e` survives it (including `(x << s) & m` when the shift moves
/// everything past the mask), nested masks combine, a mask distributes
/// over `|`, a mask of low bits takes the cuts inside `e` those bits
/// pass through ([`low_bits_read`]), and the low bit of the negation of a
/// value that can only be 0 or 1 is that value (`cmpeqss` then `and` by 1).
///
/// # Arguments
///
/// * `e` - The value.
/// * `m` - The mask.
pub(super) fn mask(e: Expr, m: u64) -> Expr {
    let e = match m.checked_add(1) {
        Some(p) if p.is_power_of_two() => {
            low_bits_read(e, u8::try_from(p.trailing_zeros()).unwrap_or(64))
        }
        Some(_) | None => e,
    };
    let known = known_bits(&e);
    if known & !m == 0 {
        return e;
    }
    if known & m == 0 {
        return Expr::Const(0);
    }
    match &e {
        Expr::Const(c) => Expr::Const(c & m),
        Expr::Cond(_) => e,
        Expr::Un(UnOp::Neg, x) if m == 1 && known_bits(x) <= 1 => (**x).clone(),
        Expr::Bin(Op::And, a, c) => {
            if let Expr::Const(c) = **c {
                if c & m == 0 {
                    Expr::Const(0)
                } else if c & m == m {
                    mask((**a).clone(), m)
                } else {
                    Expr::Bin(Op::And, a.clone(), Box::new(Expr::Const(c & m)))
                }
            } else {
                Expr::Bin(Op::And, Box::new(e), Box::new(Expr::Const(m)))
            }
        }
        Expr::Bin(Op::Or, a, b) => {
            let a = mask((**a).clone(), m);
            let b = mask((**b).clone(), m);
            if a.is_zero() {
                b
            } else if b.is_zero() {
                a
            } else {
                Expr::Bin(Op::Or, Box::new(a), Box::new(b))
            }
        }
        Expr::Bin(Op::Shl, a, s) => {
            if let Expr::Const(s) = **s
                && s < 64
                && (m >> s) == 0
            {
                return Expr::Const(0);
            }
            let _ = a;
            Expr::Bin(Op::And, Box::new(e), Box::new(Expr::Const(m)))
        }
        Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Deref(..)
        | Expr::Ternary(..)
        | Expr::Sext(..)
        | Expr::Cast(..)
        | Expr::Bitcast(..)
        | Expr::Call(..)
        | Expr::Helper(..)
        | Expr::FConst(..) => Expr::Bin(Op::And, Box::new(e), Box::new(Expr::Const(m))),
    }
}

/// Applies a unary operator with constant folding at width `bits`.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `e` - The operand.
/// * `bits` - Operation width; constant results are masked to it.
///
/// # Returns
///
/// The folded expression; `bsr` or `bsf` of a constant zero stays symbolic
/// (undefined), and a negation or complement of its own kind cancels.
pub(super) fn unary(op: UnOp, e: Expr, bits: u8) -> Expr {
    let m = mask_bits(bits);
    if let Expr::Const(c) = e {
        let v = match op {
            UnOp::Neg => c.wrapping_neg(),
            UnOp::Not => !c,
            UnOp::Bswap => match bits {
                16 => u64::from(lo16(c).swap_bytes()),
                32 => u64::from(lo32(c).swap_bytes()),
                _ => c.swap_bytes(),
            },
            UnOp::Tzcnt | UnOp::Bsf => {
                let masked = c & m;
                match op {
                    UnOp::Bsf if masked == 0 => return Expr::Un(op, Box::new(e)),
                    _ if masked == 0 => u64::from(bits),
                    _ => u64::from(masked.trailing_zeros()),
                }
            }
            UnOp::Lzcnt => {
                let masked = c & m;
                u64::from(masked.leading_zeros()) - (64 - u64::from(bits))
            }
            UnOp::Bsr => {
                let masked = c & m;
                if masked == 0 {
                    return Expr::Un(op, Box::new(e));
                }
                63 - u64::from(masked.leading_zeros())
            }
            UnOp::Popcnt => u64::from((c & m).count_ones()),
            UnOp::Sqrt | UnOp::Fabs => return Expr::Un(op, Box::new(e)),
        };
        return Expr::Const(v & m);
    }
    if let Expr::Un(inner, x) = &e
        && *inner == op
        && matches!(op, UnOp::Neg | UnOp::Not)
    {
        return (**x).clone();
    }
    Expr::Un(op, Box::new(e))
}

/// Sign-extends the low `from_bits` bits of `e` to 64 bits.
///
/// # Arguments
///
/// * `e` - The value; constants fold, an inner narrower extension is kept.
/// * `from_bits` - Width of the signed field.
pub(super) fn sign_extend(e: Expr, from_bits: u8) -> Expr {
    match e {
        Expr::Const(c) => Expr::Const(sext(c & mask_bits(from_bits), from_bits)),
        Expr::Sext(inner, b) if b <= from_bits => Expr::Sext(inner, b),
        other => Expr::Sext(Box::new(low_bits_read(other, from_bits)), from_bits),
    }
}

/// `e` without the cuts its low `bits` bits pass through unchanged, for a
/// reader of those bits alone.
///
/// The low bits of a sum, a difference, a product, a left shift, a bitwise
/// operation, a negation or a complement depend only on the low bits of
/// their operands, so a mask keeping all of them and a sign extension from
/// at least as many change none of them: `(int32_t)((x & 0xffffffff) + y)`
/// is `(int32_t)(x + y)`, the shape a whole read of a `w` register leaves
/// inside a 32-bit operation. A cast stays: from a float it converts. A
/// mask of a float stays too, because it is the encoding; without it the
/// cast converts the number.
///
/// # Arguments
///
/// * `e` - The value.
/// * `bits` - How many low bits are read, below 64.
pub(super) fn low_bits_read(e: Expr, bits: u8) -> Expr {
    let keep = mask_bits(bits);
    let go = |x: Box<Expr>| Box::new(low_bits_read(*x, bits));
    match e {
        Expr::Bin(Op::And, x, m)
            if !x.is_float() && const_of(&m).is_some_and(|c| c & keep == keep) =>
        {
            low_bits_read(*x, bits)
        }
        Expr::Bin(op @ (Op::Add | Op::Sub | Op::Mul | Op::And | Op::Or | Op::Xor), a, b) => {
            Expr::Bin(op, go(a), go(b))
        }
        Expr::Bin(Op::Shl, a, s) => Expr::Bin(Op::Shl, go(a), s),
        Expr::Un(op @ (UnOp::Neg | UnOp::Not), a) => Expr::Un(op, go(a)),
        Expr::Sext(x, b) if b >= bits => low_bits_read(*x, bits),
        other => other,
    }
}

/// Writes `new` into bit position `shift` of `old` (a partial register write).
///
/// # Arguments
///
/// * `old` - The full-width value being partially overwritten.
/// * `new` - The written value, masked here to `bits`.
/// * `bits` - Width of the written field.
/// * `shift` - Bit position of the field (8 for `ah`-style high bytes).
pub(super) fn merge_bits(old: Expr, new: Expr, bits: u8, shift: u8) -> Expr {
    let field = mask_bits(bits) << shift;
    let kept = fold(Op::And, old, Expr::Const(!field), 64);
    let placed = if shift == 0 {
        mask(new, mask_bits(bits))
    } else {
        fold(
            Op::Shl,
            mask(new, mask_bits(bits)),
            Expr::Const(u64::from(shift)),
            64,
        )
    };
    fold(Op::Or, kept, placed, 64)
}

/// First of the synthetic addresses that stand for TLS block offsets: a
/// singleton slot at offset `off` is the global `TLS_BASE + off`.
pub(super) const TLS_BASE: u64 = 0xffff_f000_0000_0000;

/// Returns the TLS block offset a synthetic global address stands for.
///
/// # Arguments
///
/// * `addr` - A global's address.
pub(super) fn tls_slot(addr: u64) -> Option<u64> {
    addr.checked_sub(TLS_BASE)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod cond_tests;

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod fold_tests;
