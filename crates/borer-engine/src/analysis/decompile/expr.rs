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
    /// constant, load or conversion, a float operation, or a vector or x87
    /// register.
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
            Expr::Call(f, _) => matches!(f.as_str(), "__lane_f32" | "__lane_f64"),
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
    if let Some(e) = select_idiom(op, &l, &r) {
        return e;
    }
    if let Some(e) = sign_absolute(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = rotate_idiom(op, &l, &r, bits) {
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
            return Expr::Sp(k.wrapping_add(sext(*c, bits).cast_signed()));
        }
        (Op::Sub, Expr::Sp(k), Expr::Const(c)) => {
            return Expr::Sp(k.wrapping_sub(sext(*c, bits).cast_signed()));
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
/// * `e` - An address expression, searched anywhere for `table + x * 4` or `* 8`.
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
        Expr::Helper(Helper::RoundToInt(RoundToInt::Signed(32) | RoundToInt::Unsigned(32)), _) => {
            0xffff_ffff
        }
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
fn as_float(v: u64, fb: u8) -> Option<f64> {
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

/// Which `fcvtz` call a name is: the signedness and the integer width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum RoundToInt {
    /// Toward zero into a signed integer of this width.
    Signed(u8),
    /// Toward zero into an unsigned integer of this width.
    Unsigned(u8),
}

impl RoundToInt {
    /// `fcvtzs32`, `fcvtzs64`, `fcvtzu32` or `fcvtzu64`.
    ///
    /// # Arguments
    ///
    /// * `name` - The call's name.
    pub(super) fn parse(name: &str) -> Option<Self> {
        match name {
            "fcvtzs32" => Some(Self::Signed(32)),
            "fcvtzs64" => Some(Self::Signed(64)),
            "fcvtzu32" => Some(Self::Unsigned(32)),
            "fcvtzu64" => Some(Self::Unsigned(64)),
            _ => None,
        }
    }

    /// The operation for a signedness and an integer width.
    ///
    /// A width other than 32 or 64 is `None`.
    ///
    /// # Arguments
    ///
    /// * `signed` - Whether the integer is signed.
    /// * `bits` - The integer's width.
    pub(super) fn new(signed: bool, bits: u8) -> Option<Self> {
        match (signed, bits) {
            (true, 32 | 64) => Some(Self::Signed(bits)),
            (false, 32 | 64) => Some(Self::Unsigned(bits)),
            _ => None,
        }
    }

    /// The printed name, or `None` when the width is not 32 or 64.
    pub(super) fn name(self) -> Option<&'static str> {
        match self {
            Self::Signed(32) => Some("fcvtzs32"),
            Self::Signed(64) => Some("fcvtzs64"),
            Self::Unsigned(32) => Some("fcvtzu32"),
            Self::Unsigned(64) => Some("fcvtzu64"),
            Self::Signed(_) | Self::Unsigned(_) => None,
        }
    }

    /// Converts `v`, a float of `fb` bits, as this operation.
    ///
    /// # Arguments
    ///
    /// * `v` - The float's bits.
    /// * `fb` - The float's width.
    pub(super) fn apply(self, v: u64, fb: u8) -> Option<u64> {
        match self {
            Self::Signed(bits) => fcvtzs_bits(v, fb, bits),
            Self::Unsigned(bits) => fcvtzu_bits(v, fb, bits),
        }
    }
}

/// The float width a `fcvtz` call records in its second argument.
///
/// A missing argument uses `fallback`. A present argument that is not the
/// constant 32 or 64 is `None`: that is not a width, and it is not read
/// from the value instead.
///
/// # Arguments
///
/// * `width` - The call's second argument.
/// * `fallback` - The width the value's own type gives, when the call
///   records none.
pub(super) fn fcvt_float_width(width: Option<&Expr>, fallback: Option<u8>) -> Option<u8> {
    match width {
        Some(Expr::Const(32)) => Some(32),
        Some(Expr::Const(64)) => Some(64),
        Some(_) => None,
        None => fallback,
    }
}

/// `v` as a float of `fb` bits, rounded toward zero into a signed integer
/// of `bits`.
///
/// This is arm64 `fcvtzs`. A NaN is 0. A value past either signed bound
/// saturates to that bound. Any width other than 32 or 64, for the float
/// or the integer, is `None`.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width.
/// * `bits` - The integer's width.
#[expect(
    clippy::cast_possible_truncation,
    reason = "the bounds keep the truncated value within the signed integer"
)]
pub(super) fn fcvtzs_bits(v: u64, fb: u8, bits: u8) -> Option<u64> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let t = as_float(v, fb)?.trunc();
    if t.is_nan() {
        return Some(0);
    }
    let top = 2f64.powi(i32::from(bits) - 1);
    let bound = 1u64 << (u32::from(bits) - 1);
    if t < -top {
        return Some(bound);
    }
    if t >= top {
        return Some(bound - 1);
    }
    Some((t as i64).cast_unsigned() & mask_bits(bits))
}

/// `v` as a float of `fb` bits, rounded toward zero into an unsigned
/// integer of `bits`.
///
/// This is arm64 `fcvtzu`. A NaN or a negative value is 0. A value past
/// the unsigned bound saturates to every bit set. Any width other than
/// 32 or 64, for the float or the integer, is `None`. A value in
/// `[2^63, 2^64)` fits the result and not `i64`, so the cast goes
/// straight to `u64`.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width.
/// * `bits` - The integer's width.
pub(super) fn fcvtzu_bits(v: u64, fb: u8, bits: u8) -> Option<u64> {
    if !matches!(bits, 32 | 64) {
        return None;
    }
    let t = as_float(v, fb)?.trunc();
    if t.is_nan() || t < 0.0 {
        return Some(0);
    }
    let top = 2f64.powi(i32::from(bits) - 1);
    if t >= top * 2.0 {
        return Some(mask_bits(bits));
    }
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "the bounds keep the truncated value within the unsigned width"
    )]
    let v = t as u64;
    Some(v & mask_bits(bits))
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
/// narrower than 64 bits stays a ternary: a 32-bit signed minimum is not
/// the signed minimum of the zero-extended values. An equality test, or a
/// value that is not one of the two operands, stays a ternary.
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
fn extremum(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    use ConditionCode as C;
    let Flags::Cmp(l, r, bits) = &cond.flags else {
        return None;
    };
    if *bits < 64 || l.is_float() || r.is_float() {
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
        .or_else(|| extremum(&cond, &a, &b))
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
mod tests {
    /// A bit scan against the width is a leading-zero count.
    ///
    /// A compiler writes `clz` as `(width - 1) - bsr(x)` and spells the
    /// subtraction as an exclusive or, so both forms have to read as the
    /// count, and the width has to match the operands.
    #[test]
    fn a_bit_scan_against_the_width_is_a_count() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let scan = Expr::Un(super::UnOp::Bsr, Box::new(x.clone()));
        let want = Expr::Un(super::UnOp::Lzcnt, Box::new(x));
        assert_eq!(
            super::fold(Op::Xor, scan.clone(), Expr::Const(63), 64),
            want
        );
        assert_eq!(
            super::fold(Op::Xor, Expr::Const(63), scan.clone(), 64),
            want
        );
        assert_eq!(
            super::fold(Op::Sub, Expr::Const(63), scan.clone(), 64),
            want
        );
        assert_eq!(
            super::fold(Op::Xor, scan.clone(), Expr::Const(31), 32),
            want
        );
        assert_ne!(super::fold(Op::Xor, scan.clone(), Expr::Const(7), 64), want);
        assert_ne!(super::fold(Op::Xor, scan, Expr::Const(31), 64), want);
    }

    /// Every rewritten identity is true for all inputs, checked numerically.
    ///
    /// A rewrite that is merely believed changes what the code does, silently
    /// and everywhere. These are the five the folder applies, evaluated over
    /// a spread of values including the edges where carries wrap.
    #[test]
    fn the_rewritten_identities_hold() {
        let values: Vec<u64> = vec![
            0,
            1,
            2,
            3,
            0xff,
            0x100,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_ffff,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            u64::MAX,
            0xdead_beef_cafe_babe,
            0x0123_4567_89ab_cdef,
        ];
        for &x in &values {
            for &y in &values {
                assert_eq!(
                    (x ^ y).wrapping_add(2u64.wrapping_mul(x & y)),
                    x.wrapping_add(y),
                    "(x^y) + 2*(x&y) == x+y at {x:#x}, {y:#x}"
                );
                assert_eq!(
                    (x ^ y).wrapping_add((x & y) << 1),
                    x.wrapping_add(y),
                    "(x^y) + ((x&y)<<1) == x+y at {x:#x}, {y:#x}"
                );
                assert_eq!(
                    (x & y).wrapping_add(x | y),
                    x.wrapping_add(y),
                    "(x&y) + (x|y) == x+y at {x:#x}, {y:#x}"
                );
                assert_eq!(
                    (x ^ y).wrapping_add(x & y),
                    x | y,
                    "(x^y) + (x&y) == x|y at {x:#x}, {y:#x}"
                );
                assert_eq!(
                    (x | y).wrapping_sub(x & y),
                    x ^ y,
                    "(x|y) - (x&y) == x^y at {x:#x}, {y:#x}"
                );
                assert_eq!(
                    (x | y).wrapping_sub(x ^ y),
                    x & y,
                    "(x|y) - (x^y) == x&y at {x:#x}, {y:#x}"
                );
            }
        }
    }

    /// The folder applies those identities to the expressions it builds.
    #[test]
    fn an_obfuscated_addition_folds_back() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let y = Expr::Var(Key::Reg(crate::isa::x86::Register::RCX));
        let bin =
            |o: Op, a: &Expr, b: &Expr| Expr::Bin(o, Box::new(a.clone()), Box::new(b.clone()));
        let plain = bin(Op::Add, &x, &y);
        let doubled = bin(Op::Mul, &bin(Op::And, &x, &y), &Expr::Const(2));
        assert_eq!(
            super::fold(Op::Add, bin(Op::Xor, &x, &y), doubled, 64),
            plain
        );
        let shifted = bin(Op::Shl, &bin(Op::And, &x, &y), &Expr::Const(1));
        assert_eq!(
            super::fold(Op::Add, bin(Op::Xor, &x, &y), shifted, 64),
            plain
        );
        assert_eq!(
            super::fold(Op::Sub, bin(Op::Or, &x, &y), bin(Op::And, &x, &y), 64),
            bin(Op::Xor, &x, &y)
        );
        let doubled = bin(Op::Mul, &Expr::Const(2), &bin(Op::And, &y, &x));
        assert_eq!(
            super::fold(Op::Add, doubled, bin(Op::Xor, &x, &y), 64),
            plain
        );
    }

    /// A division by a constant whose bits within the width are all zero
    /// is a division by zero, and stays as it is written.
    ///
    /// The divisor `0x100` of an 8-bit division is zero in that width:
    /// folding it divides by its low bits, which are zero.
    #[test]
    fn a_divisor_zero_in_its_width_is_no_constant() {
        for op in [Op::Div, Op::Rem] {
            let folded = super::fold(op, Expr::Const(5), Expr::Const(0x100), 8);
            assert_eq!(
                folded,
                Expr::Bin(op, Box::new(Expr::Const(5)), Box::new(Expr::Const(0x100)))
            );
        }
        assert_eq!(
            super::fold(Op::Div, Expr::Const(0x205), Expr::Const(0x102), 8),
            Expr::Const(2)
        );
    }

    /// A multiply and shift is a division only when it divides every
    /// dividend of its width.
    ///
    /// `0x92492493` is `2^34 / 7` rounded up, but a shift of two leaves its
    /// error too large: at `0xfffffffb` the high half shifted is
    /// `0x24924924`, one more than the quotient by seven. Compilers divide by
    /// seven with the 33-bit magic instead; `0xaaaaaaab >> 1`, a third,
    /// holds everywhere and still reads as the division, of the 32 bits the
    /// multiply read.
    #[test]
    fn a_magic_that_misses_a_dividend_is_no_division() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let shifted = |m: u64, s: u64| {
            let hi = Expr::Bin(Op::MulHi(32), Box::new(Expr::Const(m)), Box::new(x.clone()));
            super::fold(Op::Shr, hi, Expr::Const(s), 32)
        };
        assert!(
            !matches!(shifted(0x9249_2493, 2), Expr::Bin(Op::Div, ..)),
            "{:?}",
            shifted(0x9249_2493, 2)
        );
        let word = Expr::Bin(
            Op::And,
            Box::new(x.clone()),
            Box::new(Expr::Const(0xffff_ffff)),
        );
        assert_eq!(
            shifted(0xaaaa_aaab, 1),
            Expr::Bin(Op::Div, Box::new(word), Box::new(Expr::Const(3)))
        );
        let wrong = (0x9249_2493u128 * 0xffff_fffb) >> 34;
        assert_eq!((wrong, 0xffff_fffbu128 / 7), (0x2492_4924, 0x2492_4923));
    }

    /// A quotient times its divisor less the dividend is the remainder's
    /// negation, no remainder: `7 * (x / 7) - x` stays as it is.
    #[test]
    fn a_product_less_its_dividend_is_no_remainder() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let q = Expr::Bin(Op::SDiv, Box::new(x.clone()), Box::new(Expr::Const(7)));
        let product = Expr::Bin(Op::Mul, Box::new(q), Box::new(Expr::Const(7)));
        for bits in [32, 64] {
            let folded = super::fold(Op::Sub, product.clone(), x.clone(), bits);
            assert!(
                !matches!(folded, Expr::Bin(Op::SRem | Op::Rem, ..)),
                "{folded:?}"
            );
            let rem = super::fold(Op::Sub, x.clone(), product.clone(), bits);
            assert!(matches!(rem, Expr::Bin(Op::SRem, ..)), "{rem:?}");
        }
    }

    /// A signed magic quotient is a division only when its magic has the
    /// sign its shape expects and rounds every negative dividend toward
    /// zero.
    ///
    /// `0x92492493` is the negative magic of a division by seven, the one
    /// whose shape adds the dividend back; without that, at `x = 7` the
    /// product shifted is `-1` and its sign fix makes `0`, not `1`. `2^30`
    /// divides by four exactly, so at `x = -4` the high half is already the
    /// quotient `-1` and the sign fix makes it `0`. `0x66666667 >> 1` with
    /// its fix is a fifth on every dividend and still reads as the division.
    #[test]
    fn a_signed_magic_that_misses_a_dividend_is_no_division() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let fixed = |m: u64, s: u64| {
            let hi = Expr::Bin(
                Op::SMulHi(32),
                Box::new(Expr::Const(m)),
                Box::new(x.clone()),
            );
            let q = super::fold(Op::Sar, hi, Expr::Const(s), 32);
            let sign = super::fold(Op::Shr, q.clone(), Expr::Const(31), 32);
            super::fold(Op::Add, q, sign, 32)
        };
        for (m, s) in [(0x9249_2493, 2), (0x4000_0000, 0)] {
            let out = fixed(m, s);
            assert!(!matches!(out, Expr::Bin(Op::SDiv, ..)), "{m:#x}: {out:?}");
        }
        let fifth = Expr::Bin(
            Op::SDiv,
            Box::new(Expr::Sext(Box::new(x.clone()), 32)),
            Box::new(Expr::Const(5)),
        );
        assert_eq!(fixed(0x6666_6667, 1), fifth);
        let wrong = |m: i64, s: u32, v: i64| {
            let q = (m * v) >> (32 + s);
            q + i64::from(q < 0)
        };
        let negative = i64::from(0x9249_2493u32.cast_signed());
        assert_eq!((wrong(negative, 2, 7), wrong(0x4000_0000, 0, -4)), (0, 0));
    }

    /// A halving through a sign is a division only at the sign's width.
    ///
    /// `(x + (x >>> 63)) >> 1` as a 32-bit shift adds a sign bit the 32-bit
    /// value does not have: at `x = 0x80000001` it is `0xc0000000`, where
    /// the quotient by two is `0xc0000001`. The same shape as a 64-bit shift
    /// is the division.
    #[test]
    fn a_halving_through_another_widths_sign_is_no_division() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let halved = |bits: u8| {
            let sign = Expr::Bin(Op::Shr, Box::new(x.clone()), Box::new(Expr::Const(63)));
            let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(sign));
            super::fold(Op::Sar, sum, Expr::Const(1), bits)
        };
        assert!(
            !matches!(halved(32), Expr::Bin(Op::SDiv, ..)),
            "{:?}",
            halved(32)
        );
        assert_eq!(
            halved(64),
            Expr::Bin(Op::SDiv, Box::new(x), Box::new(Expr::Const(2)))
        );
    }

    /// A 32-bit shift by 31 through the sign is no division by `2^31`.
    ///
    /// `(x + ((int32_t)x >> 31 & 0x7fffffff)) >> 31` is `-1` at
    /// `x = INT_MIN`; a 32-bit division by `0x80000000` is a division by
    /// `INT_MIN`, which gives `1`. A shift by 30 is still a quotient.
    #[test]
    fn a_shift_by_the_sign_bit_is_no_power_quotient() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let quotient = |k: u64| {
            let lane = Expr::Sext(Box::new(x.clone()), 32);
            let sign = Expr::Bin(Op::Sar, Box::new(lane), Box::new(Expr::Const(31)));
            let fix = Expr::Bin(Op::And, Box::new(sign), Box::new(Expr::Const((1 << k) - 1)));
            let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(fix));
            super::fold(Op::Sar, sum, Expr::Const(k), 32)
        };
        assert!(
            !matches!(quotient(31), Expr::Bin(Op::SDiv, ..)),
            "{:?}",
            quotient(31)
        );
        assert!(
            matches!(quotient(30), Expr::Bin(Op::SDiv, ..)),
            "{:?}",
            quotient(30)
        );
    }

    /// A shift of a sign-extended lane halves through the lane's sign.
    ///
    /// `(int32_t)(x + ((x >> 63) & 1)) >> 1` keeps the low 32 bits of a sum
    /// fixed by the 64-bit sign: at `x = 0x80000000` it is `0xc0000000`
    /// sign-extended, where `x / 2` is `0x40000000`. Fixed by the lane's own
    /// sign it is `(int32_t)x / 2`.
    #[test]
    fn a_lane_halves_through_its_own_sign() {
        let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
        let halved = |sign: Expr| {
            let fix = Expr::Bin(Op::And, Box::new(sign), Box::new(Expr::Const(1)));
            let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(fix));
            super::fold(Op::Sar, Expr::Sext(Box::new(sum), 32), Expr::Const(1), 64)
        };
        let wide = Expr::Bin(Op::Sar, Box::new(x.clone()), Box::new(Expr::Const(63)));
        assert!(
            !matches!(halved(wide.clone()), Expr::Bin(Op::SDiv, ..)),
            "{:?}",
            halved(wide)
        );
        let lane = Expr::Sext(Box::new(x.clone()), 32);
        let own = Expr::Bin(Op::Sar, Box::new(lane.clone()), Box::new(Expr::Const(31)));
        assert_eq!(
            halved(own),
            Expr::Bin(Op::SDiv, Box::new(lane), Box::new(Expr::Const(2)))
        );
    }

    use super::{Expr, Key, Op};
    use crate::analysis::decompile::expr_render::{compact_literal, vector_equality};

    /// A float constant renders compactly, never as a 336-character decimal.
    ///
    /// A value with many digits takes an exponent, and the bytes of a wide
    /// string moved through `movsd` (or a subnormal) take the exact
    /// hexadecimal literal.
    #[test]
    fn float_constants_render_compactly() {
        use super::Ty;
        use crate::analysis::decompile::expr_render::render_fconst;
        let f64s = |v: f64| render_fconst(v.to_bits(), Ty::F64);
        assert_eq!(f64s(2.0), "2.0");
        assert_eq!(f64s(0.1), "0.1");
        assert_eq!(f64s(-1.5), "-1.5");
        assert_eq!(f64s(1e30), "1e30");
        assert_eq!(f64s(1.25e-25), "1.25e-25");
        assert_eq!(
            render_fconst(0x0073_0074_006e_0065, Ty::F64),
            "0x1.30074006e0065p-1016"
        );
        assert_eq!(render_fconst(1, Ty::F64), "0x0.0000000000001p-1022");
        assert_eq!(render_fconst(0x41, Ty::F32), "0x0.000082p-126f");
        assert_eq!(render_fconst(0x3f80_0000, Ty::F32), "1.0f");
    }

    /// Builds the gathered-mask expression a fixed string compare produces.
    ///
    /// # Arguments
    ///
    /// * `gather` - The mask-gathering mnemonic.
    /// * `lanes` - The lane-comparing mnemonic.
    fn mask_of(gather: &str, lanes: &str) -> Expr {
        Expr::Call(
            gather.to_owned(),
            vec![Expr::Call(
                lanes.to_owned(),
                vec![Expr::Const(1), Expr::Const(2)],
            )],
        )
    }

    /// An all-lanes-equal mask test is the two vectors being equal.
    ///
    /// # Panics
    ///
    /// When the fold does not recognise the idiom.
    #[test]
    fn a_lane_mask_test_is_a_vector_comparison() {
        let m = mask_of("pmovmskb", "pcmpeqb");
        assert_eq!(
            vector_equality(&m, &Expr::Const(0xffff)),
            Some((&Expr::Const(1), &Expr::Const(2)))
        );
        let v = mask_of("vpmovmskb", "vpcmpeqb");
        assert!(vector_equality(&v, &Expr::Const(0xffff_ffff)).is_some());
    }

    /// A mask tested against anything but all ones is some other test.
    ///
    /// # Panics
    ///
    /// When the fold claims an idiom that is not there.
    #[test]
    fn a_partial_lane_mask_test_is_not_a_vector_comparison() {
        let m = mask_of("pmovmskb", "pcmpeqb");
        assert_eq!(vector_equality(&m, &Expr::Const(0x8000)), None);
        assert_eq!(vector_equality(&m, &Expr::Const(0)), None);
        let other = mask_of("pmovmskb", "pcmpgtb");
        assert_eq!(vector_equality(&other, &Expr::Const(0xffff)), None);
    }

    /// Signature literals become `__FUNCSIG__`, foreign ones keep the name,
    /// paths keep two components, prose stays.
    ///
    /// # Panics
    ///
    /// When a rendering disagrees with its expectation.
    #[test]
    fn literals_compact() {
        let sig = "\"int __cdecl Foo::Bar(void)\"";
        assert_eq!(compact_literal(sig, "Foo::Bar"), "__FUNCSIG__");
        assert_eq!(compact_literal(sig, "Baz"), "__FUNCSIG__(Foo::Bar)");
        let path = "\"C:\\\\ws\\\\code\\\\foundation\\\\util/fourcc.h\"";
        assert_eq!(compact_literal(path, "x"), "\"util/fourcc.h\"");
        assert_eq!(compact_literal("\"f.IsValid()\"", "x"), "\"f.IsValid()\"");
        assert_eq!(compact_literal("\"a/b.h\"", "x"), "\"a/b.h\"");
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod cond_tests {
    //! Conditions read back as C: a small evaluator of the C the renderer
    //! writes for a condition, and the property that every rendering means
    //! what the flags mean and its inversion is its negation.

    use std::sync::Arc;

    use crate::isa::x86::{ConditionCode, Register};

    use super::{Cc, Cond, Expr, Flags, Key, Names, Op, Ty};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// A C value: an integer with its width and signedness, or a double.
    #[derive(Debug, Clone, Copy)]
    enum V {
        /// An integer, held exactly, of this many bits, signed or not.
        I(i128, u8, bool),
        /// A floating-point value.
        F(f64),
    }

    impl V {
        /// The value wrapped to an integer type, as a C conversion does.
        ///
        /// # Arguments
        ///
        /// * `bits` - The type's width.
        /// * `signed` - The type is signed.
        fn to_int(self, bits: u8, signed: bool) -> V {
            let raw = match self {
                V::I(v, ..) => v,
                #[expect(clippy::cast_possible_truncation, reason = "C truncates toward zero")]
                V::F(f) => f as i128,
            };
            let m = (1i128 << bits) - 1;
            let mut v = raw & m;
            if signed && v >> (bits - 1) & 1 == 1 {
                v -= 1i128 << bits;
            }
            V::I(v, bits, signed)
        }

        /// The value as a double.
        #[expect(clippy::cast_precision_loss, reason = "the test values are exact")]
        fn to_f(self) -> f64 {
            match self {
                V::I(v, ..) => v as f64,
                V::F(f) => f,
            }
        }

        /// The value is nonzero, as a condition reads it.
        fn truth(self) -> bool {
            match self {
                V::I(v, ..) => v != 0,
                V::F(f) => f != 0.0,
            }
        }

        /// A C boolean result.
        ///
        /// # Arguments
        ///
        /// * `b` - The truth.
        fn of(b: bool) -> V {
            V::I(i128::from(b), 32, true)
        }
    }

    /// Promotes two operands to their common type (the usual arithmetic
    /// conversions).
    ///
    /// # Arguments
    ///
    /// * `a` - Left operand.
    /// * `b` - Right operand.
    fn common(a: V, b: V) -> (V, V) {
        match (promote(a), promote(b)) {
            (x @ V::I(_, xb, xs), y @ V::I(_, yb, ys)) => {
                let (bits, signed) = match xb.cmp(&yb) {
                    std::cmp::Ordering::Equal => (xb, xs && ys),
                    std::cmp::Ordering::Greater => (xb, xs),
                    std::cmp::Ordering::Less => (yb, ys),
                };
                (x.to_int(bits, signed), y.to_int(bits, signed))
            }
            (x, y) => (V::F(x.to_f()), V::F(y.to_f())),
        }
    }

    /// Promotes an integer narrower than `int` to `int`.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn promote(v: V) -> V {
        match v {
            V::I(_, bits, _) if bits < 32 => v.to_int(32, true),
            other => other,
        }
    }

    /// A recursive-descent reader of the C a condition renders as.
    struct P<'s> {
        /// The text.
        s: &'s [u8],
        /// The read position.
        i: usize,
        /// The two integer variables' values.
        ints: (u32, u32),
        /// The two float variables' values.
        floats: (f64, f64),
    }

    impl P<'_> {
        /// Skips blanks and comments.
        fn ws(&mut self) {
            loop {
                while self.s.get(self.i).is_some_and(u8::is_ascii_whitespace) {
                    self.i += 1;
                }
                if self.s[self.i..].starts_with(b"/*") {
                    let end = self.s[self.i..]
                        .windows(2)
                        .position(|w| w == b"*/")
                        .unwrap_or(0);
                    self.i += end + 2;
                } else {
                    return;
                }
            }
        }

        /// Consumes `tok` when it comes next and is not the start of a longer
        /// operator.
        ///
        /// # Arguments
        ///
        /// * `tok` - The operator.
        fn eat(&mut self, tok: &str) -> bool {
            self.ws();
            let t = tok.as_bytes();
            if !self.s[self.i..].starts_with(t) {
                return false;
            }
            let next = self.s.get(self.i + t.len()).copied();
            let longer = match tok {
                "&" => next == Some(b'&'),
                "|" => next == Some(b'|'),
                "<" | ">" => matches!(next, Some(b'=' | b'<' | b'>')),
                "!" => next == Some(b'='),
                _ => false,
            };
            if longer {
                return false;
            }
            self.i += t.len();
            true
        }

        /// Reads a whole expression, the conditional operator included.
        fn expr(&mut self) -> V {
            let c = self.binary(0);
            if self.eat("?") {
                let a = self.expr();
                assert!(self.eat(":"));
                let b = self.expr();
                return if c.truth() { a } else { b };
            }
            c
        }

        /// Reads binary operators of precedence `level` and up.
        ///
        /// # Arguments
        ///
        /// * `level` - Index into the precedence table.
        fn binary(&mut self, level: usize) -> V {
            /// The binary operators by precedence, loosest first.
            const LEVELS: [&[&str]; 10] = [
                &["||"],
                &["&&"],
                &["|"],
                &["^"],
                &["&"],
                &["==", "!="],
                &["<=", ">=", "<", ">"],
                &["<<", ">>"],
                &["+", "-"],
                &["*", "/", "%"],
            ];
            let Some(ops) = LEVELS.get(level) else {
                return self.unary();
            };
            let mut l = self.binary(level + 1);
            'outer: loop {
                for op in *ops {
                    if self.eat(op) {
                        let r = self.binary(level + 1);
                        l = apply(op, l, r);
                        continue 'outer;
                    }
                }
                return l;
            }
        }

        /// Reads a prefix operator, a cast, or a primary.
        fn unary(&mut self) -> V {
            self.ws();
            if self.eat("!") {
                return V::of(!self.unary().truth());
            }
            if self.eat("-") {
                return match promote(self.unary()) {
                    V::F(f) => V::F(-f),
                    V::I(x, bits, signed) => V::I(-x, bits, signed).to_int(bits, signed),
                };
            }
            if self.eat("~") {
                return match promote(self.unary()) {
                    V::F(f) => V::F(f),
                    V::I(x, bits, signed) => V::I(!x, bits, signed).to_int(bits, signed),
                };
            }
            let save = self.i;
            if self.eat("(") {
                let start = self.i;
                while self
                    .s
                    .get(self.i)
                    .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_')
                {
                    self.i += 1;
                }
                let name = std::str::from_utf8(&self.s[start..self.i]).unwrap_or("");
                let ty = match name {
                    "int8_t" => Some((8, true)),
                    "int16_t" => Some((16, true)),
                    "int32_t" => Some((32, true)),
                    "int64_t" => Some((64, true)),
                    "uint8_t" => Some((8, false)),
                    "uint16_t" => Some((16, false)),
                    "uint32_t" => Some((32, false)),
                    "uint64_t" => Some((64, false)),
                    "float" | "double" => Some((0, true)),
                    _ => None,
                };
                if let Some((bits, signed)) = ty
                    && self.eat(")")
                {
                    let v = self.unary();
                    return if bits == 0 {
                        V::F(v.to_f())
                    } else {
                        v.to_int(bits, signed)
                    };
                }
                self.i = save;
                assert!(self.eat("("));
                let v = self.expr();
                assert!(self.eat(")"), "unclosed at {}", self.i);
                return v;
            }
            self.primary()
        }

        /// Reads a literal, a variable or a call.
        fn primary(&mut self) -> V {
            self.ws();
            let start = self.i;
            while self
                .s
                .get(self.i)
                .is_some_and(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'.'))
            {
                self.i += 1;
            }
            let word = std::str::from_utf8(&self.s[start..self.i]).unwrap_or("");
            assert!(!word.is_empty(), "nothing to read at {start}");
            if word.starts_with(|c: char| c.is_ascii_digit()) {
                if let Some(h) = word.strip_prefix("0x") {
                    let v = i128::from_str_radix(h, 16).unwrap_or(0);
                    let (bits, signed) = if v <= i128::from(i32::MAX) {
                        (32, true)
                    } else if v <= i128::from(u32::MAX) {
                        (32, false)
                    } else {
                        (64, v <= i128::from(i64::MAX))
                    };
                    return V::I(v, bits, signed);
                }
                if word.contains('.') {
                    return V::F(word.trim_end_matches('f').parse().unwrap_or(0.0));
                }
                let v: i128 = word.parse().unwrap_or(0);
                return V::I(v, if v <= i128::from(i32::MAX) { 32 } else { 64 }, true);
            }
            match word {
                "rax" => return V::I(i128::from(self.ints.0), 32, false),
                "rcx" => return V::I(i128::from(self.ints.1), 32, false),
                "xmm0" => return V::F(self.floats.0),
                "xmm1" => return V::F(self.floats.1),
                "NAN" => return V::F(f64::NAN),
                "INFINITY" => return V::F(f64::INFINITY),
                "FLAGS_UNKNOWN" => return V::of(opaque(word, &[])),
                _ => {}
            }
            assert!(self.eat("("), "unknown name {word}");
            let mut args = Vec::new();
            if !self.eat(")") {
                loop {
                    args.push(self.expr());
                    if self.eat(")") {
                        break;
                    }
                    assert!(self.eat(","), "bad call at {}", self.i);
                }
            }
            call(word, &args)
        }
    }

    /// A stable pseudo-random truth for a test the renderer cannot decide,
    /// the same for the same call.
    ///
    /// # Arguments
    ///
    /// * `name` - The opaque test's name.
    /// * `args` - Its arguments.
    fn opaque(name: &str, args: &[V]) -> bool {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in name.bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
        for a in args {
            let V::I(v, ..) = a.to_int(64, false) else {
                continue;
            };
            h = (h ^ u64::try_from(v).unwrap_or(0)).wrapping_mul(0x0100_0000_01b3);
        }
        h >> 63 == 1
    }

    /// Evaluates one of the calls the renderer writes in a condition.
    ///
    /// # Arguments
    ///
    /// * `name` - The function.
    /// * `args` - Its evaluated arguments.
    fn call(name: &str, args: &[V]) -> V {
        let f = |i: usize| args.get(i).map_or(0.0, |a| a.to_f());
        let u = |i: usize, bits: u8| match args.get(i).map(|a| a.to_int(bits, false)) {
            Some(V::I(v, ..)) => v,
            _ => 0,
        };
        let s = |i: usize, bits: u8| match args.get(i).map(|a| a.to_int(bits, true)) {
            Some(V::I(v, ..)) => v,
            _ => 0,
        };
        let width = |prefix: &str| name.strip_prefix(prefix).and_then(|w| w.parse::<u8>().ok());
        let signed_out = |t: i128, w: u8| t >= 1i128 << (w - 1) || t < -(1i128 << (w - 1));
        if let Some(w) = width("uaddo") {
            return V::of(u(0, w) + u(1, w) >= 1i128 << w);
        }
        if let Some(w) = width("saddo") {
            return V::of(signed_out(s(0, w) + s(1, w), w));
        }
        if let Some(w) = width("ssubo") {
            return V::of(signed_out(s(0, w) - s(1, w), w));
        }
        if name.starts_with("flags_") {
            return V::of(opaque(name, args));
        }
        V::of(match name {
            "isgreater" => f(0) > f(1),
            "isgreaterequal" => f(0) >= f(1),
            "isless" => f(0) < f(1),
            "islessequal" => f(0) <= f(1),
            "isunordered" => f(0).is_nan() || f(1).is_nan(),
            "parity8" => u(0, 8).count_ones().is_multiple_of(2),
            _ => panic!("unknown call {name}"),
        })
    }

    /// Applies a binary operator under C's conversions.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `l` - Left operand.
    /// * `r` - Right operand.
    fn apply(op: &str, l: V, r: V) -> V {
        if op == "&&" {
            return V::of(l.truth() && r.truth());
        }
        if op == "||" {
            return V::of(l.truth() || r.truth());
        }
        let (l, r) = common(l, r);
        match (l, r) {
            (V::F(a), V::F(b)) => match op {
                "==" => V::of(a == b),
                "!=" => V::of(a != b),
                "<" => V::of(a < b),
                "<=" => V::of(a <= b),
                ">" => V::of(a > b),
                ">=" => V::of(a >= b),
                "+" => V::F(a + b),
                "-" => V::F(a - b),
                "*" => V::F(a * b),
                _ => panic!("float {op}"),
            },
            (V::I(a, bits, signed), V::I(b, ..)) => {
                let v = match op {
                    "==" => return V::of(a == b),
                    "!=" => return V::of(a != b),
                    "<" => return V::of(a < b),
                    "<=" => return V::of(a <= b),
                    ">" => return V::of(a > b),
                    ">=" => return V::of(a >= b),
                    "+" => a + b,
                    "-" => a - b,
                    "*" => a * b,
                    "&" => a & b,
                    "|" => a | b,
                    "^" => a ^ b,
                    "<<" => a << (b & 63),
                    ">>" => a >> (b & 63),
                    _ => panic!("int {op}"),
                };
                V::I(v, bits, signed).to_int(bits, signed)
            }
            _ => panic!("mixed operands"),
        }
    }

    /// Evaluates a rendered condition.
    ///
    /// # Arguments
    ///
    /// * `text` - The condition.
    /// * `ints` - `rax` and `rcx`.
    /// * `floats` - `xmm0` and `xmm1`.
    fn eval(text: &str, ints: (u32, u32), floats: (f64, f64)) -> bool {
        let mut p = P {
            s: text.as_bytes(),
            i: 0,
            ints,
            floats,
        };
        let v = p.expr();
        p.ws();
        assert_eq!(p.i, text.len(), "unread text in {text:?}");
        v.truth()
    }

    /// The flags x86 leaves, as a condition reads them.
    #[derive(Debug, Clone, Copy, Default)]
    struct Machine {
        /// Carry.
        cf: Option<bool>,
        /// Zero.
        zf: Option<bool>,
        /// Sign.
        sf: Option<bool>,
        /// Overflow.
        of: Option<bool>,
        /// Parity.
        pf: Option<bool>,
    }

    impl Machine {
        /// The flags an integer result sets, carry and overflow given.
        ///
        /// # Arguments
        ///
        /// * `r` - The 32-bit result.
        /// * `cf` - The carry, when defined.
        /// * `of` - The overflow, when defined.
        fn of_result(r: u32, cf: Option<bool>, of: Option<bool>) -> Machine {
            Machine {
                cf,
                zf: Some(r == 0),
                sf: Some(r >> 31 == 1),
                of,
                pf: Some((r & 0xff).count_ones().is_multiple_of(2)),
            }
        }

        /// The truth of a condition code over these flags, when every flag
        /// it reads is defined (a condition reading an undefined flag is
        /// undecided even where the defined one would settle it).
        ///
        /// # Arguments
        ///
        /// * `cc` - The condition code.
        fn holds(self, cc: ConditionCode) -> Option<bool> {
            use ConditionCode as C;
            let (cf, zf) = (self.cf, self.zf);
            let lt = || Some(self.sf? != self.of?);
            Some(match cc {
                C::o => self.of?,
                C::no => !self.of?,
                C::b => cf?,
                C::ae => !cf?,
                C::e => zf?,
                C::ne => !zf?,
                C::be => {
                    let (c, z) = (cf?, zf?);
                    c || z
                }
                C::a => {
                    let (c, z) = (cf?, zf?);
                    !c && !z
                }
                C::s => self.sf?,
                C::ns => !self.sf?,
                C::p => self.pf?,
                C::np => !self.pf?,
                C::l => lt()?,
                C::ge => !lt()?,
                C::le => {
                    let (z, l) = (zf?, lt()?);
                    z || l
                }
                C::g => {
                    let (z, l) = (zf?, lt()?);
                    !z && !l
                }
                C::None => return None,
            })
        }
    }

    /// Every condition code, `None` included.
    const CCS: [ConditionCode; 17] = [
        ConditionCode::None,
        ConditionCode::o,
        ConditionCode::no,
        ConditionCode::b,
        ConditionCode::ae,
        ConditionCode::e,
        ConditionCode::ne,
        ConditionCode::be,
        ConditionCode::a,
        ConditionCode::s,
        ConditionCode::ns,
        ConditionCode::p,
        ConditionCode::np,
        ConditionCode::l,
        ConditionCode::ge,
        ConditionCode::le,
        ConditionCode::g,
    ];

    /// What a flag shape sets on given values of its two variables.
    type Sets = Box<dyn Fn(u32, u32) -> Machine>;

    /// Boxes a flag model.
    ///
    /// # Arguments
    ///
    /// * `f` - The model.
    fn sets(f: impl Fn(u32, u32) -> Machine + 'static) -> Sets {
        Box::new(f)
    }

    /// The flags `sub a, b` sets.
    ///
    /// # Arguments
    ///
    /// * `a` - The minuend.
    /// * `b` - The subtrahend.
    fn sub(a: u32, b: u32) -> Machine {
        let of = a.cast_signed().overflowing_sub(b.cast_signed()).1;
        Machine::of_result(a.wrapping_sub(b), Some(a < b), Some(of))
    }

    /// The flags `add a, b` sets.
    ///
    /// # Arguments
    ///
    /// * `a` - One addend.
    /// * `b` - The other.
    fn add(a: u32, b: u32) -> Machine {
        let of = a.cast_signed().overflowing_add(b.cast_signed()).1;
        Machine::of_result(a.wrapping_add(b), Some(a.overflowing_add(b).1), Some(of))
    }

    /// The flag shapes the lifter builds, over two 32-bit variables, with
    /// what each sets on given values.
    fn shapes() -> Vec<(Flags, Sets)> {
        let x = Expr::Var(Key::Reg(Register::RAX));
        let y = Expr::Var(Key::Reg(Register::RCX));
        let low_bit = Expr::Bin(Op::And, Box::new(y.clone()), Box::new(Expr::Const(1)));
        let truth =
            |cc: ConditionCode, flags: Flags| Expr::Cond(Box::new(Cond { cc: Cc(cc), flags }));
        let below = truth(ConditionCode::b, Flags::Cmp(x.clone(), y.clone(), 32));
        let five = truth(ConditionCode::e, Flags::Cmp(x.clone(), Expr::Const(5), 32));
        let none = truth(ConditionCode::e, Flags::Test(y.clone(), y.clone(), 32));
        let either = Expr::Bin(Op::Or, Box::new(below.clone()), Box::new(five.clone()));
        let both = Expr::Bin(
            Op::And,
            Box::new(below),
            Box::new(Expr::Bin(Op::Or, Box::new(five), Box::new(none))),
        );
        let bits = |a: u32, b: u32| (u32::from(a < b), u32::from(a == 5), u32::from(b == 0));
        vec![
            (
                Flags::Result(either.clone(), 32),
                sets(move |a, b| {
                    let (l, f, _) = bits(a, b);
                    Machine::of_result(l | f, None, None)
                }),
            ),
            (
                Flags::Test(both.clone(), both, 32),
                sets(move |a, b| {
                    let (l, f, z) = bits(a, b);
                    Machine::of_result(l & (f | z), Some(false), Some(false))
                }),
            ),
            (
                Flags::Truth(either, Cc(ConditionCode::ne)),
                sets(move |a, b| {
                    let (l, f, _) = bits(a, b);
                    Machine {
                        zf: Some((l | f) == 0),
                        ..Machine::default()
                    }
                }),
            ),
            (Flags::Cmp(x.clone(), y.clone(), 32), sets(sub)),
            (
                Flags::Cmp(x.clone(), Expr::Const(5), 32),
                sets(|a, _| sub(a, 5)),
            ),
            (
                Flags::Cmp(x.clone(), Expr::Const(0x8000_0000), 32),
                sets(|a, _| sub(a, 0x8000_0000)),
            ),
            (
                Flags::Test(x.clone(), y.clone(), 32),
                sets(|a, b| Machine::of_result(a & b, Some(false), Some(false))),
            ),
            (
                Flags::Test(x.clone(), x.clone(), 32),
                sets(|a, _| Machine::of_result(a, Some(false), Some(false))),
            ),
            (Flags::Add(x.clone(), y, 32), sets(add)),
            (
                Flags::Add(x.clone(), Expr::Const(1), 32),
                sets(|a, _| add(a, 1)),
            ),
            (
                Flags::Add(x.clone(), Expr::Const(0xffff_ffff), 32),
                sets(|a, _| add(a, 0xffff_ffff)),
            ),
            (Flags::Add(x.clone(), x.clone(), 32), sets(|a, _| add(a, a))),
            (
                Flags::Result(x.clone(), 32),
                sets(|a, _| Machine::of_result(a, None, None)),
            ),
            (
                Flags::Carry(x.clone()),
                sets(|a, _| Machine {
                    cf: Some(a != 0),
                    of: Some(a != 0),
                    ..Machine::default()
                }),
            ),
            (
                Flags::Shift(x.clone(), 32, low_bit),
                sets(|a, b| Machine::of_result(a, Some(b & 1 == 1), None)),
            ),
            (
                Flags::Truth(x, Cc(ConditionCode::b)),
                sets(|a, _| Machine {
                    cf: Some(a != 0),
                    ..Machine::default()
                }),
            ),
            (Flags::Unknown, sets(|_, _| Machine::default())),
        ]
    }

    /// Builds the names a rendering needs, over an empty image.
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    /// * `a` - Its analysis.
    /// * `o` - The overlay.
    fn names<'a>(p: &'a Program, a: &'a Analysis, o: &'a Overlay) -> Names<'a> {
        Names {
            program: p,
            analysis: a,
            overlay: o,
            this_param: false,
            result_param: None,
            own_name: Arc::from("f"),
            debug_params: Arc::from(Vec::new()),
            debug_locals: Arc::default(),
            first_stack: 8,
            stack_params: 0,
            reg_params: 0,
            word: 8,
            slot_types: Arc::default(),
            global_types: Arc::default(),
        }
    }

    /// Every condition renders as C that means what the flags mean, and
    /// its inversion renders as that C's negation.
    ///
    /// Each flag shape the lifter builds is paired with each condition
    /// code and read back on 32-bit values around the overflow edges and
    /// on floats including NaN. A condition the flags decide must evaluate
    /// to the processor's outcome (a sign test after `dec` misses it at
    /// `INT_MIN`, a flipped float compare at NaN); one they do not decide
    /// renders as an opaque call whose inversion is the same call under
    /// `!`. A lone float `e` is equality or unordered, and `ne` is that
    /// test inverted: C's `==` and `!=` hold on NaN the other way from the
    /// zero flag. With the parity test before them, as compilers emit
    /// them, the pair folds to exactly C's comparison, so only their
    /// inversion is checked here.
    #[test]
    fn a_condition_means_its_flags_and_inverts_to_its_negation() {
        let mut bytes = vec![0u8; 0x2000];
        bytes[0] = 0xc3;
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0x40_0000,
            Some(0x40_1000),
            vec![
                Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x40_2000, 0x1000, 0x1000, false, false),
            ],
        );
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let n = names(&p, &a, &o);
        let ints: [u32; 10] = [
            0,
            1,
            2,
            5,
            0x7f,
            0x80,
            0x7fff_ffff,
            0x8000_0000,
            0x8000_0001,
            0xffff_ffff,
        ];
        for (flags, machine) in shapes() {
            for cc in CCS {
                let cond = Cond {
                    cc: Cc(cc),
                    flags: flags.clone(),
                };
                let normal = cond.render(&n, false);
                let inverted = cond.render(&n, true);
                for &x in &ints {
                    for &y in &ints {
                        let yes = eval(&normal, (x, y), (0.0, 0.0));
                        let no = eval(&inverted, (x, y), (0.0, 0.0));
                        assert_ne!(
                            yes, no,
                            "{cc:?} {flags:?}: {normal} vs {inverted} at {x:#x}, {y:#x}"
                        );
                        if let Some(want) = machine(x, y).holds(cc) {
                            assert_eq!(yes, want, "{cc:?} {flags:?}: {normal} at {x:#x}, {y:#x}");
                        }
                    }
                }
            }
        }
        let floats = [f64::NAN, -1.0, 0.0, 1.0, f64::INFINITY, f64::NEG_INFINITY];
        let fx = Expr::Var(Key::Reg(Register::XMM0));
        for flags in [
            Flags::Cmp(fx.clone(), Expr::Var(Key::Reg(Register::XMM1)), 32),
            Flags::Cmp(fx, Expr::FConst(1.0f32.to_bits().into(), Ty::F32), 32),
        ] {
            for cc in CCS {
                let cond = Cond {
                    cc: Cc(cc),
                    flags: flags.clone(),
                };
                let normal = cond.render(&n, false);
                let inverted = cond.render(&n, true);
                for &a in &floats {
                    for &b in &floats {
                        let b = if matches!(flags, Flags::Cmp(_, Expr::FConst(..), _)) {
                            1.0
                        } else {
                            b
                        };
                        let yes = eval(&normal, (0, 0), (a, b));
                        let no = eval(&inverted, (0, 0), (a, b));
                        assert_ne!(yes, no, "{cc:?}: {normal} vs {inverted} at {a}, {b}");
                        let unordered = a.is_nan() || b.is_nan();
                        let m = Machine {
                            cf: Some(unordered || a < b),
                            zf: Some(unordered || a == b),
                            pf: Some(unordered),
                            ..Machine::default()
                        };
                        let decided = matches!(
                            cc,
                            ConditionCode::a
                                | ConditionCode::ae
                                | ConditionCode::b
                                | ConditionCode::be
                                | ConditionCode::p
                                | ConditionCode::np
                        );
                        if decided && let Some(want) = m.holds(cc) {
                            assert_eq!(yes, want, "{cc:?}: {normal} at {a}, {b}");
                        }
                    }
                }
            }
        }
    }

    /// A guard chain a text pass negates reads as each operand negated
    /// under the other operator, and means the chain's negation.
    ///
    /// Nested chains keep their parentheses, a negated operand loses its
    /// `!`, and a float relation, a comparison macro in the text, negates
    /// as a whole call.
    #[test]
    fn a_negated_chain_negates_each_operand() {
        use super::super::rewrite::invert_condition;
        let ints: [u32; 6] = [0, 1, 2, 5, 9, 0xffff_ffff];
        for chain in [
            "rax < rcx && rax != 5",
            "rax == 0 || rcx > 3 || rax >= rcx",
            "(rax == 0 || rcx > 3) && rax < 7",
            "rax != 1 && (rcx == 2 || (rax > rcx && rcx != 0))",
            "!(rax < rcx) || rcx == 9",
        ] {
            let negated = invert_condition(chain);
            assert!(!negated.starts_with("!("), "{chain}: {negated}");
            for &x in &ints {
                for &y in &ints {
                    assert_ne!(
                        eval(chain, (x, y), (0.0, 0.0)),
                        eval(&negated, (x, y), (0.0, 0.0)),
                        "{chain} vs {negated} at {x:#x}, {y:#x}"
                    );
                }
            }
        }
        assert_eq!(
            invert_condition("rax < rcx && rax != 5"),
            "rax >= rcx || rax == 5"
        );
        assert_eq!(
            invert_condition("isless(xmm0, xmm1) && rax == 0"),
            "!isless(xmm0, xmm1) || rax != 0"
        );
    }

    /// A float compare means its predicate, NaN order included, through
    /// every way the text reaches C.
    ///
    /// Each of the sixteen predicates, and each code over a float compare's
    /// flags, renders as the predicate and inverts to its negation, both by
    /// the renderer and by the text pass that inverts a written condition,
    /// and still means the same once the comparison macros are spelled as
    /// operators.
    #[test]
    fn a_float_predicate_survives_inversion_and_spelling() {
        use super::super::fcmp::FPred;
        use super::super::rewrite::{invert_condition, spell_float_relations};
        let mut bytes = vec![0u8; 0x2000];
        bytes[0] = 0xc3;
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0x40_0000,
            Some(0x40_1000),
            vec![Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true)],
        );
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let n = names(&p, &a, &o);
        let (x, y) = (
            Expr::Var(Key::Reg(Register::XMM0)),
            Expr::Var(Key::Reg(Register::XMM1)),
        );
        let mut conds: Vec<Cond> = FPred::ALL
            .iter()
            .map(|&pred| Cond {
                cc: Cc(ConditionCode::ne),
                flags: Flags::FCmp(pred, x.clone(), y.clone(), 64),
            })
            .collect();
        conds.extend(CCS.iter().map(|&cc| Cond {
            cc: Cc(cc),
            flags: Flags::Float(x.clone(), y.clone(), 64),
        }));
        let floats = [f64::NAN, -1.0, 0.0, 1.0, f64::INFINITY];
        for cond in conds {
            let Some((pred, ..)) = cond.fcmp() else {
                continue;
            };
            let normal = cond.render(&n, false);
            let inverted = cond.render(&n, true);
            let flipped = invert_condition(&normal);
            let shown = |t: &str| {
                spell_float_relations(&format!("if ({t}) {{"))
                    .trim()
                    .to_owned()
            };
            for &fa in &floats {
                for &fb in &floats {
                    let want = pred.holds(fa, fb);
                    let at = |t: &str| eval(t, (0, 0), (fa, fb));
                    let spelled = |t: &str| {
                        let line = shown(t);
                        let inner = line
                            .strip_prefix("if (")
                            .and_then(|l| l.strip_suffix(") {"))
                            .unwrap_or_default()
                            .to_owned();
                        at(&inner)
                    };
                    assert_eq!(at(&normal), want, "{pred:?}: {normal} at {fa}, {fb}");
                    assert_eq!(at(&inverted), !want, "{pred:?}: {inverted} at {fa}, {fb}");
                    assert_eq!(at(&flipped), !want, "{pred:?}: {flipped} at {fa}, {fb}");
                    assert_eq!(
                        spelled(&normal),
                        want,
                        "{pred:?}: {} at {fa}, {fb}",
                        shown(&normal)
                    );
                    assert_eq!(
                        spelled(&flipped),
                        !want,
                        "{pred:?}: {} at {fa}, {fb}",
                        shown(&flipped)
                    );
                }
            }
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod fold_tests {
    //! The folder's algebra checked by enumeration, Alive-style without a
    //! solver.
    //!
    //! Every rewrite [`fold`] and the constructors beside it apply is
    //! compared with the expression it replaces, under an evaluator of this
    //! module's own, on every 8-bit operand and on harvested and sampled
    //! 32- and 64-bit ones.

    use std::collections::BTreeMap;

    use crate::isa::x86::{ConditionCode as C, Register};

    use super::{
        Cc, Cond, Expr, Flags, Helper, Key, Op, Ty, UnOp, fold, lo64, mask, merge_bits,
        sign_extend, ternary, unary, without_addend,
    };
    use crate::num::{lo16, lo32};

    /// The first variable.
    const X: Expr = Expr::Var(Key::Reg(Register::RAX));
    /// The second variable.
    const Y: Expr = Expr::Var(Key::Reg(Register::RCX));
    /// The entry stack pointer the evaluator gives `Sp` offsets.
    const SP: u64 = 0x7ff0_1230;

    /// The mask of the low `w` bits.
    ///
    /// # Arguments
    ///
    /// * `w` - The width.
    fn lane(w: u8) -> u64 {
        u64::MAX >> (64 - u32::from(w.clamp(1, 64)))
    }

    /// The low `w` bits of `v` read as a signed number.
    ///
    /// # Arguments
    ///
    /// * `v` - The bits.
    /// * `w` - The width.
    fn signed(v: u64, w: u8) -> i128 {
        let v = i128::from(v & lane(w));
        if v >> (w - 1) & 1 == 1 {
            v - (1i128 << w)
        } else {
            v
        }
    }

    /// What `op` gives at width `w`, by the definitions the lifter states
    /// for [`Op`], or `None` where it is undefined (a zero divisor, floats).
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `a` - Left operand.
    /// * `b` - Right operand.
    /// * `w` - The width of the operation.
    fn bin(op: Op, a: u64, b: u64, w: u8) -> Option<u64> {
        let (ua, ub) = (u128::from(a & lane(w)), u128::from(b & lane(w)));
        let (sa, sb) = (signed(a, w), signed(b, w));
        let n = b % 64;
        let own = |hw: u8| (u128::from(a & lane(hw)), u128::from(b & lane(hw)));
        let rotl = |hw: u8, k: u64| {
            let (v, k) = (own(hw).0, k % u64::from(hw));
            ((v << k) | (v >> (u64::from(hw) - k))) & u128::from(lane(hw))
        };
        let v = match op {
            Op::Add => ua + ub,
            Op::Sub => ua.wrapping_sub(ub),
            Op::Mul => ua.wrapping_mul(ub),
            Op::Div => ua.checked_div(ub)?,
            Op::Rem => ua.checked_rem(ub)?,
            Op::SDiv => sa.checked_div(sb)?.cast_unsigned(),
            Op::SRem => sa.checked_rem(sb)?.cast_unsigned(),
            Op::And => ua & ub,
            Op::Or => ua | ub,
            Op::Xor => ua ^ ub,
            Op::Shl => ua << n,
            Op::Shr => ua >> n,
            Op::Sar => (sa >> n).cast_unsigned(),
            Op::Rol(hw) => rotl(hw, b),
            Op::Ror(hw) => rotl(hw, u64::from(hw) - b % u64::from(hw)),
            Op::MulHi(hw) => (own(hw).0 * own(hw).1) >> hw,
            Op::SMulHi(hw) => {
                ((signed(a, hw) * signed(b, hw)) >> hw).cast_unsigned() & u128::from(lane(hw))
            }
            Op::SMulO(hw) => {
                let p = signed(a, hw) * signed(b, hw);
                u128::from(p < -(1i128 << (hw - 1)) || p >= 1i128 << (hw - 1))
            }
            Op::UAddO(hw) => u128::from(own(hw).0 + own(hw).1 > u128::from(lane(hw))),
            Op::USubO(hw) => u128::from(own(hw).0 < own(hw).1),
            Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FMin | Op::FMax => return None,
        };
        Some(lo64(v) & lane(w))
    }

    /// What `op` gives at width `w`, or `None` where it is undefined (a bit
    /// scan of zero, a byte swap of a byte, floats).
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `a` - The operand.
    /// * `w` - The width of the operation.
    fn un(op: UnOp, a: u64, w: u8) -> Option<u64> {
        let v = a & lane(w);
        let lz = v.leading_zeros() - (64 - u32::from(w));
        let v = match op {
            UnOp::Neg => v.wrapping_neg(),
            UnOp::Not => !v,
            UnOp::Bswap => match w {
                16 => u64::from(lo16(v).swap_bytes()),
                32 => u64::from(lo32(v).swap_bytes()),
                64 => v.swap_bytes(),
                _ => return None,
            },
            UnOp::Tzcnt => u64::from(v.trailing_zeros().min(u32::from(w))),
            UnOp::Bsf => u64::from((v != 0).then(|| v.trailing_zeros())?),
            UnOp::Lzcnt => u64::from(lz),
            UnOp::Bsr => u64::from((v != 0).then(|| u32::from(w) - 1 - lz)?),
            UnOp::Popcnt => u64::from(v.count_ones()),
            UnOp::Sqrt | UnOp::Fabs => return None,
        };
        Some(v & lane(w))
    }

    /// The truth of a condition, from the flags the processor would set,
    /// or `None` where a flag it reads is not defined.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `x` - The first variable's value.
    /// * `y` - The second's.
    fn truth(c: &Cond, x: u64, y: u64) -> Option<bool> {
        let v = |e: &Expr, w: u8| ev(e, w, x, y);
        let res = |r: u64, w: u8| {
            let r = r & lane(w);
            (
                r == 0,
                r >> (w - 1) & 1 == 1,
                (r & 0xff).count_ones().is_multiple_of(2),
            )
        };
        let (cf, (zf, sf, pf), of) = match &c.flags {
            Flags::Cmp(l, r, w) => {
                let (a, b) = (v(l, *w)?, v(r, *w)?);
                let d = a.wrapping_sub(b);
                let of = signed(a, *w) - signed(b, *w) != signed(d, *w);
                (Some(a & lane(*w) < b & lane(*w)), res(d, *w), Some(of))
            }
            Flags::Float(l, r, w) => {
                let f = |e: &Expr| -> Option<f64> {
                    let bits = v(e, *w)?;
                    Some(if *w == 32 {
                        f64::from(f32::from_bits(u32::try_from(bits).ok()?))
                    } else {
                        f64::from_bits(bits)
                    })
                };
                let (a, b) = (f(l)?, f(r)?);
                match a.partial_cmp(&b) {
                    None => (Some(true), (true, false, true), None),
                    Some(std::cmp::Ordering::Less) => (Some(true), (false, false, false), None),
                    Some(std::cmp::Ordering::Equal) => (Some(false), (true, false, false), None),
                    Some(std::cmp::Ordering::Greater) => (Some(false), (false, false, false), None),
                }
            }
            Flags::Test(l, r, w) => (Some(false), res(v(l, *w)? & v(r, *w)?, *w), Some(false)),
            Flags::Add(l, r, w) => {
                let (a, b) = (v(l, *w)?, v(r, *w)?);
                let s = a.wrapping_add(b);
                let wide = u128::from(a & lane(*w)) + u128::from(b & lane(*w));
                let of = signed(a, *w) + signed(b, *w) != signed(s, *w);
                (Some(wide > u128::from(lane(*w))), res(s, *w), Some(of))
            }
            Flags::Result(e, w) => (None, res(v(e, *w)?, *w), None),
            Flags::Carry(e) => {
                let set = v(e, 64)? != 0;
                return match c.cc.0 {
                    C::b | C::o => Some(set),
                    C::ae | C::no => Some(!set),
                    _ => None,
                };
            }
            Flags::Truth(e, cc) => {
                let set = v(e, 64)? != 0;
                return if c.cc == *cc {
                    Some(set)
                } else {
                    (c.cc == cc.invert()).then_some(!set)
                };
            }
            Flags::FCmp(p, l, r, w) => {
                let f = |e: &Expr| -> Option<f64> {
                    let bits = v(e, *w)?;
                    Some(if *w == 32 {
                        f64::from(f32::from_bits(u32::try_from(bits).ok()?))
                    } else {
                        f64::from_bits(bits)
                    })
                };
                let held = p.holds(f(l)?, f(r)?);
                return match c.cc.0 {
                    C::ne => Some(held),
                    C::e => Some(!held),
                    _ => None,
                };
            }
            Flags::Shift(..) | Flags::Unknown => return None,
        };
        let lt = || Some(sf != of?);
        Some(match c.cc.0 {
            C::o => of?,
            C::no => !of?,
            C::b => cf?,
            C::ae => !cf?,
            C::e => zf,
            C::ne => !zf,
            C::be => cf? || zf,
            C::a => !cf? && !zf,
            C::s => sf,
            C::ns => !sf,
            C::p => pf,
            C::np => !pf,
            C::l => lt()?,
            C::ge => !lt()?,
            C::le => zf || lt()?,
            C::g => !zf && !lt()?,
            C::None => return None,
        })
    }

    /// The value of `e` with every operation at width `w`, or `None` where
    /// it is undefined or not modeled here.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `w` - The width its operations run at.
    /// * `x` - The first variable's value.
    /// * `y` - The second's.
    fn ev(e: &Expr, w: u8, x: u64, y: u64) -> Option<u64> {
        let v = |e: &Expr| ev(e, w, x, y);
        Some(match e {
            Expr::Const(c) => *c,
            Expr::Var(Key::Reg(Register::RAX)) => x,
            Expr::Var(Key::Reg(Register::RCX)) => y,
            Expr::Var(Key::Reg(Register::EAX)) => x & 0xffff_ffff,
            Expr::Sp(k) => SP.wrapping_add_signed(*k),
            Expr::Bin(op, l, r) => bin(*op, v(l)?, v(r)?, w)?,
            Expr::Un(op, a) => un(*op, v(a)?, w)?,
            Expr::Sext(a, bits) => lo64(signed(v(a)?, *bits).cast_unsigned()),
            Expr::Deref(a, ty) => v(a)?.wrapping_mul(0x9e37_79b9_7f4a_7c15) & lane(ty.bits()),
            Expr::Cond(c) => u64::from(truth(c, x, y)?),
            Expr::Ternary(c, a, b) => v(if truth(c, x, y)? { a } else { b })?,
            Expr::Helper(h, args) => {
                let vals = args.iter().map(v).collect::<Option<Vec<u64>>>()?;
                h.eval(&vals, w, w)?
            }
            _ => return None,
        })
    }

    /// Builds `l op r` without folding.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `l` - Left operand.
    /// * `r` - Right operand.
    fn b(op: Op, l: &Expr, r: &Expr) -> Expr {
        Expr::Bin(op, Box::new(l.clone()), Box::new(r.clone()))
    }

    /// Builds a constant.
    ///
    /// # Arguments
    ///
    /// * `c` - Its value.
    fn k(c: u64) -> Expr {
        Expr::Const(c)
    }

    /// Builds a complement.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression complemented.
    fn u(e: Expr) -> Expr {
        Expr::Un(UnOp::Not, Box::new(e))
    }

    /// Every rewrite seen and the first counterexample found to each.
    #[derive(Default)]
    struct Tally {
        /// How often each rewrite was handed its shape, and how often it
        /// changed it.
        fired: BTreeMap<&'static str, (usize, usize)>,
        /// The first counterexample to each rewrite that has one.
        fails: BTreeMap<&'static str, String>,
    }

    impl Tally {
        /// Compares `after` with `before` on every pair of values, noting
        /// the first pair they differ on in the low `w` bits.
        ///
        /// # Arguments
        ///
        /// * `name` - The rewrite.
        /// * `before` - The expression as handed in.
        /// * `after` - What the rewrite made of it.
        /// * `w` - The width both are evaluated at.
        /// * `xs` - The first variable's values.
        /// * `ys` - The second's.
        fn same(
            &mut self,
            name: &'static str,
            before: &Expr,
            after: &Expr,
            w: u8,
            xs: &[u64],
            ys: &[u64],
        ) {
            let seen = self.fired.entry(name).or_default();
            seen.0 += 1;
            seen.1 += usize::from(after != before);
            if self.fails.contains_key(name) {
                return;
            }
            for &x in xs {
                for &y in ys {
                    let Some(want) = ev(before, w, x, y) else {
                        continue;
                    };
                    let got = ev(after, w, x, y);
                    if got.is_none_or(|g| (g ^ want) & lane(w) != 0) {
                        self.fails.insert(
                            name,
                            format!(
                                "{before:?} became {after:?} at width {w}: x={x:#x} y={y:#x} gives {got:x?}, not {want:#x}"
                            ),
                        );
                        return;
                    }
                }
            }
        }

        /// Folds `l op r` at width `w` and compares it with the unfolded node.
        ///
        /// # Arguments
        ///
        /// * `name` - The rewrite.
        /// * `op` - The operator.
        /// * `l` - Left operand.
        /// * `r` - Right operand.
        /// * `w` - The width of the operation.
        /// * `xs` - The first variable's values.
        /// * `ys` - The second's.
        fn fold(
            &mut self,
            name: &'static str,
            (op, l, r): (Op, Expr, Expr),
            w: u8,
            xs: &[u64],
            ys: &[u64],
        ) {
            let before = b(op, &l, &r);
            self.same(name, &before, &fold(op, l, r, w), w, xs, ys);
        }

        /// Requires no counterexample, and every rewrite to have changed at
        /// least one expression it was handed: a shape that never fires
        /// checks nothing.
        fn verdict(&self) {
            let idle: Vec<&str> = self
                .fired
                .iter()
                .filter(|(_, (_, changed))| *changed == 0)
                .map(|(name, _)| *name)
                .collect();
            assert!(
                self.fails.is_empty() && idle.is_empty(),
                "counterexamples: {:#?}\nshapes never rewritten: {idle:?}",
                self.fails
            );
        }
    }

    /// Harvested 64-bit values: zero, one, each width's signed and unsigned
    /// edges, every power of two and its neighbours, their negations, and a
    /// seeded spread of others.
    fn harvest() -> Vec<u64> {
        let mut v = vec![0, 1, 2, 3, 5, 7, 10, 0x55, 0xaa, 0xdead_beef];
        for w in [8u8, 16, 32, 64] {
            let top = 1u64 << (w - 1);
            v.extend([top - 1, top, top + 1, lane(w), lane(w) - 1]);
        }
        for s in 0..64 {
            v.extend([1u64 << s, (1u64 << s) - 1, (1u64 << s) + 1]);
        }
        let mut seed = 0x0123_4567_89ab_cdefu64;
        for _ in 0..24 {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            v.push(z ^ (z >> 31));
        }
        let negated: Vec<u64> = v.iter().map(|x| x.wrapping_neg()).collect();
        v.extend(negated);
        v.sort_unstable();
        v.dedup();
        v
    }

    /// The values the checks at one width run over.
    struct Domain {
        /// The width.
        w: u8,
        /// The first variable's values.
        xs: Vec<u64>,
        /// The second variable's values where the first is swept too.
        ys: Vec<u64>,
        /// The first constant's values.
        cs: Vec<u64>,
        /// A second constant's, and the second variable's beside a constant.
        ds: Vec<u64>,
    }

    /// Every operator with an integer meaning, at width `w`.
    ///
    /// # Arguments
    ///
    /// * `w` - The width the width-carrying operators take.
    fn ops(w: u8) -> [Op; 20] {
        [
            Op::Add,
            Op::Sub,
            Op::Mul,
            Op::Div,
            Op::Rem,
            Op::SDiv,
            Op::SRem,
            Op::And,
            Op::Or,
            Op::Xor,
            Op::Shl,
            Op::Shr,
            Op::Sar,
            Op::Rol(w),
            Op::Ror(w),
            Op::MulHi(w),
            Op::SMulHi(w),
            Op::SMulO(w),
            Op::UAddO(w),
            Op::USubO(w),
        ]
    }

    /// Every condition code.
    const CCS: [C; 16] = [
        C::o,
        C::no,
        C::b,
        C::ae,
        C::e,
        C::ne,
        C::be,
        C::a,
        C::s,
        C::ns,
        C::p,
        C::np,
        C::l,
        C::ge,
        C::le,
        C::g,
    ];

    /// Builds a condition.
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    /// * `flags` - What set the flags.
    fn cond(cc: C, flags: Flags) -> Cond {
        Cond { cc: Cc(cc), flags }
    }

    /// Constant folding, the local identities, like terms, constant
    /// re-association, remainders and the stack-address arithmetic of
    /// [`fold`].
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `d` - The values.
    fn local(t: &mut Tally, d: &Domain) {
        let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
        for (name, op, l, r) in [
            ("x ^ x", Op::Xor, X, X),
            ("x - x", Op::Sub, X, X),
            ("x + 0", Op::Add, X, k(0)),
            ("x - 0", Op::Sub, X, k(0)),
            ("x | 0", Op::Or, X, k(0)),
            ("x ^ 0", Op::Xor, X, k(0)),
            ("x << 0", Op::Shl, X, k(0)),
            ("x >> 0", Op::Shr, X, k(0)),
            ("x sar 0", Op::Sar, X, k(0)),
            ("x * 1", Op::Mul, X, k(1)),
            ("x / 1", Op::Div, X, k(1)),
            ("x sdiv 1", Op::SDiv, X, k(1)),
            ("uaddo(x, 0)", Op::UAddO(w), X, k(0)),
            ("usubo(x, 0)", Op::USubO(w), X, k(0)),
            ("x & 0", Op::And, X, k(0)),
            ("0 & x", Op::And, k(0), X),
            ("x * 0", Op::Mul, X, k(0)),
            ("0 * x", Op::Mul, k(0), X),
            ("0 + x", Op::Add, k(0), X),
            ("0 | x", Op::Or, k(0), X),
            ("0 ^ x", Op::Xor, k(0), X),
            ("0 - x", Op::Sub, k(0), X),
            ("x + x", Op::Add, X, X),
        ] {
            t.fold(name, (op, l, r), w, xs, one);
        }
        for &c in &d.cs {
            for op in ops(w) {
                for &e in xs {
                    t.fold("constant folding", (op, k(c), k(e)), w, one, one);
                }
            }
            let s = c % 64;
            for (name, op, l, r) in [
                ("x & c", Op::And, X, k(c)),
                ("x | c", Op::Or, X, k(c)),
                ("c | x", Op::Or, k(c), X),
                ("x - c", Op::Sub, X, k(c)),
                ("sp + c", Op::Add, Expr::Sp(-0x28), k(c)),
                ("c + sp", Op::Add, k(c), Expr::Sp(0x10)),
                ("sp - c", Op::Sub, Expr::Sp(-8), k(c)),
                ("x + x * c", Op::Add, X, b(Op::Mul, &X, &k(c))),
                ("x * c + x", Op::Add, b(Op::Mul, &X, &k(c)), X),
                ("x * c - x", Op::Sub, b(Op::Mul, &X, &k(c)), X),
                ("x - x * c", Op::Sub, X, b(Op::Mul, &X, &k(c))),
                ("(x << s) + x", Op::Add, b(Op::Shl, &X, &k(s)), X),
                ("x - (x << s)", Op::Sub, X, b(Op::Shl, &X, &k(s))),
                (
                    "x - x / c * c",
                    Op::Sub,
                    X,
                    b(Op::Mul, &b(Op::Div, &X, &k(c)), &k(c)),
                ),
                (
                    "x - c * x / c",
                    Op::Sub,
                    X,
                    b(Op::Mul, &k(c), &b(Op::Div, &X, &k(c))),
                ),
                (
                    "x - x sdiv c * c",
                    Op::Sub,
                    X,
                    b(Op::Mul, &b(Op::SDiv, &X, &k(c)), &k(c)),
                ),
                (
                    "x + x / c * -c",
                    Op::Add,
                    X,
                    b(Op::Mul, &b(Op::Div, &X, &k(c)), &k(c.wrapping_neg())),
                ),
                (
                    "x sdiv c * -c + x",
                    Op::Add,
                    b(Op::Mul, &k(c.wrapping_neg()), &b(Op::SDiv, &X, &k(c))),
                    X,
                ),
            ] {
                t.fold(name, (op, l, r), w, xs, one);
            }
            for &e in &d.ds {
                for (name, op, l, r) in [
                    ("(x + c) + e", Op::Add, b(Op::Add, &X, &k(c)), k(e)),
                    (
                        "x * c + x * e",
                        Op::Add,
                        b(Op::Mul, &X, &k(c)),
                        b(Op::Mul, &X, &k(e)),
                    ),
                    (
                        "x * c - x * e",
                        Op::Sub,
                        b(Op::Mul, &X, &k(c)),
                        b(Op::Mul, &X, &k(e)),
                    ),
                    ("(x * c) * e", Op::Mul, b(Op::Mul, &X, &k(c)), k(e)),
                    ("(x << s) * e", Op::Mul, b(Op::Shl, &X, &k(s)), k(e)),
                ] {
                    t.fold(name, (op, l, r), w, xs, one);
                }
            }
            t.fold(
                "(x + c) - y",
                (Op::Sub, b(Op::Add, &X, &k(c)), Y),
                w,
                xs,
                &d.ds,
            );
        }
        for cc in CCS {
            for &c in &d.ds {
                let test = Expr::Cond(Box::new(cond(cc, Flags::Cmp(Y, k(c), w))));
                let neg = Expr::Un(UnOp::Neg, Box::new(test.clone()));
                t.fold("-(c) & x", (Op::And, neg, X), w, xs, &d.ds);
                t.fold(
                    "x & (0 - c)",
                    (Op::And, X, b(Op::Sub, &k(0), &test)),
                    w,
                    xs,
                    &d.ds,
                );
            }
        }
        let word = |e: &Expr| Expr::Sext(Box::new(e.clone()), 32);
        for (name, div) in [("x - x / y * y", Op::Div), ("x - x sdiv y * y", Op::SDiv)] {
            let rem = b(Op::Sub, &X, &b(Op::Mul, &b(div, &X, &Y), &Y));
            if let Expr::Bin(op, l, r) = rem {
                t.fold(name, (op, *l, *r), w, xs, ys);
            }
        }
        if w <= 32 {
            let quot = b(Op::SDiv, &word(&X), &word(&Y));
            t.fold(
                "x - sext(x) sdiv sext(y) * y",
                (Op::Sub, X, b(Op::Mul, &quot, &Y)),
                w,
                xs,
                ys,
            );
            for &c in &d.cs {
                let quot = b(Op::SDiv, &word(&X), &k(c));
                t.fold(
                    "x + sext(x) sdiv c * -c",
                    (
                        Op::Add,
                        X,
                        b(Op::Mul, &quot, &k(c.wrapping_neg() & lane(w))),
                    ),
                    w,
                    xs,
                    one,
                );
            }
        }
        for (name, op, l, r) in [
            (
                "(x ^ y) + (x & y) * 2",
                Op::Add,
                b(Op::Xor, &X, &Y),
                b(Op::Mul, &b(Op::And, &X, &Y), &k(2)),
            ),
            (
                "(y & x) << 1 + (x ^ y)",
                Op::Add,
                b(Op::Shl, &b(Op::And, &Y, &X), &k(1)),
                b(Op::Xor, &X, &Y),
            ),
            (
                "(x ^ y) + 2 * (y & x)",
                Op::Add,
                b(Op::Xor, &X, &Y),
                b(Op::Mul, &k(2), &b(Op::And, &Y, &X)),
            ),
            (
                "(x & y) + (x | y)",
                Op::Add,
                b(Op::And, &X, &Y),
                b(Op::Or, &X, &Y),
            ),
            (
                "(y | x) + (x & y)",
                Op::Add,
                b(Op::Or, &Y, &X),
                b(Op::And, &X, &Y),
            ),
            (
                "(x ^ y) + (y & x)",
                Op::Add,
                b(Op::Xor, &X, &Y),
                b(Op::And, &Y, &X),
            ),
            (
                "(x & y) + (x ^ y)",
                Op::Add,
                b(Op::And, &X, &Y),
                b(Op::Xor, &X, &Y),
            ),
            (
                "(x | y) - (y & x)",
                Op::Sub,
                b(Op::Or, &X, &Y),
                b(Op::And, &Y, &X),
            ),
            (
                "(x | y) - (x ^ y)",
                Op::Sub,
                b(Op::Or, &X, &Y),
                b(Op::Xor, &X, &Y),
            ),
            (
                "2 * (x & y) + (x ^ y) - (x & y)",
                Op::Sub,
                b(
                    Op::Add,
                    &b(Op::Mul, &k(2), &b(Op::And, &X, &Y)),
                    &b(Op::Xor, &X, &Y),
                ),
                b(Op::And, &X, &Y),
            ),
            (
                "(x & ~y) + (x & y) + 5",
                Op::Add,
                b(Op::Add, &b(Op::And, &X, &u(Y.clone())), &b(Op::And, &X, &Y)),
                k(5),
            ),
            (
                "(x | y) - (x & y) - (x ^ y)",
                Op::Sub,
                b(Op::Sub, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
                b(Op::Xor, &X, &Y),
            ),
            (
                "~(x ^ y) & (x | y)",
                Op::And,
                u(b(Op::Xor, &X, &Y)),
                b(Op::Or, &X, &Y),
            ),
        ] {
            t.fold(name, (op, l, r), w, xs, ys);
        }
        for (name, op, l, r) in [
            (
                "(x ^ y) + ((x & y) << 1) - (x & y)",
                Op::Sub,
                b(
                    Op::Add,
                    &b(Op::Xor, &X, &Y),
                    &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
                ),
                b(Op::And, &X, &Y),
            ),
            (
                "(x & ~y) - (~x & y)",
                Op::Sub,
                b(Op::And, &X, &u(Y.clone())),
                b(Op::And, &u(X.clone()), &Y),
            ),
            (
                "(x | y) + (x & y) - (x + y)",
                Op::Sub,
                b(Op::Add, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
                b(Op::Add, &X, &Y),
            ),
            ("~x + y + 1", Op::Add, b(Op::Add, &u(X.clone()), &Y), k(1)),
        ] {
            t.fold(name, (op, l, r), w, xs, ys);
        }
        let top = k(u64::from(w) - 1);
        let scan = Expr::Un(UnOp::Bsr, Box::new(X));
        t.fold(
            "bsr(x) ^ (w - 1)",
            (Op::Xor, scan.clone(), top.clone()),
            w,
            xs,
            one,
        );
        t.fold(
            "(w - 1) ^ bsr(x)",
            (Op::Xor, top.clone(), scan.clone()),
            w,
            xs,
            one,
        );
        t.fold("(w - 1) - bsr(x)", (Op::Sub, top, scan), w, xs, one);
    }

    /// The general MBA collapse under attack: shapes that smuggle a
    /// non-linear step past the linear gate, sign-extension layers, stack
    /// slots as variables, and constants above the width.
    ///
    /// Every row is a shape the collapse either rewrites or must refuse;
    /// [`fold`] comparing it with the unfolded node on the domain's values
    /// is the ground truth either way. Rows that must come back unchanged
    /// are pinned structurally in [`mba_refusals_stay_unfolded`].
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `d` - The values.
    fn mba_stress(t: &mut Tally, d: &Domain) {
        let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
        let sext = |e: Expr| Expr::Sext(Box::new(e), w);
        for (name, op, l, r, sweep) in [
            (
                "(x & ~y) + (~x & y) + ((x & y) << 1)",
                Op::Add,
                b(
                    Op::Add,
                    &b(Op::And, &X, &u(Y.clone())),
                    &b(Op::And, &u(X.clone()), &Y),
                ),
                b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
                ys,
            ),
            (
                "(x ^ y) + (x & y) + (x & y)",
                Op::Add,
                b(Op::Add, &b(Op::Xor, &X, &Y), &b(Op::And, &X, &Y)),
                b(Op::And, &X, &Y),
                ys,
            ),
            (
                "sext(x ^ y) + sext((x & y) << 1)",
                Op::Add,
                sext(b(Op::Xor, &X, &Y)),
                sext(b(Op::Shl, &b(Op::And, &X, &Y), &k(1))),
                ys,
            ),
            (
                "sext(~(x + c))",
                Op::Add,
                sext(u(b(Op::Add, &X, &k(0x5a)))),
                k(0),
                one,
            ),
            (
                "~(~(x + c)) + c",
                Op::Add,
                u(u(b(Op::Add, &X, &k(7)))),
                k(7),
                one,
            ),
            (
                "(x ^ above) ^ above",
                Op::Xor,
                b(Op::Xor, &X, &k(lane(w).wrapping_add(3))),
                k(lane(w).wrapping_add(3)),
                one,
            ),
            ("~(x + c) + 1", Op::Add, u(b(Op::Add, &X, &k(9))), k(1), one),
            (
                "(sp ^ y) + ((sp & y) << 1)",
                Op::Add,
                b(Op::Xor, &Expr::Sp(-0x28), &Y),
                b(Op::Shl, &b(Op::And, &Expr::Sp(-0x28), &Y), &k(1)),
                ys,
            ),
            (
                "(x | y) - (x & y) - 1",
                Op::Sub,
                b(Op::Sub, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
                k(1),
                ys,
            ),
        ] {
            t.fold(name, (op, l, r), w, xs, sweep);
        }
        for &c in &d.cs {
            t.fold(
                "(x ^ c) ^ c",
                (Op::Xor, b(Op::Xor, &X, &k(c)), k(c)),
                w,
                xs,
                one,
            );
        }
        let pad = b(Op::Xor, &b(Op::And, &X, &Y), &b(Op::And, &X, &Y));
        let mut capped = b(
            Op::Add,
            &b(Op::Xor, &X, &Y),
            &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
        );
        for _ in 0..2 {
            capped = b(Op::Add, &capped, &pad.clone());
        }
        t.fold("x + y at the node cap", (Op::Add, capped, k(0)), w, xs, ys);
    }

    /// The MBA collapse's rows hold at width 16, between the exhaustive
    /// byte sweep and the sampled words, where the negative-looking
    /// constants `0xff` and `0xfe` sit inside the lane.
    ///
    /// # Panics
    ///
    /// When a rewrite changed a row's value.
    #[test]
    fn mba_rows_hold_at_16_bits() {
        let wide = harvest();
        let pick: Vec<u64> = wide.iter().copied().step_by(7).collect();
        let d = Domain {
            w: 16,
            xs: wide,
            ys: pick.clone(),
            cs: pick.clone(),
            ds: pick,
        };
        let mut t = Tally::default();
        mba_stress(&mut t, &d);
        assert!(t.fails.is_empty(), "counterexamples: {:#?}", t.fails);
    }

    /// The divisions a compiler strength-reduces, as [`fold`] reverses them.
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `w` - The width.
    /// * `magics` - The multipliers and shifts to try.
    /// * `xs` - The dividends.
    fn divisions(t: &mut Tally, w: u8, magics: &[(u64, u64)], xs: &[u64]) {
        let one = [0u64];
        for &(m, s) in magics {
            let hi = b(Op::MulHi(w), &k(m), &X);
            t.fold("mulhi(m, x) >> s", (Op::Shr, hi.clone(), k(s)), w, xs, &one);
            let quot = fold(Op::MulHi(w), k(m), X, w);
            t.fold("x / d >> s", (Op::Shr, quot, k(s)), w, xs, &one);
            t.fold(
                "mulhi(x, m) >> s",
                (Op::Shr, b(Op::MulHi(w), &X, &k(m)), k(s)),
                w,
                xs,
                &one,
            );
            if s >= 1 {
                let half = b(Op::Shr, &b(Op::Sub, &X, &hi), &k(1));
                t.fold(
                    "((x - hi) >> 1 + hi) >> s",
                    (Op::Shr, b(Op::Add, &half, &hi), k(s - 1)),
                    w,
                    xs,
                    &one,
                );
                t.fold(
                    "(hi + (x - hi) >> 1) >> s",
                    (Op::Shr, b(Op::Add, &hi, &half), k(s - 1)),
                    w,
                    xs,
                    &one,
                );
                let x5 = b(Op::Add, &X, &k(5));
                let hi5 = b(Op::MulHi(w), &k(m), &x5);
                let half5 = b(Op::Shr, &b(Op::Add, &b(Op::Sub, &X, &hi5), &k(5)), &k(1));
                t.fold(
                    "((x - hi) + 5 >> 1 + hi) >> s",
                    (Op::Shr, b(Op::Add, &half5, &hi5), k(s - 1)),
                    w,
                    xs,
                    &one,
                );
            }
            let shi = b(Op::SMulHi(w), &k(m), &X);
            let sar = |e: &Expr| {
                if s == 0 {
                    e.clone()
                } else {
                    b(Op::Sar, e, &k(s))
                }
            };
            let quotients = [
                ("smulhi(m, x) sar s", sar(&shi)),
                ("(smulhi(m, x) + x) sar s", sar(&b(Op::Add, &shi, &X))),
                (
                    "sext(smulhi(m, x)) sar s",
                    sar(&Expr::Sext(Box::new(shi.clone()), w)),
                ),
            ];
            let sign = |e: &Expr| b(Op::Shr, e, &k(u64::from(w) - 1));
            for (name, q) in quotients {
                t.fold(name, (Op::Shr, q.clone(), k(u64::from(w) - 1)), w, xs, &one);
                t.fold(
                    "q + (q >> w - 1)",
                    (Op::Add, q.clone(), sign(&q)),
                    w,
                    xs,
                    &one,
                );
                t.fold(
                    "(q >> w - 1) + q",
                    (Op::Add, sign(&q), q.clone()),
                    w,
                    xs,
                    &one,
                );
                t.fold(
                    "q + (x >> w - 1)",
                    (Op::Add, q.clone(), sign(&X)),
                    w,
                    xs,
                    &one,
                );
                let masked = b(Op::And, &q, &k(lane(w)));
                t.fold(
                    "q + ((q & lane) >> w - 1)",
                    (Op::Add, q.clone(), sign(&masked)),
                    w,
                    xs,
                    &one,
                );
            }
        }
    }

    /// The quotients read off the whole 64-bit product of a word.
    ///
    /// As [`fold`] reverses them: clang's `imul` of a sign-extended word,
    /// its high word shifted and its sign added, and arm64's `smull` and
    /// `umull`, the dividend added back to a negative magic's high word.
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `magics` - The 32-bit multipliers and shifts to try.
    /// * `xs` - The dividends.
    fn wide_quotients(t: &mut Tally, magics: &[(u64, u64)], xs: &[u64]) {
        let one = [0u64];
        let word = 0xffff_ffff;
        for &(m, s) in magics {
            let c = lo64(signed(m, 32).cast_unsigned());
            let p = b(Op::Mul, &Expr::Sext(Box::new(X), 32), &k(c));
            t.fold(
                "sext(x) * c >> k",
                (Op::Shr, p.clone(), k(32 + s)),
                64,
                xs,
                &one,
            );
            t.fold(
                "sext(x) * c sar k",
                (Op::Sar, p.clone(), k(32 + s)),
                64,
                xs,
                &one,
            );
            let u = b(Op::Mul, &b(Op::And, &X, &k(word)), &k(m));
            t.fold("(x & word) * c >> k", (Op::Shr, u, k(32 + s)), 64, xs, &one);
            let q = fold(Op::Sar, p.clone(), k(32 + s), 64);
            let sign = fold(Op::Shr, p.clone(), k(63), 64);
            t.fold("q + (p >> 63)", (Op::Add, q, sign), 64, xs, &one);
            let hi = fold(Op::Shr, p, k(32), 64);
            let sum = fold(Op::Add, b(Op::And, &X, &k(word)), hi, 64);
            let q = fold(Op::Sar, sign_extend(sum.clone(), 32), k(s), 64);
            let fix = fold(Op::Shr, mask(sum, word), k(31), 64);
            t.fold("q + ((x + hi) >> 31)", (Op::Add, q, fix), 32, xs, &one);
        }
    }

    /// The signed divisions by powers of two a compiler writes as shifts,
    /// as [`fold`] reverses them.
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `w` - The width.
    /// * `xs` - The dividends.
    fn power_quotients(t: &mut Tally, w: u8, xs: &[u64]) {
        let one = [0u64];
        let signs = [
            b(Op::Sar, &X, &k(63)),
            b(Op::Sar, &Expr::Sext(Box::new(X), 32), &k(31)),
        ];
        for kk in 1..u64::from(w) {
            for sign in &signs {
                let fix = b(Op::And, sign, &k((1u64 << kk) - 1));
                for inner in [b(Op::Add, &X, &fix), b(Op::Add, &fix, &X)] {
                    t.fold(
                        "(x + (sign & 2^k - 1)) sar k",
                        (Op::Sar, inner.clone(), k(kk)),
                        w,
                        xs,
                        &one,
                    );
                    let lane_of = Expr::Sext(Box::new(inner), 32);
                    t.fold(
                        "sext(x + (sign & 2^k - 1)) sar k",
                        (Op::Sar, lane_of, k(kk)),
                        w,
                        xs,
                        &one,
                    );
                }
            }
        }
        for sign in &signs {
            t.fold(
                "(x - sign) sar 1",
                (Op::Sar, b(Op::Sub, &X, sign), k(1)),
                w,
                xs,
                &one,
            );
        }
        for top in [31, 63] {
            let bit = b(Op::Shr, &X, &k(top));
            t.fold(
                "(x + (x >> top)) sar 1",
                (Op::Sar, b(Op::Add, &X, &bit), k(1)),
                w,
                xs,
                &one,
            );
            t.fold(
                "((x >> top) + x) sar 1",
                (Op::Sar, b(Op::Add, &bit, &X), k(1)),
                w,
                xs,
                &one,
            );
        }
    }

    /// The constructors beside [`fold`]: masks, unary operators, sign
    /// extension, partial writes, selects, the equality folds of
    /// [`Cond::simplify`], and taking an addend out of a sum.
    ///
    /// # Arguments
    ///
    /// * `t` - The tally.
    /// * `d` - The values.
    fn builders(t: &mut Tally, d: &Domain) {
        let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
        let cut = |e: &Expr, m: u64| b(Op::And, e, &k(m));
        let inner = b(
            Op::Add,
            &cut(&X, 0xffff_ffff),
            &b(Op::Mul, &cut(&Y, 0xffff), &k(3)),
        );
        t.same(
            "sext(x) reads through low cuts",
            &Expr::Sext(Box::new(inner.clone()), 16),
            &sign_extend(inner.clone(), 16),
            w,
            xs,
            ys,
        );
        t.same(
            "mask reads through low cuts",
            &cut(&inner, 0xff),
            &mask(inner, 0xff),
            w,
            xs,
            ys,
        );
        for (name, e) in [
            ("mulhi fits its width", b(Op::MulHi(w), &X, &Y)),
            ("rotate fits its width", b(Op::Rol(w), &X, &k(3))),
        ] {
            t.same(
                name,
                &cut(&e, lane(w)),
                &mask(e.clone(), lane(w)),
                w,
                xs,
                ys,
            );
        }
        let unops = [
            UnOp::Neg,
            UnOp::Not,
            UnOp::Bswap,
            UnOp::Tzcnt,
            UnOp::Lzcnt,
            UnOp::Popcnt,
            UnOp::Bsf,
            UnOp::Bsr,
        ];
        for op in unops {
            for &c in xs {
                let before = Expr::Un(op, Box::new(k(c)));
                t.same("unary folding", &before, &unary(op, k(c), w), w, one, one);
            }
        }
        for op in [UnOp::Neg, UnOp::Not] {
            let twice = Expr::Un(op, Box::new(Expr::Un(op, Box::new(X))));
            t.same(
                "op(op(x))",
                &twice,
                &unary(op, Expr::Un(op, Box::new(X)), w),
                w,
                xs,
                one,
            );
        }
        for from in [8u8, 16, 32] {
            for &c in &d.cs {
                let before = Expr::Sext(Box::new(k(c)), from);
                t.same("sext(c)", &before, &sign_extend(k(c), from), w, one, one);
            }
            for inner in [8u8, 16, 32].into_iter().filter(|b| *b <= from) {
                let x = Expr::Sext(Box::new(X), inner);
                let before = Expr::Sext(Box::new(x.clone()), from);
                t.same("sext(sext(x))", &before, &sign_extend(x, from), w, xs, one);
            }
        }
        for (bits, shift) in [(8u8, 0u8), (8, 8), (16, 0), (32, 0)]
            .into_iter()
            .filter(|&(bits, shift)| bits + shift <= w)
        {
            let field = lane(bits) << shift;
            let placed = b(
                Op::Shl,
                &b(Op::And, &Y, &k(lane(bits))),
                &k(u64::from(shift)),
            );
            let before = b(Op::Or, &b(Op::And, &X, &k(!field)), &placed);
            t.same(
                "merge_bits",
                &before,
                &merge_bits(X, Y, bits, shift),
                64,
                xs,
                ys,
            );
        }
        let test = Expr::Cond(Box::new(cond(C::l, Flags::Cmp(X, Y, w))));
        for &c in &d.cs {
            for &e in &d.ds {
                for (name, l) in [
                    ("(x & e) & c", b(Op::And, &X, &k(e))),
                    ("(x << e) & c", b(Op::Shl, &X, &k(e % 64))),
                    ("(x >> e) & c", b(Op::Shr, &X, &k(e % 64))),
                ] {
                    t.fold(name, (Op::And, l, k(c)), w, xs, one);
                }
                let l = b(Op::Or, &b(Op::And, &X, &k(e)), &Y);
                t.fold(
                    "((x & e) | y) & c",
                    (Op::And, l, k(c)),
                    w,
                    xs,
                    &[0, 0xa5, lane(w)],
                );
            }
            t.fold(
                "(x | y) & c",
                (Op::And, b(Op::Or, &X, &Y), k(c)),
                w,
                xs,
                &d.ds,
            );
            for (name, l) in [
                ("cond & c", test.clone()),
                ("*(uint8_t*)x & c", Expr::Deref(Box::new(X), Ty::U8)),
                ("*(uint16_t*)x & c", Expr::Deref(Box::new(X), Ty::U16)),
                ("eax & c", Expr::Var(Key::Reg(Register::EAX))),
            ] {
                t.fold(name, (Op::And, l, k(c)), w, xs, one);
            }
        }
        for cc in CCS {
            let test = cond(cc, Flags::Cmp(X, Y, w));
            for (name, a, z) in [
                ("c ? 1 : 0", k(1), k(0)),
                ("c ? 0 : 1", k(0), k(1)),
                ("c ? x : x", X, X),
            ] {
                let before = Expr::Ternary(
                    Box::new(test.clone()),
                    Box::new(a.clone()),
                    Box::new(z.clone()),
                );
                t.same(name, &before, &ternary(test.clone(), a, z), w, xs, ys);
            }
            for &c in &d.cs {
                for &e in &d.ds {
                    let decided = cond(cc, Flags::Cmp(k(c), k(e), w));
                    let before = Expr::Ternary(Box::new(decided.clone()), Box::new(X), Box::new(Y));
                    t.same(
                        "decided ? x : y",
                        &before,
                        &ternary(decided, X, Y),
                        w,
                        &[0x12],
                        &[0x34],
                    );
                }
            }
        }
        let all = k(lane(w));
        for (cc, sat) in [(C::b, true), (C::o, true), (C::ae, false), (C::no, false)] {
            let carry = cond(cc, Flags::Carry(b(Op::MulHi(w), &X, &Y)));
            for product in [b(Op::Mul, &X, &Y), b(Op::Mul, &Y, &X)] {
                let (a, z) = if sat {
                    (all.clone(), product)
                } else {
                    (product, all.clone())
                };
                let before = Expr::Ternary(
                    Box::new(carry.clone()),
                    Box::new(a.clone()),
                    Box::new(z.clone()),
                );
                t.same("mul_sat", &before, &ternary(carry.clone(), a, z), w, xs, ys);
            }
        }
        for (cc, sat) in [(C::b, true), (C::ae, false)] {
            let carry = cond(cc, Flags::Add(X, Y, w));
            let sum = b(Op::Add, &X, &Y);
            let (a, z) = if sat {
                (all.clone(), sum)
            } else {
                (sum, all.clone())
            };
            let before = Expr::Ternary(
                Box::new(carry.clone()),
                Box::new(a.clone()),
                Box::new(z.clone()),
            );
            t.same("add_sat", &before, &ternary(carry, a, z), w, xs, ys);
        }
        let diff = b(Op::Sub, &X, &Y);
        for (cc, zero_first) in [(C::b, true), (C::be, true), (C::a, false), (C::ae, false)] {
            let test = cond(cc, Flags::Cmp(X, Y, w));
            let (arm_t, arm_f) = if zero_first {
                (k(0), diff.clone())
            } else {
                (diff.clone(), k(0))
            };
            let before = Expr::Ternary(
                Box::new(test.clone()),
                Box::new(arm_t.clone()),
                Box::new(arm_f.clone()),
            );
            let after = ternary(test, arm_t, arm_f);
            if w >= 64 {
                t.same("sub sat", &before, &after, w, xs, ys);
                assert!(
                    matches!(&after, Expr::Helper(Helper::SubSat, args) if args.len() == 2 && args[0] == X && args[1] == Y),
                    "{cc:?} at {w}: {after:?}"
                );
            } else {
                assert!(
                    matches!(after, Expr::Ternary(..)),
                    "{cc:?} at {w} folded: {after:?}"
                );
            }
        }
        let signed = ternary(cond(C::l, Flags::Cmp(X, Y, w)), k(0), diff);
        let swapped = ternary(cond(C::b, Flags::Cmp(X, Y, w)), k(0), b(Op::Sub, &Y, &X));
        let other = ternary(cond(C::b, Flags::Cmp(X, Y, w)), k(0), b(Op::Sub, &X, &k(1)));
        let called = Expr::Call("g".to_owned(), vec![X]);
        let calling = ternary(
            cond(C::b, Flags::Cmp(called.clone(), Y, w)),
            k(0),
            b(Op::Sub, &called, &Y),
        );
        assert!(
            matches!(signed, Expr::Ternary(..))
                && !matches!(swapped, Expr::Helper(Helper::SubSat, _))
                && !matches!(other, Expr::Helper(Helper::SubSat, _)),
            "width {w}: {signed:?} {swapped:?} {other:?}"
        );
        if w >= 64 {
            assert!(
                matches!(calling, Expr::Helper(Helper::SubSat, ref args) if args.len() == 2 && args[0] == called && args[1] == Y),
                "{calling:?}"
            );
        } else {
            assert!(
                matches!(calling, Expr::Ternary(..)),
                "width {w} folded a call: {calling:?}"
            );
        }
        for cc in [C::l, C::le, C::g, C::ge, C::b, C::be, C::a, C::ae] {
            let test = cond(cc, Flags::Cmp(X, Y, w));
            for (a, z) in [(X, Y), (Y, X)] {
                let before = Expr::Ternary(
                    Box::new(test.clone()),
                    Box::new(a.clone()),
                    Box::new(z.clone()),
                );
                let after = ternary(test.clone(), a, z);
                if w >= 64 {
                    t.same("extremum", &before, &after, w, xs, ys);
                    assert!(
                        matches!(&after, Expr::Helper(_, args) if args.len() == 2 && args[0] == X && args[1] == Y),
                        "{cc:?} at {w}: {after:?}"
                    );
                } else {
                    assert!(
                        matches!(after, Expr::Ternary(..)),
                        "{cc:?} at {w} folded: {after:?}"
                    );
                }
            }
        }
        for cc in [C::e, C::ne] {
            let stayed = ternary(cond(cc, Flags::Cmp(X, Y, w)), X, Y);
            assert!(
                !matches!(stayed, Expr::Helper(..)),
                "{cc:?} at {w} became {stayed:?}"
            );
        }
        let third = ternary(cond(C::a, Flags::Cmp(X, Y, w)), X, k(1));
        assert!(
            matches!(third, Expr::Ternary(..)),
            "a third value at {w} became {third:?}"
        );
        let neg = Expr::Un(UnOp::Neg, Box::new(X));
        for cc in [C::l, C::le, C::g, C::ge, C::s, C::ns] {
            for flags in [Flags::Cmp(X, k(0), w), Flags::Cmp(k(0), X, w)] {
                let test = cond(cc, flags);
                for (a, z) in [(neg.clone(), X), (X, neg.clone())] {
                    let before = Expr::Ternary(
                        Box::new(test.clone()),
                        Box::new(a.clone()),
                        Box::new(z.clone()),
                    );
                    let after = ternary(test.clone(), a, z);
                    let is_abs = match &after {
                        Expr::Helper(Helper::Llabs, args) => args.len() == 1 && args[0] == X,
                        Expr::Un(UnOp::Neg, inner) => {
                            matches!(inner.as_ref(), Expr::Helper(Helper::Llabs, args) if args.len() == 1 && args[0] == X)
                        }
                        _ => false,
                    };
                    if w >= 64 {
                        t.same("absolute", &before, &after, w, xs, ys);
                        assert!(is_abs, "{cc:?} at {w}: {after:?}");
                    } else {
                        assert!(
                            matches!(after, Expr::Ternary(..)),
                            "{cc:?} at {w} folded: {after:?}"
                        );
                    }
                }
            }
        }
        for cc in [C::e, C::ne, C::b, C::a] {
            let stayed = ternary(cond(cc, Flags::Cmp(X, k(0), w)), neg.clone(), X);
            assert!(
                !matches!(stayed, Expr::Helper(..) | Expr::Un(UnOp::Neg, _)),
                "{cc:?} at {w} became {stayed:?}"
            );
        }
        let other = ternary(cond(C::s, Flags::Cmp(k(0), X, w)), Y, neg);
        assert!(
            matches!(other, Expr::Ternary(..)),
            "a third value at {w} became {other:?}"
        );
        let sign = b(Op::Sar, &X, &k(63));
        let is_sign_abs = |e: &Expr| matches!(e, Expr::Helper(Helper::Llabs, args) if args.len() == 1 && args[0] == X);
        for (before, after) in [
            (
                b(Op::Sub, &b(Op::Xor, &X, &sign), &sign),
                fold(Op::Sub, b(Op::Xor, &X, &sign), sign.clone(), w),
            ),
            (
                b(Op::Xor, &b(Op::Add, &X, &sign), &sign),
                fold(Op::Xor, b(Op::Add, &X, &sign), sign.clone(), w),
            ),
        ] {
            if w >= 64 {
                t.same("sign absolute", &before, &after, w, xs, ys);
                assert!(is_sign_abs(&after), "{after:?}");
            } else {
                assert!(!is_sign_abs(&after), "width {w} folded: {after:?}");
            }
        }
        let shifted = b(Op::Sar, &X, &k(31));
        let narrow = fold(Op::Sub, b(Op::Xor, &X, &shifted), shifted, w);
        assert!(
            !is_sign_abs(&narrow),
            "a 31-bit splat at {w} became {narrow:?}"
        );
        let foreign = fold(Op::Sub, b(Op::Xor, &Y, &sign), sign, w);
        assert!(
            !matches!(foreign, Expr::Helper(Helper::Llabs, _)),
            "a different value at {w} became {foreign:?}"
        );
        let width = u64::from(w);
        let is_rotate = |e: &Expr, n: u64, right: bool| match e {
            Expr::Bin(op, v, c) => {
                v.as_ref() == &X
                    && c.as_ref() == &k(n)
                    && match op {
                        Op::Ror(b) => right && *b == w,
                        Op::Rol(b) => !right && *b == w,
                        _ => false,
                    }
            }
            _ => false,
        };
        let turned = fold(
            Op::Or,
            b(Op::Shl, &X, &k(1)),
            b(Op::Shr, &X, &k(width - 1)),
            w,
        );
        let other_way = fold(
            Op::Or,
            b(Op::Shr, &X, &k(1)),
            b(Op::Shl, &X, &k(width - 1)),
            w,
        );
        t.same(
            "rotate",
            &b(
                Op::Or,
                &b(Op::Shl, &X, &k(1)),
                &b(Op::Shr, &X, &k(width - 1)),
            ),
            &turned,
            w,
            xs,
            one,
        );
        t.same(
            "rotate",
            &b(
                Op::Or,
                &b(Op::Shr, &X, &k(1)),
                &b(Op::Shl, &X, &k(width - 1)),
            ),
            &other_way,
            w,
            xs,
            one,
        );
        assert!(is_rotate(&turned, 1, false), "{turned:?}");
        assert!(is_rotate(&other_way, 1, true), "{other_way:?}");
        let mixed = fold(
            Op::Or,
            b(Op::Shl, &X, &k(1)),
            b(Op::Shr, &Y, &k(width - 1)),
            w,
        );
        let arithmetic = fold(
            Op::Or,
            b(Op::Shl, &X, &k(1)),
            b(Op::Sar, &X, &k(width - 1)),
            w,
        );
        let called = Expr::Call("f".to_owned(), vec![X]);
        let calling = fold(
            Op::Or,
            b(Op::Shl, &called, &k(1)),
            b(Op::Shr, &called, &k(width - 1)),
            w,
        );
        assert!(
            !matches!(mixed, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                && !matches!(arithmetic, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                && !matches!(calling, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
            "width {w}: {mixed:?} {arithmetic:?} {calling:?}"
        );
        let mask_n = u64::from(w) - 1;
        let cnt = b(Op::And, &X, &k(mask_n));
        let rest = b(Op::Sub, &k(mask_n), &cnt);
        let spun = fold(
            Op::Or,
            b(Op::Shl, &Y, &cnt),
            b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
            w,
        );
        let spun_r = fold(
            Op::Or,
            b(Op::Shr, &Y, &cnt),
            b(Op::Shl, &b(Op::Shl, &Y, &k(1)), &rest),
            w,
        );
        let is_var = |e: &Expr, right: bool| match e {
            Expr::Bin(op, v, c) => {
                v.as_ref() == &Y
                    && c.as_ref() == &X
                    && match op {
                        Op::Ror(b) => right && *b == w,
                        Op::Rol(b) => !right && *b == w,
                        _ => false,
                    }
            }
            _ => false,
        };
        if matches!(w, 32 | 64) {
            t.same(
                "variable rotate",
                &b(
                    Op::Or,
                    &b(Op::Shl, &Y, &cnt),
                    &b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
                ),
                &spun,
                w,
                xs,
                ys,
            );
            t.same(
                "variable rotate",
                &b(
                    Op::Or,
                    &b(Op::Shr, &Y, &cnt),
                    &b(Op::Shl, &b(Op::Shl, &Y, &k(1)), &rest),
                ),
                &spun_r,
                w,
                xs,
                ys,
            );
            assert!(
                is_var(&spun, false) && is_var(&spun_r, true),
                "{spun:?} {spun_r:?}"
            );
        } else {
            assert!(
                !matches!(spun, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                    && !matches!(spun_r, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
                "width {w} folded: {spun:?} {spun_r:?}"
            );
        }
        let unmasked = fold(
            Op::Or,
            b(Op::Shl, &Y, &X),
            b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &b(Op::Sub, &k(mask_n), &X)),
            w,
        );
        let other = fold(
            Op::Or,
            b(Op::Shl, &X, &cnt),
            b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
            w,
        );
        let called_y = Expr::Call("g".to_owned(), vec![Y]);
        let calling_y = fold(
            Op::Or,
            b(Op::Shl, &called_y, &cnt),
            b(Op::Shr, &b(Op::Shr, &called_y, &k(1)), &rest),
            w,
        );
        assert!(
            !matches!(unmasked, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                && !matches!(other, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                && !matches!(calling_y, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
            "width {w}: {unmasked:?} {other:?} {calling_y:?}"
        );
        let average = b(
            Op::Add,
            &b(Op::And, &X, &Y),
            &b(Op::Shr, &b(Op::Xor, &Y, &X), &k(1)),
        );
        let averaged = fold(
            Op::Add,
            b(Op::And, &X, &Y),
            b(Op::Shr, &b(Op::Xor, &Y, &X), &k(1)),
            w,
        );
        let is_mid = |e: &Expr| {
            matches!(e, Expr::Helper(Helper::Midpoint, args)
                if args.len() == 2 && args[0] == X && args[1] == Y)
        };
        if w >= 64 {
            t.same("midpoint", &average, &averaged, w, xs, ys);
            assert!(is_mid(&averaged), "{averaged:?}");
        } else {
            assert!(!is_mid(&averaged), "width {w} folded: {averaged:?}");
        }
        let signed_avg = fold(
            Op::Add,
            b(Op::And, &X, &Y),
            b(Op::Sar, &b(Op::Xor, &X, &Y), &k(1)),
            w,
        );
        let called_avg = fold(
            Op::Add,
            b(Op::And, &called, &Y),
            b(Op::Shr, &b(Op::Xor, &called, &Y), &k(1)),
            w,
        );
        assert!(
            !is_mid(&signed_avg) && !matches!(called_avg, Expr::Helper(Helper::Midpoint, _)),
            "width {w}: {signed_avg:?} {called_avg:?}"
        );
        let rounded = fold(Op::And, b(Op::Add, &X, &k(15)), k(!15u64), w);
        let is_align = |e: &Expr| {
            matches!(e, Expr::Helper(Helper::AlignUp, args)
                if args.len() == 2 && args[0] == X && args[1] == k(16))
        };
        if w >= 64 {
            t.same(
                "align up",
                &b(Op::And, &b(Op::Add, &X, &k(15)), &k(!15u64)),
                &rounded,
                w,
                xs,
                one,
            );
            assert!(is_align(&rounded), "{rounded:?}");
        } else {
            assert!(!is_align(&rounded), "width {w} folded: {rounded:?}");
        }
        let bare = fold(Op::And, X.clone(), k(!15u64), w);
        let bumped = fold(Op::And, b(Op::Add, &X, &k(16)), k(!15u64), w);
        let pair = fold(Op::And, b(Op::Add, &X, &k(1)), k(!1u64), w);
        assert!(
            !matches!(bare, Expr::Helper(..))
                && !matches!(bumped, Expr::Helper(..))
                && !matches!(pair, Expr::Helper(..)),
            "width {w}: {bare:?} {bumped:?} {pair:?}"
        );
        for cc in [C::e, C::ne] {
            for &c in &d.cs {
                for &e in &d.ds {
                    let less = b(Op::Sub, &X, &k(c));
                    let more = b(Op::Add, &X, &k(c));
                    for (name, flags) in [
                        ("x - c == e", Flags::Cmp(less.clone(), k(e), w)),
                        ("x + c == e", Flags::Cmp(more.clone(), k(e), w)),
                        ("test x - c", Flags::Test(less.clone(), less.clone(), w)),
                        ("test x + c", Flags::Test(more.clone(), more.clone(), w)),
                        ("x - c sets zf", Flags::Result(less.clone(), w)),
                        ("x + c sets zf", Flags::Result(more.clone(), w)),
                        ("add x, c", Flags::Add(X, k(c), w)),
                    ] {
                        let c0 = cond(cc, flags);
                        let Some(s) = c0.simplify() else { continue };
                        let before = Expr::Cond(Box::new(c0));
                        t.same(name, &before, &Expr::Cond(Box::new(s)), w, xs, one);
                    }
                }
            }
        }
        for &c in &d.cs {
            for (sum, term) in [
                (b(Op::Add, &X, &Y), X),
                (b(Op::Add, &X, &Y), Y),
                (b(Op::Add, &b(Op::Add, &X, &k(c)), &Y), X),
                (b(Op::Add, &X, &b(Op::Add, &Y, &k(c))), Y),
                (b(Op::Add, &b(Op::Add, &X, &Y), &k(c)), Y),
            ] {
                let Some(rest) = without_addend(&sum, &term, w) else {
                    continue;
                };
                t.same(
                    "without_addend",
                    &sum,
                    &b(Op::Add, &rest, &term),
                    w,
                    xs,
                    &d.ds,
                );
            }
        }
    }

    /// Every rewrite the folder applies holds on every 8-bit operand.
    ///
    /// Each shape is folded with every constant and every value of its
    /// first variable, and a second variable runs over every value or a
    /// spread of edges, as the shape's size allows.
    #[test]
    fn every_rewrite_of_the_folder_holds_on_every_byte() {
        let all: Vec<u64> = (0..=255).collect();
        let edges = vec![0, 1, 2, 3, 0x7e, 0x7f, 0x80, 0x81, 0xfe, 0xff];
        let d = Domain {
            w: 8,
            xs: all.clone(),
            ys: all.clone(),
            cs: all.clone(),
            ds: edges,
        };
        let mut t = Tally::default();
        local(&mut t, &d);
        mba_stress(&mut t, &d);
        builders(&mut t, &d);
        let magics: Vec<(u64, u64)> = (0..=255)
            .flat_map(|m| (0..8).map(move |s| (m, s)))
            .collect();
        divisions(&mut t, 8, &magics, &all);
        t.verdict();
    }

    /// Every rewrite the folder applies holds at 32 and 64 bits.
    ///
    /// The operands are harvested (zero, one, minus one, each width's
    /// signed and unsigned limits, powers of two and their neighbours) or
    /// seeded; the division idioms run over the multipliers a compiler
    /// would pick for a spread of divisors at every shift, and over the
    /// dividends just below each multiple of the divisor near the top of
    /// the range, where an inexact multiplier first goes wrong.
    #[test]
    fn every_rewrite_of_the_folder_holds_on_sampled_words() {
        let wide = harvest();
        let pick: Vec<u64> = wide.iter().copied().step_by(13).collect();
        let divisors = [
            3u64,
            5,
            6,
            7,
            9,
            10,
            11,
            12,
            13,
            25,
            60,
            100,
            641,
            1000,
            86_400,
            1_000_000_007,
            0x7fff_ffff,
        ];
        let mut t = Tally::default();
        for w in [32u8, 64] {
            let d = Domain {
                w,
                xs: wide.clone(),
                ys: pick.clone(),
                cs: pick.clone(),
                ds: pick.iter().copied().step_by(3).collect(),
            };
            local(&mut t, &d);
            mba_stress(&mut t, &d);
            builders(&mut t, &d);
            power_quotients(&mut t, w, &wide);
            let mut xs = wide.clone();
            let mut magics = Vec::new();
            for dv in divisors.into_iter().filter(|dv| *dv < 1 << (w - 1)) {
                for top in [lane(w), lane(w) >> 1] {
                    let q = top / dv;
                    xs.extend([q * dv - 1, q * dv, (q - 1) * dv + dv - 1]);
                    xs.extend([(q * dv - 1).wrapping_neg(), (q * dv).wrapping_neg()]);
                }
                for s in 0..u64::from(w) {
                    let pow = 1u128 << (u64::from(w) + s);
                    if let Ok(m) = u64::try_from(pow.div_ceil(u128::from(dv)))
                        && m <= lane(w)
                    {
                        magics.push((m, s));
                    }
                }
            }
            if w == 32 {
                wide_quotients(&mut t, &magics, &xs);
            }
            for &(m, _) in &magics {
                t.fold("mulhi(m, x)", (Op::MulHi(w), k(m), X), w, &xs, &[0]);
            }
            divisions(&mut t, w, &magics, &xs);
        }
        t.verdict();
    }

    /// What the collapse must refuse, pinned on the tree it returns.
    ///
    /// A right shift anywhere in a linear form, a shift whose count is
    /// the second variable, a multiplication of a selector by a constant
    /// wider than one bit, a tree past [`MBA_NODES_MAX`] nodes, and a
    /// negation or a sum inside an and, or or xor (its carries move bits
    /// between positions, off the lattice the collapse measures) all
    /// come back unfolded. A stack slot leaf is a variable, so the
    /// collapse that fires names it, not a constant.
    ///
    /// # Panics
    ///
    /// When a refused shape is rewritten, or the stack-slot form collapses
    /// to something but `sp + y`.
    #[test]
    fn mba_refusals_stay_unfolded() {
        let unchanged = |op, l: &Expr, r: &Expr, w| {
            assert_eq!(
                fold(op, l.clone(), r.clone(), w),
                b(op, l, r),
                "rewrote a refused shape at width {w}"
            );
        };
        let smuggled_l = b(
            Op::Add,
            &b(Op::Add, &b(Op::Shr, &X, &k(1)), &Y),
            &b(Op::And, &X, &Y),
        );
        let smuggled_r = b(Op::Add, &Y, &b(Op::And, &X, &Y));
        unchanged(Op::Sub, &smuggled_l, &smuggled_r, 64);
        unchanged(
            Op::Add,
            &b(Op::Xor, &X, &Y),
            &b(Op::Shl, &b(Op::And, &X, &Y), &Y),
            32,
        );
        unchanged(Op::Mul, &b(Op::And, &X, &Y), &k(2), 8);
        unchanged(Op::Mul, &b(Op::And, &X, &Y), &k(3), 8);
        unchanged(
            Op::Mul,
            &k(2),
            &b(
                Op::Add,
                &b(Op::Xor, &X, &Y),
                &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
            ),
            32,
        );
        let borrows = b(
            Op::And,
            &u(Y.clone()),
            &b(
                Op::And,
                &Expr::Un(UnOp::Neg, Box::new(X.clone())),
                &b(Op::Shl, &k(11_444_343_663_368_143_628), &k(7)),
            ),
        );
        unchanged(Op::Or, &Y, &u(borrows), 32);
        unchanged(Op::And, &u(b(Op::Add, &X, &k(3))), &Y, 32);
        let pad = b(Op::Xor, &b(Op::And, &X, &Y), &b(Op::And, &X, &Y));
        let mut capped = b(
            Op::Add,
            &b(Op::Xor, &X, &Y),
            &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
        );
        for _ in 0..3 {
            capped = b(Op::Add, &capped, &pad.clone());
        }
        assert_eq!(
            fold(Op::Add, capped.clone(), k(0), 32),
            capped,
            "a tree past MBA_NODES_MAX must come back unfolded"
        );
        let sp = b(
            Op::Add,
            &b(Op::Xor, &Expr::Sp(-0x28), &Y),
            &b(Op::Shl, &b(Op::And, &Expr::Sp(-0x28), &Y), &k(1)),
        );
        assert_eq!(
            fold(Op::Add, sp, k(0), 64),
            b(Op::Add, &Expr::Sp(-0x28), &Y),
            "a stack slot leaf must collapse as a variable"
        );
    }

    /// Builds the next seeded value of a splitmix64 stream.
    ///
    /// # Arguments
    ///
    /// * `s` - The stream state, advanced in place.
    fn next(s: &mut u64) -> u64 {
        *s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *s;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Builds one seeded random tree over the folder's algebra.
    ///
    /// # Arguments
    ///
    /// * `s` - The stream state, advanced in place.
    /// * `depth` - Remaining recursion; at zero only leaves are built.
    /// * `sext` - Whether [`Expr::Sext`] layers may appear.
    fn tree(s: &mut u64, depth: u8, sext: bool) -> Expr {
        let pick = |s: &mut u64, n: u64| next(s) % n;
        let leaf = |s: &mut u64| match pick(s, 4) {
            0 => X.clone(),
            1 => Y.clone(),
            _ => k(next(s)),
        };
        let sub = |s: &mut u64, d: u8| tree(s, d, sext);
        if depth == 0 {
            return leaf(s);
        }
        if sext && pick(s, 6) == 0 {
            let from = [8u8, 16, 24, 31, 32, 64][usize::try_from(pick(s, 6)).unwrap()];
            return Expr::Sext(Box::new(sub(s, depth - 1)), from);
        }
        match pick(s, 13) {
            0 => b(Op::And, &sub(s, depth - 1), &sub(s, depth - 1)),
            1 => b(Op::Or, &sub(s, depth - 1), &sub(s, depth - 1)),
            2 => b(Op::Xor, &sub(s, depth - 1), &sub(s, depth - 1)),
            3 => b(Op::Add, &sub(s, depth - 1), &sub(s, depth - 1)),
            4 => b(Op::Sub, &sub(s, depth - 1), &sub(s, depth - 1)),
            5 => b(Op::Mul, &sub(s, depth - 1), &k(next(s))),
            6 => b(Op::Shl, &sub(s, depth - 1), &k(pick(s, 40))),
            7 => b(Op::Shr, &sub(s, depth - 1), &k(pick(s, 40))),
            8 => u(sub(s, depth - 1)),
            9 => Expr::Un(UnOp::Neg, Box::new(sub(s, depth - 1))),
            _ => leaf(s),
        }
    }

    /// Folds seeded random trees and holds every rewrite they survive
    /// against the unfolded tree on seeded inputs.
    ///
    /// # Arguments
    ///
    /// * `s` - The stream state, advanced in place.
    /// * `sext` - Whether the trees may sign-extend.
    /// * `name` - The check's name, for the failure message.
    ///
    /// # Panics
    ///
    /// When a rewrite changes a tree's value, or no tree was rewritten at
    /// all (the sweep would then check nothing).
    fn sweep_holds(s: &mut u64, sext: bool, name: &str) {
        const W: u8 = 32;
        let mut changed = 0usize;
        for _ in 0..300 {
            let op = match next(s) % 5 {
                0 => Op::Add,
                1 => Op::Sub,
                2 => Op::And,
                3 => Op::Or,
                _ => Op::Xor,
            };
            let l = tree(s, 4, sext);
            let r = tree(s, 4, sext);
            let before = b(op, &l, &r);
            let after = fold(op, l, r, W);
            changed += usize::from(after != before);
            for _ in 0..64 {
                let (x, y) = (next(s), next(s));
                let Some(want) = ev(&before, W, x, y) else {
                    continue;
                };
                let got = ev(&after, W, x, y);
                assert_eq!(
                    got.map(|v| v & lane(W)),
                    Some(want & lane(W)),
                    "{name}: {before:?} became {after:?} at x={x:#x} y={y:#x}"
                );
            }
        }
        assert!(changed > 0, "{name}: no tree was rewritten");
    }

    /// The folder's rewrites hold on seeded random trees.
    ///
    /// # Panics
    ///
    /// When a rewrite changes a tree's value.
    #[test]
    fn rewrites_hold_on_seeded_trees() {
        for seed in [0x0123_4567_89ab_cdefu64, 0x243f_6a88_85a3_08d3] {
            let mut s = seed;
            sweep_holds(&mut s, false, "plain");
        }
    }

    /// The collapse holds with sign-extension layers in the tree.
    ///
    /// A [`Expr::Sext`] from fewer bits than the width is not linear on
    /// the lattice the collapse measures, so this is the shape a misread
    /// would slip through on.
    ///
    /// # Panics
    ///
    /// When a rewrite changes a tree's value.
    #[test]
    fn rewrites_hold_on_seeded_trees_with_sign_extensions() {
        for seed in [0xfeed_face_dead_beefu64, 0x1319_8a2e_0370_7344] {
            let mut s = seed;
            sweep_holds(&mut s, true, "sext");
        }
    }

    /// An unsigned conversion of a value in `[2^63, 2^64)` keeps that value.
    ///
    /// Casting the truncated float through `i64` saturates at the signed
    /// maximum, one binade early. The unsigned result is the value itself
    /// until `2^64`, and every bit set from there on. A NaN or a negative
    /// value is 0. The signed conversion still saturates at its own bound,
    /// including an exact `-2^63`.
    #[test]
    fn an_unsigned_conversion_keeps_the_binade_past_the_signed_maximum() {
        let zu = |bits: u64, fb: u8, width: u8| super::fcvtzu_bits(bits, fb, width);
        let zs = |bits: u64, fb: u8, width: u8| super::fcvtzs_bits(bits, fb, width);
        let two63 = 0x43E0_0000_0000_0000;
        let below64 = 0x43EF_FFFF_FFFF_FFFF;
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "these two values are exact integers inside the unsigned width"
        )]
        let (high, near) = (f64::from_bits(two63) as u64, f64::from_bits(below64) as u64);
        assert_eq!((high, near), (0x8000_0000_0000_0000, 0xffff_ffff_ffff_f800));
        assert_eq!(zu(two63, 64, 64), Some(0x8000_0000_0000_0000));
        assert_eq!(zu(below64, 64, 64), Some(0xffff_ffff_ffff_f800));
        assert_eq!(zu(0x43F0_0000_0000_0000, 64, 64), Some(u64::MAX));
        assert_eq!(zu(0x7FF0_0000_0000_0000, 64, 64), Some(u64::MAX));
        assert_eq!(zu(0x7FF8_0000_0000_0000, 64, 64), Some(0));
        assert_eq!(zu(0xBFF0_0000_0000_0000, 64, 64), Some(0));
        assert_eq!(zs(two63, 64, 64), Some(0x7fff_ffff_ffff_ffff));
        assert_eq!(
            zs(0xC3E0_0000_0000_0000, 64, 64),
            Some(0x8000_0000_0000_0000)
        );
        assert_eq!(zs(0x7FF8_0000_0000_0000, 64, 64), Some(0));
        assert_eq!(zu(0x4F00_0000, 32, 32), Some(0x8000_0000));
        assert_eq!(zu(0x4F80_0000, 32, 32), Some(0xffff_ffff));
        assert_eq!(zu(two63, 64, 32), Some(0xffff_ffff));
        assert_eq!(zs(0xC1E0_0000_0000_0000, 64, 32), Some(0x8000_0000));
        assert_eq!(zu(0, 16, 64), None);
        assert_eq!(zu(two63, 64, 16), None);
        assert_eq!(super::RoundToInt::parse("fcvtzu"), None);
        assert_eq!(super::RoundToInt::parse("__fcvtzs64"), None);
        assert_eq!(
            super::RoundToInt::parse("fcvtzu64").and_then(|op| op.apply(two63, 64)),
            Some(0x8000_0000_0000_0000)
        );
        assert_eq!(
            super::fcvt_float_width(Some(&Expr::Const(16)), Some(64)),
            None
        );
        assert_eq!(
            super::fcvt_float_width(Some(&Expr::Const(32)), None),
            Some(32)
        );
        assert_eq!(super::fcvt_float_width(None, Some(64)), Some(64));
    }
}
