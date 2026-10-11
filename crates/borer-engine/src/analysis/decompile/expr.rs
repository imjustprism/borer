//! Symbolic expressions for the decompiler: text variables ([`Key`]), access
//! types ([`Ty`]), constant folding, and precedence-aware C rendering.
//!
//! Every `Var` refers to the *current text value* of a variable in the emitted
//! pseudo-C, never to a machine register at some earlier time. That invariant
//! is what lets the lifter keep expressions symbolic until they are needed.

use crate::isa::{ConditionCode, Register};

use crate::analysis::Overlay;
use crate::num::{lo16, lo32};
use crate::program::{BinaryFormat, Program, SymbolKind};

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// IEEE-754 minimum (`fmin`).
    FMin,
    /// IEEE-754 maximum (`fmax`).
    FMax,
}

impl Op {
    /// Returns the C precedence level (higher binds tighter; [`ATOM`] for calls).
    fn prec(self) -> u8 {
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
    fn sym(self) -> &'static str {
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
    fn commutative(self) -> bool {
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

    /// Tells whether `a op b == b op a` (the public form of [`Op::commutative`]).
    pub(super) fn is_commutative(self) -> bool {
        self.commutative()
    }

    /// Tells whether constant operands read better in hex (bitwise masks).
    fn hex_operands(self) -> bool {
        matches!(self, Op::And | Op::Or | Op::Xor)
    }

    /// Returns the operator family; mixing families gets explicit parentheses
    /// even when C precedence would not need them (`a & b | c`, `a + b << 2`).
    fn family(self) -> u8 {
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// Returns the function-style spelling, or `None` for the prefix operators.
    fn func_name(self) -> Option<&'static str> {
        match self {
            UnOp::Neg | UnOp::Not => None,
            UnOp::Bswap => Some("bswap"),
            UnOp::Tzcnt => Some("tzcnt"),
            UnOp::Lzcnt => Some("lzcnt"),
            UnOp::Popcnt => Some("popcnt"),
            UnOp::Sqrt => Some("sqrt"),
            UnOp::Fabs => Some("fabs"),
            UnOp::Bsf => Some("bsf"),
            UnOp::Bsr => Some("bsr"),
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
    fn signed(self) -> bool {
        use ConditionCode as C;
        matches!(self.0, C::l | C::ge | C::le | C::g)
    }

    /// Returns the C relational operator for a compare.
    ///
    /// # Returns
    ///
    /// `==`, `!=`, `<`, `>=`, `<=` or `>`; `None` for flag tests that are not
    /// comparisons (overflow, parity, no condition).
    fn rel(self) -> Option<&'static str> {
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
            Flags::Cmp(l, r, _) | Flags::Test(l, r, _) | Flags::Add(l, r, _) => {
                l.any_var(pred) || r.any_var(pred)
            }
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.any_var(pred),
            Flags::Shift(e, _, c) => e.any_var(pred) || c.any_var(pred),
            Flags::Unknown => false,
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
    /// Convert to another type (`(float)x`, `(int32_t)x`).
    Cast(Box<Expr>, Ty),
    /// An intrinsic or library call the C vocabulary has no operator for;
    /// constant arguments render in hex (shuffle and blend masks).
    Call(String, Vec<Expr>),
    /// An IEEE-754 constant: its bit pattern and type.
    FConst(u64, Ty),
}

/// Precedence of an atom (name, constant, call): never parenthesized.
const ATOM: u8 = 13;
/// Precedence of the prefix operators (`-`, `~`, `*`, casts).
const UNARY: u8 = 12;

/// Returns the mask of the low `bits` bits (all ones for 64 or more).
///
/// # Arguments
///
/// * `bits` - Width in bits.
fn mask_bits(bits: u8) -> u64 {
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
fn sext(v: u64, bits: u8) -> u64 {
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
            Expr::Un(_, e) | Expr::Deref(e, _) | Expr::Sext(e, _) | Expr::Cast(e, _) => {
                1 + e.size()
            }
            Expr::Call(_, args) => 1 + args.iter().map(Expr::size).sum::<usize>(),
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

    /// Tells whether the expression may read text variable `k`: it reads
    /// it, or, for a stack slot, reads through a computed frame address at
    /// or below the slot (`*(&local_14 + ebx * 4)` may read any slot from
    /// `local_14` up), which a write of the slot changes as well.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    pub(super) fn may_read(&self, k: Key) -> bool {
        self.mentions(k)
            || matches!(k, Key::Slot(o) if self.frame_read_base().is_some_and(|b| b <= o))
    }

    /// The lowest frame offset the expression reads through a computed
    /// address from: `k` for `*(&local + x)`, never for a slot read whole.
    fn frame_read_base(&self) -> Option<i64> {
        match self {
            Expr::Deref(a, _) => match **a {
                Expr::Sp(_) => None,
                _ => min_opt(a.frame_address(), a.frame_read_base()),
            },
            Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Var(_) | Expr::FConst(..) => None,
            Expr::Bin(_, l, r) => min_opt(l.frame_read_base(), r.frame_read_base()),
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) => e.frame_read_base(),
            Expr::Call(_, args) => args.iter().filter_map(Expr::frame_read_base).min(),
            Expr::Cond(c) => c.frame_read_base(),
            Expr::Ternary(c, a, b) => min_opt(
                c.frame_read_base(),
                min_opt(a.frame_read_base(), b.frame_read_base()),
            ),
        }
    }

    /// The lowest frame offset the expression's value can point at, as an
    /// address: `k` for `&local_k + x`, never through a value loaded from
    /// memory.
    fn frame_address(&self) -> Option<i64> {
        match self {
            Expr::Sp(k) => Some(*k),
            Expr::Bin(_, l, r) => min_opt(l.frame_address(), r.frame_address()),
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) => e.frame_address(),
            Expr::Ternary(_, a, b) => min_opt(a.frame_address(), b.frame_address()),
            Expr::Const(_)
            | Expr::Str(_)
            | Expr::Var(_)
            | Expr::FConst(..)
            | Expr::Deref(..)
            | Expr::Call(..)
            | Expr::Cond(_) => None,
        }
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
            Expr::Un(_, e) | Expr::Deref(e, _) | Expr::Sext(e, _) | Expr::Cast(e, _) => {
                e.any_var(pred)
            }
            Expr::Call(_, args) => args.iter().any(|a| a.any_var(pred)),
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
            Expr::Un(_, e) | Expr::Deref(e, _) | Expr::Sext(e, _) | Expr::Cast(e, _) => {
                e.partial_idiom()
            }
            Expr::Call(_, args) => args.iter().any(Expr::partial_idiom),
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
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) => e.mem_dependent(),
            Expr::Call(_, args) => args.iter().any(Expr::mem_dependent),
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
            Expr::Un(_, e) | Expr::Deref(e, _) | Expr::Sext(e, _) | Expr::Cast(e, _) => e.min_sp(),
            Expr::Call(_, args) => args.iter().filter_map(Expr::min_sp).min(),
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
            Expr::Call(f, args) => {
                Expr::Call(f.clone(), args.iter().map(|a| a.subst(from, to)).collect())
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
            Expr::Deref(_, ty) | Expr::Cast(_, ty) => matches!(ty, Ty::F32 | Ty::F64),
            Expr::Bin(op, ..) => op.is_float(),
            Expr::Un(UnOp::Sqrt | UnOp::Fabs, _) => true,
            Expr::Un(UnOp::Neg, inner) => inner.is_float(),
            Expr::Var(Key::Reg(r)) => {
                r.is_vector_register() || (*r >= Register::ST0 && *r <= Register::ST7)
            }
            Expr::Call(f, _) => f == "fabs",
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
            Flags::Cmp(l, r, _) | Flags::Test(l, r, _) | Flags::Add(l, r, _) => {
                min_opt(l.frame_read_base(), r.frame_read_base())
            }
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.frame_read_base(),
            Flags::Shift(e, _, c) => min_opt(e.frame_read_base(), c.frame_read_base()),
            Flags::Unknown => None,
        }
    }

    /// Returns the lowest stack offset whose address appears in the flags operands.
    fn min_sp(&self) -> Option<i64> {
        match &self.flags {
            Flags::Cmp(l, r, _) | Flags::Test(l, r, _) | Flags::Add(l, r, _) => {
                min_opt(l.min_sp(), r.min_sp())
            }
            Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => e.min_sp(),
            Flags::Shift(e, _, c) => min_opt(e.min_sp(), c.min_sp()),
            Flags::Unknown => None,
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
    fn bool_operand(&self) -> Option<&Cond> {
        let inner = match &self.flags {
            Flags::Test(l, r, _) if l == r || matches!(r, Expr::Const(1)) => l,
            Flags::Result(e, _) | Flags::Shift(e, _, _) => e,
            Flags::Cmp(l, Expr::Const(0), _) => l,
            Flags::Cmp(..)
            | Flags::Test(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Truth(..)
            | Flags::Unknown => {
                return None;
            }
        };
        match inner {
            Expr::Cond(c) => Some(c),
            _ => None,
        }
    }

    /// Returns the node count of the flags operands.
    pub(super) fn size(&self) -> usize {
        match &self.flags {
            Flags::Cmp(l, r, _) | Flags::Test(l, r, _) | Flags::Add(l, r, _) => l.size() + r.size(),
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
            Flags::Cmp(l, r, _) | Flags::Test(l, r, _) | Flags::Add(l, r, _) => {
                l.mem_dependent() || r.mem_dependent()
            }
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
                // INVARIANT: `jl` reads SF != OF, the sign of the sum taken
                // without wrapping, which overflow makes disagree with the
                // sign of the machine sum.
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
                    // A 64-bit carry is the add overflowing `u64` itself, which
                    // `lu + ru` cannot represent: it panics in debug and wraps
                    // to a wrong answer in release.
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
            // INVARIANT: the sign flag is the top bit of the difference at the
            // compare's width, which overflow can make disagree with the sign
            // of the wide difference (`0x7fffffff - -1` at 32 bits is
            // negative).
            C::s | C::ns => {
                let top = lu.wrapping_sub(ru) & m & (1u64 << (bits.clamp(1, 64) - 1)) != 0;
                (self.cc.0 == C::s) == top
            }
            C::None | C::o | C::no | C::p | C::np => return None,
        })
    }
}

// ------------------------------------------------------------------ folding --

/// Returns the C signed integer type of `bits` bits.
///
/// # Arguments
///
/// * `bits` - Width in bits; rounded up to the next C type.
fn signed_ty(bits: u8) -> &'static str {
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
fn term_of(e: &Expr) -> (&Expr, u64) {
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
            Box::new(dividend),
            Box::new(Expr::Const(d)),
        ));
    }
    None
}

/// Reverses the strength reduction of a division or remainder by a constant.
///
/// Unsigned `x / d` comes back as `mulhi(M, x) >> s` (or the shape of
/// [`overflow_division`] when the magic needs a bit more); signed as the quotient
/// of [`signed_quotient_of`] plus its own sign bit (`q + (q >>> (w - 1))`);
/// `x % d` as `x - (x / d) * d` or `x + (x / d) * -d` once the division is
/// back. Each is rendered as the operator it was, the divisor recovered by
/// [`magic_divisor`] or [`signed_magic_divisor`]. The sign bit of such a
/// quotient on its own, that is `q >>> (w - 1)` for a quotient the compiler
/// kept in a register and fixed up elsewhere, is the sign bit of the
/// dividend, since the divisor is positive; the fix-up then matches either
/// spelling.
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
            // A 32-bit `sar` takes its operand sign-extended from the lane,
            // so the idiom is looked for inside that extension too, where
            // the sum is a 32-bit one whatever the shift's width.
            let k = const_of(r)?;
            match l {
                Expr::Sext(inner, 32) => signed_power_quotient(inner, k, 32),
                _ => None,
            }
            .or_else(|| signed_power_quotient(l, k, bits))
        }
        Op::Shr => {
            let s = const_of(r)?;
            if let Some((w, m, x)) = mulhi_of(l, false)
                && let Some(d) = magic_divisor(w, m, s)
            {
                return Some(Expr::Bin(
                    Op::Div,
                    Box::new(x.clone()),
                    Box::new(Expr::Const(d)),
                ));
            }
            if let Some((w, m, x, s2, negative)) = signed_quotient_of(l)
                && s == u64::from(w) - 1
                && signed_magic_divisor(w, m, s2, negative).is_some()
            {
                return Some(Expr::Bin(
                    Op::Shr,
                    Box::new(x.clone()),
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
                // A 32-bit copy of the quotient masks it to its lane before
                // its sign bit is shifted down.
                let sign_of = match sign_of.as_ref() {
                    Expr::Bin(Op::And, v, k) if const_of(k) == Some(mask_bits(w)) => v.as_ref(),
                    other => other,
                };
                if const_of(amount) != Some(u64::from(w) - 1) || (sign_of != q && sign_of != x) {
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
            for (x, product) in [(l, r), (r, l)] {
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
                    let Some(dc) = const_of(d2) else { continue };
                    let factor = if negated { dc.wrapping_neg() } else { dc };
                    if x2.as_ref() == x && const_of(d) == Some(factor) {
                        return Some(Expr::Bin(rem, Box::new(x.clone()), d2.clone()));
                    }
                }
                if op == Op::Sub {
                    break;
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

/// The note for a condition whose outcome never varied while sampling.
///
/// Naming the outcome names the dead branch: a condition that is always true
/// makes its `else` unreachable, and a reader can stop following the half of
/// the function that never runs. The condition itself is kept, because this
/// is a sample rather than a proof.
///
/// # Arguments
///
/// * `outcome` - What the condition evaluated to on every sampled input.
/// * `inverted` - Whether the condition is being rendered negated.
///
/// # Returns
///
/// The comment to append.
pub(super) fn opaque_note(outcome: bool, inverted: bool) -> String {
    let taken = outcome != inverted;
    let dead = if taken { "else" } else { "body" };
    format!("/* opaque: always {taken} on every sampled input, so the {dead} never runs */")
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
        // The exclusive or is the subtraction, since the scan's result fits
        // in the same bits the constant covers.
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
                // The xor is the sum without carries and the and is exactly
                // the carries, so adding the carries in twice completes it.
                if let Some(x) = pair(first, Op::Xor)
                    && let Some(d) = doubled(second)
                    && let Some(y) = pair(d, Op::And)
                    && same_pair(x, y)
                {
                    return Some(sum(x.0, x.1));
                }
                // Every bit is in exactly one of the and and the or, except
                // the bits in both operands, which are in both.
                if let Some(x) = pair(first, Op::And)
                    && let Some(y) = pair(second, Op::Or)
                    && same_pair(x, y)
                {
                    return Some(sum(x.0, x.1));
                }
                // The or holds each bit once and the xor holds the ones in
                // only one operand, so their difference is the shared bits.
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
            // Removing the shared bits from the union leaves the bits in
            // exactly one operand.
            if let Some(x) = pair(l, Op::Or)
                && let Some(y) = pair(r, Op::And)
                && same_pair(x, y)
            {
                return Some(bits(Op::Xor, x.0, x.1));
            }
            // And removing the bits in exactly one leaves the shared ones.
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
fn indexed(addr: &Expr, ty: Ty) -> Option<(Expr, Expr)> {
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
/// constant stays outermost. Division by a constant that is zero in its
/// low `bits` is left symbolic.
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
    if let Some(e) = division_idiom(op, &l, &r, bits) {
        return e;
    }
    if let Some(e) = select_idiom(op, &l, &r) {
        return e;
    }
    if let Some(e) = mba_idiom(op, &l, &r) {
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
        // The constant is signed at the operation's width: a 32-bit
        // `add esp, 0xfffffd30` moves the pointer down by 0x2d0, not up by
        // four gigabytes.
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
            if matches!(**a, Expr::Const(_))
                && let Some(x) = scaled(b)
            {
                return Some(x);
            }
            if matches!(**b, Expr::Const(_))
                && let Some(x) = scaled(a)
            {
                return Some(x);
            }
            table_index(a).or_else(|| table_index(b))
        }
        Expr::Bin(_, a, b) => table_index(a).or_else(|| table_index(b)),
        Expr::Un(_, x) | Expr::Deref(x, _) | Expr::Sext(x, _) | Expr::Cast(x, _) => table_index(x),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Cond(_)
        | Expr::Call(..)
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
        Expr::Deref(_, ty) => mask_bits(ty.bits().min(64)),
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
        // INVARIANT: only 32-bit code keys a register by its 32-bit name
        // (64-bit code keys every one at full width), and there it holds no
        // more than 32 bits.
        Expr::Var(Key::Reg(r)) if r.size() == 4 => 0xffff_ffff,
        // INVARIANT: a global is read at the width its key names and is
        // declared `uintN_t` at it, so `mov ecx, [tls_index]` leaves `rcx`
        // no wider than 32 bits and an index read from it needs no mask.
        Expr::Var(Key::Global(_, bits)) => mask_bits(*bits),
        Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Sext(..)
        | Expr::Cast(..)
        | Expr::Call(..)
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
    let (name, l, r, bits) = match &cond.flags {
        Flags::Carry(Expr::Bin(Op::MulHi(w), l, r)) => ("mul_sat", l.as_ref(), r.as_ref(), *w),
        Flags::Add(l, r, w) if matches!(cond.cc.0, C::b | C::ae) => ("add_sat", l, r, *w),
        _ => return None,
    };
    if !matches!(taken, Expr::Const(c) if *c == mask_bits(bits)) {
        return None;
    }
    let (x, y) = match other {
        Expr::Bin(Op::Mul, x, y) if name == "mul_sat" => (x.as_ref(), y.as_ref()),
        Expr::Bin(Op::Add, x, y) if name == "add_sat" => (x.as_ref(), y.as_ref()),
        _ => return None,
    };
    let same = (x == l && y == r) || (x == r && y == l);
    same.then(|| Expr::Call(name.to_owned(), vec![l.clone(), r.clone()]))
}

/// Builds `cond ? a : b` with the boolean idioms folded.
///
/// A decidable condition picks its side; equal sides collapse; `c ? 1 : 0`
/// is `c` and `c ? 0 : 1` is `!c`; all ones on a carry over the product or
/// sum that set it is the saturating operation ([`saturating`]).
///
/// # Arguments
///
/// * `cond` - The condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
pub(super) fn ternary(cond: Cond, a: Expr, b: Expr) -> Expr {
    match cond.eval() {
        Some(true) => return a,
        Some(false) => return b,
        None => {}
    }
    if a == b {
        return a;
    }
    if let Some(e) = saturating(&cond, &a, &b) {
        return e;
    }
    match (&a, &b) {
        (Expr::Const(1), Expr::Const(0)) => Expr::Cond(Box::new(cond)),
        (Expr::Const(0), Expr::Const(1)) => Expr::Cond(Box::new(cond.invert())),
        _ => Expr::Ternary(Box::new(cond), Box::new(a), Box::new(b)),
    }
}

/// Builds `e & m` simplified.
///
/// The mask is dropped when `e` provably fits in it, the result is `0` when no
/// bit of `e` survives it (including `(x << s) & m` when the shift moves
/// everything past the mask), nested masks combine, and a mask distributes
/// over `|`.
///
/// # Arguments
///
/// * `e` - The value.
/// * `m` - The mask.
pub(super) fn mask(e: Expr, m: u64) -> Expr {
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
        | Expr::Call(..)
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
                    // INVARIANT: a scan of zero leaves its destination as it
                    // was, no value the expression can name; `tzcnt` of zero
                    // is the width.
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
        other => Expr::Sext(Box::new(other), from_bits),
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

// ---------------------------------------------------------------- rendering --

/// Name resolution for rendering: overlay names beat symbol names beat
/// debug-recorded locals beat synthesized `g{bits}_{addr}` / `local_N` /
/// register names.
pub(super) struct Names<'a> {
    /// Supplies the symbol table.
    pub program: &'a Program,
    /// Supplies function entries and the symbol index.
    pub analysis: &'a crate::analysis::Analysis,
    /// Supplies user names.
    pub overlay: &'a Overlay,
    /// The first parameter is the `this` object of a member function.
    pub this_param: bool,
    /// Index of the hidden return-pointer parameter, named `result`.
    pub result_param: Option<u8>,
    /// The function being rendered, so its own `__FUNCSIG__` literal reads
    /// as that macro.
    pub own_name: std::sync::Arc<str>,
    /// Parameters the debug information recorded, in order.
    pub debug_params: std::sync::Arc<[crate::dwarf::Parameter]>,
    /// The frame-relative locals the debug information recorded, as slot
    /// offset to name; a slot one names renders that name where the
    /// synthesized `local_N` would.
    pub debug_locals: std::sync::Arc<std::collections::BTreeMap<i64, String>>,
    /// Frame offset of the first stack-passed argument, above the return
    /// address and the shadow space.
    pub first_stack: i64,
    /// How many stack-passed arguments the function reads.
    pub stack_params: u32,
    /// How many arguments the convention passes in registers, which is
    /// where the stack ones continue counting from.
    pub reg_params: u32,
    /// Stack word size in bytes: the width of the return address and the
    /// distance between two stack-passed arguments.
    pub word: i64,
    /// The type each stack slot the text names is declared with, by its
    /// frame offset: what its name reads and writes.
    pub slot_types: std::sync::Arc<std::collections::BTreeMap<i64, Ty>>,
}

impl Names<'_> {
    /// Names a constant that is the address of a function, a data symbol or
    /// a string literal.
    ///
    /// # Arguments
    ///
    /// * `v` - The constant.
    /// * `literal` - Whether the string at the address may name it: true
    ///   where the constant is a value passed, stored, returned or loaded
    ///   through, false where it is an operand of arithmetic or a
    ///   comparison, which a number lands on as often as an address does.
    ///
    /// # Returns
    ///
    /// The function's name, `&symbol` for an export/local data symbol (also
    /// in `.bss`), `&Class::vftable` for a recovered vtable,
    /// `&Class::staticMetaObject` for a `moc` meta-object, `&Class::RTTI` for
    /// a class's type descriptor, `&Class::Id` for a registered message
    /// class's id, the name of a
    /// known algorithm's table (`crc_32_table`), `&__ImageBase` for a PE's
    /// own image base, a mapped overlay-named address, the quoted literal
    /// for a string in non-code memory when `literal` allows it, `&gN_addr`
    /// for an address in
    /// writable data that holds no literal, or `None` when the value names
    /// nothing.
    pub(super) fn const_name(&self, v: u64, literal: bool) -> Option<String> {
        if let Some(f) = self.analysis.function(v) {
            return Some(
                bare(&crate::analysis::name_of(
                    self.analysis,
                    self.overlay,
                    f.entry,
                ))
                .to_owned(),
            );
        }
        if let Some(s) = self
            .analysis
            .symbol_at(self.program, v)
            .filter(|s| s.kind != SymbolKind::Import)
        {
            return Some(format!("&{}", crate::search::demangled_name(&s.name)));
        }
        if let Some(class) = self.analysis.classes.vtables.get(&v) {
            return Some(format!("&{class}::vftable"));
        }
        if let Some(name) = self.analysis.classes.secondary_vtables.get(&v) {
            return Some(format!("&{name}"));
        }
        if let Some(class) = self.analysis.qt.iter().find(|c| c.meta_object == v) {
            return Some(format!("&{}::staticMetaObject", class.name));
        }
        if let Some(name) = self.analysis.crypto.get(&v) {
            return Some(crate::crypto::identifier(name));
        }
        // INVARIANT: a PE reads its own headers through the image base, which
        // the linker names `__ImageBase`; `*(uint16_t*)&__ImageBase == 0x5a4d`
        // is the DOS signature check it is.
        if v == self.program.image_base && self.program.format == BinaryFormat::Pe {
            return Some("&__ImageBase".to_owned());
        }
        let mapped = self
            .program
            .sections
            .iter()
            .any(|s| v >= s.va && v < s.va + s.vsize.max(s.file_size));
        if mapped && let Some(n) = self.overlay.names.get(&v) {
            return Some(format!("&{n}"));
        }
        if let Some(class) = self.analysis.classes.descriptors.get(&v) {
            return Some(format!(
                "&{class}::{}",
                self.analysis.packs.name_for("class_info")
            ));
        }
        if mapped {
            let homes = self.analysis.derived.get_or_build("id_homes", (), || {
                crate::analysis::messages::id_homes(self.program, self.analysis)
            });
            if let Some(class) = homes.get(&v) {
                return Some(format!(
                    "&{class}::{}",
                    self.analysis.packs.name_for("class_id")
                ));
            }
        }
        // INVARIANT: a status code is looked up only off the image, so a
        // 32-bit program large enough to map 0x406d1388 keeps it an address.
        if !mapped && let Some(n) = crate::winconst::name(v) {
            return Some(n.to_owned());
        }
        if literal && let Some(text) = super::literal_at(self.program, v, &self.own_name) {
            return Some(text);
        }
        // INVARIANT: an address in writable data is a variable's, and the
        // variable is named by the word as a read of it would be, so the
        // object passed to one call and read by another has one name.
        self.program
            .section_at(v)
            .filter(|s| s.writable && !s.executable)
            .map(|_| format!("&g{}_{v:x}", self.word * 8))
    }

    /// Tells whether a constant is the address of a string's first
    /// character.
    ///
    /// A literal of at least one character starts there, and the byte before
    /// it ends whatever came before (a terminator), or the section starts
    /// there. An address inside a string, where an unrelated number lands as
    /// often as not, is no start, and neither is a lone terminator, which
    /// no sum indexes as text.
    ///
    /// # Arguments
    ///
    /// * `v` - The constant.
    fn starts_string(&self, v: u64) -> bool {
        let first = self.program.section_at(v).is_some_and(|s| s.va == v)
            || v.checked_sub(1)
                .and_then(|b| self.program.read_va(b, 1))
                .is_some_and(|b| b == [0]);
        first
            && super::literal_at(self.program, v, &self.own_name)
                .is_some_and(|l| !matches!(l.as_str(), "\"\"" | "L\"\""))
    }

    /// Returns the bare import name whose IAT slot is `addr`: demangled,
    /// without the `dll!` prefix, so a call through the slot reads as
    /// `QString::QString` and not `??0QString@@QAE@PBD@Z`.
    ///
    /// # Arguments
    ///
    /// * `addr` - A candidate IAT slot address.
    pub(super) fn import_at(&self, addr: u64) -> Option<String> {
        self.program
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Import && s.addr == addr && s.addr != 0)
            .map(|s| bare(&crate::search::demangled_name(&s.name)).to_owned())
    }

    /// Renders the text name of a variable.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    ///
    /// # Returns
    ///
    /// The lowercase register name, `local_N`/`arg_N`, the overlay, import or
    /// data-symbol name of a global, `Class::Id` for the id a registered
    /// message class hands out, `Class::RTTI` for a class's type descriptor
    /// (else `g{bits}_{addr}`), `tmp_N`, or `aN` for an incoming argument.
    pub(super) fn key(&self, k: Key) -> String {
        match k {
            Key::Reg(r) => format!("{r:?}").to_lowercase(),
            Key::Slot(off) => self.slot(off),
            Key::Global(addr, bits) => {
                if let Some(off) = tls_slot(addr) {
                    return match self.analysis.classes.tls_slots.get(&off) {
                        Some(c) => format!("{c}::{}", self.analysis.packs.name_for("singleton")),
                        None => format!("tls_{off:#x}"),
                    };
                }
                if let Some(n) = self.overlay.names.get(&addr) {
                    return n.clone();
                }
                if let Some(n) = self.import_at(addr) {
                    return n;
                }
                if let Some(s) = self.analysis.symbol_at(self.program, addr) {
                    return crate::search::demangled_name(&s.name);
                }
                let homes = self.analysis.derived.get_or_build("id_homes", (), || {
                    crate::analysis::messages::id_homes(self.program, self.analysis)
                });
                if let Some(class) = homes.get(&addr) {
                    return format!("{class}::{}", self.analysis.packs.name_for("class_id"));
                }
                if let Some(class) = self.analysis.classes.descriptors.get(&addr) {
                    return format!("{class}::{}", self.analysis.packs.name_for("class_info"));
                }
                format!("g{bits}_{addr:x}")
            }
            Key::Tmp(n) => format!("tmp_{n}"),
            Key::Param(0) if self.this_param => "this".to_owned(),
            Key::Param(i) if Some(i) == self.result_param => "result".to_owned(),
            // The compiler's own name for the parameter, when it left one.
            Key::Param(i) => self
                .debug_params
                .get(usize::from(i))
                .map(|p| p.name.clone())
                .filter(|n| !n.is_empty())
                .unwrap_or_else(|| format!("a{}", u32::from(i) + 1)),
        }
    }
}

/// Strips the `dll!` prefix from an import name.
///
/// # Arguments
///
/// * `name` - A symbol name, possibly `DLL!name`.
pub(super) fn bare(name: &str) -> &str {
    crate::analysis::bare_name(name)
}

/// Renders the text name of a stack slot.
///
/// # Arguments
///
/// * `off` - Byte offset from the entry stack pointer.
/// * `word` - Stack word size in bytes, which is the width of the return
///   address the arguments sit above.
/// * `shadow` - Bytes of callee-owned home space above the return address:
///   32 under the Microsoft x64 convention, 0 elsewhere.
///
/// # Returns
///
/// `local_N` below the return address, `retaddr` at it, `home_N` in the
/// shadow space above it and `arg_N` past that, where N counts from the
/// first slot past the return address: the home slots
/// are the callee's own, where it spills or keeps a local, so a write
/// there is no write to an argument.
pub(super) fn slot_name(off: i64, word: i64, shadow: i64) -> String {
    if off < 0 {
        format!("local_{:x}", -off)
    } else if off == 0 {
        "retaddr".to_owned()
    } else if off < word + shadow {
        format!("home_{:x}", off - word)
    } else {
        format!("arg_{:x}", off - word)
    }
}

impl Names<'_> {
    /// Names a stack slot: an incoming argument by its parameter name, a
    /// slot the debug information named by that name, and anything else by
    /// [`slot_name`].
    ///
    /// The arguments a convention passes on the stack sit above the return
    /// address and the shadow space, one word apart, and continue the
    /// numbering the register arguments start. A local the debug
    /// information states for the slot is the compiler's own name for it,
    /// so it beats the synthesis the way any debug name does; it names the
    /// slot alone, never its width, which the lifting's own declaration
    /// keeps stating.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    pub(super) fn slot(&self, off: i64) -> String {
        if let Some(i) = self.stack_param(off) {
            return self.key(Key::Param(i));
        }
        if let Some(name) = self.debug_locals.get(&off) {
            return name.clone();
        }
        slot_name(off, self.word, self.first_stack - self.word)
    }

    /// Names an access of `ty` to the stack slot at `off`: the slot's name
    /// where the access is as wide as its declaration, else a load or a
    /// store of that width through its address.
    ///
    /// A C variable reads and writes as wide as it is declared, where the
    /// machine reads `mov edx, [rsp+4]` over a byte slot and the three
    /// bytes above it: `*(uint32_t*)&local_c`, not `local_c`. A stack
    /// parameter read narrower than the word is its low bytes, `(uint16_t)
    /// a1`.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    /// * `ty` - The access type.
    ///
    /// # Returns
    ///
    /// `(text, precedence)`.
    pub(super) fn slot_at(&self, off: i64, ty: Ty) -> (String, u8) {
        let name = self.slot(off);
        // INVARIANT: a stack parameter is a value of the machine's word; a
        // narrower read of it is its low bytes (`mov cx, [ebp+8]`).
        if self.stack_param(off).is_some() {
            return if matches!(ty, Ty::U8 | Ty::U16 | Ty::U32)
                && i64::from(ty.bits()) < self.word * 8
            {
                (format!("({}){name}", ty.name()), UNARY)
            } else {
                (name, ATOM)
            };
        }
        match self.slot_types.get(&off) {
            Some(declared)
                if declared.bits() != ty.bits()
                    && !matches!(ty, Ty::U128)
                    && !matches!(declared, Ty::U128) =>
            {
                (format!("*({}*)&{name}", ty.name()), UNARY)
            }
            _ => (name, ATOM),
        }
    }

    /// The parameter index of an incoming stack-argument slot.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    ///
    /// # Returns
    ///
    /// The index, or `None` when the slot is a local or beyond the count.
    pub(super) fn stack_param(&self, off: i64) -> Option<u8> {
        let past = off.checked_sub(self.first_stack)?;
        if past < 0 || past % self.word != 0 {
            return None;
        }
        let nth = u32::try_from(past / self.word).ok()?;
        (nth < self.stack_params)
            .then(|| u8::try_from(self.reg_params + nth).ok())
            .flatten()
    }
}

/// Renders an IEEE-754 constant as a C literal (`0.5f`, `2.0`, `NAN`, `-INFINITY`).
///
/// # Arguments
///
/// * `bits` - The bit pattern (low 32 bits for a `float`).
/// * `ty` - [`Ty::F32`] or [`Ty::F64`]; anything else renders the bits in hex.
fn render_fconst(bits: u64, ty: Ty) -> String {
    let (value, text, suffix) = match ty {
        Ty::F32 => {
            let f = f32::from_bits(u32::try_from(bits & 0xffff_ffff).unwrap_or(0));
            (f64::from(f), format!("{f}"), "f")
        }
        Ty::F64 => {
            let f = f64::from_bits(bits);
            (f, format!("{f}"), "")
        }
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => return format!("{bits:#x}"),
    };
    if value.is_nan() {
        return "NAN".to_owned();
    }
    if value.is_infinite() {
        return if value > 0.0 { "INFINITY" } else { "-INFINITY" }.to_owned();
    }
    let mut s = text;
    if !s.contains(['.', 'e']) {
        s.push_str(".0");
    }
    s.push_str(suffix);
    s
}

/// Returns the C type a cast to `ty` spells: floats by name, integers as
/// their signed form (the conversions that produce them are signed).
///
/// # Arguments
///
/// * `ty` - The target type.
fn cast_name(ty: Ty) -> &'static str {
    match ty {
        Ty::F32 | Ty::F64 | Ty::U128 => ty.name(),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 => signed_ty(ty.bits()),
    }
}

/// The low bits an `and` mask clears, when it clears only those.
///
/// A mask with its top bit set and fewer than twelve low bits off is a
/// clearing mask: `x & 0xffffffffffffff00` reads better as `x & ~0xff`.
///
/// # Arguments
///
/// * `mask` - The right operand of the `and`.
fn low_clear(mask: &Expr) -> Option<u64> {
    match mask {
        Expr::Const(c) if *c >= 1 << 63 && !*c < 0x1000 => Some(!*c),
        _ => None,
    }
}

/// Renders a constant: small values as decimal, small negatives as `-N`, the rest as hex.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - The context prefers hex (bitwise masks, address arithmetic):
///   values of ten and up render as hex and negatives stay hex.
pub(super) fn render_const(v: u64, hex: bool) -> String {
    render_const_in(v, hex, 8)
}

/// Renders a constant as [`render_const`] does, reading it as a value of
/// the machine word: on a 32-bit target `0xffffffff` is `-1`.
///
/// A value that spells four characters reads as the code it spells
/// ([`fourcc_literal`]).
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - Render in hex (inside bitwise operators).
/// * `word` - The machine word in bytes.
pub(super) fn render_const_in(v: u64, hex: bool, word: i64) -> String {
    if !hex
        && v >= 256
        && let Some(code) = fourcc_literal(v)
    {
        return code;
    }
    render_number(v, hex, word)
}

/// Renders a constant as a number of the machine word, never as the
/// characters it might spell.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - Render in hex (inside bitwise operators).
/// * `word` - The machine word in bytes.
fn render_number(v: u64, hex: bool, word: i64) -> String {
    if hex && v >= 10 {
        return format!("{v:#x}");
    }
    if v < 256 {
        return v.to_string();
    }
    if !hex && let Some(m) = negative_magnitude(v, word) {
        return format!("-{m}");
    }
    format!("{v:#x}")
}

/// Renders a constant that spells four printable characters as the
/// multi-character literal the source wrote, `'AUEV'`.
///
/// Nebula3 registers every class and attribute under such a code and a
/// DDS header names its pixel format by one; the number is the code read
/// with its first character in the high byte, as MSVC evaluates the
/// literal, so `MAKEFOURCC('D','X','T','5')` reads `'5TXD'`. Four
/// printable bytes with at least three letters or digits among them are
/// taken as a code: a mask or a size nearly always has a byte below a
/// space or above a tilde.
///
/// # Arguments
///
/// * `v` - The constant.
///
/// # Returns
///
/// The literal, or `None` for a number.
pub(super) fn fourcc_literal(v: u64) -> Option<String> {
    let bytes = u32::try_from(v).ok()?.to_be_bytes();
    if !bytes.iter().all(|b| (0x20..0x7f).contains(b))
        || bytes.iter().filter(|b| b.is_ascii_alphanumeric()).count() < 3
    {
        return None;
    }
    let text: String = bytes
        .iter()
        .flat_map(|&b| match b {
            b'\\' => vec!['\\', '\\'],
            b'\'' => vec!['\\', '\''],
            _ => vec![char::from(b)],
        })
        .collect();
    Some(format!("'{text}'"))
}

/// Reads a constant as a negative number of the machine word.
///
/// A value with the sign bit of the word set whose magnitude fits in
/// thirty-two bits (sixteen on a 32-bit word, so `0x80000000` stays the
/// flag it usually is) is the negative number the source wrote.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `word` - The machine word in bytes.
///
/// # Returns
///
/// The magnitude, or `None` when the value reads better unsigned.
pub(super) fn negative_magnitude(v: u64, word: i64) -> Option<u64> {
    let wide = (v >= 1 << 63 && v.wrapping_neg() <= 0xffff_ffff).then(|| v.wrapping_neg());
    if word != 4 {
        return wide;
    }
    // INVARIANT: a 32-bit immediate arrives zero-extended when the decoder
    // read a 32-bit operand and sign-extended to 64 bits when it read an
    // 8-bit one; both spell the same number.
    if v > 0x7fff_ffff && v <= 0xffff_ffff {
        let m = (1u64 << 32) - v;
        return (m <= 0xffff).then_some(m);
    }
    wide.filter(|m| *m <= 0xffff)
}

impl Expr {
    /// Renders the expression as C text.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution for variables and globals.
    pub(super) fn render(&self, n: &Names<'_>) -> String {
        self.render_prec(n, false, false).0
    }

    /// Renders the expression with its outermost precedence.
    ///
    /// Operands are parenthesized when their precedence is lower, when they
    /// share the precedence of a non-commutative operator on the right, or
    /// when they belong to another operator family. `x + (-c)` renders as
    /// `x - c`.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `hex` - Render constants in hex (inside bitwise operators).
    /// * `address` - The expression is the address a load or store goes
    ///   through, or a term of its sum, where a constant may be the string
    ///   literal read from (`"0123456789abcdef"[i]`).
    ///
    /// # Returns
    ///
    /// `(text, precedence of the outermost operator)`.
    fn render_prec(&self, n: &Names<'_>, hex: bool, address: bool) -> (String, u8) {
        self.render_in(n, hex, address, true)
    }

    /// Renders the expression as [`Expr::render_prec`] does, knowing
    /// whether the bits above the low 32 of its value are read.
    ///
    /// The machine's arithmetic is 64 bits wide where C computes a narrow
    /// operand in `int` or `unsigned int`: `*(uint16_t*)p << 0x20` shifts
    /// the word out of an `int` where `shl rax, 0x20` keeps it. Where the
    /// upper bits are read and the text's shift or product would lose them
    /// ([`computes_narrow`]), its left operand is cast to `uint64_t`; under
    /// a mask to 32 bits or fewer they are not read, and the text stays as
    /// it is.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `hex` - Render constants in hex (inside bitwise operators).
    /// * `address` - The expression is an address or a term of its sum
    ///   ([`Expr::render_prec`]).
    /// * `wide` - The bits above the low 32 of the value are read.
    ///
    /// # Returns
    ///
    /// `(text, precedence of the outermost operator)`.
    fn render_in(&self, n: &Names<'_>, hex: bool, address: bool, wide: bool) -> (String, u8) {
        match self {
            Expr::Const(v) => (
                n.const_name(*v, true)
                    .unwrap_or_else(|| render_const_in(*v, hex, n.word)),
                ATOM,
            ),
            Expr::Var(k) => (n.key(*k), ATOM),
            Expr::Str(s) => (s.clone(), ATOM),
            Expr::Sp(k) => (format!("&{}", n.slot(*k)), UNARY),
            Expr::FConst(bits, ty) => (render_fconst(*bits, *ty), ATOM),
            Expr::Call(f, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| a.render_prec(n, true, false).0)
                    .collect();
                (format!("{f}({})", args.join(", ")), ATOM)
            }
            Expr::Cast(e, ty) => {
                let (es, ep) = match &**e {
                    Expr::Sext(inner, bits) => {
                        let (s, p) = inner.render_prec(n, false, false);
                        let s = if p < UNARY { format!("({s})") } else { s };
                        (format!("({}){s}", signed_ty(*bits)), UNARY)
                    }
                    other => other.render_prec(n, false, false),
                };
                let es = if ep < UNARY { format!("({es})") } else { es };
                (format!("({}){es}", cast_name(*ty)), UNARY)
            }
            Expr::Bin(op, l, r) => {
                if let Op::FMin | Op::FMax = op {
                    let name = if *op == Op::FMin { "fmin" } else { "fmax" };
                    return (format!("{name}({}, {})", l.render(n), r.render(n)), ATOM);
                }
                if let Op::Rol(w)
                | Op::Ror(w)
                | Op::MulHi(w)
                | Op::SMulHi(w)
                | Op::SMulO(w)
                | Op::UAddO(w)
                | Op::USubO(w) = op
                {
                    let name = match op {
                        Op::Rol(_) => "rotl",
                        Op::Ror(_) => "rotr",
                        Op::MulHi(_) => "mulhi",
                        Op::SMulHi(_) => "smulhi",
                        Op::UAddO(_) => "uaddo",
                        Op::USubO(_) => "usubo",
                        _ => "smulo",
                    };
                    return (
                        format!(
                            "{name}{w}({}, {})",
                            number(l, n, false).0,
                            number(r, n, false).0
                        ),
                        ATOM,
                    );
                }
                let p = op.prec();
                let hexo = hex || op.hex_operands();
                let sum = address && matches!(op, Op::Add | Op::Sub);
                // INVARIANT: the low bits of a sum, a difference, a product,
                // a left shift or a bitwise operation are read from the low
                // bits of its operands alone; a mask to 32 bits reads no more,
                // and any other operation reads them all.
                let inner = match (op, &**r) {
                    (Op::And, Expr::Const(m)) if *m <= 0xffff_ffff => false,
                    (Op::Add | Op::Sub | Op::Mul | Op::Shl | Op::And | Op::Or | Op::Xor, _) => wide,
                    _ => true,
                };
                let widen = wide && !address && n.word == 8 && computes_narrow(*op, l, r);
                let widened = |(s, sp): (String, u8)| {
                    if widen {
                        let s = if sp < UNARY { format!("({s})") } else { s };
                        (format!("(uint64_t){s}"), UNARY)
                    } else {
                        (s, sp)
                    }
                };
                if *op == Op::Add
                    && let Expr::Const(c) = **r
                    && let Some(m) = negative_magnitude(c, n.word)
                {
                    let (ls, lp) = widened(l.render_in(n, hexo, sum, inner));
                    let ls = if lp < p { format!("({ls})") } else { ls };
                    return (format!("{ls} - {m}"), p);
                }
                // INVARIANT: a constant a bitwise operator applies is a mask,
                // never an address, even when its value lands in the image
                // (`and edi, 0xff00ff` is not `edi & "some literal"`); one
                // any other operator applies is no string literal unless it
                // is a term of an address loaded through, or the first
                // character of a string a sum indexes (`i * 3 +
                // "SunMonTue"`).
                let indexes = |v: u64| matches!(op, Op::Add | Op::Sub) && n.starts_string(v);
                let operand = |e: &Expr| match e {
                    Expr::Const(v) if op.hex_operands() => {
                        (render_const_in(*v, true, n.word), ATOM)
                    }
                    Expr::Const(v) if !sum && !indexes(*v) => number(e, n, hexo),
                    _ => e.render_in(n, hexo, sum, inner),
                };
                let (ls, lp) = match (op, &**l) {
                    // INVARIANT: a logical shift shifts the constant's
                    // unsigned bits, which only its hex spelling has: `-1 >>
                    // n` shifts an `int` and keeps its sign.
                    (Op::Shr, Expr::Const(v)) if negative_magnitude(*v, n.word).is_some() => {
                        (render_const_in(*v, true, n.word), ATOM)
                    }
                    _ => widened(operand(l)),
                };
                let (rs, rp) = operand(r);
                let other_family = |e: &Expr| match e {
                    Expr::Bin(o, ..) => {
                        o.family() != op.family() || (*o != *op && op.family() == 2)
                    }
                    _ => false,
                };
                let ls = if lp < p || other_family(l) {
                    format!("({ls})")
                } else {
                    ls
                };
                let rs = if rp < p || (rp == p && !op.commutative()) || other_family(r) {
                    format!("({rs})")
                } else {
                    rs
                };
                match op {
                    Op::SDiv | Op::SRem => {
                        // INVARIANT: a narrow signed quotient converts back
                        // to 64 bits by sign extension, so dividing the
                        // narrow value is dividing its extension.
                        let signed = |side: &Expr, text: String| {
                            if let Expr::Sext(inner, from) = side {
                                let (s, p) = inner.render_prec(n, hex, false);
                                let s = if p < UNARY { format!("({s})") } else { s };
                                format!("({}){s}", signed_ty(*from))
                            } else if text.starts_with("(int64_t)")
                                || matches!(side, Expr::Const(_))
                            {
                                text
                            } else {
                                format!("(int64_t){text}")
                            }
                        };
                        let rs = match **r {
                            Expr::Const(c) => c.to_string(),
                            _ => rs,
                        };
                        (
                            format!("{} {} {}", signed(l, ls), op.sym(), signed(r, rs)),
                            p,
                        )
                    }
                    Op::Div | Op::Rem if matches!(**r, Expr::Const(_)) => {
                        let rs = match **r {
                            Expr::Const(c) => c.to_string(),
                            _ => rs,
                        };
                        (format!("{ls} {} {rs}", op.sym()), p)
                    }
                    Op::And if low_clear(r).is_some() => {
                        let cleared = low_clear(r).map_or(0, |c| c);
                        (format!("{ls} & ~{}", render_const(cleared, true)), p)
                    }
                    Op::Sar => {
                        let ls = if ls.starts_with("(int64_t)") {
                            ls
                        } else {
                            format!("(int64_t){ls}")
                        };
                        (format!("{ls} >> {rs}"), p)
                    }
                    _ => (format!("{ls} {} {rs}", op.sym()), p),
                }
            }
            Expr::Un(op, e) => match op.func_name() {
                Some(f) => (format!("{f}({})", e.render(n)), ATOM),
                None => {
                    let (es, ep) = number(e, n, hex);
                    let es = if ep < UNARY { format!("({es})") } else { es };
                    let sym = if *op == UnOp::Neg { "-" } else { "~" };
                    (format!("{sym}{es}"), UNARY)
                }
            },
            Expr::Deref(a, ty) => {
                if let Expr::Sp(k) = **a {
                    return n.slot_at(k, *ty);
                }
                if let Some(field) = teb_field(a, n.word) {
                    return (format!("NtCurrentTeb()->{field}"), ATOM);
                }
                render_load(a, *ty, ty.name(), n)
            }
            Expr::Cond(c) => match &c.flags {
                Flags::Truth(e, tcc) if c.cc == *tcc => e.render_prec(n, hex, false),
                Flags::Truth(e, tcc) if c.cc == tcc.invert() && equality(e).is_none() => {
                    (c.render(n, false), UNARY)
                }
                _ => (c.render(n, false), 6),
            },
            Expr::Ternary(c, a, b) => (
                format!(
                    "({} ? {} : {})",
                    c.render(n, false),
                    a.render(n),
                    b.render(n)
                ),
                ATOM,
            ),
            Expr::Sext(e, bits) => {
                if let Expr::Deref(a, ty) = e.as_ref()
                    && matches!(ty, Ty::U8 | Ty::U16 | Ty::U32)
                    && ty.bits() == *bits
                    && !matches!(**a, Expr::Sp(_))
                {
                    return render_load(a, *ty, signed_ty(*bits), n);
                }
                let (es, ep) = e.render_prec(n, false, false);
                let es = if ep < UNARY { format!("({es})") } else { es };
                (format!("(int64_t)({}){es}", signed_ty(*bits)), UNARY)
            }
        }
    }
}

/// Returns the condition a truth value is when it is an equality test,
/// whose negation is the inequality, NaN operands included: `!(a == b)` is
/// `a != b`, where `!(a < b)` is not `a >= b` for floats.
///
/// # Arguments
///
/// * `e` - The truth value.
fn equality(e: &Expr) -> Option<&Cond> {
    match e {
        Expr::Cond(c) if matches!(c.cc.0, ConditionCode::e | ConditionCode::ne) => Some(c),
        _ => None,
    }
}

/// Renders a sign test of a value at a width: `(int32_t)x < 0`.
///
/// The value is parenthesized only when its own operator binds looser than
/// the cast, so a variable or a load reads bare.
///
/// # Arguments
///
/// * `n` - Names for the rendering.
/// * `bits` - The width the sign is read at.
/// * `e` - The value.
/// * `rel` - The relation to zero: `<`, `>=`, `<=` or `>`.
fn signed_sign(n: &Names<'_>, bits: u8, e: &Expr, rel: &str) -> String {
    let (s, p) = number(e, n, false);
    let s = if p < UNARY { format!("({s})") } else { s };
    format!("({}){s} {rel} 0", signed_ty(bits))
}

impl Cond {
    /// Renders the condition as a C boolean expression.
    ///
    /// Flags set in another block or by an unmodeled instruction render as
    /// the obviously symbolic `FLAGS_UNKNOWN`, never as a fake constant. A
    /// `test` can never set CF, so `b`/`ae` after it are the constants `0`
    /// and `1` with a comment.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `inverted` - Render the negated condition.
    pub(super) fn render(&self, n: &Names<'_>, inverted: bool) -> String {
        let text = self.render_plain(n, inverted);
        if self.eval().is_none()
            && let Some(outcome) = super::opaque::constant_outcome(self)
        {
            return format!("{text} {}", opaque_note(outcome, inverted));
        }
        text
    }

    /// Renders the condition without judging whether its outcome can vary.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `inverted` - Render the negated condition.
    fn render_plain(&self, n: &Names<'_>, inverted: bool) -> String {
        if let Some(s) = self.simplify() {
            return s.render(n, inverted);
        }
        let cc = if inverted { self.cc.invert() } else { self.cc };
        use ConditionCode as C;
        if let Some(inner) = self.bool_operand() {
            match cc.0 {
                C::e => return inner.render(n, true),
                C::ne => return inner.render(n, false),
                _ => {}
            }
        }
        match &self.flags {
            Flags::Unknown => {
                if inverted {
                    "!FLAGS_UNKNOWN".to_owned()
                } else {
                    "FLAGS_UNKNOWN".to_owned()
                }
            }
            Flags::Carry(e) => match cc.0 {
                C::b | C::o => format!("{} != 0", paren_if_lower(e, n, 6)),
                C::ae | C::no => format!("{} == 0", paren_if_lower(e, n, 6)),
                _ => undecided(n, self.cc, inverted, &[e]),
            },
            Flags::Shift(e, bits, c) => {
                let flags = match cc.0 {
                    C::be | C::a => {
                        let (bit, zero, join) = if cc.0 == C::be {
                            ("!=", "==", "||")
                        } else {
                            ("==", "!=", "&&")
                        };
                        return format!(
                            "({} {bit} 0 {join} {} {zero} 0)",
                            paren_if_lower(c, n, 6),
                            paren_if_lower(e, n, 6)
                        );
                    }
                    C::b | C::ae => Flags::Carry(c.clone()),
                    // The overflow of a shift is not its carry: `shl x, 1`
                    // sets it to the top bit of the result against CF, and
                    // a longer shift leaves it undefined.
                    C::o | C::no => return undecided(n, self.cc, inverted, &[e, c]),
                    _ => Flags::Result(e.clone(), *bits),
                };
                Cond { cc: self.cc, flags }.render(n, inverted)
            }
            Flags::Truth(e, tcc) if cc == *tcc => e.render(n),
            Flags::Truth(e, tcc) if cc == tcc.invert() => match equality(e) {
                Some(inner) => inner.render(n, true),
                None => format!("!{}", paren_if_lower(e, n, UNARY)),
            },
            Flags::Truth(e, _) => undecided(n, self.cc, inverted, &[e]),
            Flags::Cmp(l, r, bits) if matches!(cc.0, C::p | C::np) => {
                let unordered = l.is_float()
                    || r.is_float()
                    || super::line::float_like(&l.render(n))
                    || super::line::float_like(&r.render(n));
                let not = if cc.0 == C::np { "!" } else { "" };
                if unordered {
                    format!("{not}isunordered({}, {})", l.render(n), r.render(n))
                } else {
                    parity(n, cc, &fold(Op::Sub, l.clone(), r.clone(), *bits))
                }
            }
            Flags::Cmp(l, r, _)
                if (l.is_float() || r.is_float())
                    && matches!(cc.0, C::a | C::ae | C::b | C::be) =>
            {
                float_relation(n, cc, l, r)
            }
            Flags::Cmp(l, r, bits) if matches!(cc.0, C::s | C::ns) => signed_sign(
                n,
                *bits,
                &fold(Op::Sub, l.clone(), r.clone(), *bits),
                if cc.0 == C::s { "<" } else { ">=" },
            ),
            Flags::Cmp(l, r, bits) => match cc.rel() {
                Some(rel @ ("==" | "!=")) => match vector_equality(l, r) {
                    Some((a, b)) => compare(
                        n,
                        &packed_literal(n, a).unwrap_or_else(|| a.clone()),
                        &packed_literal(n, b).unwrap_or_else(|| b.clone()),
                        rel,
                        false,
                        128,
                    ),
                    None => compare(n, l, r, rel, cc.signed(), *bits),
                },
                Some(rel) => compare(n, l, r, rel, cc.signed(), *bits),
                None => match cc.0 {
                    C::o => format!(
                        "ssubo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::no => format!(
                        "ssubo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    _ => undecided(n, self.cc, inverted, &[l, r]),
                },
            },
            Flags::Add(l, r, bits) => {
                let sum = fold(Op::Add, l.clone(), r.clone(), *bits);
                match cc.0 {
                    C::e => format!("{} == 0", paren_if_lower(&sum, n, 6)),
                    C::ne => format!("{} != 0", paren_if_lower(&sum, n, 6)),
                    C::s => signed_sign(n, *bits, &sum, "<"),
                    C::ns => signed_sign(n, *bits, &sum, ">="),
                    C::l => sum_relation(n, l, r, *bits, "<"),
                    C::ge => sum_relation(n, l, r, *bits, ">="),
                    C::le => sum_relation(n, l, r, *bits, "<="),
                    C::g => sum_relation(n, l, r, *bits, ">"),
                    C::b => format!(
                        "uaddo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::ae => format!(
                        "uaddo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::o => format!(
                        "saddo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::no => format!(
                        "saddo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::be => format!(
                        "(uaddo{bits}({}, {}) != 0 || {} == 0)",
                        number(l, n, false).0,
                        number(r, n, false).0,
                        paren_if_lower(&sum, n, 6)
                    ),
                    C::a => format!(
                        "(uaddo{bits}({}, {}) == 0 && {} != 0)",
                        number(l, n, false).0,
                        number(r, n, false).0,
                        paren_if_lower(&sum, n, 6)
                    ),
                    C::p | C::np => parity(n, cc, &sum),
                    C::None => undecided(n, self.cc, inverted, &[l, r]),
                }
            }
            Flags::Test(l, r, bits) => {
                let single = l == r;
                let and = if single {
                    l.clone()
                } else {
                    fold(Op::And, l.clone(), r.clone(), *bits)
                };
                match cc.0 {
                    C::e | C::ne => format!(
                        "{} {} 0",
                        paren_if_lower(&and, n, 6),
                        if cc.0 == C::e { "==" } else { "!=" }
                    ),
                    C::s | C::l => signed_sign(n, *bits, &and, "<"),
                    C::ns | C::ge => signed_sign(n, *bits, &and, ">="),
                    C::le => signed_sign(n, *bits, &and, "<="),
                    C::g => signed_sign(n, *bits, &and, ">"),
                    C::b => "0 /*CF=0 after test*/".to_owned(),
                    C::ae => "1 /*CF=0 after test*/".to_owned(),
                    C::o => "0 /*OF=0 after test*/".to_owned(),
                    C::no => "1 /*OF=0 after test*/".to_owned(),
                    C::be => format!("{} == 0", paren_if_lower(&and, n, 6)),
                    C::a => format!("{} != 0", paren_if_lower(&and, n, 6)),
                    C::p | C::np => parity(n, cc, &and),
                    C::None => undecided(n, self.cc, inverted, &[l, r]),
                }
            }
            Flags::Result(e, bits) => match cc.0 {
                C::e => format!("{} == 0", paren_if_lower(e, n, 6)),
                C::ne => format!("{} != 0", paren_if_lower(e, n, 6)),
                C::s | C::l => signed_sign(n, *bits, e, "<"),
                C::ns | C::ge => signed_sign(n, *bits, e, ">="),
                C::le => signed_sign(n, *bits, e, "<="),
                C::g => signed_sign(n, *bits, e, ">"),
                C::p | C::np => parity(n, cc, e),
                C::b | C::ae | C::be | C::a | C::None | C::o | C::no => {
                    undecided(n, self.cc, inverted, &[e])
                }
            },
        }
    }
}

/// Renders a condition the recorded flags cannot decide as the opaque test
/// `flags_b(x)`: condition code `b` of the flags an operation on `x` left.
///
/// The carry an arithmetic result leaves depends on the operation, which
/// [`Flags::Result`] does not keep, and so on for the other undecided
/// shapes. Spelled as a call the condition is still C, and negated it is
/// the same call under `!`, so a condition and its inversion stay each
/// other's negation; a bare value with a comment would read as the value's
/// truth both ways.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - The condition code as recorded, before any inversion.
/// * `inverted` - Render the negation.
/// * `operands` - What the flags were computed from.
fn undecided(n: &Names<'_>, cc: Cc, inverted: bool, operands: &[&Expr]) -> String {
    let args: Vec<String> = operands.iter().map(|e| number(e, n, false).0).collect();
    let not = if inverted { "!" } else { "" };
    format!("{not}flags_{:?}({})", cc.0, args.join(", "))
}

/// Renders the parity flag of a value: `p` holds when the low byte has an
/// even number of set bits, `parity8(x)`, and `np` is its negation.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - `p` or `np`.
/// * `e` - The value the flags were set from.
fn parity(n: &Names<'_>, cc: Cc, e: &Expr) -> String {
    let not = if cc.0 == ConditionCode::np { "!" } else { "" };
    format!("{not}parity8({})", e.render(n))
}

/// Renders `e`, parenthesized when its precedence is below `prec`.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `n` - Name resolution.
/// * `prec` - Precedence of the operator `e` becomes an operand of.
fn paren_if_lower(e: &Expr, n: &Names<'_>, prec: u8) -> String {
    let (s, p) = e.render_prec(n, false, false);
    if p < prec { format!("({s})") } else { s }
}

/// Renders an operand of arithmetic.
///
/// A constant there is a number, a bound or a multiplier: it may still
/// name the function, symbol or variable at its value (a pointer to a
/// table's end), but not the string literal that happens to sit there, nor
/// the characters its bytes happen to spell. In a 32-bit image every
/// constant from the image base up lands somewhere in it, and `imul eax,
/// 0x1010101` is not `a2 * "void) const"`; the magic multiplier of a
/// division by three is `0x55555556`, not `'UUUV'`.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `n` - Name resolution.
/// * `hex` - Render a constant in hex.
///
/// # Returns
///
/// `(text, precedence of the outermost operator)`.
fn number(e: &Expr, n: &Names<'_>, hex: bool) -> (String, u8) {
    match e {
        Expr::Const(v) => (
            n.const_name(*v, false)
                .unwrap_or_else(|| render_number(*v, hex, n.word)),
            ATOM,
        ),
        _ => e.render_prec(n, hex, false),
    }
}

/// Renders an operand of a comparison, parenthesized when its precedence
/// is below `prec`.
///
/// A constant there is a bound or a tag the value is tested against: it
/// reads as the code it spells (`id == 'MESH'`, a switch over tags lowered
/// to `id > '3TXD'`), but as for [`number`] never as a string literal.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `n` - Name resolution.
/// * `prec` - Precedence of the operator `e` becomes an operand of.
fn paren_compared(e: &Expr, n: &Names<'_>, prec: u8) -> String {
    let (s, p) = match e {
        Expr::Const(v) => (
            n.const_name(*v, false)
                .unwrap_or_else(|| render_const_in(*v, false, n.word)),
            ATOM,
        ),
        _ => e.render_prec(n, false, false),
    };
    if p < prec { format!("({s})") } else { s }
}

/// Names a read through the thread environment block's segment.
///
/// `fs:[K]` on a 32-bit target and `gs:[K]` on a 64-bit one address the
/// current thread's TEB, and the fields a program reads there are a
/// short, fixed list: the exception chain, the stack bounds, the TEB's
/// own address, the process and thread ids, the thread-local storage
/// pointer, the PEB and the last error.
///
/// # Arguments
///
/// * `addr` - The address expression: the segment register, alone or
///   plus a constant.
/// * `word` - Machine word in bytes, which decides the layout.
///
/// # Returns
///
/// The field's name, or `None` when the read is not through the segment
/// or lands on no known field.
fn teb_field(addr: &Expr, word: i64) -> Option<&'static str> {
    let (seg, off) = match addr {
        Expr::Var(Key::Reg(r)) => (*r, 0),
        Expr::Bin(Op::Add, a, b) => match (&**a, &**b) {
            (Expr::Var(Key::Reg(r)), Expr::Const(k)) | (Expr::Const(k), Expr::Var(Key::Reg(r))) => {
                (*r, *k)
            }
            _ => return None,
        },
        _ => return None,
    };
    let wide = match (seg, word) {
        (Register::FS, 4) => false,
        (Register::GS, 8) => true,
        _ => return None,
    };
    TEB_FIELDS
        .iter()
        .find(|&&(_, at32, at64)| off == if wide { at64 } else { at32 })
        .map(|&(name, ..)| name)
}

/// The thread block fields the text names, with their offsets.
///
/// Each one's offset in a 32-bit block and in a 64-bit one: the exception
/// chain, the stack bounds, the block's own address, the process and
/// thread ids, the thread-local storage pointer, the PEB and the last
/// error. Every one is a machine word but `LastErrorValue`, 32 bits.
pub(super) const TEB_FIELDS: [(&str, u64, u64); 9] = [
    ("NtTib.ExceptionList", 0x00, 0x00),
    ("NtTib.StackBase", 0x04, 0x08),
    ("NtTib.StackLimit", 0x08, 0x10),
    ("NtTib.Self", 0x18, 0x30),
    ("ClientId.UniqueProcess", 0x20, 0x40),
    ("ClientId.UniqueThread", 0x24, 0x48),
    ("ThreadLocalStoragePointer", 0x2c, 0x58),
    ("ProcessEnvironmentBlock", 0x30, 0x60),
    ("LastErrorValue", 0x34, 0x68),
];

/// The C type a text expression computes in where it is narrower than the
/// machine's 64 bits ([`c_narrow`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Narrow {
    /// `int`: a promoted byte or word, a constant up to `INT_MAX`, a truth
    /// value.
    Int,
    /// `unsigned int`: a 32-bit load, a constant past `INT_MAX` that fits
    /// 32 bits.
    UInt,
}

/// The type C computes two operands in, by the usual conversions: `None`
/// when either is 64 bits wide.
///
/// # Arguments
///
/// * `a` - One operand's type.
/// * `b` - The other's.
fn converted(a: Option<Narrow>, b: Option<Narrow>) -> Option<Narrow> {
    match (a?, b?) {
        (Narrow::Int, Narrow::Int) => Some(Narrow::Int),
        _ => Some(Narrow::UInt),
    }
}

/// The narrow C type the text of an expression computes in.
///
/// `None` when it is 64 bits wide or its type is not known (a variable, a
/// call). A `uint8_t` or `uint16_t` load promotes to `int` and a `uint32_t` one
/// is `unsigned int`; a constant is the type its literal is (a negative one
/// renders as `-m`, an `int`, except in a bitwise operation, which spells
/// it in hex); an operation that would lose bits is widened when it renders
/// ([`computes_narrow`]), so it is 64 bits wide.
///
/// # Arguments
///
/// * `e` - The expression.
fn c_narrow(e: &Expr) -> Option<Narrow> {
    let hexed = |e: &Expr| match e {
        Expr::Const(v) if *v > 0xffff_ffff => None,
        other => c_narrow(other),
    };
    match e {
        Expr::Const(v) => match *v {
            0..=0x7fff_ffff => Some(Narrow::Int),
            0x8000_0000..=0xffff_ffff => Some(Narrow::UInt),
            v => negative_magnitude(v, 8).map(|_| Narrow::Int),
        },
        Expr::Deref(_, Ty::U8 | Ty::U16) | Expr::Cond(_) => Some(Narrow::Int),
        Expr::Deref(_, Ty::U32) => Some(Narrow::UInt),
        Expr::Un(UnOp::Neg | UnOp::Not, x) => c_narrow(x),
        Expr::Bin(op @ (Op::Shl | Op::Mul), l, r) => {
            if computes_narrow(*op, l, r) {
                None
            } else if *op == Op::Shl {
                c_narrow(l)
            } else {
                converted(c_narrow(l), c_narrow(r))
            }
        }
        Expr::Bin(Op::Add | Op::Sub, l, r) => converted(c_narrow(l), c_narrow(r)),
        Expr::Bin(Op::Shr, l, _) => c_narrow(l),
        Expr::Bin(Op::Div | Op::Rem, l, r) => converted(c_narrow(l), c_narrow(r)),
        Expr::Bin(Op::And | Op::Or | Op::Xor, l, r) => converted(hexed(l), hexed(r)),
        Expr::Ternary(_, a, b) => converted(c_narrow(a), c_narrow(b)),
        _ => None,
    }
}

/// The most bits the machine's value of an expression occupies: a load its
/// width, a constant its length, a product the sum of its operands'.
///
/// # Arguments
///
/// * `e` - The expression.
fn value_bits(e: &Expr) -> u64 {
    match e {
        Expr::Const(v) => u64::from(64 - v.leading_zeros()),
        Expr::Deref(_, ty) => u64::from(ty.bits()).min(64),
        Expr::Cond(_) => 1,
        Expr::Bin(op, l, r) => {
            let (a, b) = (value_bits(l), value_bits(r));
            match (op, &**r) {
                (Op::And, _) => a.min(b),
                (Op::Or | Op::Xor, _) => a.max(b),
                (Op::Add, _) => (a.max(b) + 1).min(64),
                (Op::Mul, _) => (a + b).min(64),
                (Op::Shl, Expr::Const(c)) => a.saturating_add(*c).min(64),
                (Op::Shr, Expr::Const(c)) => a.saturating_sub(*c),
                (Op::Shr | Op::Div | Op::Rem, _) => a,
                _ => 64,
            }
        }
        Expr::Ternary(_, a, b) => value_bits(a).max(value_bits(b)),
        _ => 64,
    }
}

/// Tells whether C computes a 64-bit left shift or product of the machine
/// narrower than it is, so that its text loses bits the machine keeps.
///
/// In `int` a result loses bits past 31, in `unsigned int` past 32. A sum
/// or a difference is left as it is: the lifter keeps a 32-bit one unmasked
/// where nothing reads its upper half, and C's narrow sum is then the
/// machine's.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - The left operand: the value shifted, for a shift.
/// * `r` - The right operand.
fn computes_narrow(op: Op, l: &Expr, r: &Expr) -> bool {
    let (ty, bits) = match (op, r) {
        (Op::Shl, Expr::Const(c)) => (c_narrow(l), value_bits(l).saturating_add(*c)),
        (Op::Shl, _) => (c_narrow(l), 64),
        (Op::Mul, _) => (
            converted(c_narrow(l), c_narrow(r)),
            value_bits(l) + value_bits(r),
        ),
        _ => return false,
    };
    match ty {
        None => false,
        Some(Narrow::Int) => bits > 31,
        Some(Narrow::UInt) => bits > 32,
    }
}

/// Renders a load of `ty` at `a` as `*(name*)a`, or as the array element
/// `((name*)base)[index]` when the address is one ([`indexed`]).
///
/// # Arguments
///
/// * `a` - The address.
/// * `ty` - The access type, for its width.
/// * `name` - The type name to print, signed or unsigned.
/// * `n` - Name resolution.
fn render_load(a: &Expr, ty: Ty, name: &str, n: &Names<'_>) -> (String, u8) {
    if let Some((base, index)) = indexed(a, ty) {
        let (bs, bp) = base.render_prec(n, true, true);
        let bs = if bp < UNARY { format!("({bs})") } else { bs };
        let is = match &index {
            Expr::Ternary(c, x, y) => {
                format!("{} ? {} : {}", c.render(n, false), x.render(n), y.render(n))
            }
            other => other.render(n),
        };
        return (format!("(({name}*){bs})[{is}]"), ATOM);
    }
    let (as_, ap) = a.render_prec(n, true, true);
    let as_ = if ap < UNARY { format!("({as_})") } else { as_ };
    (format!("*({name}*){as_}"), UNARY)
}

/// Renders a comparison, casting both sides to the signed type when the
/// condition is signed.
///
/// A cast binds tighter than any binary operator, so non-atomic operands
/// are parenthesized; an operand already carrying an `(int64_t)` cast
/// takes no second one. An unsigned ordering of a sign-extended value
/// casts it to the unsigned type of the compared width: `ja` after `movsxd
/// rbx, ecx; cmp ebx, 0x40f` finds `-1` above `0x40f`, which C's signed
/// `(int64_t)(int32_t)a1 <= 0x40f` does not. So does an ordering of a
/// difference C computes in `int` ([`int_difference`]), and a compare
/// narrower than the machine's word of an operand that may be wider: `cmp
/// edx, eax` compares the low halves of two 64-bit variables.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `rel` - The relational operator text.
/// * `signed` - The compare is signed.
/// * `bits` - Operand width, selecting the signed type.
fn compare(n: &Names<'_>, l: &Expr, r: &Expr, rel: &str, signed: bool, bits: u8) -> String {
    let cast = |e: &Expr| -> String {
        if signed && !matches!(e, Expr::Const(c) if *c < 1 << 31) {
            let text = paren_compared(e, n, UNARY);
            if bits == 64 && text.starts_with("(int64_t)") {
                text
            } else {
                format!("({}){text}", signed_ty(bits))
            }
        } else if (!signed
            && !matches!(rel, "==" | "!=")
            && (matches!(e, Expr::Sext(..)) || int_difference(e)))
            || (i64::from(bits) < n.word * 8 && value_bits(e) > u64::from(bits))
        {
            format!(
                "({}){}",
                Ty::from_bits(bits).name(),
                paren_compared(e, n, UNARY)
            )
        } else {
            paren_compared(e, n, 7)
        }
    };
    format!("{} {rel} {}", cast(l), cast(r))
}

/// Tells whether an expression is a difference C computes in `int`, which
/// goes below zero where the machine's unsigned value wraps:
/// `*(uint8_t*)p - 12` of a byte below 12.
///
/// # Arguments
///
/// * `e` - The expression.
fn int_difference(e: &Expr) -> bool {
    let differs = match e {
        Expr::Bin(Op::Sub, ..) | Expr::Un(UnOp::Neg | UnOp::Not, _) => true,
        Expr::Bin(Op::Add, _, r) => {
            matches!(**r, Expr::Const(c) if negative_magnitude(c, 8).is_some() || negative_magnitude(c, 4).is_some())
        }
        _ => false,
    };
    differs && (c_narrow(e) == Some(Narrow::Int) || widened_difference(e))
}

/// Tells whether a difference widens a value a 32-bit write zero-extended.
///
/// Its left side casts one to 64 bits, so below the subtrahend it goes
/// negative the same way an `int` difference does, where the machine's
/// zero-extended value wraps.
///
/// # Arguments
///
/// * `e` - The difference.
fn widened_difference(e: &Expr) -> bool {
    let Expr::Bin(Op::Sub | Op::Add, l, _) = e else {
        return false;
    };
    matches!(&**l, Expr::Cast(inner, ty) if ty.bits() == 64 && c_narrow(inner).is_some())
}

/// Renders an ordered floating-point comparison exactly, NaN included.
///
/// `comiss`/`ucomiss` and `fcomi` set ZF, PF and CF all three on an
/// unordered outcome, so `ja` and `jae` hold on ordered operands only, as
/// C's `>` and `>=` do, while `jb` and `jbe` also hold on a NaN: they are
/// `!(a >= b)` and `!(a > b)`, never `a < b` and `a <= b`. When neither
/// operand's text shows it is a float ([`super::line::float_like`]), the
/// C99 comparison macros spell it instead, so a text pass that negates a
/// condition can always tell a float comparison from an integer one.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - `a`, `ae`, `b` or `be`.
/// * `l` - Left operand.
/// * `r` - Right operand.
fn float_relation(n: &Names<'_>, cc: Cc, l: &Expr, r: &Expr) -> String {
    use ConditionCode as C;
    let (rel, call, negated) = match cc.0 {
        C::a => (">", "isgreater", false),
        C::ae => (">=", "isgreaterequal", false),
        C::b => (">=", "isgreaterequal", true),
        _ => (">", "isgreater", true),
    };
    let (ls, rs) = (paren_if_lower(l, n, 7), paren_if_lower(r, n, 7));
    let not = if negated { "!" } else { "" };
    if super::line::float_like(&ls) || super::line::float_like(&rs) {
        let relation = format!("{ls} {rel} {rs}");
        return if negated {
            format!("!({relation})")
        } else {
            relation
        };
    }
    format!("{not}{call}({}, {})", l.render(n), r.render(n))
}

/// Renders the signed relation to zero of a sum taken without wrapping.
///
/// After `add`, `jl` tests SF != OF, which is the true sum being negative
/// even where the machine sum overflowed, and `jle`, `jge` and `jg` alike.
/// A constant addend `c` moves across: `x + c < 0` is `x < -c`, exact when
/// `-c` fits the width, and `x + x` relates to zero as `x` does. Otherwise
/// the sign is the machine sum's unless the signed sum overflowed, when it
/// is either addend's (both have it, and the true sum is never zero then):
/// `(saddo32(x, y) ? (int32_t)x : (int32_t)(x + y)) < 0`, which needs no
/// wider type and no cast a parameter's declared type would drop.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `l` - One addend.
/// * `r` - The other.
/// * `bits` - The width of the addition.
/// * `rel` - `<`, `>=`, `<=` or `>`.
fn sum_relation(n: &Names<'_>, l: &Expr, r: &Expr, bits: u8, rel: &str) -> String {
    let m = mask_bits(bits);
    let min = 1u64 << (bits.clamp(1, 64) - 1);
    let moved = match (l, r) {
        (x, Expr::Const(c)) | (Expr::Const(c), x) if c & m != min => Some((x, c)),
        _ => None,
    };
    if let Some((x, c)) = moved {
        let negated = Expr::Const(sext(c.wrapping_neg() & m, bits));
        return compare(n, x, &negated, rel, true, bits);
    }
    // `x + x` (`shl x, 1`) has the sign of `x` and is zero with it.
    if l == r {
        return compare(n, l, &Expr::Const(0), rel, true, bits);
    }
    let ty = signed_ty(bits);
    let sum = fold(Op::Add, l.clone(), r.clone(), bits);
    format!(
        "(saddo{bits}({}, {}) ? ({ty}){} : ({ty}){}) {rel} 0",
        number(l, n, false).0,
        number(r, n, false).0,
        paren_if_lower(l, n, UNARY),
        paren_if_lower(&sum, n, UNARY)
    )
}

/// Reads a whole-vector global as the text it holds, when that is text.
///
/// A 16-byte compare against a global is how a compiler inlines a fixed
/// string comparison, and the global is the string. Rendered as `g128_...`
/// the reader is told an address and has to look it up; rendered as the
/// literal, the comparison says what it tests.
///
/// # Arguments
///
/// * `n` - Name resolution, which carries the loaded image.
/// * `e` - The compared operand.
///
/// # Returns
///
/// The quoted literal, or `None` unless `e` is a 16-byte read of a global
/// whose bytes are all printable text. Widths are held in a `u8`, so 128
/// bits is the widest a global read can name.
fn packed_literal(n: &Names<'_>, e: &Expr) -> Option<Expr> {
    let Expr::Var(Key::Global(addr, bits)) = e else {
        return None;
    };
    if *bits != 128 {
        return None;
    }
    let len = usize::from(*bits) / 8;
    let raw = n.program.read_va(*addr, len)?;
    if !raw.iter().all(|&b| crate::strings::printable(b)) {
        return None;
    }
    let text = String::from_utf8(raw.to_vec()).ok()?;
    Some(Expr::Str(format!(
        "\"{}\"",
        text.replace('\\', "\\\\").replace('"', "\\\"")
    )))
}

/// Reads the two vectors an all-lanes-equal test compares, if that is the test.
///
/// `pcmpeqb` fills each byte lane with ones where its operands agree and
/// `pmovmskb` gathers the lanes' top bits, so testing the mask against all
/// ones asks whether every lane matched, which is the two vectors being
/// equal. Left as written it reads as bit arithmetic against an unexplained
/// constant, and the literal being compared against hides inside a `g128_`
/// global.
///
/// # Arguments
///
/// * `l` - The compared value, expected to be the gathered mask.
/// * `r` - The constant it is compared against, all ones over the lanes.
///
/// # Returns
///
/// The two compared vectors, or `None` when this is some other comparison.
fn vector_equality<'a>(l: &'a Expr, r: &Expr) -> Option<(&'a Expr, &'a Expr)> {
    let Expr::Call(gather, gathered) = l else {
        return None;
    };
    if !matches!(gather.as_str(), "pmovmskb" | "vpmovmskb") {
        return None;
    }
    let Some(Expr::Call(lanes, args)) = gathered.first() else {
        return None;
    };
    if !matches!(lanes.as_str(), "pcmpeqb" | "vpcmpeqb") || args.len() != 2 {
        return None;
    }
    // One mask bit per byte lane: 16 for an xmm gather, 32 for a ymm one.
    if !matches!(r, Expr::Const(0xffff | 0xffff_ffff)) {
        return None;
    }
    Some((args.first()?, args.get(1)?))
}

/// Shortens the literals asserts and logs carry, keeping what they say.
///
/// A signature string is the compiler's `__FUNCSIG__`: it renders as that
/// macro when it names the function being rendered and as
/// `__FUNCSIG__(Qualified::Name)` when it names another (an inlined helper's
/// assert). A source path (a separator-bearing, space-free literal ending in
/// a C or C++ file extension) keeps its last two components. Anything else
/// is returned as is.
///
/// # Arguments
///
/// * `quoted` - The literal as rendered, quotes and escapes included.
/// * `own_name` - The bare name of the function being rendered.
pub(super) fn compact_literal(quoted: &str, own_name: &str) -> String {
    const EXTENSIONS: [&str; 10] = [
        ".h", ".hpp", ".hh", ".hxx", ".inl", ".c", ".cc", ".cpp", ".cxx", ".inc",
    ];
    let Some(inner) = quoted.strip_prefix('"').and_then(|q| q.strip_suffix('"')) else {
        return quoted.to_owned();
    };
    if let Some(sig) = crate::analysis::naming::parse_signature(inner) {
        return if sig.name == own_name {
            "__FUNCSIG__".to_owned()
        } else {
            format!("__FUNCSIG__({})", sig.name)
        };
    }
    let path_like = !inner.contains(' ')
        && inner.contains(['/', '\\'])
        && EXTENSIONS.iter().any(|e| inner.ends_with(e));
    if path_like {
        let parts: Vec<&str> = inner.split(['/', '\\']).filter(|p| !p.is_empty()).collect();
        if parts.len() > 2 {
            let n = parts.len();
            return format!("\"{}/{}\"", parts[n - 2], parts[n - 1]);
        }
    }
    quoted.to_owned()
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
        let scan = Expr::Un(super::UnOp::Bsr, Box::new(x.clone()));
        let want = Expr::Un(super::UnOp::Lzcnt, Box::new(x));
        // bsr(x) ^ 63 and 63 ^ bsr(x), at 64 bits
        assert_eq!(
            super::fold(Op::Xor, scan.clone(), Expr::Const(63), 64),
            want
        );
        assert_eq!(
            super::fold(Op::Xor, Expr::Const(63), scan.clone(), 64),
            want
        );
        // 63 - bsr(x)
        assert_eq!(
            super::fold(Op::Sub, Expr::Const(63), scan.clone(), 64),
            want
        );
        // the 32-bit form uses 31
        assert_eq!(
            super::fold(Op::Xor, scan.clone(), Expr::Const(31), 32),
            want
        );
        // a constant that is not the width is left alone
        assert_ne!(super::fold(Op::Xor, scan.clone(), Expr::Const(7), 64), want);
        // and so is the wrong width for the constant
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
        let y = Expr::Var(Key::Reg(crate::isa::Register::RCX));
        let bin =
            |o: Op, a: &Expr, b: &Expr| Expr::Bin(o, Box::new(a.clone()), Box::new(b.clone()));
        let plain = bin(Op::Add, &x, &y);
        // (x ^ y) + 2 * (x & y)
        let doubled = bin(Op::Mul, &bin(Op::And, &x, &y), &Expr::Const(2));
        assert_eq!(
            super::fold(Op::Add, bin(Op::Xor, &x, &y), doubled, 64),
            plain
        );
        // (x ^ y) + ((x & y) << 1), the same form written as a shift
        let shifted = bin(Op::Shl, &bin(Op::And, &x, &y), &Expr::Const(1));
        assert_eq!(
            super::fold(Op::Add, bin(Op::Xor, &x, &y), shifted, 64),
            plain
        );
        // (x | y) - (x & y) is the exclusive or
        assert_eq!(
            super::fold(Op::Sub, bin(Op::Or, &x, &y), bin(Op::And, &x, &y), 64),
            bin(Op::Xor, &x, &y)
        );
        // and the operands may arrive the other way round
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
    /// holds everywhere and still reads as the division.
    #[test]
    fn a_magic_that_misses_a_dividend_is_no_division() {
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
        let shifted = |m: u64, s: u64| {
            let hi = Expr::Bin(Op::MulHi(32), Box::new(Expr::Const(m)), Box::new(x.clone()));
            super::fold(Op::Shr, hi, Expr::Const(s), 32)
        };
        assert!(
            !matches!(shifted(0x9249_2493, 2), Expr::Bin(Op::Div, ..)),
            "{:?}",
            shifted(0x9249_2493, 2)
        );
        assert_eq!(
            shifted(0xaaaa_aaab, 1),
            Expr::Bin(Op::Div, Box::new(x), Box::new(Expr::Const(3)))
        );
        let wrong = (0x9249_2493u128 * 0xffff_fffb) >> 34;
        assert_eq!((wrong, 0xffff_fffbu128 / 7), (0x2492_4924, 0x2492_4923));
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
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
        let x = Expr::Var(Key::Reg(crate::isa::Register::RAX));
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

    use super::{Expr, Key, Op, compact_literal, vector_equality};

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

    use crate::isa::{ConditionCode, Register};

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
        vec![
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
    /// `!`. The float `e` and `ne` render as C's `==` and `!=`, which hold
    /// on NaN the other way from the zero flag; with the parity test before
    /// them, as compilers emit them, the pair folds to exactly C's
    /// comparison, so only their inversion is checked here.
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

    use crate::isa::{ConditionCode as C, Register};

    use super::{
        Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp, fold, lo64, merge_bits, sign_extend, ternary,
        unary, without_addend,
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
            Op::SMulHi(hw) => ((signed(a, hw) * signed(b, hw)) >> hw).cast_unsigned(),
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
            Expr::Call(f, args) => {
                let (a, b) = (v(args.first()?)? & lane(w), v(args.get(1)?)? & lane(w));
                let wide = match f.as_str() {
                    "mul_sat" => u128::from(a) * u128::from(b),
                    "add_sat" => u128::from(a) + u128::from(b),
                    _ => return None,
                };
                lo64(wide.min(u128::from(lane(w))))
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
            divisions(&mut t, w, &magics, &xs);
        }
        t.verdict();
    }
}
