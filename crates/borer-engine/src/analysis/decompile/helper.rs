//! The closed vocabulary of helper calls the decompiler prints.
//!
//! A helper is an operation C has no operator for: a rotate, the high half
//! of a product, an overflow test, a bit count, a saturating add, an arm64
//! bit reversal. Each one is a [`Helper`] variant with its spelling, its
//! value ([`Helper::eval`], what every reader of the text computes), and
//! the C that defines it ([`Helper::define`]). A finished text gets the
//! definitions of the helpers it calls from [`declare`], so it compiles as
//! printed. A helper that C's own library already names (`llabs`, `sqrt`)
//! needs no definition.

use std::collections::BTreeSet;
use std::fmt;

use super::expr::{Expr, Op, RoundToInt, UnOp, fold, mask_bits, sext, unary};
use super::expr::{
    abs_bits, align_up_bits, cls_bits, midpoint_bits, rbit_bits, rev16_bits, rev32_bits, rint_bits,
    sub_sat_bits,
};
use crate::program::Program;

/// One helper call the decompiler prints.
///
/// A width in a variant is the operation's width in bits, one of 8, 16, 32
/// or 64, and is part of the spelling (`rotl32`, `uaddo64`). A helper
/// without one takes its width from its argument's type, or works at the
/// machine word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Helper {
    /// `rotlN(x, n)`: `x` rotated left by `n` modulo the width.
    Rotl(u8),
    /// `rotrN(x, n)`: `x` rotated right by `n` modulo the width.
    Rotr(u8),
    /// `mulhiN(a, b)`: the high half of the unsigned product.
    MulHi(u8),
    /// `smulhiN(a, b)`: the high half of the signed product.
    SMulHi(u8),
    /// `smuloN(a, b)`: 1 when the signed product overflows, else 0.
    SMulO(u8),
    /// `uaddoN(a, b)`: 1 when the unsigned sum carries out, else 0.
    UAddO(u8),
    /// `usuboN(a, b)`: 1 when the unsigned difference borrows, else 0.
    USubO(u8),
    /// `saddoN(a, b)`: 1 when the signed sum overflows, else 0.
    SAddO(u8),
    /// `ssuboN(a, b)`: 1 when the signed difference overflows, else 0.
    SSubO(u8),
    /// `add_sat(a, b)` at 64 bits, `add_satN` narrower: the unsigned sum,
    /// all ones when it carries out.
    AddSat(u8),
    /// `mul_sat(a, b)` at 64 bits, `mul_satN` narrower: the unsigned
    /// product, all ones when it does not fit.
    MulSat(u8),
    /// `parity8(x)`: 1 when the low byte has an even number of set bits.
    Parity8,
    /// `bswap(x)`: the bytes of `x` reversed at its type's width.
    Bswap,
    /// `tzcnt(x)`: the trailing zeros of `x`, its width when zero.
    Tzcnt,
    /// `lzcnt(x)`: the leading zeros of `x`, its width when zero.
    Lzcnt,
    /// `popcnt(x)`: the set bits of `x`.
    Popcnt,
    /// `bsf(x)`: the index of the lowest set bit; undefined for zero.
    Bsf,
    /// `bsr(x)`: the index of the highest set bit; undefined for zero.
    Bsr,
    /// `rbit(x)`: the bits of a 32- or 64-bit `x` reversed.
    Rbit,
    /// `rev16(x)`: the bytes of each 16-bit half of a 32- or 64-bit `x` swapped.
    Rev16,
    /// `rev32(x)`: the bytes of each 32-bit half of a 64-bit `x` swapped.
    Rev32,
    /// `cls(x)`: the leading sign bits of a 32- or 64-bit `x`, not counting
    /// the sign.
    Cls,
    /// `min(a, b)`: the signed minimum at the machine word, `a` when equal.
    Min,
    /// `max(a, b)`: the signed maximum at the machine word, `a` when equal.
    Max,
    /// `umin(a, b)`: the unsigned minimum at the machine word, `a` when equal.
    UMin,
    /// `umax(a, b)`: the unsigned maximum at the machine word, `a` when equal.
    UMax,
    /// `sub_sat(a, b)`: the unsigned difference at the machine word, 0
    /// below `b`.
    SubSat,
    /// `midpoint(a, b)`: the floor of the unsigned mean at the machine
    /// word, without the carry a plain sum drops.
    Midpoint,
    /// `align_up(x, a)`: `x` rounded up to a multiple of the power of two
    /// `a` at the machine word.
    AlignUp,
    /// `llabs(x)`: the two's-complement absolute value at the machine word.
    Llabs,
    /// `sqrt(x)`: the IEEE-754 square root.
    Sqrt,
    /// `fabs(x)`: the IEEE-754 absolute value.
    Fabs,
    /// `rint(x)`: `x` rounded to an integer, ties to even, still a float.
    Rint,
    /// `sin(x)`: the sine (`fsin`).
    Sin,
    /// `cos(x)`: the cosine (`fsincos`).
    Cos,
    /// `tan(x)`: the tangent (`fptan`).
    Tan,
    /// `fcvtzsN(x, fb)` or `fcvtzuN(x, fb)`: a float of `fb` bits converted
    /// toward zero to an integer, saturating, NaN as 0.
    RoundToInt(RoundToInt),
    /// `x87_load80(p)`: the 80-bit float at `p`, which no C type here holds.
    X87Load80,
    /// `stmxcsr()`: the SSE control and status register.
    Stmxcsr,
    /// `xgetbv(n)`: the low half of extended control register `n`.
    Xgetbv,
    /// `xgetbv_hi(n)`: the high half of extended control register `n`.
    XgetbvHi,
    /// `fpu_status()`: the x87 status word.
    FpuStatus,
    /// `lahf()`: the low byte of the flags register.
    Lahf,
}

/// How a reader converts a helper's arguments before [`Helper::eval`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Operands {
    /// As they are, the first one's type giving the width.
    Raw,
    /// To a float; the first one's float width is the width.
    Float,
    /// To an integer of the machine word, signed or not.
    Word {
        /// Whether the conversion is to the signed type.
        signed: bool,
    },
    /// To a 64-bit unsigned integer; the helper's own width cuts them.
    Wide,
}

/// The C type a helper's result has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Yields {
    /// An unsigned integer of this many bits.
    Unsigned(u8),
    /// An integer of the machine word, signed or not.
    Word {
        /// Whether the type is signed.
        signed: bool,
    },
    /// The type of the first argument.
    Arg,
}

/// The widths a sized helper has, narrowest first.
const WIDTHS: [u8; 4] = [8, 16, 32, 64];

impl Helper {
    /// Returns every helper, in [`Ord`] order.
    #[cfg(test)]
    pub(super) fn all() -> Vec<Helper> {
        let sized: [fn(u8) -> Helper; 11] = [
            Helper::Rotl,
            Helper::Rotr,
            Helper::MulHi,
            Helper::SMulHi,
            Helper::SMulO,
            Helper::UAddO,
            Helper::USubO,
            Helper::SAddO,
            Helper::SSubO,
            Helper::AddSat,
            Helper::MulSat,
        ];
        let mut all: Vec<Helper> = sized
            .iter()
            .flat_map(|make| WIDTHS.map(make))
            .chain([
                Helper::Parity8,
                Helper::Bswap,
                Helper::Tzcnt,
                Helper::Lzcnt,
                Helper::Popcnt,
                Helper::Bsf,
                Helper::Bsr,
                Helper::Rbit,
                Helper::Rev16,
                Helper::Rev32,
                Helper::Cls,
                Helper::Min,
                Helper::Max,
                Helper::UMin,
                Helper::UMax,
                Helper::SubSat,
                Helper::Midpoint,
                Helper::AlignUp,
                Helper::Llabs,
                Helper::Sqrt,
                Helper::Fabs,
                Helper::Rint,
                Helper::Sin,
                Helper::Cos,
                Helper::Tan,
            ])
            .chain(
                [true, false]
                    .into_iter()
                    .flat_map(|signed| [32, 64].map(|b| RoundToInt::new(signed, b)))
                    .flatten()
                    .map(Helper::RoundToInt),
            )
            .chain([
                Helper::X87Load80,
                Helper::Stmxcsr,
                Helper::Xgetbv,
                Helper::XgetbvHi,
                Helper::FpuStatus,
                Helper::Lahf,
            ])
            .collect();
        all.sort();
        all
    }

    /// Reads a printed name back as its helper.
    ///
    /// # Arguments
    ///
    /// * `name` - A call's name as the text spells it.
    ///
    /// # Returns
    ///
    /// The helper, or `None` for any other name.
    pub(super) fn parse(name: &str) -> Option<Helper> {
        let fixed = match name {
            "parity8" => Some(Helper::Parity8),
            "bswap" => Some(Helper::Bswap),
            "tzcnt" => Some(Helper::Tzcnt),
            "lzcnt" => Some(Helper::Lzcnt),
            "popcnt" => Some(Helper::Popcnt),
            "bsf" => Some(Helper::Bsf),
            "bsr" => Some(Helper::Bsr),
            "rbit" => Some(Helper::Rbit),
            "rev16" => Some(Helper::Rev16),
            "rev32" => Some(Helper::Rev32),
            "cls" => Some(Helper::Cls),
            "min" => Some(Helper::Min),
            "max" => Some(Helper::Max),
            "umin" => Some(Helper::UMin),
            "umax" => Some(Helper::UMax),
            "sub_sat" => Some(Helper::SubSat),
            "midpoint" => Some(Helper::Midpoint),
            "align_up" => Some(Helper::AlignUp),
            "add_sat" => Some(Helper::AddSat(64)),
            "mul_sat" => Some(Helper::MulSat(64)),
            "llabs" => Some(Helper::Llabs),
            "sqrt" => Some(Helper::Sqrt),
            "fabs" => Some(Helper::Fabs),
            "rint" => Some(Helper::Rint),
            "sin" => Some(Helper::Sin),
            "cos" => Some(Helper::Cos),
            "tan" => Some(Helper::Tan),
            "x87_load80" => Some(Helper::X87Load80),
            "stmxcsr" => Some(Helper::Stmxcsr),
            "xgetbv" => Some(Helper::Xgetbv),
            "xgetbv_hi" => Some(Helper::XgetbvHi),
            "fpu_status" => Some(Helper::FpuStatus),
            "lahf" => Some(Helper::Lahf),
            _ => None,
        };
        if fixed.is_some() {
            return fixed;
        }
        if let Some(round) = RoundToInt::parse(name) {
            return Some(Helper::RoundToInt(round));
        }
        let stem = name.trim_end_matches(|c: char| c.is_ascii_digit());
        let w = name
            .get(stem.len()..)
            .and_then(|d| WIDTHS.into_iter().find(|w| w.to_string() == d))?;
        let make: fn(u8) -> Helper = match stem {
            "rotl" => Helper::Rotl,
            "rotr" => Helper::Rotr,
            "mulhi" => Helper::MulHi,
            "smulhi" => Helper::SMulHi,
            "smulo" => Helper::SMulO,
            "uaddo" => Helper::UAddO,
            "usubo" => Helper::USubO,
            "saddo" => Helper::SAddO,
            "ssubo" => Helper::SSubO,
            "add_sat" if w < 64 => Helper::AddSat,
            "mul_sat" if w < 64 => Helper::MulSat,
            _ => return None,
        };
        Some(make(w))
    }

    /// The width-taking operator this helper prints, if it is one.
    ///
    /// # Returns
    ///
    /// The [`Op`] whose constant folding is this helper's value, or `None`.
    fn op(self) -> Option<Op> {
        match self {
            Helper::Rotl(w) => Some(Op::Rol(w)),
            Helper::Rotr(w) => Some(Op::Ror(w)),
            Helper::MulHi(w) => Some(Op::MulHi(w)),
            Helper::SMulHi(w) => Some(Op::SMulHi(w)),
            Helper::SMulO(w) => Some(Op::SMulO(w)),
            Helper::UAddO(w) => Some(Op::UAddO(w)),
            Helper::USubO(w) => Some(Op::USubO(w)),
            Helper::SAddO(_)
            | Helper::SSubO(_)
            | Helper::AddSat(_)
            | Helper::MulSat(_)
            | Helper::Parity8
            | Helper::Bswap
            | Helper::Tzcnt
            | Helper::Lzcnt
            | Helper::Popcnt
            | Helper::Bsf
            | Helper::Bsr
            | Helper::Rbit
            | Helper::Rev16
            | Helper::Rev32
            | Helper::Cls
            | Helper::Min
            | Helper::Max
            | Helper::UMin
            | Helper::UMax
            | Helper::SubSat
            | Helper::Midpoint
            | Helper::AlignUp
            | Helper::Llabs
            | Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan
            | Helper::RoundToInt(_)
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => None,
        }
    }

    /// The bit operator over one operand this helper prints, if it is one.
    ///
    /// # Returns
    ///
    /// The [`UnOp`] whose constant folding is this helper's value, or `None`.
    fn unop(self) -> Option<UnOp> {
        match self {
            Helper::Bswap => Some(UnOp::Bswap),
            Helper::Tzcnt => Some(UnOp::Tzcnt),
            Helper::Lzcnt => Some(UnOp::Lzcnt),
            Helper::Popcnt => Some(UnOp::Popcnt),
            Helper::Bsf => Some(UnOp::Bsf),
            Helper::Bsr => Some(UnOp::Bsr),
            Helper::Rotl(_)
            | Helper::Rotr(_)
            | Helper::MulHi(_)
            | Helper::SMulHi(_)
            | Helper::SMulO(_)
            | Helper::UAddO(_)
            | Helper::USubO(_)
            | Helper::SAddO(_)
            | Helper::SSubO(_)
            | Helper::AddSat(_)
            | Helper::MulSat(_)
            | Helper::Parity8
            | Helper::Rbit
            | Helper::Rev16
            | Helper::Rev32
            | Helper::Cls
            | Helper::Min
            | Helper::Max
            | Helper::UMin
            | Helper::UMax
            | Helper::SubSat
            | Helper::Midpoint
            | Helper::AlignUp
            | Helper::Llabs
            | Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan
            | Helper::RoundToInt(_)
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => None,
        }
    }

    /// Returns how a reader converts the arguments before [`Helper::eval`].
    pub(super) fn operands(self) -> Operands {
        match self {
            Helper::Rotl(_)
            | Helper::Rotr(_)
            | Helper::MulHi(_)
            | Helper::SMulHi(_)
            | Helper::SMulO(_)
            | Helper::UAddO(_)
            | Helper::USubO(_)
            | Helper::SAddO(_)
            | Helper::SSubO(_)
            | Helper::AddSat(_)
            | Helper::MulSat(_)
            | Helper::Parity8 => Operands::Wide,
            Helper::Bswap
            | Helper::Tzcnt
            | Helper::Lzcnt
            | Helper::Popcnt
            | Helper::Bsf
            | Helper::Bsr
            | Helper::Rbit
            | Helper::Rev16
            | Helper::Rev32
            | Helper::Cls
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => Operands::Raw,
            Helper::Min | Helper::Max | Helper::Llabs => Operands::Word { signed: true },
            Helper::UMin | Helper::UMax | Helper::SubSat | Helper::Midpoint | Helper::AlignUp => {
                Operands::Word { signed: false }
            }
            Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan
            | Helper::RoundToInt(_) => Operands::Float,
        }
    }

    /// Returns the C type of the result, the one [`Helper::define`] gives it.
    pub(super) fn yields(self) -> Yields {
        match self {
            Helper::Rotl(w)
            | Helper::Rotr(w)
            | Helper::MulHi(w)
            | Helper::SMulHi(w)
            | Helper::SMulO(w)
            | Helper::UAddO(w)
            | Helper::USubO(w)
            | Helper::SAddO(w)
            | Helper::SSubO(w)
            | Helper::AddSat(w)
            | Helper::MulSat(w) => Yields::Unsigned(w),
            Helper::Parity8 => Yields::Unsigned(8),
            Helper::Bswap
            | Helper::Tzcnt
            | Helper::Lzcnt
            | Helper::Popcnt
            | Helper::Bsf
            | Helper::Bsr
            | Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan => Yields::Arg,
            Helper::Min | Helper::Max | Helper::Llabs => Yields::Word { signed: true },
            Helper::Rbit
            | Helper::Rev16
            | Helper::Rev32
            | Helper::Cls
            | Helper::UMin
            | Helper::UMax
            | Helper::SubSat
            | Helper::Midpoint
            | Helper::AlignUp
            | Helper::RoundToInt(_)
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => Yields::Word { signed: false },
        }
    }

    /// Computes the helper's value.
    ///
    /// # Arguments
    ///
    /// * `args` - The arguments' bits, converted as [`Helper::operands`] says.
    /// * `bits` - The first argument's width: its type's for
    ///   [`Operands::Raw`], its float width for [`Operands::Float`].
    /// * `word` - The machine word's width.
    ///
    /// # Returns
    ///
    /// The result's bits, or `None` where the value is undefined (a bit scan
    /// of zero), the width is not one the helper has, an argument is
    /// missing, or the helper reads state no argument holds.
    pub(super) fn eval(self, args: &[u64], bits: u8, word: u8) -> Option<u64> {
        let a = args.first().copied();
        let b = args.get(1).copied();
        if let Some(op) = self.op() {
            return match fold(op, Expr::Const(a?), Expr::Const(b?), self.width()?) {
                Expr::Const(c) => Some(c),
                Expr::Var(_)
                | Expr::Str(_)
                | Expr::Sp(_)
                | Expr::Bin(..)
                | Expr::Un(..)
                | Expr::Deref(..)
                | Expr::Cond(_)
                | Expr::Ternary(..)
                | Expr::Sext(..)
                | Expr::Cast(..)
                | Expr::Bitcast(..)
                | Expr::Call(..)
                | Expr::Helper(..)
                | Expr::FConst(..) => None,
            };
        }
        if let Some(op) = self.unop() {
            return match unary(op, Expr::Const(a?), bits) {
                Expr::Const(c) => Some(c),
                Expr::Var(_)
                | Expr::Str(_)
                | Expr::Sp(_)
                | Expr::Bin(..)
                | Expr::Un(..)
                | Expr::Deref(..)
                | Expr::Cond(_)
                | Expr::Ternary(..)
                | Expr::Sext(..)
                | Expr::Cast(..)
                | Expr::Bitcast(..)
                | Expr::Call(..)
                | Expr::Helper(..)
                | Expr::FConst(..) => None,
            };
        }
        let signed_out = |t: i128, w: u8| t >= 1i128 << (w - 1) || t < -(1i128 << (w - 1));
        let signed = |v: u64, w: u8| i128::from(sext(v & mask_bits(w), w).cast_signed());
        match self {
            Helper::SAddO(w) => Some(u64::from(signed_out(signed(a?, w) + signed(b?, w), w))),
            Helper::SSubO(w) => Some(u64::from(signed_out(signed(a?, w) - signed(b?, w), w))),
            Helper::AddSat(w) | Helper::MulSat(w) => {
                let m = mask_bits(w);
                let (x, y) = (u128::from(a? & m), u128::from(b? & m));
                let wide = if matches!(self, Helper::AddSat(_)) {
                    x + y
                } else {
                    x * y
                };
                u64::try_from(wide.min(u128::from(m))).ok()
            }
            Helper::Parity8 => Some(u64::from((a? & 0xff).count_ones().is_multiple_of(2))),
            Helper::Rbit => rbit_bits(a?, bits),
            Helper::Rev16 => rev16_bits(a?, bits),
            Helper::Rev32 => rev32_bits(a?, bits),
            Helper::Cls => cls_bits(a?, bits),
            Helper::Min => extremum(a?, b?, word, |x, y| signed(x, word) <= signed(y, word)),
            Helper::Max => extremum(a?, b?, word, |x, y| signed(x, word) >= signed(y, word)),
            Helper::UMin => extremum(a?, b?, word, |x, y| x <= y),
            Helper::UMax => extremum(a?, b?, word, |x, y| x >= y),
            Helper::SubSat => sub_sat_bits(a?, b?, word),
            Helper::Midpoint => midpoint_bits(a?, b?, word),
            Helper::AlignUp => align_up_bits(a?, b?, word),
            Helper::Llabs => abs_bits(a?, word),
            Helper::Sqrt => match bits {
                32 => Some(u64::from(
                    f32::from_bits(crate::num::lo32(a?)).sqrt().to_bits(),
                )),
                64 => Some(f64::from_bits(a?).sqrt().to_bits()),
                _ => None,
            },
            Helper::Fabs => match bits {
                32 => Some(a? & 0x7fff_ffff),
                64 => Some(a? & 0x7fff_ffff_ffff_ffff),
                _ => None,
            },
            Helper::Rint => rint_bits(a?, bits),
            Helper::RoundToInt(round) => round.apply(a?, bits),
            Helper::Rotl(_)
            | Helper::Rotr(_)
            | Helper::MulHi(_)
            | Helper::SMulHi(_)
            | Helper::SMulO(_)
            | Helper::UAddO(_)
            | Helper::USubO(_)
            | Helper::Bswap
            | Helper::Tzcnt
            | Helper::Lzcnt
            | Helper::Popcnt
            | Helper::Bsf
            | Helper::Bsr
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => None,
        }
    }

    /// The width the spelling carries, for the sized helpers.
    ///
    /// # Returns
    ///
    /// The width in bits, or `None` for a helper without one.
    fn width(self) -> Option<u8> {
        match self {
            Helper::Rotl(w)
            | Helper::Rotr(w)
            | Helper::MulHi(w)
            | Helper::SMulHi(w)
            | Helper::SMulO(w)
            | Helper::UAddO(w)
            | Helper::USubO(w)
            | Helper::SAddO(w)
            | Helper::SSubO(w)
            | Helper::AddSat(w)
            | Helper::MulSat(w) => Some(w),
            Helper::Parity8
            | Helper::Bswap
            | Helper::Tzcnt
            | Helper::Lzcnt
            | Helper::Popcnt
            | Helper::Bsf
            | Helper::Bsr
            | Helper::Rbit
            | Helper::Rev16
            | Helper::Rev32
            | Helper::Cls
            | Helper::Min
            | Helper::Max
            | Helper::UMin
            | Helper::UMax
            | Helper::SubSat
            | Helper::Midpoint
            | Helper::AlignUp
            | Helper::Llabs
            | Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan
            | Helper::RoundToInt(_)
            | Helper::X87Load80
            | Helper::Stmxcsr
            | Helper::Xgetbv
            | Helper::XgetbvHi
            | Helper::FpuStatus
            | Helper::Lahf => None,
        }
    }

    /// Returns the C that defines the helper, one line each.
    ///
    /// A helper C's library names (`llabs`, `sqrt`, `rint`) has none. A
    /// helper whose width is its argument's type is a `_Generic` over one
    /// function per width. A helper that reads machine state no argument
    /// holds is declared `extern`: the text compiles, and only a link
    /// shows it was never C.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width, 32 or 64; the word-wide helpers
    ///   take and return integers of it.
    ///
    /// # Returns
    ///
    /// The lines, empty when the library already defines the helper.
    pub(super) fn define(self, word: u8) -> Vec<String> {
        let wu = format!("uint{word}_t");
        let ws = format!("int{word}_t");
        let two = |ret: &str, body: &str| {
            vec![format!(
                "static inline {ret} {self}(uint64_t a, uint64_t b) {{ {body} }}"
            )]
        };
        let overflow = |w: u8, signed: bool, op: &str| {
            let t = if signed {
                format!("int{w}_t")
            } else {
                format!("uint{w}_t")
            };
            two(
                &format!("uint{w}_t"),
                &format!("{t} r; return __builtin_{op}_overflow(({t})a, ({t})b, &r);"),
            )
        };
        let word_two = |ret: &str, t: &str, body: &str| {
            vec![format!(
                "static inline {ret} {self}({t} a, {t} b) {{ return {body}; }}"
            )]
        };
        match self {
            Helper::Rotl(w) | Helper::Rotr(w) => {
                let (first, second) = if matches!(self, Helper::Rotl(_)) {
                    ("<<", ">>")
                } else {
                    (">>", "<<")
                };
                vec![format!(
                    "static inline uint{w}_t {self}(uint64_t x, uint64_t n) {{ uint{w}_t v = \
                     (uint{w}_t)x; n &= {w} - 1; return n ? (uint{w}_t)((v {first} n) | (v \
                     {second} ({w} - n))) : v; }}"
                )]
            }
            Helper::MulHi(64) => two(
                "uint64_t",
                "return (uint64_t)(((unsigned __int128)a * b) >> 64);",
            ),
            Helper::MulHi(w) => two(
                &format!("uint{w}_t"),
                &format!("return (uint{w}_t)(((uint64_t)(uint{w}_t)a * (uint{w}_t)b) >> {w});"),
            ),
            Helper::SMulHi(64) => two(
                "uint64_t",
                "return (uint64_t)(((__int128)(int64_t)a * (int64_t)b) >> 64);",
            ),
            Helper::SMulHi(w) => two(
                &format!("uint{w}_t"),
                &format!("return (uint{w}_t)(((int64_t)(int{w}_t)a * (int{w}_t)b) >> {w});"),
            ),
            Helper::SMulO(w) => overflow(w, true, "mul"),
            Helper::UAddO(w) => overflow(w, false, "add"),
            Helper::USubO(w) => overflow(w, false, "sub"),
            Helper::SAddO(w) => overflow(w, true, "add"),
            Helper::SSubO(w) => overflow(w, true, "sub"),
            Helper::AddSat(w) | Helper::MulSat(w) => {
                let op = if matches!(self, Helper::AddSat(_)) {
                    "add"
                } else {
                    "mul"
                };
                two(
                    &format!("uint{w}_t"),
                    &format!(
                        "uint{w}_t r; return __builtin_{op}_overflow((uint{w}_t)a, (uint{w}_t)b, \
                         &r) ? (uint{w}_t)-1 : r;"
                    ),
                )
            }
            Helper::Parity8 => vec![
                "static inline uint8_t parity8(uint64_t x) { return !__builtin_parity((uint8_t)x); }"
                    .to_owned(),
            ],
            Helper::Bswap => generic(self, &[8, 16, 32, 64], None, |w| match w {
                8 => "(uint8_t)__builtin_bswap64(x)".to_owned(),
                _ => format!("__builtin_bswap{w}(x)"),
            }),
            Helper::Tzcnt => generic(self, &[8, 16, 32, 64], None, |w| {
                format!("x ? (uint{w}_t)__builtin_ctzll(x) : {w}")
            }),
            Helper::Lzcnt => generic(self, &[8, 16, 32, 64], None, |w| {
                format!("x ? (uint{w}_t)(__builtin_clzll(x) - {}) : {w}", 64 - w)
            }),
            Helper::Popcnt => generic(self, &[8, 16, 32, 64], None, |w| {
                format!("(uint{w}_t)__builtin_popcountll(x)")
            }),
            Helper::Bsf => generic(self, &[8, 16, 32, 64], None, |w| {
                format!("x ? (uint{w}_t)__builtin_ctzll(x) : 0")
            }),
            Helper::Bsr => generic(self, &[8, 16, 32, 64], None, |w| {
                format!("x ? (uint{w}_t)(63 - __builtin_clzll(x)) : 0")
            }),
            Helper::Rbit => generic(self, &[32, 64], Some(word), |w| {
                let mut steps = String::new();
                for (k, m) in [
                    (1, 0x5555_5555_5555_5555u64),
                    (2, 0x3333_3333_3333_3333),
                    (4, 0x0f0f_0f0f_0f0f_0f0f),
                ] {
                    let m = m & mask_bits(w);
                    steps.push_str(&format!("x = ((x >> {k}) & {m:#x}) | ((x & {m:#x}) << {k}), "));
                }
                format!("({steps}__builtin_bswap{w}(x))")
            }),
            Helper::Rev16 => generic(self, &[32, 64], Some(word), |w| {
                let m = 0x00ff_00ff_00ff_00ffu64 & mask_bits(w);
                format!("((x & {m:#x}) << 8) | ((x >> 8) & {m:#x})")
            }),
            Helper::Rev32 => generic(self, &[64], Some(word), |_| {
                "(x = ((x & 0x00ff00ff00ff00ff) << 8) | ((x >> 8) & 0x00ff00ff00ff00ff), ((x & \
                 0x0000ffff0000ffff) << 16) | ((x >> 16) & 0x0000ffff0000ffff))"
                    .to_owned()
            }),
            Helper::Cls => generic(self, &[32, 64], Some(word), |w| {
                let clz = if w == 64 { "__builtin_clzll" } else { "__builtin_clz" };
                format!("{clz}((x ^ (x << 1)) | 1)")
            }),
            Helper::Min | Helper::Max => {
                let rel = if matches!(self, Helper::Min) { "<=" } else { ">=" };
                let mut lines = vec![format!("#undef {self}")];
                lines.extend(word_two(&ws, &ws, &format!("a {rel} b ? a : b")));
                lines
            }
            Helper::UMin | Helper::UMax => {
                let rel = if matches!(self, Helper::UMin) {
                    "<="
                } else {
                    ">="
                };
                word_two(&wu, &wu, &format!("a {rel} b ? a : b"))
            }
            Helper::SubSat => word_two(&wu, &wu, "a > b ? a - b : 0"),
            Helper::Midpoint => word_two(&wu, &wu, "(a & b) + ((a ^ b) >> 1)"),
            Helper::AlignUp => word_two(&wu, &wu, "(a + b - 1) & ~(b - 1)"),
            Helper::RoundToInt(round) => {
                let (t, lo, hi) = match round {
                    RoundToInt::Signed(32) => {
                        ("int32_t", "d <= -2147483648.0 ? -2147483647 - 1", "2147483647.0 ? 2147483647")
                    }
                    RoundToInt::Signed(_) => (
                        "int64_t",
                        "d <= -9223372036854775808.0 ? INT64_MIN",
                        "9223372036854775807.0 ? INT64_MAX",
                    ),
                    RoundToInt::Unsigned(32) => ("uint32_t", "d <= 0 ? 0", "4294967295.0 ? 4294967295u"),
                    RoundToInt::Unsigned(_) => {
                        ("uint64_t", "d <= 0 ? 0", "18446744073709551615.0 ? UINT64_MAX")
                    }
                };
                vec![format!(
                    "static inline {t} {self}(double d, int fb) {{ (void)fb; return d != d ? 0 : d \
                     >= {hi} : {lo} : ({t})d; }}"
                )]
            }
            Helper::X87Load80 => vec!["extern double x87_load80(uint64_t p);".to_owned()],
            Helper::Stmxcsr | Helper::FpuStatus | Helper::Lahf => {
                vec![format!("extern {wu} {self}(void);")]
            }
            Helper::Xgetbv | Helper::XgetbvHi => vec![format!("extern {wu} {self}(uint64_t n);")],
            Helper::Llabs
            | Helper::Sqrt
            | Helper::Fabs
            | Helper::Rint
            | Helper::Sin
            | Helper::Cos
            | Helper::Tan => Vec::new(),
        }
    }
}

/// The operand a compare-select keeps, at `bits`.
///
/// # Arguments
///
/// * `a` - The first operand, kept when `first` holds, and when equal.
/// * `b` - The second operand.
/// * `bits` - The width; 0 or above 64 is `None`.
/// * `first` - Whether the masked `a` is kept over the masked `b`.
///
/// # Returns
///
/// The kept operand's bits.
fn extremum(a: u64, b: u64, bits: u8, first: impl Fn(u64, u64) -> bool) -> Option<u64> {
    if bits == 0 || bits > 64 {
        return None;
    }
    let m = mask_bits(bits);
    let (x, y) = (a & m, b & m);
    Some(if first(x, y) { x } else { y })
}

/// Defines a helper whose width is its argument's type: one function per
/// width, named with the width, and a `_Generic` that picks one by the
/// argument and gives a signed argument's result its type back.
///
/// # Arguments
///
/// * `h` - The helper.
/// * `widths` - The widths it has; the widest is the default.
/// * `ret` - The result width for every argument width, or `None` for the
///   argument's own width.
/// * `body` - The result expression over `x` at a width.
///
/// # Returns
///
/// The definition's lines.
fn generic(h: Helper, widths: &[u8], ret: Option<u8>, body: impl Fn(u8) -> String) -> Vec<String> {
    let mut lines: Vec<String> = widths
        .iter()
        .map(|&w| {
            let r = ret.unwrap_or(w);
            format!(
                "static inline uint{r}_t {h}{w}(uint{w}_t x) {{ return {}; }}",
                body(w)
            )
        })
        .collect();
    let widest = widths.last().copied().unwrap_or(64);
    let mut picks = String::new();
    for &w in widths.iter().filter(|w| **w != widest) {
        let back = if ret.is_none() {
            format!("(int{w}_t)")
        } else {
            String::new()
        };
        picks.push_str(&format!(
            "int{w}_t: {back}{h}{w}((uint{w}_t)(x)), uint{w}_t: {h}{w}(x), "
        ));
    }
    lines.push(format!(
        "#define {h}(x) _Generic((x), {picks}default: {h}{widest}(x))"
    ));
    lines
}

impl fmt::Display for Helper {
    /// Writes the helper's printed name.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter.
    ///
    /// # Errors
    ///
    /// When the formatter does.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (stem, w) = match *self {
            Helper::Rotl(w) => ("rotl", w),
            Helper::Rotr(w) => ("rotr", w),
            Helper::MulHi(w) => ("mulhi", w),
            Helper::SMulHi(w) => ("smulhi", w),
            Helper::SMulO(w) => ("smulo", w),
            Helper::UAddO(w) => ("uaddo", w),
            Helper::USubO(w) => ("usubo", w),
            Helper::SAddO(w) => ("saddo", w),
            Helper::SSubO(w) => ("ssubo", w),
            Helper::AddSat(64) => return f.write_str("add_sat"),
            Helper::MulSat(64) => return f.write_str("mul_sat"),
            Helper::AddSat(w) => ("add_sat", w),
            Helper::MulSat(w) => ("mul_sat", w),
            Helper::RoundToInt(round) => return f.write_str(round.name().unwrap_or("fcvtz")),
            Helper::Parity8 => return f.write_str("parity8"),
            Helper::Bswap => return f.write_str("bswap"),
            Helper::Tzcnt => return f.write_str("tzcnt"),
            Helper::Lzcnt => return f.write_str("lzcnt"),
            Helper::Popcnt => return f.write_str("popcnt"),
            Helper::Bsf => return f.write_str("bsf"),
            Helper::Bsr => return f.write_str("bsr"),
            Helper::Rbit => return f.write_str("rbit"),
            Helper::Rev16 => return f.write_str("rev16"),
            Helper::Rev32 => return f.write_str("rev32"),
            Helper::Cls => return f.write_str("cls"),
            Helper::Min => return f.write_str("min"),
            Helper::Max => return f.write_str("max"),
            Helper::UMin => return f.write_str("umin"),
            Helper::UMax => return f.write_str("umax"),
            Helper::SubSat => return f.write_str("sub_sat"),
            Helper::Midpoint => return f.write_str("midpoint"),
            Helper::AlignUp => return f.write_str("align_up"),
            Helper::Llabs => return f.write_str("llabs"),
            Helper::Sqrt => return f.write_str("sqrt"),
            Helper::Fabs => return f.write_str("fabs"),
            Helper::Rint => return f.write_str("rint"),
            Helper::Sin => return f.write_str("sin"),
            Helper::Cos => return f.write_str("cos"),
            Helper::Tan => return f.write_str("tan"),
            Helper::X87Load80 => return f.write_str("x87_load80"),
            Helper::Stmxcsr => return f.write_str("stmxcsr"),
            Helper::Xgetbv => return f.write_str("xgetbv"),
            Helper::XgetbvHi => return f.write_str("xgetbv_hi"),
            Helper::FpuStatus => return f.write_str("fpu_status"),
            Helper::Lahf => return f.write_str("lahf"),
        };
        write!(f, "{stem}{w}")
    }
}

/// The width an argument carries for a helper that works at its
/// argument's type: the type a cast or a load gives it, at most the word.
///
/// # Arguments
///
/// * `e` - The argument.
/// * `word` - The machine word's width, the width of anything untyped.
fn arg_bits(e: &Expr, word: u8) -> u8 {
    match e {
        Expr::Cast(_, ty) | Expr::Bitcast(_, ty) | Expr::Deref(_, ty) => ty.bits().min(word),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Cond(_)
        | Expr::Ternary(..)
        | Expr::Sext(..)
        | Expr::Call(..)
        | Expr::Helper(..)
        | Expr::FConst(..) => word,
    }
}

/// Evaluates a helper call over expression arguments, as the replay and
/// the verifier read an [`Expr::Helper`].
///
/// # Arguments
///
/// * `h` - The helper.
/// * `args` - Its arguments.
/// * `word` - The machine word's width.
/// * `value` - An argument's value, `None` when unknown.
/// * `float_bits` - An argument's float width, `None` for an integer.
///
/// # Returns
///
/// The value, or `None` when an argument or the helper's value is unknown.
pub(super) fn eval_call(
    h: Helper,
    args: &[Expr],
    word: u8,
    value: impl FnMut(&Expr) -> Option<u64>,
    float_bits: impl Fn(&Expr) -> Option<u8>,
) -> Option<u64> {
    let first = args.first();
    let bits = match h.operands() {
        Operands::Float => float_bits(first?)?,
        Operands::Raw => first.map_or(word, |a| arg_bits(a, word)),
        Operands::Word { .. } | Operands::Wide => word,
    };
    let vals = args.iter().map(value).collect::<Option<Vec<u64>>>()?;
    h.eval(&vals, bits, word)
}

/// The starts of the lines [`declare`] writes.
const DEFINING: [&str; 4] = ["static inline ", "#define ", "#undef ", "extern "];

/// Tells whether a line of a finished text is one of the helper
/// definitions [`declare`] put there.
///
/// # Arguments
///
/// * `line` - The line.
pub(super) fn defines(line: &str) -> bool {
    DEFINING.iter().any(|d| line.starts_with(d))
}

/// Returns the helpers a text calls, in [`Ord`] order.
///
/// A helper counts where its name is a whole word followed by `(` on a
/// line that is not a comment, outside string and character literals.
///
/// # Arguments
///
/// * `text` - A finished decompilation.
fn called(text: &str) -> BTreeSet<Helper> {
    let mut found = BTreeSet::new();
    for line in text.lines().filter(|l| !l.trim_start().starts_with("//")) {
        let mut word = String::new();
        let mut quote: Option<char> = None;
        let mut escaped = false;
        let mut chars = line.chars().peekable();
        while let Some(c) = chars.next() {
            if let Some(q) = quote {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == q {
                    quote = None;
                }
                continue;
            }
            if c.is_ascii_alphanumeric() || c == '_' {
                word.push(c);
                continue;
            }
            if c == '(' && !word.starts_with(|d: char| d.is_ascii_digit()) {
                found.extend(Helper::parse(&word));
            }
            if c == '/' && chars.peek() == Some(&'/') {
                break;
            }
            if c == '"' || c == '\'' {
                quote = Some(c);
            }
            word.clear();
        }
    }
    found
}

/// Puts the definition of every helper a finished text calls at its top.
///
/// The lines go after the leading comment lines, where a reader looks for
/// declarations, each helper once, in [`Ord`] order. A text that calls no
/// helper C's library does not define comes back unchanged.
///
/// # Arguments
///
/// * `text` - A finished decompilation.
/// * `program` - The image, whose word width the word-wide helpers take.
///
/// # Returns
///
/// The text with its helpers defined.
pub(super) fn declare(text: &str, program: &Program) -> String {
    let word = program
        .arch
        .bitness()
        .and_then(|b| u8::try_from(b).ok())
        .unwrap_or(64);
    let defs: Vec<String> = called(text)
        .into_iter()
        .flat_map(|h| h.define(word))
        .collect();
    if defs.is_empty() {
        return text.to_owned();
    }
    let mut lines: Vec<&str> = text.lines().collect();
    let at = lines.iter().take_while(|l| l.starts_with("//")).count();
    lines.splice(at..at, defs.iter().map(String::as_str));
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::{Helper, Operands, Yields, declare};
    use crate::program::Program;

    /// Every helper's printed name reads back as that helper.
    ///
    /// No two helpers print the same name.
    ///
    /// # Panics
    ///
    /// When a name does not round-trip.
    #[test]
    fn every_helper_name_reads_back() {
        let all = Helper::all();
        for h in &all {
            assert_eq!(Helper::parse(&h.to_string()), Some(*h), "{h}");
        }
        let mut names: Vec<String> = all.iter().map(ToString::to_string).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), all.len());
        assert_eq!(Helper::parse("add_sat64"), None);
        assert_eq!(Helper::parse("rotl12"), None);
        assert_eq!(Helper::parse("paddd"), None);
    }

    /// Every helper C's library does not name has a definition.
    ///
    /// The library names (`llabs`, `sqrt`) get none.
    ///
    /// # Panics
    ///
    /// When a helper lacks its definition.
    #[test]
    fn every_helper_c_does_not_name_is_defined() {
        for h in Helper::all() {
            let lines = h.define(64);
            let library = matches!(
                h,
                Helper::Llabs
                    | Helper::Sqrt
                    | Helper::Fabs
                    | Helper::Rint
                    | Helper::Sin
                    | Helper::Cos
                    | Helper::Tan
            );
            assert_eq!(lines.is_empty(), library, "{h}");
            let name = h.to_string();
            assert!(
                library || lines.iter().any(|l| l.contains(&format!(" {name}("))),
                "{h}: {lines:?}"
            );
        }
    }

    /// A text gets the definitions of the helpers it calls.
    ///
    /// They go after its comment lines, each once; a name in a comment or a
    /// string, or one that only starts the same, does not count.
    ///
    /// # Panics
    ///
    /// When a definition is missing, doubled or misplaced.
    #[test]
    fn a_text_gets_the_helpers_it_calls() {
        let text = "// signature: uint64_t f(uint64_t a1)\n\
                    \n\
                    if (uaddo64(a1, 1) != 0) {\n  return bsr(a1); // bsr(x)\n}\n\
                    puts(\"umin(a, b)\");\n\
                    return bsr(a1) + umin_x(a1);\n";
        let p = Program::raw_x64(&[0xc3]);
        let out = declare(text, &p);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[0], "// signature: uint64_t f(uint64_t a1)");
        assert!(
            lines[1].starts_with("static inline uint64_t uaddo64("),
            "{out}"
        );
        assert!(
            lines[2].starts_with("static inline uint8_t bsr8(uint8_t x)"),
            "{out}"
        );
        assert_eq!(out.matches("#define bsr(x)").count(), 1, "{out}");
        assert_eq!(
            out.matches("uaddo64(uint64_t a, uint64_t b)").count(),
            1,
            "{out}"
        );
        assert!(!out.contains("umin(uint64_t"), "{out}");
        let body = text.split_once('\n').map_or("", |(_, b)| b);
        assert!(out.ends_with(body), "{out}");
        let plain = "// signature: uint64_t f(uint64_t a1)\n\nreturn llabs(a1) + g(a1);\n";
        assert_eq!(declare(plain, &p), plain);
    }

    /// The condition helpers have values.
    ///
    /// The overflow tests the renderer writes only in conditions, and the
    /// parity flag, no longer leave a run unchecked.
    ///
    /// # Panics
    ///
    /// When a value is wrong.
    #[test]
    fn the_condition_helpers_have_values() {
        assert_eq!(Helper::SAddO(16).eval(&[0x7fff, 1], 64, 64), Some(1));
        assert_eq!(Helper::SAddO(16).eval(&[0x7ffe, 1], 64, 64), Some(0));
        assert_eq!(Helper::SSubO(32).eval(&[0x8000_0000, 1], 64, 64), Some(1));
        assert_eq!(Helper::UAddO(64).eval(&[u64::MAX, 1], 64, 64), Some(1));
        assert_eq!(Helper::Parity8.eval(&[0x103], 64, 64), Some(1));
        assert_eq!(Helper::Parity8.eval(&[0x1], 64, 64), Some(0));
        assert_eq!(Helper::AddSat(16).eval(&[0xffff, 2], 64, 64), Some(0xffff));
        assert_eq!(Helper::Bsr.eval(&[0], 32, 64), None);
        assert_eq!(Helper::Bsr.eval(&[0x10], 32, 64), Some(4));
        assert_eq!(Helper::UMin.eval(&[3, 2], 64, 64), Some(2));
        assert_eq!(Helper::Min.eval(&[u64::MAX, 2], 64, 64), Some(u64::MAX));
        assert_eq!(Helper::UMin.operands(), Operands::Word { signed: false });
        assert_eq!(Helper::Bsr.yields(), Yields::Arg);
    }
}
