//! Float arithmetic bit for bit as the machine does it.
//!
//! The encodings, the operations at single and double width, and the
//! conversions to and from integers, shared by every evaluator that
//! compares with the machine.

use super::expr::{Expr, Op, Ty, UnOp};
use super::verify::{low, sext};
use crate::num::lo32;

/// The float the low `fb` bits of `v` encode.
///
/// # Arguments
///
/// * `v` - The bits.
/// * `fb` - 32 or 64.
pub(super) fn float_of(v: u64, fb: u8) -> f64 {
    if fb == 32 {
        f64::from(f32::from_bits(lo32(v)))
    } else {
        f64::from_bits(v)
    }
}

/// A float operation a cast names a width for, computed at that width.
///
/// The cast is not a conversion. A scalar `fadd` of two bare registers
/// carries no type of its own, and the cast records the width the
/// instruction used, so the bits are that operation's. An integer under
/// the cast is `None` here and converts by [`integer_to_float`]. A float
/// constant of a different width is `None`, not a value read at the wrong
/// width.
///
/// # Arguments
///
/// * `e` - The cast's operand.
/// * `fb` - The width the cast names, 32 or 64.
/// * `leaf` - The bits of one operand.
pub(super) fn float_carried(
    e: &Expr,
    fb: u8,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    if !matches!(fb, 32 | 64) {
        return None;
    }
    let wrong = |e: &Expr| matches!(e, Expr::FConst(_, ty) if ty.bits() != fb);
    match e {
        Expr::Bin(op, _, _) if op.is_float() => float_scale_at(e, fb, leaf),
        Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), inner) if !wrong(inner) => {
            float_un(*op, leaf(inner)?, fb)
        }
        Expr::Un(UnOp::Neg, inner) if inner.is_float() && !wrong(inner) => {
            Some(leaf(inner)? ^ (1u64 << (u32::from(fb) - 1)))
        }
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(_, _, _)
        | Expr::Un(_, _)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Ternary(_, _, _)
        | Expr::Sext(_, _)
        | Expr::Cast(_, _)
        | Expr::Call(_, _)
        | Expr::Bitcast(_, _)
        | Expr::Helper(_, _) => None,
    }
}

/// A float cast of a bitwise cut of a float, as the bits, not the number.
///
/// The cut is the encoding ([`super::interp`] does the same for the
/// operator). Casting those bits to a float keeps them, zero above a
/// single: converting them would be the integer the bits happen to be.
/// Anything other than that cut is `None`, and the cast converts by
/// [`integer_to_float`].
///
/// # Arguments
///
/// * `e` - The cast's operand.
/// * `to` - The float the cast names.
/// * `leaf` - The bits of one operand.
pub(super) fn reinterpret_float(
    e: &Expr,
    to: Ty,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    let Expr::Bin(op @ (Op::And | Op::Or | Op::Xor), l, r) = e else {
        return None;
    };
    if !l.is_float() && !r.is_float() {
        return None;
    }
    let (a, b) = (leaf(l)?, leaf(r)?);
    let v = match op {
        Op::And => a & b,
        Op::Or => a | b,
        Op::Xor => a ^ b,
        _ => return None,
    };
    match to {
        Ty::F32 => Some(u64::from(lo32(v))),
        Ty::F64 => Some(v),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => None,
    }
}

/// A float operation whose operands carry no float type, computed at `fb`.
///
/// A fixed-point conversion scales its register by a power of two before
/// rounding. The register's bits are the float; it has no float type of
/// its own, so the ordinary evaluator stops. The scale is exact at `fb`,
/// which is the width the conversion recorded. A float constant of a
/// different width is `None`, not a value read at the wrong width.
///
/// # Arguments
///
/// * `e` - The operation. Anything other than a float binary is `None`.
/// * `fb` - The width, 32 or 64.
/// * `leaf` - The bits of one operand.
pub(super) fn float_scale_at(
    e: &Expr,
    fb: u8,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    if !matches!(fb, 32 | 64) {
        return None;
    }
    let Expr::Bin(op, l, r) = e else {
        return None;
    };
    if !op.is_float() {
        return None;
    }
    let width_ok = |e: &Expr| !matches!(e, Expr::FConst(_, ty) if ty.bits() != fb);
    if !width_ok(l) || !width_ok(r) {
        return None;
    }
    float_arith(*op, float_of(leaf(l)?, fb), float_of(leaf(r)?, fb), fb)
}

/// Applies a float binary operator at the width its operands carry, as the
/// emulator computes it, and returns the result's bits.
///
/// A single's operation rounds its result to a single the way the
/// machine's `*ss` does, at the operation and not at the store, so a
/// quotient never rounds twice; a double's computes in a double. The
/// operands arrive as doubles over the same bits and narrow to `bits`
/// first, exactly for a value that width already holds.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - The left operand.
/// * `r` - The right operand.
/// * `bits` - The width both operands carry, 32 or 64.
///
/// # Returns
///
/// The result's bits, or `None` for an operator that is not a float one.
#[expect(
    clippy::cast_possible_truncation,
    reason = "narrowing a double to the single its operation computes in is the rounding itself"
)]
pub(super) fn float_arith(op: Op, l: f64, r: f64, bits: u8) -> Option<u64> {
    macro_rules! f {
        ($t:ty, $from:expr, $to:expr) => {{
            let (x, y): ($t, $t) = ($from(l), $from(r));
            let v: $t = match op {
                Op::FAdd => x + y,
                Op::FSub => x - y,
                Op::FMul => x * y,
                Op::FDiv => x / y,
                Op::FMin => {
                    if x < y {
                        x
                    } else {
                        y
                    }
                }
                Op::FMax => {
                    if x > y {
                        x
                    } else {
                        y
                    }
                }
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
                | Op::Rol(_)
                | Op::Ror(_)
                | Op::MulHi(_)
                | Op::SMulHi(_)
                | Op::SMulO(_)
                | Op::UAddO(_)
                | Op::USubO(_) => return None,
            };
            Some($to(v))
        }};
    }
    match bits {
        64 => f!(f64, |v: f64| v, f64::to_bits),
        _ => f!(f32, |v: f64| v as f32, |v: f32| u64::from(v.to_bits())),
    }
}

/// Applies a float unary operator at the width its operand carries, as
/// the emulator computes it, and returns the result's bits.
///
/// `fabs` clears the sign bit of the width, `sqrt` takes the square root
/// in the width's own arithmetic, so a single's root rounds to a single
/// the way the machine's `sqrtss` does.
///
/// # Arguments
///
/// * `op` - The operator, [`UnOp::Sqrt`] or [`UnOp::Fabs`].
/// * `v` - The operand's bits.
/// * `bits` - The width the operand carries, 32 or 64.
///
/// # Returns
///
/// The result's bits, or `None` for an operator that is not a float one.
pub(super) fn float_un(op: UnOp, v: u64, bits: u8) -> Option<u64> {
    match op {
        UnOp::Fabs => Some(v & !(1u64 << (u32::from(bits) - 1))),
        UnOp::Sqrt => match bits {
            64 => Some(f64::from_bits(v).sqrt().to_bits()),
            _ => Some(u64::from(f32::from_bits(lo32(v)).sqrt().to_bits())),
        },
        UnOp::Neg
        | UnOp::Not
        | UnOp::Bswap
        | UnOp::Tzcnt
        | UnOp::Lzcnt
        | UnOp::Popcnt
        | UnOp::Bsf
        | UnOp::Bsr => None,
    }
}

/// The integer a float cast converts, and whether that integer is signed.
///
/// A sign extension is signed, including from a full 64-bit register,
/// which [`sext`] does not re-extend. Anything else is the unsigned value
/// of its bits: an unsigned conversion masks a narrower source first, so
/// the high bit of a 32-bit value is already clear.
///
/// # Arguments
///
/// * `inner` - The cast's operand.
/// * `eval` - The bits of one subexpression.
pub(super) fn cast_integer(
    inner: &Expr,
    mut eval: impl FnMut(&Expr) -> Option<u64>,
) -> Option<(u64, bool)> {
    match inner {
        Expr::Sext(x, bits) => {
            let v = eval(x)?;
            let v = if *bits >= 64 { v } else { sext(v, *bits)? };
            Some((v, true))
        }
        other => Some((eval(other)?, false)),
    }
}

/// An integer rounded to `to`, the way `scvtf` and `ucvtf` do.
///
/// The value becomes a double first and a single narrows that double.
/// For an integer that is the same rounding as a direct conversion to a
/// single, and it is the rounding the fixed-point form divides before.
///
/// # Arguments
///
/// * `v` - The integer's bits, already sign-extended when `signed`.
/// * `signed` - Whether those bits are signed.
/// * `to` - The float written. Anything else returns `v`.
#[expect(
    clippy::cast_precision_loss,
    reason = "an integer converted to a float rounds, as the conversion does"
)]
pub(super) fn integer_to_float(v: u64, signed: bool, to: Ty) -> u64 {
    let wide = if signed {
        v.cast_signed() as f64
    } else {
        v as f64
    };
    match to {
        Ty::F32 => {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "narrowing the double to a single is the conversion's last rounding"
            )]
            let n = wide as f32;
            u64::from(n.to_bits())
        }
        Ty::F64 => wide.to_bits(),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => v,
    }
}

/// Converts a float's bits to the width a store gives it, rounding a
/// double to a single as an x87 store to a single does.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `from` - Its width, or `None` for an integer.
/// * `to` - The type stored.
#[expect(
    clippy::cast_possible_truncation,
    reason = "rounding a double to a single is the conversion the store makes"
)]
pub(super) fn convert_float(v: u64, from: Option<u8>, to: Ty) -> u64 {
    match (from, to) {
        (Some(64), Ty::F32) => u64::from((f64::from_bits(v) as f32).to_bits()),
        (Some(32), Ty::F64) => f64::from(f32::from_bits(lo32(v))).to_bits(),
        _ => v,
    }
}

/// Tells whether a value the emulator left and a lifted one agree.
///
/// Equal in the low `bits`, or, for a float, both NaNs: the x87 load the
/// emulator models quiets a signaling NaN the lifter copies as it is.
///
/// # Arguments
///
/// * `a` - One value.
/// * `b` - The other.
/// * `bits` - The width compared.
/// * `float` - Whether the value is a float.
pub(super) fn agree(a: u64, b: u64, bits: u8, float: bool) -> bool {
    let nan = |v: u64| match bits {
        32 => f32::from_bits(lo32(v)).is_nan(),
        64 => f64::from_bits(v).is_nan(),
        _ => false,
    };
    (a ^ b) & low(bits) == 0 || (float && nan(a) && nan(b))
}

/// Converts a float's bits to an integer the way `cvttss2si` does: toward
/// zero, and to the integer indefinite (the most negative value) when the
/// float is a NaN or does not fit.
///
/// A 32-bit or 64-bit destination uses that signed range. An 8-bit or
/// 16-bit destination uses its own: `fist` and `fisttp` of a word store
/// the indefinite integer there, not the low bits of a wider conversion.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width, 32 or 64.
/// * `bits` - The integer's width.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    reason = "the range checks guarantee the truncated float fits the integer, and the bound is a power of two"
)]
pub(super) fn float_to_int(v: u64, fb: u8, bits: u8) -> u64 {
    let f = float_of(v, fb).trunc();
    if matches!(bits, 8 | 16) {
        let shift = u32::from(bits) - 1;
        let top = (1u64 << shift) as f64;
        if f.is_nan() || f < -top || f >= top {
            return 1u64 << shift;
        }
        return (f as i64).cast_unsigned() & low(bits);
    }
    if bits <= 32 {
        if f.is_nan() || !(-2_147_483_648.0..=2_147_483_647.0).contains(&f) {
            return 0x8000_0000;
        }
        (f as i32).cast_unsigned().into()
    } else {
        if f.is_nan() || !(-9_223_372_036_854_775_808.0..9_223_372_036_854_775_808.0).contains(&f) {
            return 0x8000_0000_0000_0000;
        }
        (f as i64).cast_unsigned()
    }
}
