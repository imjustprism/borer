//! The conversions of a float toward zero into an integer that the
//! decompiler names as calls ([`RoundToInt`]).
//!
//! Arm's `fcvtzs` and `fcvtzu` and RISC-V's `fcvt` with `rtz` differ in
//! what a NaN becomes.

use super::expr::{Expr, as_float, mask_bits};

/// Which `fcvtz` call a name is: the signedness, the integer width, and
/// what a NaN converts to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum RoundToInt {
    /// Toward zero into a signed integer of this width, a NaN 0 (arm).
    Signed(u8),
    /// Toward zero into an unsigned integer of this width, a NaN 0 (arm).
    Unsigned(u8),
    /// Toward zero into a signed integer of this width, a NaN the largest
    /// value (RISC-V `fcvt` with `rtz`).
    SignedNanMax(u8),
    /// Toward zero into an unsigned integer of this width, a NaN every bit
    /// set (RISC-V `fcvt` with `rtz`).
    UnsignedNanMax(u8),
}

/// Each conversion of [`RoundToInt`] and its printed name.
const ROUND_NAMES: [(RoundToInt, &str); 8] = [
    (RoundToInt::Signed(32), "fcvtzs32"),
    (RoundToInt::Signed(64), "fcvtzs64"),
    (RoundToInt::Unsigned(32), "fcvtzu32"),
    (RoundToInt::Unsigned(64), "fcvtzu64"),
    (RoundToInt::SignedNanMax(32), "fcvt_rtz_i32"),
    (RoundToInt::SignedNanMax(64), "fcvt_rtz_i64"),
    (RoundToInt::UnsignedNanMax(32), "fcvt_rtz_u32"),
    (RoundToInt::UnsignedNanMax(64), "fcvt_rtz_u64"),
];

impl RoundToInt {
    /// The conversion a call's name prints ([`ROUND_NAMES`]).
    ///
    /// # Arguments
    ///
    /// * `name` - The call's name.
    pub(super) fn parse(name: &str) -> Option<Self> {
        ROUND_NAMES
            .iter()
            .find(|(_, n)| *n == name)
            .map(|&(r, _)| r)
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

    /// The same conversion, a NaN converting to the largest value as
    /// RISC-V's does.
    pub(super) fn nan_max(self) -> Self {
        match self {
            Self::Signed(bits) | Self::SignedNanMax(bits) => Self::SignedNanMax(bits),
            Self::Unsigned(bits) | Self::UnsignedNanMax(bits) => Self::UnsignedNanMax(bits),
        }
    }

    /// The printed name, or `None` when the width is not 32 or 64.
    pub(super) fn name(self) -> Option<&'static str> {
        ROUND_NAMES
            .iter()
            .find(|(r, _)| *r == self)
            .map(|&(_, n)| n)
    }

    /// The integer's width in bits.
    pub(super) fn bits(self) -> u8 {
        match self {
            Self::Signed(bits)
            | Self::Unsigned(bits)
            | Self::SignedNanMax(bits)
            | Self::UnsignedNanMax(bits) => bits,
        }
    }

    /// Whether the integer is signed.
    pub(super) fn signed(self) -> bool {
        matches!(self, Self::Signed(_) | Self::SignedNanMax(_))
    }

    /// Converts `v`, a float of `fb` bits, as this operation.
    ///
    /// # Arguments
    ///
    /// * `v` - The float's bits.
    /// * `fb` - The float's width.
    pub(super) fn apply(self, v: u64, fb: u8) -> Option<u64> {
        let nan = as_float(v, fb)?.is_nan();
        match self {
            Self::SignedNanMax(bits) if nan => Some(mask_bits(bits) >> 1),
            Self::UnsignedNanMax(bits) if nan => Some(mask_bits(bits)),
            Self::Signed(bits) | Self::SignedNanMax(bits) => fcvtzs_bits(v, fb, bits),
            Self::Unsigned(bits) | Self::UnsignedNanMax(bits) => fcvtzu_bits(v, fb, bits),
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

#[cfg(test)]
mod tests {
    use super::super::expr::Expr;
    use super::{RoundToInt, fcvt_float_width, fcvtzs_bits, fcvtzu_bits};

    /// An unsigned conversion of a value in `[2^63, 2^64)` keeps that value.
    ///
    /// Casting the truncated float through `i64` saturates at the signed
    /// maximum, one binade early. The unsigned result is the value itself
    /// until `2^64`, and every bit set from there on. A NaN or a negative
    /// value is 0. The signed conversion still saturates at its own bound,
    /// including an exact `-2^63`.
    ///
    /// # Panics
    ///
    /// When a conversion differs.
    #[test]
    fn an_unsigned_conversion_keeps_the_binade_past_the_signed_maximum() {
        let zu = |bits: u64, fb: u8, width: u8| fcvtzu_bits(bits, fb, width);
        let zs = |bits: u64, fb: u8, width: u8| fcvtzs_bits(bits, fb, width);
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
        assert_eq!(RoundToInt::parse("fcvtzu"), None);
        assert_eq!(RoundToInt::parse("__fcvtzs64"), None);
        assert_eq!(
            RoundToInt::parse("fcvtzu64").and_then(|op| op.apply(two63, 64)),
            Some(0x8000_0000_0000_0000)
        );
        assert_eq!(fcvt_float_width(Some(&Expr::Const(16)), Some(64)), None);
        assert_eq!(fcvt_float_width(Some(&Expr::Const(32)), None), Some(32));
        assert_eq!(fcvt_float_width(None, Some(64)), Some(64));
    }

    /// RISC-V's conversion toward zero makes a NaN the largest value, and
    /// converts anything else as arm's does.
    ///
    /// # Panics
    ///
    /// When a conversion differs.
    #[test]
    fn a_risc_v_conversion_makes_a_nan_the_largest_value() {
        let nan = 0x7FF8_0000_0000_0000;
        let i32_max = RoundToInt::SignedNanMax(32);
        let u64_max = RoundToInt::UnsignedNanMax(64);
        assert_eq!(i32_max.apply(nan, 64), Some(0x7fff_ffff));
        assert_eq!(u64_max.apply(nan, 64), Some(u64::MAX));
        assert_eq!(i32_max.apply(0xC004_0000_0000_0000, 64), Some(0xffff_fffe));
        assert_eq!(RoundToInt::parse("fcvt_rtz_u64"), Some(u64_max));
        assert_eq!(RoundToInt::Signed(32).nan_max(), i32_max);
    }
}
