//! The selects [`super::ternary`] reads as something else: an `abs`, a
//! signed remainder, and the arms a select on the same condition decides.

use super::{Cond, ConditionCode, Expr, Flags, Helper, Op, UnOp, const_of};

/// Returns the operation a select computes, when it is one this module
/// reads: an `abs` ([`absolute`]) or a signed remainder ([`signed_power_remainder`]).
///
/// # Arguments
///
/// * `cond` - The condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
///
/// # Returns
///
/// The operation, or `None` when the select is none of them.
pub(super) fn known_select(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    absolute(cond, a, b).or_else(|| signed_power_remainder(cond, a, b))
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

/// Reverses a signed remainder by a power of two taken through the
/// magnitude.
///
/// GCC writes `x % 2^k` on ARM as the low bits of `x`, or the negated low
/// bits of `-x` when `-x` is not negative: `rsbs r2, r3, #0; and r3, r3,
/// #m; and r2, r2, #m; it pl; rsbpl r3, r2, #0` lifts as `-x >= 0 ? -(-x &
/// m) : x & m` with `m = 2^k - 1` (arm64's `negs; and; and; csneg ..., mi`
/// is the same select with the arms swapped). `-x` has its sign clear for
/// every `x` from `INT_MIN + 1` to 0, where the negated low bits of the
/// magnitude are the remainder; for a positive `x` the low bits are, and
/// `INT_MIN`, whose negation keeps its sign, has low bits and remainder 0.
///
/// # Arguments
///
/// * `cond` - The condition, the sign of `0 - x`.
/// * `a` - Value when true.
/// * `b` - Value when false.
///
/// # Returns
///
/// `x % 2^k`, the 32-bit `x` read through its sign extension, or `None`
/// when the select is not that shape.
fn signed_power_remainder(cond: &Cond, a: &Expr, b: &Expr) -> Option<Expr> {
    let Flags::Cmp(Expr::Const(0), x, bits @ (32 | 64)) = &cond.flags else {
        return None;
    };
    let (neg, pos) = match cond.cc.0 {
        ConditionCode::ns => (a, b),
        ConditionCode::s => (b, a),
        _ => return None,
    };
    let negated = |e: &Expr| match e {
        Expr::Un(UnOp::Neg, v) => Some(v.as_ref().clone()),
        Expr::Bin(Op::Sub, z, v) if matches!(**z, Expr::Const(0)) => Some(v.as_ref().clone()),
        _ => None,
    };
    let (Expr::Bin(Op::And, px, pm), Expr::Bin(Op::And, nx, nm)) = (pos, &negated(neg)?) else {
        return None;
    };
    let m = const_of(pm)?;
    let d = m.checked_add(1).filter(|d| d.is_power_of_two() && *d > 1)?;
    if px.as_ref() != x || negated(nx).as_ref() != Some(x) || const_of(nm) != Some(m) {
        return None;
    }
    if d >= 1u64 << (bits - 1) {
        return None;
    }
    let dividend = if *bits == 32 {
        Expr::Sext(Box::new(x.clone()), 32)
    } else {
        x.clone()
    };
    Some(Expr::Bin(
        Op::SRem,
        Box::new(dividend),
        Box::new(Expr::Const(d)),
    ))
}

/// Returns one arm of a select with the selects inside it on the same
/// condition decided.
///
/// On the side where `cond` is `holds`, a select on `cond` takes its
/// matching side and one on the inverse its other side.
///
/// `ite ne; movne r3, #1; moveq r3, #0` lifts as `eq ? 0 : (ne ? 1 : r3)`,
/// whose inner `r3` is never read; `ite eq; biceq; orrne` as `ne ? (eq ?
/// x & ~k : x) | k : (eq ? x & ~k : x)`, whose arms are `x | k` and `x &
/// ~k`. Selects are looked for through operators, extensions and casts.
///
/// Two conditions are the same test only when their flags name the values
/// they were set from: every [`Flags`] variant holds those values, so equal
/// flags are flags of equal values, except [`Flags::Unknown`], which holds
/// nothing and stands for any flags at all. A condition on unknown flags
/// decides nothing.
///
/// # Arguments
///
/// * `cond` - The outer condition.
/// * `holds` - Whether `cond` is true on the arm's side.
/// * `arm` - The arm.
///
/// # Returns
///
/// The arm with those selects replaced by their taken sides.
pub(super) fn arm_under(cond: &Cond, holds: bool, arm: Expr) -> Expr {
    let inverse = cond.invert();
    if matches!(cond.flags, Flags::Unknown) || inverse == *cond {
        return arm;
    }
    let down = |e: Box<Expr>| Box::new(arm_under(cond, holds, *e));
    match arm {
        Expr::Ternary(c, t, f) if *c == *cond => arm_under(cond, holds, *if holds { t } else { f }),
        Expr::Ternary(c, t, f) if *c == inverse => {
            arm_under(cond, holds, *if holds { f } else { t })
        }
        Expr::Ternary(c, t, f) => Expr::Ternary(c, down(t), down(f)),
        Expr::Bin(op, l, r) => Expr::Bin(op, down(l), down(r)),
        Expr::Un(op, e) => Expr::Un(op, down(e)),
        Expr::Sext(e, b) => Expr::Sext(down(e), b),
        Expr::Cast(e, t) => Expr::Cast(down(e), t),
        other => other,
    }
}
