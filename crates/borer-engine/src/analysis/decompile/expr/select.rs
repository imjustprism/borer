//! The selects [`super::ternary`] reads as something else: an `abs`, and
//! the arms a select on the same condition decides.

use super::{Cond, ConditionCode, Expr, Flags, Helper, UnOp};

/// Returns the operation a select computes, when it is one this module
/// reads: an `abs` ([`absolute`]).
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
    absolute(cond, a, b)
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
    if inverse == *cond {
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
