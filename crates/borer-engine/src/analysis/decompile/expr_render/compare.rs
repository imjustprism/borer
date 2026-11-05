//! Comparisons as C reads them: which side takes a signed or unsigned
//! cast, and which difference C computes in `int`.

use super::*;

/// Renders a comparison, casting both sides to the signed type when the
/// condition is signed.
///
/// A cast binds tighter than any binary operator, so non-atomic operands
/// are parenthesized; an operand already carrying an `(int64_t)` cast
/// takes no second one, and a negative constant an `int` holds is the
/// signed literal it prints as (`a1 < -12345`). An unsigned ordering of a sign-extended value
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
pub(super) fn compare(
    n: &Names<'_>,
    l: &Expr,
    r: &Expr,
    rel: &str,
    signed: bool,
    bits: u8,
) -> String {
    let cast = |e: &Expr| -> String {
        if signed && matches!(e, Expr::Const(_)) {
            let text = paren_compared(e, n, UNARY);
            if text
                .strip_prefix('-')
                .and_then(|m| m.parse::<u32>().ok())
                .is_some_and(|m| m <= 1 << 31)
            {
                return text;
            }
        }
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
pub(super) fn int_difference(e: &Expr) -> bool {
    let differs = match e {
        Expr::Bin(Op::Sub, ..) | Expr::Un(UnOp::Neg | UnOp::Not, _) => true,
        Expr::Bin(Op::Add, _, r) => {
            matches!(**r, Expr::Const(c) if negative_magnitude(c, 8).is_some() || negative_magnitude(c, 4).is_some())
        }
        _ => false,
    };
    differs && (c_narrow(e) == Some(Narrow::Int) || widened_difference(e))
}
