//! The values of the arm64 lifter's packed calls under a check's starting
//! state, for the evaluator [`super::verify::eval`].
//!
//! A packed call (`__bsl_16b(d, n, m)`) is a whole `v` register, wider
//! than the evaluator's 64-bit values, so it is computed here at 128 bits,
//! from operands read whole ([`wide`]), and the evaluator takes its low 64
//! bits, the lanes the check compares. The lane arithmetic the machine
//! shares ([`crate::emulate::a64`]) is called, not written again; what is
//! checked is that the lifter named the instruction with the operands and
//! the arrangement the machine ran it with.

use super::expr::{Expr, Key, Ty};
use super::verify::{Bench, State, eval, low};
use crate::emulate::a64::{Saturate, convert_lanes, lookup, narrow_lanes};
use crate::num::lo8;

/// The lane width and span an arrangement suffix names: `4s` is 32-bit
/// lanes over 128 bits.
///
/// # Arguments
///
/// * `arrangement` - The suffix.
///
/// # Returns
///
/// `(lane bits, span bits)`, or `None` for a suffix of no 64- or 128-bit
/// arrangement.
fn arrangement(arrangement: &str) -> Option<(u32, u32)> {
    let split = arrangement.find(|c: char| !c.is_ascii_digit())?;
    let count: u32 = arrangement.get(..split)?.parse().ok()?;
    let bits = match arrangement.get(split..)? {
        "b" => 8,
        "h" => 16,
        "s" => 32,
        "d" => 64,
        _ => return None,
    };
    let span = count.checked_mul(bits)?;
    matches!(span, 64 | 128).then_some((bits, span))
}

/// All ones in the low `bits` of a 128-bit value.
///
/// # Arguments
///
/// * `bits` - The width, 1 to 128.
fn ones(bits: u32) -> u128 {
    u128::MAX >> (128 - bits.min(128))
}

/// Evaluates an operand of a packed call at its whole width: a 128-bit
/// load or global, a temporary, a packed call, or a narrower value
/// zero-extended.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `st` - The starting state.
/// * `reads` - Where each memory read is recorded.
/// * `depth` - How much deeper the evaluation may go.
///
/// # Returns
///
/// The value, or `None` where the evaluator cannot read it.
pub(super) fn wide<M: Bench>(
    e: &Expr,
    st: &State<'_, M>,
    reads: &mut Vec<(u64, u64)>,
    depth: u8,
) -> Option<u128> {
    let d = depth.checked_sub(1)?;
    let at_rest = |at: u64, reads: &mut Vec<(u64, u64)>| {
        reads.push((at, 16));
        let bytes: Vec<u8> = (0..16).map(|k| st.byte(at.wrapping_add(k))).collect();
        Some(u128::from_le_bytes(bytes.try_into().ok()?))
    };
    match e {
        Expr::Deref(addr, Ty::U128) => {
            let at = eval(addr, st, reads, d)? & low(st.width);
            at_rest(at, reads)
        }
        Expr::Var(Key::Global(at, 128)) => at_rest(*at, reads),
        Expr::Var(Key::Tmp(id)) => wide(st.temps.get(id)?, st, reads, d),
        Expr::Call(name, args) => {
            packed(name, args, st, reads, d).or_else(|| eval(e, st, reads, d).map(u128::from))
        }
        _ => eval(e, st, reads, d).map(u128::from),
    }
}

/// Evaluates a packed call of the arm64 lifter at its whole width.
///
/// # Arguments
///
/// * `name` - The call's name, `__op_arrangement`.
/// * `args` - Its arguments.
/// * `st` - The starting state.
/// * `reads` - Where each memory read is recorded.
/// * `depth` - How much deeper the evaluation may go.
///
/// # Returns
///
/// The register's 128 bits, zero past the arrangement; `None` for a call
/// this does not compute, or an operand the evaluator cannot read.
pub(super) fn packed<M: Bench>(
    name: &str,
    args: &[Expr],
    st: &State<'_, M>,
    reads: &mut Vec<(u64, u64)>,
    depth: u8,
) -> Option<u128> {
    let d = depth.checked_sub(1)?;
    let (op, suffix) = name.strip_prefix("__")?.rsplit_once('_')?;
    let (bits, span) = arrangement(suffix)?;
    let mut val = |e: &Expr| wide(e, st, reads, d);
    let lane = ones(bits);
    let v = match (op, args) {
        ("dup", [x]) => {
            let one = val(x)? & lane;
            (0..span / bits).fold(0, |v, k| v | one << (k * bits))
        }
        ("ins", [dst, x, Expr::Const(k)]) => {
            let at = u32::try_from(*k).ok()?.checked_mul(bits)?;
            (val(dst)? & !(lane << at)) | ((val(x)? & lane) << at)
        }
        ("bsl", [dd, a, b]) => {
            let (dd, a, b) = (val(dd)?, val(a)?, val(b)?);
            (dd & a) | (!dd & b)
        }
        ("bit", [dd, a, b]) => {
            let (dd, a, b) = (val(dd)?, val(a)?, val(b)?);
            (a & b) | (dd & !b)
        }
        ("bif", [dd, a, b]) => {
            let (dd, a, b) = (val(dd)?, val(a)?, val(b)?);
            (a & !b) | (dd & b)
        }
        ("rbit", [x]) => u128::from_le_bytes(val(x)?.to_le_bytes().map(u8::reverse_bits)),
        ("cnt", [x]) => u128::from_le_bytes(
            val(x)?
                .to_le_bytes()
                .map(|b| lo8(u64::from(b.count_ones()))),
        ),
        ("tbl" | "tbx", [first, ..]) => {
            let (old, rest) = if op == "tbx" {
                (Some(val(first)?), args.get(1..)?)
            } else {
                (None, args)
            };
            let (index, tables) = rest.split_last()?;
            let mut table = Vec::with_capacity(64);
            for t in tables {
                table.extend(val(t)?.to_le_bytes());
            }
            lookup(&table, val(index)?, old, usize::try_from(span / 8).ok()?)
        }
        ("ld2" | "ld3" | "ld4", [blocks @ .., Expr::Const(k)]) => {
            let parts = blocks.iter().map(&mut val).collect::<Option<Vec<_>>>()?;
            let count = u32::try_from(parts.len()).ok()?;
            let lanes = span / bits;
            let k = u32::try_from(*k).ok()?;
            (0..lanes).fold(0, |v, e| {
                let g = e * count + k;
                let part = parts.get(usize::try_from(g / lanes).unwrap_or(usize::MAX));
                v | ((part.copied().unwrap_or(0) >> ((g % lanes) * bits)) & lane) << (e * bits)
            })
        }
        ("st2" | "st3" | "st4", [regs @ .., Expr::Const(j)]) => {
            let parts = regs.iter().map(&mut val).collect::<Option<Vec<_>>>()?;
            let count = u32::try_from(parts.len()).ok()?;
            let lanes = span / bits;
            let j = u32::try_from(*j).ok()?;
            (0..lanes).fold(0, |v, m| {
                let g = j * lanes + m;
                let part = parts.get(usize::try_from(g % count).unwrap_or(usize::MAX));
                v | ((part.copied().unwrap_or(0) >> ((g / count) * bits)) & lane) << (m * bits)
            })
        }
        ("scvtf" | "ucvtf", [x, rest @ ..]) => {
            let fbits = match rest {
                [] => 0,
                [Expr::Const(f)] => *f,
                _ => return None,
            };
            let lane = u16::try_from(bits).ok()?;
            let span = u16::try_from(span).ok()?;
            convert_lanes(val(x)?, op == "scvtf", lane, fbits, span)
        }
        (op, [rest @ .., Expr::Const(k)]) => {
            let (base, high) = op.strip_suffix('2').map_or((op, false), |b| (b, true));
            let (sat, rounded) = match base {
                "shrn" => (Saturate::Cut, false),
                "rshrn" => (Saturate::Cut, true),
                "sqshrn" => (Saturate::Signed, false),
                "sqrshrn" => (Saturate::Signed, true),
                "uqshrn" => (Saturate::Unsigned, false),
                "uqrshrn" => (Saturate::Unsigned, true),
                _ => return None,
            };
            let shift = u32::try_from(*k).ok()?;
            match (high, rest) {
                (false, [x]) => u128::from(narrow_lanes(val(x)?, bits, shift, sat, rounded)),
                (true, [dd, x]) => {
                    let half = narrow_lanes(val(x)?, bits, shift, sat, rounded);
                    (val(dd)? & u128::from(u64::MAX)) | (u128::from(half) << 64)
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    Some(v & ones(span))
}
