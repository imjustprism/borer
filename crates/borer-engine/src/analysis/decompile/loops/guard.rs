//! A guarded loop whose guard is its own test on entry, decided on the
//! values rather than their spelling ([`guarded_loops`]).

use super::super::ctext::{Ast, Bin, CTy, Un};
use super::entry::{RUN_MAX, assignment, step, sweep};
use super::linear::{Declared, Eval, Lin, children, read};
use super::*;
use crate::analysis::protos::local_depth;

/// Writes each `if (G) { inits; do { B } while (C); }` of a function whose
/// guard is the loop's test after the inits as a `while` or a `for`
/// ([`proved`]).
///
/// It runs after the decided-entry rewrite, on the split variables and
/// their declarations, which give the decision its widths.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `word` - The image's word in bits (32 or 64).
///
/// # Returns
///
/// The text with those loops rewritten.
pub(in crate::analysis::decompile) fn guarded_loops(text: String, word: u8) -> String {
    sweep(text, |lines, k, declared| proved(lines, k, word, declared))
}

/// Rewrites the guarded loop at line `k` when its guard and its test after
/// the inits are one test.
///
/// `if (G) { inits; do { B } while (C); }` and `inits; while (C) { B }` run
/// the same statements whenever `G` holds exactly when `C` does after the
/// inits ran ([`Eval::pred`], [`super::linear::Pred::same`]), and the inits
/// leave the same values on the path that skips the loop: each init's
/// variable is dead there ([`dead_after`]) or the line in front of the `if`
/// gives it the same literal, and no init reads memory the guard did not
/// ([`hoistable`]). With `v`'s step ending `B` ([`step`]), the loop is a
/// `for` on `v`. One more form: `if (a < b) { v = a; do { B; v += 1; }
/// while (v != b); }` walks `v` from `a` up to `b` one at a time, so its
/// test is `v < b` ([`exit_bound`]). Anything undecided stays as it is.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
/// * `word` - The image's word in bits.
/// * `declared` - The declarations looked up so far.
///
/// # Returns
///
/// Whether the `if` became a `while` or a `for`.
fn proved(lines: &mut Vec<String>, k: usize, word: u8, declared: &mut Declared) -> bool {
    let Some(parts) = guarded_parts(lines, k) else {
        return false;
    };
    let (pad, close, cond) = (parts.pad, parts.close, &parts.cond);
    let inits = lines.get(k + 1..parts.d).unwrap_or(&[]);
    let body = lines.get(parts.d + 1..parts.latch).unwrap_or(&[]);
    if inits.len() > RUN_MAX {
        return false;
    }
    let (Some(parsed), Some(steps), Some(g), Some(c)) = (
        guarded_inits(inits, pad + 2),
        inits
            .iter()
            .map(|l| assignment(l, word))
            .collect::<Option<Vec<Ast>>>(),
        read(&parts.guard, word),
        read(cond, word),
    ) else {
        return false;
    };
    let distinct = parsed
        .iter()
        .enumerate()
        .all(|(i, (t, _))| parsed.iter().skip(i + 1).all(|(u, _)| u != t));
    let aliased = parsed.iter().any(|(t, _)| {
        let amp = format!("&{t}");
        local_depth(t).is_some()
            && lines
                .iter()
                .any(|l| l.contains(&amp) && takes_address(l, t))
    });
    if !distinct || aliased || !hoistable(lines, &parsed, &parts.guard) {
        return false;
    }
    let counted = parsed.iter().enumerate().rev().find_map(|(at, (v, _))| {
        let (idx, step) = mentions_ident(cond, v)
            .then(|| step(body, pad + 2, v))
            .flatten()?;
        Some(Counted { at, idx, step })
    });
    let mut eval = Eval::new(lines, word, declared, true);
    let before = eval.pred(&g);
    let bounds = order_bounds(&mut eval, &g);
    for s in &steps {
        eval.assign(s);
    }
    let same = before.zip(eval.pred(&c)).is_some_and(|(p, q)| p.same(&q));
    let head = if same {
        Some(cond.clone())
    } else {
        counted.as_ref().and_then(|n| {
            let (v, _) = parsed.get(n.at)?;
            exit_bound(
                &mut eval,
                bounds.as_ref()?,
                (&c, cond),
                (v, n.idx, &n.step),
                (body, lines),
            )
        })
    };
    let kept = parsed
        .iter()
        .all(|(t, r)| dead_after(lines, close + 1, pad, t) || same_before(lines, k, pad, t, r));
    let counted = counted.filter(|n| apart(&parsed, n.at));
    let Some(head) = head.filter(|h| kept && (h == cond || counted.is_some())) else {
        return false;
    };
    let last = parsed
        .iter()
        .rposition(|(v, _)| mentions_ident(cond, v))
        .filter(|&at| apart(&parsed, at));
    let out = guarded_lines(&parts, inits, body, (&parsed, counted, last), &head);
    lines.splice(k..=close, out);
    true
}

/// Tells whether the line in front of the `if` at line `k` gives `t` the
/// literal `value` the `if`'s init gives it, so the path that skips the
/// loop leaves it the same.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
/// * `pad` - The `if`'s indentation.
/// * `t` - The variable.
/// * `value` - The init's value.
fn same_before(lines: &[String], k: usize, pad: usize, t: &str, value: &str) -> bool {
    parse_const(value).is_some()
        && k.checked_sub(1)
            .and_then(|j| lines.get(j))
            .filter(|l| indent_of(l) == pad)
            .and_then(|l| plain_assignment(l))
            == Some((t, value))
}

/// The sides of a guard `a < b`, at the type they meet at.
#[derive(Debug, Clone)]
struct Bounds {
    /// The lower side.
    low: Lin,
    /// The upper side.
    high: Lin,
    /// The type both meet at.
    ty: CTy,
}

/// Returns the sides of a guard `a < b` (or `b > a`), before the inits run.
///
/// # Arguments
///
/// * `eval` - The evaluator, nothing assigned yet.
/// * `g` - The guard.
///
/// # Returns
///
/// The sides, `None` for any other guard.
fn order_bounds(eval: &mut Eval<'_>, g: &Ast) -> Option<Bounds> {
    let (a, b) = match g {
        Ast::Bin(Bin::Lt, a, b) | Ast::Bin(Bin::Gt, b, a) => (&**a, &**b),
        _ => return None,
    };
    let (a, b) = (eval.value(a)?, eval.value(b)?);
    let ty = eval.common(a.ty, b.ty);
    Some(Bounds {
        low: eval.convert(a, ty)?.lin,
        high: eval.convert(b, ty)?.lin,
        ty,
    })
}

/// Returns the header test of the exit-test form, `if (a < b) { v = a; do
/// { B; v += 1; } while (v != b); }`: `v < b`.
///
/// `v` takes `a, a + 1, ..` and the loop leaves at `b`, so `v < b` and `v
/// != b` agree at every test when `a < b`, `v` is an integer (or a pointer
/// to bytes) stepping by one at the guard's width and signedness, is
/// written nowhere else, and nothing in `B` changes `b`: its names are
/// written nowhere in `B`, no address reaches them and it reads no memory.
///
/// # Arguments
///
/// * `eval` - The evaluator, the inits run.
/// * `bounds` - The guard's sides ([`order_bounds`]).
/// * `(c, text)` - The loop's test, as read and as written.
/// * `(v, idx, step)` - The counted variable, its step's line in the body
///   and the step's text.
/// * `(body, lines)` - The loop body's lines and the function's, for the
///   addresses taken.
///
/// # Returns
///
/// The header test, `None` when the loop is not of this form.
fn exit_bound(
    eval: &mut Eval<'_>,
    bounds: &Bounds,
    (c, text): (&Ast, &str),
    (v, idx, step): (&str, usize, &str),
    (body, lines): (&[String], &[String]),
) -> Option<String> {
    let bound = match c {
        Ast::Bin(Bin::Ne, x, y) | Ast::Bin(Bin::Ne, y, x) if **x == Ast::Name(v.to_owned()) => &**y,
        _ => return None,
    };
    let w = eval.bits(bounds.ty)?;
    let tv = eval.type_of(v)?;
    let bytes = tv.pointee().map_or(Some(1), |p| p.size(64)) == Some(1);
    let first = eval.value(&Ast::Name(v.to_owned()))?;
    let end = eval.value(bound)?;
    let latch = eval.common(tv, end.ty);
    let typed = bytes
        && eval.bits(tv) == Some(w)
        && tv.signed() == bounds.ty.signed()
        && latch == bounds.ty;
    let walks = typed
        && eval.convert(first, bounds.ty)?.lin.same(&bounds.low)
        && eval.convert(end, bounds.ty)?.lin.same(&bounds.high);
    let names = names_of(bound)?;
    let still = [format!("{v} += 1"), format!("{v} = {v} + 1")]
        .iter()
        .any(|s| s == step)
        && body
            .iter()
            .enumerate()
            .all(|(i, l)| i == idx || !writes_var(l.trim(), v))
        && names
            .iter()
            .all(|n| body.iter().all(|l| !writes_var(l.trim(), n)))
        && names
            .iter()
            .chain(std::iter::once(&v))
            .all(|n| lines.iter().all(|l| !takes_address(l, n)));
    if !walks || !still {
        return None;
    }
    let spelled = text
        .strip_prefix(&format!("{v} != "))
        .or_else(|| text.strip_suffix(&format!(" != {v}")))?;
    let loose = matches!(bound, Ast::Bin(op, ..) if op.compares() || matches!(op, Bin::And | Bin::Xor | Bin::Or))
        || matches!(bound, Ast::Logic(..));
    Some(if loose {
        format!("{v} < ({spelled})")
    } else {
        format!("{v} < {spelled}")
    })
}

/// Returns the names a loop bound reads, when it reads no memory and calls
/// nothing.
///
/// # Arguments
///
/// * `e` - The bound.
///
/// # Returns
///
/// The names, `None` when the bound reads memory or calls.
fn names_of(e: &Ast) -> Option<Vec<&str>> {
    let mut out = Vec::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        match x {
            Ast::Name(n) => out.push(n.as_str()),
            Ast::Int(..) | Ast::Cast(..) | Ast::Bin(..) | Ast::Logic(..) => {
                stack.extend(children(x));
            }
            Ast::Un(op, _) if !matches!(op, Un::Deref | Un::Addr) => {
                stack.extend(children(x));
            }
            Ast::Un(..)
            | Ast::Float(..)
            | Ast::Str(_)
            | Ast::Pick(..)
            | Ast::Call(..)
            | Ast::Index(..)
            | Ast::Arrow(..)
            | Ast::Assign(..)
            | Ast::Step(..) => return None,
        }
    }
    Some(out)
}
