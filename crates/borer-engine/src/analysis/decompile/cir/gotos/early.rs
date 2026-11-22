//! The fold's rule that turns a long `if` followed by a short tail that
//! leaves into an early exit ([`flattens`]).

use super::super::wrap::weighs;
use super::super::{Else, Stmt, StmtKind};
use super::{Facts, calls_out, ends, idle, negate, stops};

/// Shortest `if` body, in printed lines, worth turning into an early exit.
const EARLY_EXIT_MIN: usize = 4;

/// Most statements a tail moved into an early exit may hold.
const EARLY_TAIL_MAX: usize = 3;

/// Turns a long `if` followed by a short tail that leaves into an early
/// exit with the body at the same level.
///
/// `if (c) { BODY } TAIL` is `if (!c) { TAIL } BODY` when `BODY` ends in a
/// `return`, `goto`, `break` or `continue` and `TAIL` is at most
/// [`EARLY_TAIL_MAX`] plain statements, the last one control never runs
/// past ([`stops`]): a `return`, `break` or `continue`, or a call the
/// binary never returns from that ends its block. A compare ladder nesting
/// once per compare becomes a run of early returns. A `BODY` that ends in
/// a call that never returns stays: it already reads as the guard of an
/// error path, as the source writes one.
///
/// When control plainly runs off `BODY`'s end ([`completes`], and [`ends`]
/// does not prove otherwise), `BODY` does not end in a call, and `TAIL`
/// ends in a call that never returns, `TAIL` is copied
/// to `BODY`'s end first: `if (c) { BODY } TAIL` is
/// `if (!c) { TAIL } BODY TAIL`, the error path a compiler laid out once
/// for several checks written as a guard per check, as the source did.
/// Each copy runs on exactly the paths that reached `TAIL` before (falling
/// off `BODY`'s end, or `c` failing), and nothing runs after the call, so
/// no path gains or loses a statement. The call counts only on evidence
/// the engine has, the facts' blocks that end in a call that never
/// returns ([`crate::analysis::functions::call_ends_path`]: a callee or
/// import known never to return by name or by discovery, glibc's `error`
/// with a nonzero status, or the call followed by padding or another
/// function's entry), never the stack protector's failure call; a call
/// not proven so leaves the text as it was. A tail that returns is not
/// copied: whether the source wrote one exit or several is not in the
/// binary. A `BODY` that ends in a call falls into `TAIL` right after that
/// call, often one that never returns though no fact shows it, and a copy
/// behind it would only repeat the error path.
///
/// Bodies shorter than [`EARLY_EXIT_MIN`] lines keep the natural form, and
/// since a tail is shorter than that, a guard is never turned back.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `f` - The facts: which blocks end in a call that never returns.
///
/// # Returns
///
/// Whether an `if` was turned.
pub(super) fn flattens(list: &mut Vec<Stmt>, f: &Facts<'_>) -> bool {
    for k in 0..list.len() {
        let StmtKind::If {
            cond,
            then,
            other: None,
        } = &list[k].kind
        else {
            continue;
        };
        if !weighs(then, EARLY_EXIT_MIN, &|s| {
            usize::from(!idle(s))
                + usize::from(matches!(
                    s.kind,
                    StmtKind::If { .. }
                        | StmtKind::While { .. }
                        | StmtKind::DoWhile { .. }
                        | StmtKind::For { .. }
                        | StmtKind::Switch { .. }
                        | StmtKind::Block(_)
                        | StmtKind::Try { .. }
                ))
        }) {
            continue;
        }
        let tail = list[k + 1..]
            .iter()
            .take(EARLY_TAIL_MAX)
            .take_while(|s| {
                matches!(
                    s.kind,
                    StmtKind::Expr(_) | StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue
                )
            })
            .enumerate()
            .find(|&(n, _)| stops(list, k + 1 + n, f));
        let Some((n, last)) = tail else {
            continue;
        };
        let fatal = matches!(last.kind, StmtKind::Expr(_));
        let closing = then.iter().rfind(|s| !idle(s)).map(|s| &s.kind);
        let copied = !matches!(
            closing,
            Some(StmtKind::Return(_) | StmtKind::Goto(_) | StmtKind::Break | StmtKind::Continue)
        );
        let called = matches!(closing, Some(StmtKind::Expr(e)) if calls_out(e));
        if copied && (!fatal || called || !completes(then) || ends(then, f)) {
            continue;
        }
        let end = k + 2 + n;
        let cond = negate(cond);
        let tail: Vec<Stmt> = list.drain(k + 1..end).collect();
        let mut body = Vec::new();
        if let StmtKind::If { cond: c, then, .. } = &mut list[k].kind {
            *c = cond;
            if copied {
                then.extend_from_slice(&tail);
            }
            body = std::mem::replace(then, tail);
        }
        list.splice(k + 1..k + 1, body);
        return true;
    }
    false
}

/// Tells whether control plainly runs off the end of a list: it is empty,
/// or its last statement is an expression, an `if` with no `else`, an
/// `if` with an arm that runs off its end, or a block that does.
///
/// Any other last statement, a loop, a `switch`, a jump, a raw line or a
/// guarded region, says no: whether control leaves it at its end is not
/// shown here, and [`ends`] proves only the other way.
///
/// # Arguments
///
/// * `list` - The statements.
fn completes(list: &[Stmt]) -> bool {
    let Some(s) = list.iter().rfind(|s| !idle(s)) else {
        return true;
    };
    if let StmtKind::Block(b) = &s.kind {
        return completes(b);
    }
    if let StmtKind::If {
        then,
        other: Some(other),
        ..
    } = &s.kind
    {
        return completes(then)
            || match other {
                Else::Block(b) => completes(b),
                Else::If(next) => completes(std::slice::from_ref(next)),
            };
    }
    matches!(s.kind, StmtKind::Expr(_) | StmtKind::If { other: None, .. })
}
