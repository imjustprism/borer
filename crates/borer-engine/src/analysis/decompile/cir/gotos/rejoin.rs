//! The fold's rule that rejoins the arms of an `if`/`else if` chain
//! running one body into one test ([`rejoins`]).

use super::super::{BinOp, Else, Expr, ExprKind, Stmt, StmtKind};
use super::{idle, negate};

/// Rejoins the arms of an `if`/`else if` chain that run one body.
///
/// A short-circuit test whose two ways lead to one block reads back as two
/// arms each holding that block: `if (a) { X } else if (b) { X }` is `if (a
/// || b) { X }`, and `if (a) { X } else if (b) { Y } else { X }` is `if (a
/// || !b) { X } else { Y }`. Either way each test runs only when the ones
/// before it failed, so a run does the same.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any chain was rejoined.
pub(super) fn rejoins(list: &mut [Stmt]) -> bool {
    let mut changed = false;
    for s in list.iter_mut() {
        while rejoin(s) {
            changed = true;
        }
    }
    changed
}

/// Rejoins the first two arms of one chain, as [`rejoins`] says.
///
/// # Arguments
///
/// * `s` - The statement.
///
/// # Returns
///
/// Whether it was an `if` whose arms were rejoined.
fn rejoin(s: &mut Stmt) -> bool {
    let StmtKind::If { cond, then, other } = &mut s.kind else {
        return false;
    };
    let joined = match other {
        Some(Else::If(next)) => match &mut next.kind {
            StmtKind::If {
                cond: second,
                then: body,
                other: rest,
            } => {
                if same(then, body) {
                    Some((either(cond, second), rest.take()))
                } else if let Some(Else::Block(last)) = rest
                    && same(then, last)
                {
                    let body = std::mem::take(body);
                    Some((either(cond, &negate(second)), Some(arm_of(body))))
                } else {
                    None
                }
            }
            _ => None,
        },
        Some(Else::Block(_)) | None => None,
    };
    let Some((joined, rest)) = joined else {
        return false;
    };
    *cond = joined;
    *other = rest;
    true
}

/// Tells whether two lists of statements do something and print alike.
///
/// # Arguments
///
/// * `a` - One list.
/// * `b` - The other.
fn same(a: &[Stmt], b: &[Stmt]) -> bool {
    let text = |list: &[Stmt]| {
        let mut out = String::new();
        super::super::print::stmts(list, 0, &mut out);
        out
    };
    a.iter().any(|s| !idle(s)) && text(a) == text(b)
}

/// Returns `a || b`, a side in parentheses unless it binds tighter than
/// `||`: an `&&`, a choice, an assignment and text the builder kept as
/// spelled are grouped.
///
/// # Arguments
///
/// * `a` - The test tried first.
/// * `b` - The test tried when it fails.
fn either(a: &Expr, b: &Expr) -> Expr {
    let side = |e: &Expr| {
        let loose = match &e.kind {
            ExprKind::Binary(op, ..) => matches!(op, BinOp::And),
            ExprKind::Cond(..) | ExprKind::Assign(..) | ExprKind::Raw(_) => true,
            ExprKind::Lit(_)
            | ExprKind::Name(_)
            | ExprKind::Unary(..)
            | ExprKind::Postfix(..)
            | ExprKind::Cast(..)
            | ExprKind::Call(..)
            | ExprKind::Index(..)
            | ExprKind::Member { .. }
            | ExprKind::Paren(_) => false,
        };
        if loose {
            Expr {
                kind: ExprKind::Paren(Box::new(e.clone())),
                ty: None,
                prov: e.prov,
            }
        } else {
            e.clone()
        }
    };
    Expr {
        kind: ExprKind::Binary(BinOp::Or, Box::new(side(a)), Box::new(side(b))),
        ty: None,
        prov: a.prov,
    }
}

/// Returns the `else` that runs a list: an `else if` when the list is one
/// `if`, else a block.
///
/// # Arguments
///
/// * `body` - The statements.
fn arm_of(mut body: Vec<Stmt>) -> Else {
    match body.pop() {
        Some(only) if body.is_empty() && matches!(only.kind, StmtKind::If { .. }) => {
            Else::If(Box::new(only))
        }
        Some(last) => {
            body.push(last);
            Else::Block(body)
        }
        None => Else::Block(body),
    }
}
