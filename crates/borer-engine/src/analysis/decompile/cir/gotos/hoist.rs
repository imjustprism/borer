//! The fold's rule that lifts the jump an `if`'s first arm ends with out
//! of the arm, past the run it skips ([`lifts`]).

use std::collections::BTreeSet;

use super::super::wrap::each;
use super::super::{BinOp, Else, Expr, ExprKind, Stmt, StmtKind, UnOp};
use super::{Cx, Facts, RUN_MAX, idle, labelled, larger, meetings, negate, run_to, sealed};

/// Lifts a guarded jump an `if`'s first arm ends with out of the arm.
///
/// `if (p) { A; if (q) goto L; } else { B } RUN L:` runs `RUN` unless `p`
/// held and then `q` did: it is `if (p) { A } else { B } if (!(p && q)) {
/// RUN }`. A vectorized loop's remainder leaves this shape: the wide loop
/// skips the narrow one when nothing is left for it, which the other path
/// always runs. The run is too long to copy into both arms ([`super::sinks`]
/// copies shorter ones), holds no label, and `p` and `q` read only names
/// and constants; `p` is read again after the arms, so its names are
/// parameters or variables in registers (`aN`, `varN`), which no store or
/// call can change, and no statement of the arms writes one, steps one,
/// takes its address or is a line the tree could not read.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
/// * `f` - The facts.
///
/// # Returns
///
/// Whether a jump was lifted.
pub(super) fn lifts(list: &mut Vec<Stmt>, cx: &Cx, f: &Facts<'_>) -> bool {
    let mut met = None;
    for k in 0..list.len() {
        let StmtKind::If {
            cond: p,
            then,
            other,
        } = &list[k].kind
        else {
            continue;
        };
        let Some(last) = then.iter().rposition(|s| !idle(s)) else {
            continue;
        };
        let StmtKind::Guard {
            cond: q,
            then: jump,
        } = &then[last].kind
        else {
            continue;
        };
        let StmtKind::Goto(l) = jump.kind else {
            continue;
        };
        let mut names = BTreeSet::new();
        visit(p, &mut |e| {
            if let ExprKind::Name(n) = &e.kind {
                names.insert(n.as_str().to_owned());
            }
        });
        let register = |n: &String| {
            ["a", "var"].iter().any(|lead| {
                n.strip_prefix(lead)
                    .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
            })
        };
        let arms = then[..last].iter().chain(else_arm(other.as_ref()));
        if !pure(p)
            || !pure(q)
            || !names.iter().all(register)
            || arms.into_iter().any(|s| touches(s, &names))
        {
            continue;
        }
        let met = met.get_or_insert_with(|| meetings(list));
        let Some(end) = run_to(list, met, k + 1, l, &cx.after) else {
            continue;
        };
        let run = &list[k + 1..end];
        if run.iter().all(idle) || larger(run, RUN_MAX) || labelled(run) || !sealed(run, f) {
            continue;
        }
        let paren = |e: &Expr| Expr {
            kind: ExprKind::Paren(Box::new(e.clone())),
            ty: None,
            prov: e.prov,
        };
        let both = Expr {
            kind: ExprKind::Binary(BinOp::And, Box::new(paren(p)), Box::new(paren(q))),
            ty: None,
            prov: p.prov,
        };
        let cond = negate(&both);
        let prov = list[k].prov;
        let run: Vec<Stmt> = list.drain(k + 1..end).collect();
        if let StmtKind::If { then, .. } = &mut list[k].kind {
            then.remove(last);
        }
        let lifted = StmtKind::If {
            cond,
            then: run,
            other: None,
        };
        list.insert(k + 1, Stmt { kind: lifted, prov });
        return true;
    }
    false
}

/// Returns the statements of an `else`: its block, or the `else if` that
/// is one statement.
///
/// # Arguments
///
/// * `other` - The `else`, when there is one.
fn else_arm(other: Option<&Else>) -> Vec<&Stmt> {
    match other {
        None => Vec::new(),
        Some(Else::Block(b)) => b.iter().collect(),
        Some(Else::If(next)) => vec![next.as_ref()],
    }
}

/// Tells whether an expression reads only names and constants through
/// operators that change nothing: no call, store, step or memory read.
///
/// # Arguments
///
/// * `e` - The expression.
fn pure(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Name(_) => true,
        ExprKind::Paren(x)
        | ExprKind::Cast(_, x)
        | ExprKind::Unary(UnOp::Neg | UnOp::Plus | UnOp::BitNot | UnOp::Not, x) => pure(x),
        ExprKind::Binary(_, a, b) => pure(a) && pure(b),
        ExprKind::Cond(a, b, c) => pure(a) && pure(b) && pure(c),
        ExprKind::Unary(..)
        | ExprKind::Postfix(..)
        | ExprKind::Assign(..)
        | ExprKind::Call(..)
        | ExprKind::Index(..)
        | ExprKind::Member { .. }
        | ExprKind::Raw(_) => false,
    }
}

/// Tells whether a statement, or one it holds, may change a name of
/// `names`, or let control in past the test that chose its arm.
///
/// That is a statement that writes a name, steps it, takes its address, a
/// line the tree could not read that may ([`raw_writes`]), a `try`, whose
/// handlers run at times the arms do not show, or a label, which a jump may
/// enter by. An instruction the lifter left as assembly assigns no name the
/// text gives a value.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `names` - The names.
fn touches(s: &Stmt, names: &BTreeSet<String>) -> bool {
    let mut hit = false;
    each(s, &mut |x| {
        let own: Vec<&Expr> = match &x.kind {
            StmtKind::Expr(e) | StmtKind::Return(Some(e)) => vec![e],
            StmtKind::If { cond, .. }
            | StmtKind::Guard { cond, .. }
            | StmtKind::While { cond, .. }
            | StmtKind::DoWhile { cond, .. } => vec![cond],
            StmtKind::For {
                init, cond, step, ..
            } => vec![init, cond, step],
            StmtKind::Switch { value, .. } => vec![value],
            StmtKind::Raw(text) => {
                hit |= names.iter().any(|n| raw_writes(text, n));
                Vec::new()
            }
            StmtKind::Label(_) | StmtKind::Try { .. } => {
                hit = true;
                Vec::new()
            }
            StmtKind::Return(None)
            | StmtKind::Asm(_)
            | StmtKind::Goto(_)
            | StmtKind::Break
            | StmtKind::Continue
            | StmtKind::Block(_)
            | StmtKind::Comment(_)
            | StmtKind::Blank => Vec::new(),
        };
        for e in own {
            visit(e, &mut |y| hit |= writes(y, names));
        }
    });
    hit
}

/// Tells whether an expression changes a name of `names` itself: assigns
/// it, steps it, takes its address, or is text the tree could not read
/// that may ([`raw_writes`]).
///
/// # Arguments
///
/// * `e` - The expression.
/// * `names` - The names.
fn writes(e: &Expr, names: &BTreeSet<String>) -> bool {
    let named = |x: &Expr| {
        let mut x = x;
        while let ExprKind::Paren(inner) = &x.kind {
            x = inner;
        }
        matches!(&x.kind, ExprKind::Name(n) if names.contains(n.as_str()))
    };
    match &e.kind {
        ExprKind::Assign(_, place, _)
        | ExprKind::Postfix(_, place)
        | ExprKind::Unary(UnOp::PreInc | UnOp::PreDec | UnOp::AddrOf, place) => named(place),
        ExprKind::Raw(text) => names.iter().any(|n| raw_writes(text, n)),
        ExprKind::Lit(_)
        | ExprKind::Name(_)
        | ExprKind::Unary(..)
        | ExprKind::Binary(..)
        | ExprKind::Cond(..)
        | ExprKind::Cast(..)
        | ExprKind::Call(..)
        | ExprKind::Index(..)
        | ExprKind::Member { .. }
        | ExprKind::Paren(_) => false,
    }
}

/// Calls `f` on an expression and every expression it holds, outermost
/// first.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `f` - The visitor.
fn visit(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Name(_) | ExprKind::Raw(_) => {}
        ExprKind::Unary(_, a)
        | ExprKind::Postfix(_, a)
        | ExprKind::Cast(_, a)
        | ExprKind::Paren(a)
        | ExprKind::Member { base: a, .. } => visit(a, f),
        ExprKind::Binary(_, a, b) | ExprKind::Assign(_, a, b) | ExprKind::Index(a, b) => {
            visit(a, f);
            visit(b, f);
        }
        ExprKind::Cond(a, b, c) => {
            visit(a, f);
            visit(b, f);
            visit(c, f);
        }
        ExprKind::Call(callee, args) => {
            visit(callee, f);
            for x in args {
                visit(x, f);
            }
        }
    }
}

/// Tells whether C text the tree could not read may change `name`.
///
/// The text, its comments taken out, writes the name when the word, past
/// any spaces and closing parentheses, is followed by an assignment (`=`,
/// not `==`, or a compound one) or a step, or, past spaces and opening
/// parentheses, preceded by a step or by `&` that is no `&&`.
///
/// # Arguments
///
/// * `text` - The text.
/// * `name` - The name, an identifier.
fn raw_writes(text: &str, name: &str) -> bool {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let mut plain = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("/*").into_iter().chain(rest.find("//")).min() {
        plain.push_str(&rest[..at]);
        plain.push(' ');
        rest = if rest[at..].starts_with("/*") {
            rest[at..]
                .find("*/")
                .map_or("", |end| &rest[at + end + 2..])
        } else {
            ""
        };
    }
    plain.push_str(rest);
    plain.match_indices(name).any(|(at, _)| {
        let before = plain[..at].trim_end_matches(|c: char| c.is_whitespace() || c == '(');
        let tail = &plain[at + name.len()..];
        let after = tail.trim_start_matches(|c: char| c.is_whitespace() || c == ')');
        if plain[..at].ends_with(word) || tail.starts_with(word) {
            return false;
        }
        let assigns = after.starts_with('=') && !after.starts_with("==");
        let compound = ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="]
            .iter()
            .any(|op| after.starts_with(op));
        let steps = |t: &str| t.starts_with("++") || t.starts_with("--");
        let address = before.ends_with('&') && !before.ends_with("&&");
        assigns
            || compound
            || steps(after)
            || before.ends_with("++")
            || before.ends_with("--")
            || address
    })
}
