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
/// parameters or variables in registers (`aN`, `varN`) whose address no
/// statement of the function takes ([`taken`]), which no store or call can
/// then change, and no statement of the arms writes one, steps one, takes
/// its address or is a line the tree could not read.
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
            || names.iter().any(|n| f.taken.contains(n))
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
        hit |= matches!(x.kind, StmtKind::Label(_) | StmtKind::Try { .. });
        if let StmtKind::Raw(text) = &x.kind {
            hit |= names.iter().any(|n| raw_writes(text, n));
        }
        for e in own(x) {
            visit(e, &mut |y| hit |= writes(y, names));
        }
    });
    hit
}

/// Adds to `out` the names a statement takes the address of: `&name` in
/// its tree, and every word a lone `&` is followed by in a line the tree
/// could not read ([`raw_taken`]).
///
/// # Arguments
///
/// * `x` - The statement; the statements inside it are not read.
/// * `out` - The names.
pub(super) fn taken(x: &Stmt, out: &mut BTreeSet<String>) {
    if let StmtKind::Raw(text) = &x.kind {
        raw_taken(text, out);
    }
    for e in own(x) {
        visit(e, &mut |y| {
            if let ExprKind::Raw(text) = &y.kind {
                raw_taken(text, out);
            } else if let ExprKind::Unary(UnOp::AddrOf, place) = &y.kind
                && let Some(n) = bare(place)
            {
                out.insert(n.to_owned());
            }
        });
    }
}

/// Returns the expressions a statement holds itself, not those of the
/// statements inside it.
///
/// # Arguments
///
/// * `x` - The statement.
fn own(x: &Stmt) -> Vec<&Expr> {
    match &x.kind {
        StmtKind::Expr(e) | StmtKind::Return(Some(e)) => vec![e],
        StmtKind::If { cond, .. }
        | StmtKind::Guard { cond, .. }
        | StmtKind::While { cond, .. }
        | StmtKind::DoWhile { cond, .. } => vec![cond],
        StmtKind::For {
            init, cond, step, ..
        } => vec![init, cond, step],
        StmtKind::Switch { value, .. } => vec![value],
        StmtKind::Raw(_)
        | StmtKind::Label(_)
        | StmtKind::Try { .. }
        | StmtKind::Return(None)
        | StmtKind::Asm(_)
        | StmtKind::Goto(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Block(_)
        | StmtKind::Comment(_)
        | StmtKind::Blank => Vec::new(),
    }
}

/// Returns the name an expression is, inside any parentheses.
///
/// # Arguments
///
/// * `x` - The expression.
fn bare(mut x: &Expr) -> Option<&str> {
    while let ExprKind::Paren(inner) = &x.kind {
        x = inner;
    }
    if let ExprKind::Name(n) = &x.kind {
        Some(n.as_str())
    } else {
        None
    }
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
    let named = |x: &Expr| bare(x).is_some_and(|n| names.contains(n));
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
/// The text writes the name when the word, past any spaces, closing
/// parentheses and block comments, is followed by an assignment (`=`, not
/// `==`, or a compound one) or a step, or, past spaces, opening parentheses
/// and block comments, preceded by a step or by `&` that is no `&&`. Only
/// comments next to the word are passed over, so a marker quoted in a
/// string hides nothing.
///
/// # Arguments
///
/// * `text` - The text, one line.
/// * `name` - The name, an identifier.
fn raw_writes(text: &str, name: &str) -> bool {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    text.match_indices(name).any(|(at, _)| {
        let head = &text[..at];
        let tail = &text[at + name.len()..];
        if head.ends_with(word) || tail.starts_with(word) {
            return false;
        }
        let before = before_word(head);
        let after = after_word(tail, ')');
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

/// Adds to `out` the names C text the tree could not read may take the
/// address of.
///
/// That is every word a lone `&` is followed by, past spaces, opening
/// parentheses and block comments. A bitwise `&` adds its right operand
/// too, which only keeps more names from moving.
///
/// # Arguments
///
/// * `text` - The text, one line.
/// * `out` - The names.
fn raw_taken(text: &str, out: &mut BTreeSet<String>) {
    for (at, _) in text.match_indices('&') {
        let (head, tail) = (&text[..at], &text[at + 1..]);
        if head.ends_with('&') || tail.starts_with('&') {
            continue;
        }
        let rest = after_word(tail, '(');
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        if end > 0 {
            out.insert(rest[..end].to_owned());
        }
    }
}

/// Returns the text after a word or an operator past the spaces, `paren`s
/// and block comments that open it.
///
/// # Arguments
///
/// * `text` - The text that follows, on its line.
/// * `paren` - The parenthesis passed over: `)` after a word, `(` after an
///   operator.
fn after_word(mut text: &str, paren: char) -> &str {
    loop {
        let rest = text.trim_start_matches(|c: char| c.is_whitespace() || c == paren);
        let Some(comment) = rest.strip_prefix("/*") else {
            return rest;
        };
        text = comment.split_once("*/").map_or("", |(_, past)| past);
    }
}

/// Returns the text before a word less the spaces, opening parentheses and
/// block comments that end it.
///
/// # Arguments
///
/// * `text` - The text that precedes the word, on its line.
fn before_word(mut text: &str) -> &str {
    loop {
        let rest = text.trim_end_matches(|c: char| c.is_whitespace() || c == '(');
        let Some(comment) = rest.strip_suffix("*/") else {
            return rest;
        };
        text = comment.rfind("/*").map_or("", |start| &comment[..start]);
    }
}
