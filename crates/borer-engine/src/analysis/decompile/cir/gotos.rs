//! Jumps folded on the tree before it is printed.
//!
//! The structurer writes every block after its label and joins its
//! structures with explicit jumps, so its text holds a `goto` wherever two
//! paths meet. [`fold_jumps`] rewrites the tree until no rule applies. A jump
//! to where control goes anyway is dropped. A jump out of a loop or a
//! `switch` is `break`, and one to a loop's next round `continue`. A
//! conditional jump over a run is an `if` around the run ("No More Gotos",
//! NDSS 2015). The statements between a structure and the label its arms
//! jump to move into the arms that fall into them, copied when several do:
//! the tail a compiler merged, written apart again ("SAILR", USENIX
//! Security 2024). A block one jump reaches moves to that jump, and a short
//! tail that returns is copied to every jump that reaches it. A run a later
//! jump goes back to is a loop. A jump to a jump goes to its label.
//!
//! Every rule keeps the paths of the tree: each statement runs on exactly
//! the paths it ran on before, so the moves and copies change the text, not
//! what it does. A call the binary never returns from ends its path, as the
//! structure check reads it ([`crate::analysis::functions::call_ends_path`]),
//! but only the call that ends its block, which is the one a label or the
//! end of its list follows, and never a stack protector's failure call,
//! which the text leaves out once the protector's check is folded. A line
//! the tree could not read is taken to make every jump it spells.

use std::collections::{BTreeMap, BTreeSet};

use super::wrap::{count, each, jumps, lists};
use super::{ArmBody, Body, Else, Expr, ExprKind, Label, LitKind, Stmt, StmtKind};

/// Most rounds of the rules one body gets.
const ROUNDS: usize = 256;

/// Most statements a tail copied to every jump that reaches it may hold.
const TAIL_MAX: usize = 8;

/// Most statements a run copied into several arms may hold.
const SINK_MAX: usize = 4;

/// Most statements a run moved whole into one arm may hold.
const RUN_MAX: usize = 400;

/// Folds the jumps of a body.
///
/// The rules that change one statement list run first, innermost list
/// first. The rules that move code run when those find nothing, one change
/// a round, so each sees the tree the last one left, the cheapest first:
/// moving a block or a run whole, then copying a short tail or a run into
/// several arms, then returning from a loop where it breaks to a `return`,
/// then moving a statement both arms of an `if` end with after it, then
/// writing a loop, then flipping a loop's last test.
///
/// # Arguments
///
/// * `body` - The structured body, rewritten in place.
/// * `ends` - The start addresses of the blocks that end in a call the
///   binary never returns from.
pub(in crate::analysis::decompile) fn fold_jumps(body: &mut Body, ends: &BTreeSet<u64>) {
    for _ in 0..ROUNDS {
        let mut refs = BTreeMap::new();
        let mut notes = Vec::new();
        for s in &body.stmts {
            each(s, &mut |x| {
                jumps(x, &mut refs);
                if let StmtKind::Comment(text) = &x.kind {
                    notes.push(format!("//{text}"));
                }
            });
        }
        for name in crate::analysis::decompile::tidy::handler_labels(&notes) {
            if let Some(va) = name
                .strip_prefix("L_")
                .and_then(|h| u64::from_str_radix(h, 16).ok())
            {
                *refs.entry(Label(va)).or_default() += 1;
            }
        }
        let facts = Facts {
            refs,
            ends,
            sets: &body.prov,
        };
        let stmts = &mut body.stmts;
        let changed = walk(stmts, &mut |list, cx| local(list, cx, &facts))
            || walk(stmts, &mut |list, _| drop_labels(list, &facts.refs))
            || thread(stmts)
            || relocate(stmts, &facts, false)
            || walk(stmts, &mut |list, cx| sinks(list, cx, &facts, false))
            || relocate(stmts, &facts, true)
            || walk(stmts, &mut |list, cx| sinks(list, cx, &facts, true))
            || walk(stmts, &mut |list, _| leaves(list))
            || walk(stmts, &mut |list, _| hoists(list))
            || walk(stmts, &mut |list, _| loops(list, &facts))
            || walk(stmts, &mut |list, cx| flips(list, cx));
        if !changed {
            break;
        }
    }
}

/// What the rules read besides the statements.
struct Facts<'f> {
    /// How many jumps name each label, those of raw lines included, and
    /// one more for each handler an unwrapped guarded region's comment
    /// names, which only the runtime enters
    /// ([`crate::analysis::decompile::tidy::handler_labels`]).
    refs: BTreeMap<Label, usize>,
    /// The start addresses of the blocks that end in a call the binary
    /// never returns from.
    ends: &'f BTreeSet<u64>,
    /// The addresses each provenance id stands for.
    sets: &'f [Vec<u64>],
}

/// What surrounds a statement list.
#[derive(Debug, Clone, Default)]
struct Cx {
    /// Where falling off the list's end goes before anything runs; no
    /// label when the end goes to the next `case` or the function's caller.
    after: Lead,
    /// The loops, switches and guarded regions around the list, innermost
    /// last.
    frames: Vec<Frame>,
}

/// Where control goes from a point before anything runs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Lead {
    /// The labels it passes.
    labels: Vec<Label>,
    /// The label of the jump it then makes at once, when the next
    /// statement is a `goto`.
    jump: Option<Label>,
    /// Whether it then starts the innermost loop's next round, as falling
    /// off the end of a loop's body does.
    round: bool,
}

impl Lead {
    /// Tells whether going on from the point ends at a label, through its
    /// labels or its one jump.
    ///
    /// # Arguments
    ///
    /// * `l` - The label.
    fn reaches(&self, l: Label) -> bool {
        self.labels.contains(&l) || self.jump == Some(l)
    }
}

/// A loop, `switch` or guarded region around a statement list.
#[derive(Debug, Clone)]
struct Frame {
    /// Its place in a walk of the tree, which tells two frames apart.
    id: usize,
    /// What it is.
    kind: Kind,
    /// Where leaving it goes before anything runs.
    exit: Lead,
    /// For a loop, the labels a `continue` reaches running nothing: its
    /// body's last ones, and those before a `while`.
    next: Vec<Label>,
}

/// The kinds of [`Frame`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// A loop: `break` and `continue` are its.
    Loop,
    /// A `switch`: `break` is its.
    Switch,
    /// A `try` or `__try`: code may not move across its edge, where the
    /// handlers and termination handlers run.
    Try,
}

/// Calls `f` on every statement list of the tree, innermost first, with
/// what surrounds each.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `f` - The rule run on each list, telling whether it changed it.
///
/// # Returns
///
/// Whether any call changed its list.
fn walk(list: &mut Vec<Stmt>, f: &mut dyn FnMut(&mut Vec<Stmt>, &Cx) -> bool) -> bool {
    visit(list, &Cx::default(), &mut 0, f)
}

/// [`walk`] from one list, with what surrounds it and the frames numbered
/// so far.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `cx` - What surrounds them.
/// * `ids` - The frames numbered so far.
/// * `f` - The rule run on each list.
///
/// # Returns
///
/// Whether any call changed its list.
fn visit(
    list: &mut Vec<Stmt>,
    cx: &Cx,
    ids: &mut usize,
    f: &mut dyn FnMut(&mut Vec<Stmt>, &Cx) -> bool,
) -> bool {
    let mut changed = false;
    for k in 0..list.len() {
        let after = lead(list, k + 1, &cx.after);
        *ids += 1;
        let inside = |kind: Kind, exit: Lead, next: Vec<Label>, after: Lead| {
            let mut frames = cx.frames.clone();
            frames.push(Frame {
                id: *ids,
                kind,
                exit,
                next,
            });
            Cx { after, frames }
        };
        let inner = match &list[k].kind {
            StmtKind::If { .. } | StmtKind::Block(_) => Cx {
                after,
                frames: cx.frames.clone(),
            },
            StmtKind::While { body, .. } => {
                let mut next = trailing(body);
                next.extend(labels_before(list, k));
                let end = round(&next);
                inside(Kind::Loop, after, next, end)
            }
            StmtKind::DoWhile { body, .. } | StmtKind::For { body, .. } => {
                let next = trailing(body);
                let end = round(&next);
                inside(Kind::Loop, after, next, end)
            }
            StmtKind::Switch { .. } => inside(Kind::Switch, after, Vec::new(), Lead::default()),
            StmtKind::Try { .. } => inside(Kind::Try, Lead::default(), Vec::new(), after),
            StmtKind::Expr(_)
            | StmtKind::Return(_)
            | StmtKind::Goto(_)
            | StmtKind::Label(_)
            | StmtKind::Break
            | StmtKind::Continue
            | StmtKind::Guard { .. }
            | StmtKind::Comment(_)
            | StmtKind::Asm(_)
            | StmtKind::Blank
            | StmtKind::Raw(_) => continue,
        };
        for body in lists(&mut list[k]) {
            changed |= visit(body, &inner, ids, f);
        }
    }
    changed | f(list, cx)
}

/// Where falling off the end of a loop's body goes: its next round, through
/// the labels a `continue` reaches.
///
/// # Arguments
///
/// * `next` - Those labels.
///
/// # Returns
///
/// The lead of the body's end.
fn round(next: &[Label]) -> Lead {
    Lead {
        labels: next.to_vec(),
        jump: None,
        round: true,
    }
}

/// Tells whether a statement runs nothing: a blank line or a comment.
///
/// # Arguments
///
/// * `s` - The statement.
fn idle(s: &Stmt) -> bool {
    matches!(s.kind, StmtKind::Blank | StmtKind::Comment(_))
}

/// Returns where control goes from position `k` of a list before running
/// anything.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `k` - The position, the list's length for its end.
/// * `after` - Where the list's end goes.
fn lead(list: &[Stmt], k: usize, after: &Lead) -> Lead {
    let mut out = Lead::default();
    for s in list.get(k..).unwrap_or(&[]) {
        if let StmtKind::Label(l) = s.kind {
            out.labels.push(l);
        } else if let StmtKind::Goto(l) = s.kind {
            out.jump = Some(l);
            return out;
        } else if !idle(s) {
            return out;
        }
    }
    out.labels.extend_from_slice(&after.labels);
    out.jump = after.jump;
    out.round = after.round;
    out
}

/// Returns the labels right before position `k` of a list, with nothing
/// that runs between them and it.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `k` - The position.
fn labels_before(list: &[Stmt], k: usize) -> Vec<Label> {
    list.get(..k)
        .unwrap_or(&[])
        .iter()
        .rev()
        .filter(|s| !idle(s))
        .map_while(|s| {
            if let StmtKind::Label(l) = s.kind {
                Some(l)
            } else {
                None
            }
        })
        .collect()
}

/// Returns the labels at the end of a list, with nothing that runs after
/// them.
///
/// # Arguments
///
/// * `list` - The statements.
fn trailing(list: &[Stmt]) -> Vec<Label> {
    labels_before(list, list.len())
}

/// Tells whether a run holds a label, nested ones included, which a jump
/// may enter by and a copy would repeat.
///
/// # Arguments
///
/// * `run` - The statements.
fn labelled(run: &[Stmt]) -> bool {
    count(run, &|s| matches!(s.kind, StmtKind::Label(_))) > 0
}

/// Counts the statements of a run that print, nested ones included.
///
/// # Arguments
///
/// * `run` - The statements.
fn size(run: &[Stmt]) -> usize {
    count(run, &|s| !idle(s))
}

/// Calls `f` on every jump of a run at the run's own level: not inside a
/// loop the run opens, nor, with `switches`, inside a `switch` it opens.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `switches` - Whether a `switch` the run opens ends the level, as it
///   does for `break`.
/// * `f` - The visitor, given each statement that is a jump, a guarded
///   one, or a raw line that may hold one.
fn level(list: &[Stmt], switches: bool, f: &mut dyn FnMut(&Stmt)) {
    for s in list {
        match &s.kind {
            StmtKind::If { then, other, .. } => {
                level(then, switches, f);
                match other {
                    None => {}
                    Some(Else::Block(b)) => level(b, switches, f),
                    Some(Else::If(next)) => level(std::slice::from_ref(next), switches, f),
                }
            }
            StmtKind::Block(b) => level(b, switches, f),
            StmtKind::Try { body, handlers, .. } => {
                level(body, switches, f);
                for h in handlers {
                    level(&h.body, switches, f);
                }
            }
            StmtKind::Switch { arms, .. } if !switches => {
                for a in arms {
                    match &a.body {
                        ArmBody::Inline(x) => level(std::slice::from_ref(x), switches, f),
                        ArmBody::Block(b) => level(b, switches, f),
                    }
                }
            }
            StmtKind::Guard { .. }
            | StmtKind::Goto(_)
            | StmtKind::Break
            | StmtKind::Continue
            | StmtKind::Return(_)
            | StmtKind::Raw(_) => f(s),
            StmtKind::Expr(_)
            | StmtKind::Label(_)
            | StmtKind::While { .. }
            | StmtKind::DoWhile { .. }
            | StmtKind::For { .. }
            | StmtKind::Switch { .. }
            | StmtKind::Comment(_)
            | StmtKind::Asm(_)
            | StmtKind::Blank => {}
        }
    }
}

/// Tells whether a run breaks or continues at its own level, so the words
/// would leave or repeat another loop wherever the run moves.
///
/// # Arguments
///
/// * `list` - The statements.
fn loose(list: &[Stmt]) -> bool {
    let mut found = false;
    level(list, true, &mut |s| found |= says(s, &StmtKind::Break));
    level(list, false, &mut |s| found |= says(s, &StmtKind::Continue));
    found
}

/// Tells whether a statement is a `break` or a `continue`, alone or
/// guarded, or a raw line whose text may hold that word.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `kind` - [`StmtKind::Break`] or [`StmtKind::Continue`].
fn says(s: &Stmt, kind: &StmtKind) -> bool {
    if let StmtKind::Raw(text) = &s.kind {
        return text.contains(if *kind == StmtKind::Break {
            "break"
        } else {
            "continue"
        });
    }
    word(s) == Some(kind)
}

/// Returns the jump a statement makes, alone or under a guard.
///
/// # Arguments
///
/// * `s` - The statement.
///
/// # Returns
///
/// The `goto`, `break`, `continue` or `return`, or `None` for any other
/// statement.
fn word(s: &Stmt) -> Option<&StmtKind> {
    let k = match &s.kind {
        StmtKind::Guard { then, .. } => &then.kind,
        other => other,
    };
    matches!(
        k,
        StmtKind::Goto(_) | StmtKind::Break | StmtKind::Continue | StmtKind::Return(_)
    )
    .then_some(k)
}

/// Returns the label a statement jumps to, alone or under a guard.
///
/// # Arguments
///
/// * `s` - The statement.
fn target(s: &Stmt) -> Option<Label> {
    match word(s) {
        Some(StmtKind::Goto(l)) => Some(*l),
        Some(_) | None => None,
    }
}

/// Tells whether control never runs past statement `k` of a list: it
/// jumps, returns, loops forever or calls what never comes back.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `k` - The statement's position.
/// * `f` - The facts: which blocks end in a call that never returns.
fn stops(list: &[Stmt], k: usize, f: &Facts<'_>) -> bool {
    let Some(s) = list.get(k) else {
        return false;
    };
    match &s.kind {
        StmtKind::Goto(_) | StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue => true,
        StmtKind::If {
            then,
            other: Some(other),
            ..
        } => {
            ends(then, f)
                && match other {
                    Else::Block(b) => ends(b, f),
                    Else::If(next) => stops(std::slice::from_ref(next), 0, f),
                }
        }
        StmtKind::Block(b) => ends(b, f),
        StmtKind::While { body, .. } => {
            let mut breaks = false;
            level(body, true, &mut |x| breaks |= says(x, &StmtKind::Break));
            forever(s) && !breaks
        }
        StmtKind::Expr(e) => {
            let block = usize::try_from(s.prov.0)
                .ok()
                .and_then(|p| f.sets.get(p))
                .and_then(|set| set.first());
            let last = list
                .get(k + 1..)
                .unwrap_or(&[])
                .iter()
                .find(|x| !idle(x))
                .is_none_or(|x| matches!(x.kind, StmtKind::Label(_)));
            last && block.is_some_and(|b| f.ends.contains(b)) && calls_out(e)
        }
        StmtKind::If { other: None, .. }
        | StmtKind::Label(_)
        | StmtKind::Guard { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Try { .. }
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => false,
    }
}

/// Tells whether an expression statement is a call, its result assigned or
/// not, other than a stack protector's failure call.
///
/// # Arguments
///
/// * `e` - The statement's expression.
fn calls_out(e: &Expr) -> bool {
    let value = if let ExprKind::Assign(_, _, v) = &e.kind {
        v
    } else {
        e
    };
    let mut line = String::new();
    super::print::expr(e, &mut line);
    line.push(';');
    matches!(value.kind, ExprKind::Call(..))
        && crate::analysis::decompile::canary::fail_callee(&line).is_none()
}

/// Tells whether control never falls off the end of a list.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `f` - The facts.
fn ends(list: &[Stmt], f: &Facts<'_>) -> bool {
    list.iter()
        .rposition(|s| !idle(s))
        .is_some_and(|k| stops(list, k, f))
}

/// Tells whether a statement is a loop only a jump leaves, `while (1)`.
///
/// # Arguments
///
/// * `s` - The statement.
fn forever(s: &Stmt) -> bool {
    matches!(&s.kind, StmtKind::While { cond, .. }
        if matches!(&cond.kind, ExprKind::Lit(l) if l.kind == LitKind::Int && l.text == "1"))
}

/// Returns the condition that holds when `cond` does not.
///
/// # Arguments
///
/// * `cond` - The condition.
fn negate(cond: &Expr) -> Expr {
    let mut text = String::new();
    super::print::expr(cond, &mut text);
    super::build::expression(
        &crate::analysis::decompile::rewrite::invert_condition(&text),
        cond.prov,
    )
}

/// Tells whether an expression holds a call, or text that may be one, so
/// dropping it would drop the call.
///
/// # Arguments
///
/// * `e` - The expression.
fn has_call(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Call(..) | ExprKind::Raw(_) => true,
        ExprKind::Lit(_) | ExprKind::Name(_) => false,
        ExprKind::Unary(_, a)
        | ExprKind::Postfix(_, a)
        | ExprKind::Cast(_, a)
        | ExprKind::Paren(a)
        | ExprKind::Member { base: a, .. } => has_call(a),
        ExprKind::Binary(_, a, b) | ExprKind::Assign(_, a, b) | ExprKind::Index(a, b) => {
            has_call(a) || has_call(b)
        }
        ExprKind::Cond(a, b, c) => has_call(a) || has_call(b) || has_call(c),
    }
}

/// Runs the rules that change one statement list in place.
///
/// They write a lone jump under an `if` as a guard, jumps out of loops and
/// switches as `break` and `continue`, and drop jumps to where control goes
/// anyway, code after a transfer and a value assigned only to be returned;
/// when none of those changes anything, a jump over a run becomes an `if`,
/// then a long arm that leaves becomes an early exit.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
/// * `f` - The facts.
///
/// # Returns
///
/// Whether the list changed.
fn local(list: &mut Vec<Stmt>, cx: &Cx, f: &Facts<'_>) -> bool {
    let mut changed = guards(list) | exits(list, cx);
    changed |= falls(list, cx);
    changed |= dead(list, f) | returns(list);
    changed || skips(list, cx, f) || flattens(list)
}

/// Shortest `if` body, in printed lines, worth turning into an early exit.
const EARLY_EXIT_MIN: usize = 4;

/// Most statements a tail moved into an early exit may hold.
const EARLY_TAIL_MAX: usize = 3;

/// Turns a long `if` whose body never falls out, followed by a short tail
/// that leaves, into an early exit with the body at the same level.
///
/// `if (c) { BODY } TAIL` is `if (!c) { TAIL } BODY` when no path through
/// `BODY` reaches its end and `TAIL` is at most [`EARLY_TAIL_MAX`] plain
/// statements ending in a `return`, `break` or `continue`: a compare ladder
/// nesting once per compare becomes a run of early returns. Bodies shorter
/// than [`EARLY_EXIT_MIN`] lines keep the natural form.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether an `if` was turned.
fn flattens(list: &mut Vec<Stmt>) -> bool {
    for k in 0..list.len() {
        let StmtKind::If {
            cond,
            then,
            other: None,
        } = &list[k].kind
        else {
            continue;
        };
        let lines = size(then)
            + count(then, &|s| {
                matches!(
                    s.kind,
                    StmtKind::If { .. }
                        | StmtKind::While { .. }
                        | StmtKind::DoWhile { .. }
                        | StmtKind::For { .. }
                        | StmtKind::Switch { .. }
                        | StmtKind::Block(_)
                        | StmtKind::Try { .. }
                )
            });
        let leaves = then.iter().rfind(|s| !idle(s)).is_some_and(|s| {
            matches!(
                s.kind,
                StmtKind::Return(_) | StmtKind::Goto(_) | StmtKind::Break | StmtKind::Continue
            )
        });
        if lines < EARLY_EXIT_MIN || !leaves {
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
            .position(|s| {
                matches!(
                    s.kind,
                    StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue
                )
            });
        let Some(end) = tail.map(|n| k + 2 + n) else {
            continue;
        };
        let cond = negate(cond);
        let tail: Vec<Stmt> = list.drain(k + 1..end).collect();
        let mut body = Vec::new();
        if let StmtKind::If { then, .. } = &mut list[k].kind {
            body = std::mem::replace(then, tail);
        }
        if let StmtKind::If { cond: c, .. } = &mut list[k].kind {
            *c = cond;
        }
        list.splice(k + 1..k + 1, body);
        return true;
    }
    false
}

/// Writes the `break`s of a loop that a lone `return` follows as that
/// `return`, when a loop nested in it still jumps to its next round.
///
/// Leaving the loop runs the `return` and nothing else, so each `break` at
/// the loop's own level returns in place. The nested loop's way out is then
/// the outer loop's only way on, and its jump becomes its own `break`.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any `break` became a `return`.
fn leaves(list: &mut [Stmt]) -> bool {
    let mut changed = false;
    for k in 0..list.len() {
        let next = list[k + 1..]
            .iter()
            .find(|s| !idle(s) && !matches!(s.kind, StmtKind::Label(_)));
        let Some(ret) = next
            .filter(|s| matches!(s.kind, StmtKind::Return(_)))
            .cloned()
        else {
            continue;
        };
        let mut round = Vec::new();
        if let StmtKind::While { body, .. } = &list[k].kind {
            round = labels_before(list, k);
            round.extend(trailing(body));
        } else if let StmtKind::DoWhile { body, .. } | StmtKind::For { body, .. } = &list[k].kind {
            round = trailing(body);
        }
        let stuck = count(
            std::slice::from_ref(&list[k]),
            &|x| matches!(x.kind, StmtKind::Goto(l) if round.contains(&l)),
        );
        if stuck == 0 {
            continue;
        }
        if let StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. } = &mut list[k].kind
        {
            let mut breaks = 0;
            level(body, true, &mut |x| {
                breaks += usize::from(says(x, &StmtKind::Break));
            });
            let mut hidden = false;
            level(body, true, &mut |x| {
                hidden |= matches!(x.kind, StmtKind::Raw(_)) && says(x, &StmtKind::Break);
            });
            if breaks > 0 && !hidden {
                before_breaks(body, std::slice::from_ref(&ret));
                changed = true;
            }
        }
    }
    changed
}

/// Moves a statement both arms of an `if`/`else` end with to after it.
///
/// `if (a) { x; s; } else { y; s; }` runs `s` last on either path, so it is
/// `if (a) { x; } else { y; }` then `s`; two arms ending in the same
/// `if (c) goto L;` leave one test the other rules can fold. The statement
/// is a simple one (an expression, a jump or a guarded jump), and each arm
/// keeps a statement.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any statement moved.
fn hoists(list: &mut Vec<Stmt>) -> bool {
    let print = |s: &Stmt| {
        super::print::print(&Body {
            stmts: vec![s.clone()],
            prov: Vec::new(),
        })
    };
    let mut changed = false;
    let mut k = 0;
    while k < list.len() {
        let mut moved = None;
        if let StmtKind::If {
            then,
            other: Some(Else::Block(other)),
            ..
        } = &mut list[k].kind
        {
            let last = |arm: &[Stmt]| {
                let code: Vec<usize> = (0..arm.len()).filter(|&i| !idle(&arm[i])).collect();
                (code.len() > 1).then(|| code[code.len() - 1])
            };
            if let (Some(a), Some(b)) = (last(then), last(other))
                && (word(&then[a]).is_some() || matches!(then[a].kind, StmtKind::Expr(_)))
                && print(&then[a]) == print(&other[b])
            {
                other.remove(b);
                moved = Some(then.remove(a));
            }
        }
        if let Some(s) = moved {
            list.insert(k + 1, s);
            changed = true;
        }
        k += 1;
    }
    changed
}

/// Writes `v = e; return v;` as `return e;`, as the text's own pass does
/// ([`crate::analysis::decompile::liveness::merge_return_assignments`]), so
/// a tail is measured as it will read.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any pair merged.
fn returns(list: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut k = 0;
    while k + 1 < list.len() {
        let mut merged = None;
        if let (StmtKind::Expr(e), StmtKind::Return(Some(r))) = (&list[k].kind, &list[k + 1].kind)
            && let (ExprKind::Assign(None, place, value), ExprKind::Name(back)) = (&e.kind, &r.kind)
            && place.kind == ExprKind::Name(back.clone())
            && crate::analysis::decompile::line::is_plain_var(back.as_str())
        {
            merged = Some((**value).clone());
        }
        if let Some(value) = merged {
            list[k + 1].kind = StmtKind::Return(Some(value));
            list.remove(k);
            changed = true;
        }
        k += 1;
    }
    changed
}

/// Writes an `if` whose whole body is one `goto` as a guard,
/// `if (c) goto L;`, the form the other rules read; a computed `goto` the
/// tree keeps as a raw line is one too.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any `if` became a guard.
fn guards(list: &mut [Stmt]) -> bool {
    let mut changed = false;
    for s in list.iter_mut() {
        let StmtKind::If {
            cond,
            then,
            other: None,
        } = &s.kind
        else {
            continue;
        };
        let [only] = then.as_slice() else {
            continue;
        };
        let jump = match &only.kind {
            StmtKind::Raw(t) => t.starts_with("goto ") && t.ends_with(';'),
            other => matches!(other, StmtKind::Goto(_)),
        };
        if jump {
            s.kind = StmtKind::Guard {
                cond: cond.clone(),
                then: Box::new(only.clone()),
            };
            changed = true;
        }
    }
    changed
}

/// Writes the jumps that leave the innermost loop or `switch` as `break`
/// and those to a loop's next round as `continue`.
///
/// A `switch` arm that is one jump is looked at here too, from the list
/// holding the `switch`, unless a `return` follows the `switch`: an arm
/// that jumps there reads better as the `return` it reaches, which the
/// copying rule writes in its place ([`relocate`]).
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
///
/// # Returns
///
/// Whether any jump changed.
fn exits(list: &mut [Stmt], cx: &Cx) -> bool {
    let mut changed = false;
    for k in 0..list.len() {
        let after = lead(list, k + 1, &cx.after);
        let returns_after = list[k + 1..]
            .iter()
            .find(|x| !idle(x) && !matches!(x.kind, StmtKind::Label(_)))
            .is_some_and(|x| matches!(x.kind, StmtKind::Return(_)));
        let s = &mut list[k];
        if let StmtKind::Switch { arms, .. } = &mut s.kind {
            if returns_after {
                continue;
            }
            let mut frames = cx.frames.clone();
            frames.push(Frame {
                id: 0,
                kind: Kind::Switch,
                exit: after,
                next: Vec::new(),
            });
            for a in arms {
                if let ArmBody::Inline(x) = &mut a.body {
                    changed |= leave(x, &frames);
                }
            }
        } else if let StmtKind::Guard { then, .. } = &mut s.kind {
            changed |= leave(then, &cx.frames);
        } else {
            changed |= leave(s, &cx.frames);
        }
    }
    changed
}

/// Writes one `goto` as `break` when it leaves the innermost loop or
/// `switch`, or as `continue` when it starts the innermost loop's next
/// round.
///
/// # Arguments
///
/// * `s` - The statement, rewritten in place.
/// * `frames` - The frames around it, innermost last.
///
/// # Returns
///
/// Whether it changed.
fn leave(s: &mut Stmt, frames: &[Frame]) -> bool {
    let StmtKind::Goto(l) = s.kind else {
        return false;
    };
    let breakable = frames
        .iter()
        .rev()
        .find(|fr| matches!(fr.kind, Kind::Loop | Kind::Switch));
    let looped = frames.iter().rev().find(|fr| fr.kind == Kind::Loop);
    if breakable.is_some_and(|fr| fr.exit.reaches(l)) {
        s.kind = StmtKind::Break;
    } else if looped.is_some_and(|fr| fr.next.contains(&l)) {
        s.kind = StmtKind::Continue;
    } else {
        return false;
    }
    true
}

/// Drops each jump to where control goes from it anyway.
///
/// The jump is alone or guarded by a condition that calls nothing: a
/// `goto` to the label it reaches running nothing, or a `continue` where
/// the loop's next round starts.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
///
/// # Returns
///
/// Whether any jump went.
fn falls(list: &mut Vec<Stmt>, cx: &Cx) -> bool {
    let mut changed = false;
    let mut k = 0;
    while k < list.len() {
        let quiet = if let StmtKind::Guard { cond, .. } = &list[k].kind {
            !has_call(cond)
        } else {
            true
        };
        let next = lead(list, k + 1, &cx.after);
        let fall = match word(&list[k]) {
            Some(StmtKind::Goto(l)) => next.reaches(*l),
            Some(StmtKind::Continue) => next.round,
            Some(_) | None => false,
        };
        if quiet && fall {
            list.remove(k);
            changed = true;
        } else {
            k += 1;
        }
    }
    changed
}

/// Drops the code after a statement control never runs past, up to the
/// next statement that holds a label, where a jump may enter.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `f` - The facts.
///
/// # Returns
///
/// Whether anything went.
fn dead(list: &mut Vec<Stmt>, f: &Facts<'_>) -> bool {
    let mut changed = false;
    for k in 0..list.len() {
        if k + 1 >= list.len() || !stops(list, k, f) {
            continue;
        }
        let end = list[k + 1..]
            .iter()
            .position(|s| labelled(std::slice::from_ref(s)))
            .map_or(list.len(), |n| k + 1 + n);
        if list[k + 1..end].iter().any(|s| !idle(s)) {
            list.drain(k + 1..end);
            changed = true;
        }
    }
    changed
}

/// Finds where the run from position `from` meets label `l`: the first
/// label or `goto` from which control reaches `l` running nothing, else the
/// list's end when its end does.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `from` - The run's first position.
/// * `l` - The label.
/// * `after` - Where the list's end goes.
///
/// # Returns
///
/// The position the run ends before, or `None` when the run never meets
/// the label.
fn run_to(list: &[Stmt], from: usize, l: Label, after: &Lead) -> Option<usize> {
    (from..list.len())
        .find(|&p| {
            matches!(list[p].kind, StmtKind::Label(_) | StmtKind::Goto(_))
                && lead(list, p, after).reaches(l)
        })
        .or_else(|| after.reaches(l).then_some(list.len()))
}

/// Tells whether every jump to a label inside a run comes from inside it,
/// so nothing enters the run past its start.
///
/// # Arguments
///
/// * `run` - The statements.
/// * `f` - The facts: every label's jumps.
fn sealed(run: &[Stmt], f: &Facts<'_>) -> bool {
    let mut inner = BTreeMap::new();
    for s in run {
        each(s, &mut |x| jumps(x, &mut inner));
    }
    let mut ok = true;
    for s in run {
        each(s, &mut |x| {
            if let StmtKind::Label(l) = x.kind {
                ok &= inner.get(&l) == f.refs.get(&l);
            }
        });
    }
    ok
}

/// Writes a conditional jump over a run, `if (c) goto L; run; L:`, as an
/// `if` around the run under the opposite condition.
///
/// The run ends where control reaches the label running nothing: at the
/// label, at another jump to it (which stays), or at the list's end when
/// that falls to it. Nothing may enter the run past its start ([`sealed`]).
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
/// * `f` - The facts.
///
/// # Returns
///
/// Whether a run was folded.
fn skips(list: &mut Vec<Stmt>, cx: &Cx, f: &Facts<'_>) -> bool {
    for k in 0..list.len() {
        let (StmtKind::Guard { cond, .. }, Some(l)) = (&list[k].kind, target(&list[k])) else {
            continue;
        };
        let Some(end) = run_to(list, k + 1, l, &cx.after) else {
            continue;
        };
        let run = &list[k + 1..end];
        if !run.iter().any(|s| !idle(s)) || size(run) > RUN_MAX || !sealed(run, f) {
            continue;
        }
        let cond = negate(cond);
        let then = list.drain(k + 1..end).collect();
        list[k].kind = StmtKind::If {
            cond,
            then,
            other: None,
        };
        return true;
    }
    false
}

/// Counts the jumps to `l` that leave a structure where control would
/// otherwise fall out of it: those that end an arm of an `if` or a block,
/// or any at the level of a `while (1)`.
///
/// # Arguments
///
/// * `s` - The structure.
/// * `l` - The label.
fn tails(s: &Stmt, l: Label) -> usize {
    let last = |list: &[Stmt]| list.iter().rfind(|x| !idle(x)).map_or(0, |x| tails(x, l));
    match &s.kind {
        StmtKind::If { then, other, .. } => {
            last(then)
                + match other {
                    None => 0,
                    Some(Else::Block(b)) => last(b),
                    Some(Else::If(next)) => tails(next, l),
                }
        }
        StmtKind::Block(b) => last(b),
        StmtKind::While { body, .. } if forever(s) => {
            let mut n = 0;
            level(body, true, &mut |x| n += usize::from(target(x) == Some(l)));
            n
        }
        StmtKind::Goto(_)
        | StmtKind::Guard { .. }
        | StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::While { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Try { .. }
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => usize::from(target(s) == Some(l)),
    }
}

/// Counts the places control falls out of a structure: each arm whose end
/// it reaches and a missing `else`, or each `break` of a `while (1)`.
///
/// # Arguments
///
/// * `s` - An `if`, a block or a `while (1)`.
/// * `f` - The facts.
///
/// # Returns
///
/// The count, `0` for a loop a raw line may break out of, where a copy in
/// front of each `break` would miss that one.
fn fallouts(s: &Stmt, f: &Facts<'_>) -> usize {
    if forever(s)
        && let StmtKind::While { body, .. } = &s.kind
    {
        let (mut n, mut hidden) = (0, false);
        level(body, true, &mut |x| {
            n += usize::from(word(x) == Some(&StmtKind::Break));
            hidden |= matches!(x.kind, StmtKind::Raw(_)) && says(x, &StmtKind::Break);
        });
        return if hidden { 0 } else { n };
    }
    let open = |list: &[Stmt]| usize::from(!ends(list, f));
    match &s.kind {
        StmtKind::If { then, other, .. } => {
            open(then)
                + match other {
                    None => 1,
                    Some(Else::Block(b)) => open(b),
                    Some(Else::If(next)) => fallouts(next, f),
                }
        }
        StmtKind::Block(b) => open(b),
        StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Guard { .. }
        | StmtKind::While { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Try { .. }
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => 0,
    }
}

/// Appends a run to every arm of a structure control falls out of, and
/// gives an `if` that has none an `else` holding it; in a `while (1)`, puts
/// it in front of every `break`.
///
/// # Arguments
///
/// * `s` - An `if`, a block or a `while (1)`, rewritten in place.
/// * `run` - The statements.
/// * `f` - The facts.
fn append(s: &mut Stmt, run: &[Stmt], f: &Facts<'_>) {
    let open = |list: &mut Vec<Stmt>| {
        if !ends(list, f) {
            list.extend_from_slice(run);
        }
    };
    match &mut s.kind {
        StmtKind::If { then, other, .. } => {
            open(then);
            match other {
                None => *other = Some(Else::Block(run.to_vec())),
                Some(Else::Block(b)) => open(b),
                Some(Else::If(next)) => append(next, run, f),
            }
        }
        StmtKind::Block(b) => open(b),
        StmtKind::While { body, .. } => before_breaks(body, run),
        StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Guard { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Try { .. }
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => {}
    }
}

/// Puts a run in front of every `break` of a list at its own level, a
/// guarded one becoming an `if` around the run and the `break`.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `run` - The statements.
fn before_breaks(list: &mut Vec<Stmt>, run: &[Stmt]) {
    let mut k = 0;
    while k < list.len() {
        let s = &mut list[k];
        if s.kind == StmtKind::Break {
            list.splice(k..k, run.iter().cloned());
            k += run.len() + 1;
            continue;
        }
        if let StmtKind::Guard { cond, then } = &s.kind
            && then.kind == StmtKind::Break
        {
            let mut arm = run.to_vec();
            arm.push((**then).clone());
            s.kind = StmtKind::If {
                cond: cond.clone(),
                then: arm,
                other: None,
            };
        } else if matches!(
            s.kind,
            StmtKind::If { .. } | StmtKind::Block(_) | StmtKind::Try { .. }
        ) {
            for inner in lists(s) {
                before_breaks(inner, run);
            }
        }
        k += 1;
    }
}

/// Moves the run between a structure and a label the structure's arms jump
/// to into the arms that fall out of the structure.
///
/// `if (a) { x; goto L; } y; L:` runs `y` only when `a` fails, so it is
/// `if (a) { x; goto L; } else { y; } L:`, and the jump, now at the end of
/// its arm, is dropped as one to where control goes anyway. Where several
/// arms fall out, each takes a copy: the compiler merged the tails the
/// source wrote apart. A run copied that way holds at most [`SINK_MAX`]
/// statements; one moved whole holds at most [`RUN_MAX`]. The run holds no label, and only arms that end in a
/// jump to the label make the move worth it. After a `while (1)` the run
/// moves in front of each `break`, and the loop's jumps to the label become
/// `break`s in turn; such a run may not break or continue itself.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
/// * `f` - The facts.
/// * `copy` - Whether a run may be copied into several arms; else only one
///   arm takes it.
///
/// # Returns
///
/// Whether a run moved.
fn sinks(list: &mut Vec<Stmt>, cx: &Cx, f: &Facts<'_>, copy: bool) -> bool {
    for k in 0..list.len() {
        let looped = forever(&list[k]);
        if !looped && !matches!(list[k].kind, StmtKind::If { .. } | StmtKind::Block(_)) {
            continue;
        }
        let mut wanted = BTreeSet::new();
        each(&list[k], &mut |x| wanted.extend(target(x)));
        for l in wanted {
            if tails(&list[k], l) == 0 {
                continue;
            }
            let Some(end) = run_to(list, k + 1, l, &cx.after) else {
                continue;
            };
            let run = &list[k + 1..end];
            let n = size(run);
            let copies = fallouts(&list[k], f);
            if n == 0
                || n > RUN_MAX
                || copies == 0
                || labelled(run)
                || (looped && loose(run))
                || (copies > 1 && (!copy || n > SINK_MAX))
            {
                continue;
            }
            let run: Vec<Stmt> = list.drain(k + 1..end).collect();
            append(&mut list[k], &run, f);
            return true;
        }
    }
    false
}

/// Drops the labels of a list that no jump names.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `refs` - The jumps to each label.
///
/// # Returns
///
/// Whether any label went.
fn drop_labels(list: &mut Vec<Stmt>, refs: &BTreeMap<Label, usize>) -> bool {
    let before = list.len();
    list.retain(|s| !matches!(s.kind, StmtKind::Label(l) if !refs.contains_key(&l)));
    list.len() != before
}

/// Sends every jump to a label whose code is only another jump straight to
/// that jump's label, through a chain; a cycle is left alone.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
///
/// # Returns
///
/// Whether any jump changed its label.
fn thread(list: &mut Vec<Stmt>) -> bool {
    let mut next = BTreeMap::new();
    walk(list, &mut |inner, cx| {
        for k in 0..inner.len() {
            if let StmtKind::Label(l) = inner[k].kind
                && let Some(m) = lead(inner, k + 1, &cx.after).jump
                && m != l
            {
                next.insert(l, m);
            }
        }
        false
    });
    let resolve = |start: Label| {
        let mut at = *next.get(&start)?;
        for _ in 0..next.len() {
            match next.get(&at) {
                Some(&m) if m == start => return None,
                Some(&m) => at = m,
                None => return Some(at),
            }
        }
        None
    };
    walk(list, &mut |inner, _| {
        let mut any = false;
        for s in inner.iter_mut() {
            if let StmtKind::Switch { arms, .. } = &mut s.kind {
                for a in arms {
                    if let ArmBody::Inline(x) = &mut a.body {
                        any |= redirect(x, &resolve);
                    }
                }
            } else if let StmtKind::Guard { then, .. } = &mut s.kind {
                any |= redirect(then, &resolve);
            } else {
                any |= redirect(s, &resolve);
            }
        }
        any
    })
}

/// Sends one `goto` to the label a chain of jumps ends at.
///
/// # Arguments
///
/// * `s` - The statement, rewritten in place.
/// * `resolve` - The label a chain from each label ends at, `None` when it
///   starts no chain or a cycle.
///
/// # Returns
///
/// Whether it changed.
fn redirect(s: &mut Stmt, resolve: &dyn Fn(Label) -> Option<Label>) -> bool {
    let StmtKind::Goto(l) = &mut s.kind else {
        return false;
    };
    resolve(*l).map(|m| *l = m).is_some()
}

/// The frames around a place: each one's id and kind, innermost last.
type Frames = Vec<(usize, Kind)>;

/// Where a label stands, for moving or copying the block it begins.
#[derive(Debug, Clone)]
struct Spot {
    /// The frames around it.
    frames: Frames,
    /// How many statements its block holds: those from the label to the
    /// next one a jump names or the list's end.
    len: usize,
    /// Whether control can fall into the label from the statement before.
    entered: bool,
    /// Whether the block may move: control never falls off its end and it
    /// holds no jump back to its own label.
    whole: bool,
    /// Whether the block breaks or continues at its own level ([`loose`]).
    loose: bool,
    /// Whether the block is a tail worth copying: it returns (or ends in a
    /// call that never does), holds no label, does not break or continue,
    /// and holds at most [`TAIL_MAX`] statements.
    tail: bool,
}

/// Records where every label and every jump stands.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `f` - The facts.
///
/// # Returns
///
/// Each label's spot, and the frames around each jump to each label.
fn survey(
    list: &mut Vec<Stmt>,
    f: &Facts<'_>,
) -> (BTreeMap<Label, Spot>, BTreeMap<Label, Vec<Frames>>) {
    let mut spots = BTreeMap::new();
    let mut sites: BTreeMap<Label, Vec<Frames>> = BTreeMap::new();
    walk(list, &mut |inner, cx| {
        let frames: Frames = cx.frames.iter().map(|fr| (fr.id, fr.kind)).collect();
        for (k, s) in inner.iter().enumerate() {
            if let StmtKind::Label(l) = s.kind {
                let end = (k + 1..inner.len())
                    .find(
                        |&p| matches!(inner[p].kind, StmtKind::Label(m) if f.refs.contains_key(&m)),
                    )
                    .unwrap_or(inner.len());
                let prev = inner[..k].iter().rposition(|x| !idle(x));
                let block = &inner[k + 1..end];
                let back = count(block, &|x| target(x) == Some(l)) > 0;
                let returns = block
                    .iter()
                    .rfind(|x| !idle(x))
                    .is_some_and(|x| matches!(x.kind, StmtKind::Return(_) | StmtKind::Expr(_)));
                let loose = loose(block);
                let spot = Spot {
                    frames: frames.clone(),
                    len: block.len(),
                    entered: prev.is_none_or(|p| !stops(inner, p, f)),
                    whole: !back && ends(block, f),
                    loose,
                    tail: returns && !loose && !labelled(block) && size(block) <= TAIL_MAX,
                };
                spots.insert(l, spot);
            }
            if let Some(l) = target(s) {
                sites.entry(l).or_default().push(frames.clone());
            }
            if let StmtKind::Switch { arms, .. } = &s.kind {
                let mut arm = frames.clone();
                arm.push((usize::MAX, Kind::Switch));
                for a in arms {
                    if let ArmBody::Inline(x) = &a.body
                        && let Some(l) = target(x)
                    {
                        sites.entry(l).or_default().push(arm.clone());
                    }
                }
            }
        }
        false
    });
    (spots, sites)
}

/// Tells whether code may move between two places: the same guarded
/// regions hold both, so no handler runs at a different time.
///
/// # Arguments
///
/// * `a` - The frames around one place.
/// * `b` - The frames around the other.
fn same_guards(a: &[(usize, Kind)], b: &[(usize, Kind)]) -> bool {
    let tries = |x: &[(usize, Kind)]| -> Vec<usize> {
        x.iter()
            .filter(|(_, k)| *k == Kind::Try)
            .map(|(id, _)| *id)
            .collect()
    };
    tries(a) == tries(b)
}

/// Moves or copies a labelled block to the jumps that reach it.
///
/// A block one jump reaches and nothing falls into, that never falls off
/// its end, moves to that jump: `goto L;` becomes the block, `if (c) goto
/// L;` an `if` around it. A block that returns (or ends in a call that
/// never does) and holds at most [`TAIL_MAX`] statements is copied to every
/// jump; the original stays for whatever falls into it. Neither crosses the edge of a guarded region, and a block
/// that breaks or continues at its own level moves only within its loop.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `f` - The facts.
/// * `copy` - Whether tails are copied; else blocks only move.
///
/// # Returns
///
/// Whether a block moved or was copied.
fn relocate(list: &mut Vec<Stmt>, f: &Facts<'_>, copy: bool) -> bool {
    let (spots, sites) = survey(list, f);
    for (l, spot) in &spots {
        let Some(at) = sites.get(l) else {
            continue;
        };
        if !spot.whole || !at.iter().all(|s| same_guards(s, &spot.frames)) {
            continue;
        }
        let moves = at.len() == 1 && !spot.entered && f.refs.get(l) == Some(&1);
        if moves && spot.loose && at.iter().any(|s| s != &spot.frames) {
            continue;
        }
        if !(moves || copy && spot.tail) {
            continue;
        }
        let Some(block) = block_of(list, *l, spot.len) else {
            continue;
        };
        if moves {
            if place(list, *l, &block) {
                take(list, *l, spot.len);
                return true;
            }
            continue;
        }
        let mut copied = false;
        while place(list, *l, &block) {
            copied = true;
        }
        if copied {
            return true;
        }
    }
    false
}

/// Returns a copy of the block a label begins.
///
/// # Arguments
///
/// * `list` - The statements, searched with their nested lists.
/// * `l` - The label.
/// * `len` - The block's length.
///
/// # Returns
///
/// The statements, or `None` when the label is nowhere.
fn block_of(list: &mut [Stmt], l: Label, len: usize) -> Option<Vec<Stmt>> {
    if let Some(k) = list
        .iter()
        .position(|s| matches!(s.kind, StmtKind::Label(m) if m == l))
    {
        return list
            .get(k + 1..(k + 1 + len).min(list.len()))
            .map(<[Stmt]>::to_vec);
    }
    list.iter_mut().find_map(|s| {
        lists(s)
            .into_iter()
            .find_map(|inner| block_of(inner, l, len))
    })
}

/// Removes the block a label begins, keeping the label.
///
/// # Arguments
///
/// * `list` - The statements, searched with their nested lists.
/// * `l` - The label.
/// * `len` - The block's length.
///
/// # Returns
///
/// Whether the label was found.
fn take(list: &mut Vec<Stmt>, l: Label, len: usize) -> bool {
    if let Some(k) = list
        .iter()
        .position(|s| matches!(s.kind, StmtKind::Label(m) if m == l))
    {
        let end = (k + 1 + len).min(list.len());
        list.drain(k + 1..end);
        return true;
    }
    list.iter_mut()
        .any(|s| lists(s).into_iter().any(|inner| take(inner, l, len)))
}

/// Puts a block in place of the first jump to a label.
///
/// The block stands in place of a `goto`, as an `if` around it for a
/// guarded one (as the guarded statement when the block is one jump), and
/// as the arm's body for a `switch` arm.
///
/// # Arguments
///
/// * `list` - The statements, searched with their nested lists.
/// * `l` - The label.
/// * `block` - The statements.
///
/// # Returns
///
/// Whether a jump was found.
fn place(list: &mut Vec<Stmt>, l: Label, block: &[Stmt]) -> bool {
    for k in 0..list.len() {
        let s = &mut list[k];
        if s.kind == StmtKind::Goto(l) {
            list.splice(k..=k, block.iter().cloned());
            return true;
        }
        if let StmtKind::Guard { cond, then } = &mut s.kind
            && then.kind == StmtKind::Goto(l)
        {
            if let [one] = block
                && word(one).is_some()
            {
                **then = one.clone();
            } else {
                s.kind = StmtKind::If {
                    cond: cond.clone(),
                    then: block.to_vec(),
                    other: None,
                };
            }
            return true;
        }
        if let StmtKind::Switch { arms, .. } = &mut s.kind
            && let Some(a) = arms
                .iter_mut()
                .find(|a| matches!(&a.body, ArmBody::Inline(x) if x.kind == StmtKind::Goto(l)))
        {
            a.body = if let [one] = block
                && (word(one).is_some() || matches!(one.kind, StmtKind::Expr(_)))
            {
                ArmBody::Inline(Box::new(one.clone()))
            } else {
                ArmBody::Block(block.to_vec())
            };
            return true;
        }
        if lists(s).into_iter().any(|inner| place(inner, l, block)) {
            return true;
        }
    }
    false
}

/// Writes a run that later jumps go back to as a loop.
///
/// `L: run; if (c) goto L;` is `do { run } while (c);`, and a run whose
/// jumps back to its label sit anywhere in it at its own level is
/// `while (1) { run }` with each of them `continue` and a `break` where the
/// run falls out. Every jump to the label comes from the run, no jump
/// enters the run past its label, and the run neither breaks nor continues
/// at its own level, since those words would then be the new loop's.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `f` - The facts.
///
/// # Returns
///
/// Whether a loop was written.
fn loops(list: &mut Vec<Stmt>, f: &Facts<'_>) -> bool {
    for a in 0..list.len() {
        let StmtKind::Label(l) = list[a].kind else {
            continue;
        };
        let named = |s: &Stmt| count(std::slice::from_ref(s), &|x| x.kind == StmtKind::Goto(l));
        let Some(b) = (a + 1..list.len()).rev().find(|&p| named(&list[p]) > 0) else {
            continue;
        };
        let run = &list[a + 1..=b];
        let mut own = 0;
        level(run, false, &mut |x| {
            own += usize::from(target(x) == Some(l));
        });
        let inside: usize = run.iter().map(named).sum();
        if Some(&inside) != f.refs.get(&l) || own == 0 || loose(run) || !sealed(run, f) {
            continue;
        }
        let prov = list[a].prov;
        let mut body: Vec<Stmt> = list.drain(a + 1..=b).collect();
        let last = body.iter().rposition(|x| !idle(x)).unwrap_or(0);
        let kind = match body.get(last).map(|s| &s.kind) {
            Some(StmtKind::Guard { cond, then }) if own == 1 && then.kind == StmtKind::Goto(l) => {
                let cond = cond.clone();
                body.truncate(last);
                StmtKind::DoWhile { body, cond }
            }
            Some(_) | None => {
                let back = body.get(last).is_some_and(|s| s.kind == StmtKind::Goto(l));
                continues(&mut body, l);
                if back {
                    body.truncate(last);
                } else if !ends(&body, f) {
                    body.push(Stmt {
                        kind: StmtKind::Break,
                        prov,
                    });
                }
                StmtKind::While {
                    cond: super::build::expression("1", prov),
                    body,
                }
            }
        };
        list.insert(a + 1, Stmt { kind, prov });
        return true;
    }
    false
}

/// Writes every jump to a label at a run's own loop level as `continue`.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `l` - The label.
fn continues(list: &mut [Stmt], l: Label) {
    for s in list.iter_mut() {
        if s.kind == StmtKind::Goto(l) {
            s.kind = StmtKind::Continue;
        } else if let StmtKind::Guard { then, .. } = &mut s.kind {
            continues(std::slice::from_mut(then.as_mut()), l);
        } else if let StmtKind::Switch { arms, .. } = &mut s.kind {
            for a in arms {
                match &mut a.body {
                    ArmBody::Inline(x) => continues(std::slice::from_mut(x.as_mut()), l),
                    ArmBody::Block(b) => continues(b, l),
                }
            }
        } else if matches!(
            s.kind,
            StmtKind::If { .. } | StmtKind::Block(_) | StmtKind::Try { .. }
        ) {
            for inner in lists(s) {
                continues(inner, l);
            }
        }
    }
}

/// Writes a loop body's last two jumps, `if (c) continue; B;`, as
/// `if (!c) B;`: the `continue` goes where the body's end goes anyway.
///
/// # Arguments
///
/// * `list` - The statements, rewritten in place.
/// * `cx` - What surrounds them.
///
/// # Returns
///
/// Whether the jumps were rewritten.
fn flips(list: &mut Vec<Stmt>, cx: &Cx) -> bool {
    let mut code = (0..list.len()).rev().filter(|&k| !idle(&list[k]));
    let (Some(b), Some(a)) = (code.next(), code.next()) else {
        return false;
    };
    let StmtKind::Guard { cond, then } = &list[a].kind else {
        return false;
    };
    if !cx.after.round || then.kind != StmtKind::Continue || word(&list[b]).is_none() {
        return false;
    }
    if matches!(list[b].kind, StmtKind::Guard { .. }) {
        return false;
    }
    let cond = negate(cond);
    let then = Box::new(list.remove(b));
    list[a].kind = StmtKind::Guard { cond, then };
    true
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::{build, print};
    use std::collections::BTreeSet;

    /// Folds a body's text and prints it back.
    ///
    /// # Arguments
    ///
    /// * `text` - The structurer's text.
    fn folded(text: &str) -> String {
        let mut body = build(text);
        super::fold_jumps(&mut body, &BTreeSet::new());
        print(&body)
    }

    /// A jump to the label after it is dropped, and the label with it.
    #[test]
    fn a_jump_to_the_next_label_goes() {
        let got = folded("if (a1 != 0) {\n  a2 = 1;\n  goto L_10;\n}\nL_10:\nreturn a2;\n");
        assert_eq!(got, "if (a1 != 0) {\n  a2 = 1;\n}\nreturn a2;\n");
    }

    /// A conditional jump over a run is an `if` around it.
    #[test]
    fn a_jump_over_a_run_is_an_if() {
        let got = folded("if (a1 == 0) goto L_10;\na2 = 1;\nf(a2);\nL_10:\nreturn a2;\n");
        assert_eq!(got, "if (a1 != 0) {\n  a2 = 1;\n  f(a2);\n}\nreturn a2;\n");
    }

    /// A jump out of a loop is `break`, and one to its end `continue`.
    #[test]
    fn jumps_out_of_a_loop_are_break_and_continue() {
        let got = folded(
            "while (1) {\n  if (a1 == 0) goto L_20;\n  if (a2 == 0) goto L_10;\n  f(a1);\n  L_10:\n}\nL_20:\nreturn 0;\n",
        );
        assert_eq!(
            got,
            "while (1) {\n  if (a1 == 0) break;\n  if (a2 == 0) continue;\n  f(a1);\n}\nreturn 0;\n"
        );
    }

    /// The run in front of a label that a nested arm jumps to moves into
    /// the arms that fall out, copied into each.
    #[test]
    fn a_shared_tail_moves_into_the_arms() {
        let got = folded(
            "if (a1 != 0) {\n  a2 = g();\n  if (a2 != 0) {\n    h(a2);\n    goto L_10;\n  }\n}\nlog(a1);\nL_10:\na3 = 1;\nL_20:\nf(a3);\nif (a4 != 0) goto L_20;\nreturn 0;\n",
        );
        assert_eq!(
            got,
            "if (a1 != 0) {\n  a2 = g();\n  if (a2 != 0) {\n    h(a2);\n  } else {\n    log(a1);\n  }\n} else {\n  log(a1);\n}\na3 = 1;\ndo {\n  f(a3);\n} while (a4 != 0);\nreturn 0;\n"
        );
    }

    /// The run after a `while (1)` that only its `break` reaches moves in
    /// front of the `break`, and the loop's other exit to the label after
    /// that run is a `break` too.
    #[test]
    fn a_loop_exit_run_moves_in_front_of_its_break() {
        let got = folded(
            "while (1) {\n  if (a1 == 0) break;\n  if (a2 == 0) goto L_10;\n  a1 -= 1;\n}\nf(a1);\nL_10:\ng(a2);\nL_20:\nh();\nif (a3 != 0) goto L_20;\nreturn 0;\n",
        );
        assert_eq!(
            got,
            "while (1) {\n  if (a1 == 0) {\n    f(a1);\n    break;\n  }\n  if (a2 == 0) break;\n  a1 -= 1;\n}\ng(a2);\ndo {\n  h();\n} while (a3 != 0);\nreturn 0;\n"
        );
    }

    /// A line the tree could not read may break out of its loop, so the
    /// code after the loop is not dead.
    #[test]
    fn a_raw_break_keeps_the_code_after_its_loop() {
        let text =
            "while (1) {\n  if (a1 != 0 /* note */) break;\n  a1 += 1;\n}\nf(a1);\nreturn 0;\n";
        assert_eq!(folded(text), text);
    }

    /// A block one jump reaches and nothing falls into moves to the jump.
    #[test]
    fn a_block_one_jump_reaches_moves_there() {
        let got = folded(
            "if (a1 != 0) {\n  if (a2 == 0) goto L_10;\n  f(a2);\n}\nreturn 1;\nL_10:\ng(a1);\nreturn 2;\n",
        );
        assert_eq!(
            got,
            "if (a1 != 0) {\n  if (a2 == 0) {\n    g(a1);\n    return 2;\n  }\n  f(a2);\n}\nreturn 1;\n"
        );
    }

    /// A short returning tail several jumps reach is copied to each.
    #[test]
    fn a_short_return_tail_is_copied() {
        let got = folded(
            "if (a1 == 0) goto L_10;\nf(a1);\nif (a2 == 0) goto L_10;\ng(a2);\nreturn 0;\nL_10:\nh();\nreturn -1;\n",
        );
        assert!(!got.contains("goto"), "{got}");
    }

    /// The run after an `else if` chain whose last arm jumps past it moves
    /// into the chain's missing `else`, not into the arm that returns.
    #[test]
    fn a_chain_without_else_takes_the_run_as_its_else() {
        let got = folded(
            "if (a1 == 1) {
  f(1);
  return 1;
} else if (a1 == 2) {
  f(2);
  goto L_10;
}
f(3);
L_10:
return 0;
",
        );
        assert_eq!(
            got,
            "if (a1 == 1) {
  f(1);
  return 1;
} else if (a1 == 2) {
  f(2);
} else {
  f(3);
}
return 0;
"
        );
    }

    /// An inner loop's jump to the outer loop's next round is its `break`
    /// once the outer loop's own `break` returns in place.
    #[test]
    fn a_break_to_a_return_returns_in_place() {
        let got = folded(
            "L_10:
while (1) {
  f();
  while (1) {
    if (a1 == 0) goto L_10;
    if (g() != 0) break;
  }
  break;
}
return a2;
",
        );
        assert_eq!(
            got,
            "while (1) {
  f();
  while (1) {
    if (a1 == 0) break;
    if (g() != 0) {
      return a2;
    }
  }
}
"
        );
    }

    /// A run a later jump goes back to is a loop.
    #[test]
    fn a_jump_back_is_a_loop() {
        let got = folded("L_10:\na1 += 1;\nif (a1 < 10) goto L_10;\nreturn a1;\n");
        assert_eq!(got, "do {\n  a1 += 1;\n} while (a1 < 10);\nreturn a1;\n");
    }

    /// A run a jump from outside enters past its start keeps its label.
    #[test]
    fn a_run_entered_from_outside_stays() {
        let got = folded(
            "if (a1 == 0) goto L_10;\nf(a1);\nL_20:\ng(a1);\nL_10:\nh(a1);\nif (a2 != 0) goto L_20;\nreturn 0;\n",
        );
        assert!(got.contains("L_20:"), "{got}");
    }

    /// A loop body that ends `if (c) continue; break;` tests the `break`.
    #[test]
    fn a_closing_continue_flips_into_its_break() {
        let got = folded("while (1) {\n  f();\n  if (a1 != 0) continue;\n  break;\n}\nreturn 0;\n");
        assert_eq!(
            got,
            "while (1) {\n  f();\n  if (a1 == 0) break;\n}\nreturn 0;\n"
        );
    }

    /// A block that ends in a call the binary never returns from moves to
    /// its one jump, and the stack protector's failure call ends nothing.
    #[test]
    fn a_call_that_never_returns_ends_its_block() {
        let shape = |call: &str| {
            format!(
                "if (a3 != 0) goto L_20;
if (a2 != 0) {{
  if (a1 == 0) goto L_10;
  h();
}}
return 0;
L_10:
f(a1);
{call}();
L_20:
g();
"
            )
        };
        let run = |text: &str, ends: &BTreeSet<u64>| {
            let mut body = build(text);
            super::fold_jumps(&mut body, ends);
            print(&body)
        };
        let ends: BTreeSet<u64> = [0x10].into_iter().collect();
        assert!(!run(&shape("abort"), &ends).contains("goto"));
        assert!(run(&shape("abort"), &BTreeSet::new()).contains("goto"));
        assert!(run(&shape("__stack_chk_fail"), &ends).contains("goto"));
    }
}
