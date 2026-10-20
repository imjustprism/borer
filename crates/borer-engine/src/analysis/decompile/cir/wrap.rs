//! Wrapping guarded regions: the statements a `try` or `__try` protects
//! become one [`StmtKind::Try`], and the code its handlers run moves into
//! the handlers.
//!
//! The structurer lays the body out as if no exception could happen: the
//! protected blocks among the others, and the code only the runtime enters
//! (a landing pad, an `__except` body, a catch's continuation) after
//! them. Every statement carries the block it came from ([`Prov`](super::Prov)), so a
//! region is wrapped only where its boundaries are exact: the protected
//! statements form one run of one statement list, nothing else in the body
//! comes from a protected block, no jump enters the run past its first
//! label, and each handler's code is one run its entry label begins. A
//! region that fails any of these is left as laid out, with a comment
//! naming what handles it, rather than a `try` drawn around the wrong
//! statements.

use std::collections::{BTreeMap, BTreeSet};

use super::{ArmBody, Body, Else, Handler, Head, Label, Stmt, StmtKind};

/// A guarded region, in the blocks the structurer emitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::decompile) struct Region {
    /// Whether it is structured exception handling, written `__try`.
    pub(in crate::analysis::decompile) seh: bool,
    /// The start addresses of the blocks it protects.
    pub(in crate::analysis::decompile) protected: BTreeSet<u64>,
    /// Its handlers, in the order the runtime tries them.
    pub(in crate::analysis::decompile) handlers: Vec<RegionHandler>,
    /// Blocks only the runtime's own dispatch runs (an Itanium landing
    /// pad's selector tests and its resume), which the `try` stands for.
    pub(in crate::analysis::decompile) dropped: BTreeSet<u64>,
    /// The protected address ranges, for the comment a region that does not
    /// wrap gets.
    pub(in crate::analysis::decompile) ranges: Vec<(u64, u64)>,
}

/// One handler of a [`Region`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::decompile) struct RegionHandler {
    /// What it handles.
    pub(in crate::analysis::decompile) head: Head,
    /// A comment its body opens with: the funclet the runtime calls.
    pub(in crate::analysis::decompile) note: Option<String>,
    /// The block of the function the runtime enters for it, when its code
    /// is the function's own.
    pub(in crate::analysis::decompile) entry: Option<u64>,
    /// The start addresses of the blocks only that entry reaches.
    pub(in crate::analysis::decompile) owned: BTreeSet<u64>,
}

/// Wraps every region whose boundaries are exact, innermost first.
///
/// # Arguments
///
/// * `body` - The structured body.
/// * `regions` - The regions, in any order.
///
/// # Returns
///
/// The body, and how many regions were left unwrapped (each with a
/// comment naming its handlers).
pub(in crate::analysis::decompile) fn wrap(mut body: Body, regions: &[Region]) -> (Body, usize) {
    let mut order: Vec<&Region> = regions.iter().collect();
    order.sort_by_key(|r| r.protected.len());
    let mut neutral: BTreeSet<u64> = BTreeSet::new();
    let mut failed = 0;
    for r in order {
        let mut trial = body.clone();
        if apply(&mut trial, r, &neutral) {
            body = trial;
            neutral.extend(r.protected.iter().copied());
            neutral.extend(r.dropped.iter().copied());
            for h in &r.handlers {
                neutral.extend(h.owned.iter().copied());
            }
        } else {
            failed += 1;
            note_unwrapped(&mut body, r);
        }
    }
    (body, failed)
}

/// Wraps one region in place.
///
/// # Arguments
///
/// * `body` - The body, changed only when this answers `true`.
/// * `r` - The region.
/// * `neutral` - Blocks of regions already wrapped, whose statements may
///   sit inside this one's run.
///
/// # Returns
///
/// Whether the region wrapped; on `false` the body is partly changed and
/// must be dropped.
fn apply(body: &mut Body, r: &Region, neutral: &BTreeSet<u64>) -> bool {
    let sets = body.prov.clone();
    let before = dangling(&body.stmts);
    let blocks_of = |s: &Stmt| -> BTreeSet<u64> {
        let mut out = BTreeSet::new();
        each(s, &mut |x| {
            if let Some(set) = usize::try_from(x.prov.0).ok().and_then(|p| sets.get(p)) {
                out.extend(set.iter().copied());
            }
        });
        out
    };
    let within = |s: &Stmt, allowed: &BTreeSet<u64>| {
        blocks_of(s)
            .iter()
            .all(|b| allowed.contains(b) || neutral.contains(b))
    };
    let mut runs: BTreeMap<u64, Vec<Stmt>> = BTreeMap::new();
    for h in &r.handlers {
        let Some(entry) = h.entry else {
            continue;
        };
        if runs.contains_key(&entry) {
            continue;
        }
        let total = count(&body.stmts, &|s| own(s, &sets, &h.owned));
        let Some(run) = take_run(&mut body.stmts, Label(entry), &|s| within(s, &h.owned)) else {
            return false;
        };
        if count(&run, &|s| own(s, &sets, &h.owned)) != total {
            return false;
        }
        runs.insert(entry, run);
    }
    drop_all(&mut body.stmts, &|s| {
        !blocks_of(s).is_empty() && blocks_of(s).iter().all(|b| r.dropped.contains(b))
    });
    if count(&body.stmts, &|s| own(s, &sets, &r.dropped)) != 0 {
        return false;
    }
    let total = count(&body.stmts, &|s| own(s, &sets, &r.protected));
    if total == 0 {
        return false;
    }
    let handlers = r
        .handlers
        .iter()
        .map(|h| Handler {
            head: h.head.clone(),
            body: h
                .note
                .iter()
                .map(|n| Stmt {
                    kind: StmtKind::Comment(format!(" {n}")),
                    prov: super::Prov::ENTRY,
                })
                .chain(
                    h.entry
                        .and_then(|e| runs.get(&e))
                        .into_iter()
                        .flatten()
                        .cloned(),
                )
                .collect(),
        })
        .collect();
    let touches = |s: &Stmt| !blocks_of(s).is_disjoint(&r.protected);
    let fits = |s: &Stmt| within(s, &r.protected);
    let Some(inside) = enclose(&mut body.stmts, &touches, &fits, r.seh, handlers) else {
        return false;
    };
    let StmtKind::Try { body: guarded, .. } = &inside.kind else {
        return false;
    };
    if count(guarded, &|s| own(s, &sets, &r.protected))
        != count(&body.stmts, &|s| own(s, &sets, &r.protected))
    {
        return false;
    }
    let mut labels = BTreeSet::new();
    let mut inner = BTreeMap::new();
    for s in guarded {
        each(s, &mut |x| {
            if let StmtKind::Label(l) = x.kind {
                labels.insert(l);
            }
            jumps(x, &mut inner);
        });
    }
    let mut all = BTreeMap::new();
    for s in &body.stmts {
        each(s, &mut |x| jumps(x, &mut all));
    }
    labels
        .iter()
        .all(|l| all.get(l).copied().unwrap_or(0) == inner.get(l).copied().unwrap_or(0))
        && dangling(&body.stmts).is_subset(&before)
}

/// Lists the labels a jump names that no statement defines.
///
/// # Arguments
///
/// * `list` - The statements.
///
/// # Returns
///
/// The labels jumped to but missing.
fn dangling(list: &[Stmt]) -> BTreeSet<Label> {
    let mut named = BTreeMap::new();
    let mut defined = BTreeSet::new();
    for s in list {
        each(s, &mut |x| {
            jumps(x, &mut named);
            if let StmtKind::Label(l) = x.kind {
                defined.insert(l);
            }
        });
    }
    named.into_keys().filter(|l| !defined.contains(l)).collect()
}

/// Tells whether a statement itself (not what it holds) comes from one of
/// `blocks`; a label, a blank line or a `try` drawn around others is no
/// code of its own.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `sets` - The addresses of each provenance id.
/// * `blocks` - Block start addresses.
///
/// # Returns
///
/// Whether it does.
fn own(s: &Stmt, sets: &[Vec<u64>], blocks: &BTreeSet<u64>) -> bool {
    !matches!(
        s.kind,
        StmtKind::Blank | StmtKind::Label(_) | StmtKind::Try { .. }
    ) && usize::try_from(s.prov.0)
        .ok()
        .and_then(|p| sets.get(p))
        .is_some_and(|set| set.iter().any(|b| blocks.contains(b)))
}

/// Counts the statements, nested ones included, a predicate holds for.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `pred` - The predicate.
///
/// # Returns
///
/// How many statements it holds for.
pub(super) fn count(list: &[Stmt], pred: &dyn Fn(&Stmt) -> bool) -> usize {
    let mut n = 0;
    for s in list {
        each(s, &mut |x| n += usize::from(pred(x)));
    }
    n
}

/// Visits a statement and every statement it holds, outermost first.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `f` - The visitor.
pub(super) fn each(s: &Stmt, f: &mut dyn FnMut(&Stmt)) {
    f(s);
    match &s.kind {
        StmtKind::If { then, other, .. } => {
            then.iter().for_each(|x| each(x, f));
            match other {
                None => {}
                Some(Else::Block(b)) => b.iter().for_each(|x| each(x, f)),
                Some(Else::If(next)) => each(next, f),
            }
        }
        StmtKind::Guard { then, .. } => each(then, f),
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Block(body) => body.iter().for_each(|x| each(x, f)),
        StmtKind::Switch { arms, .. } => {
            for a in arms {
                match &a.body {
                    ArmBody::Inline(x) => each(x, f),
                    ArmBody::Block(b) => b.iter().for_each(|x| each(x, f)),
                }
            }
        }
        StmtKind::Try { body, handlers, .. } => {
            body.iter().for_each(|x| each(x, f));
            for h in handlers {
                h.body.iter().for_each(|x| each(x, f));
            }
        }
        StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => {}
    }
}

/// Returns the statement lists a statement holds directly, an `else if`'s
/// included.
///
/// # Arguments
///
/// * `s` - The statement.
///
/// # Returns
///
/// The lists, in the order the statement prints them.
pub(super) fn lists(s: &mut Stmt) -> Vec<&mut Vec<Stmt>> {
    match &mut s.kind {
        StmtKind::If { then, other, .. } => {
            let mut out = vec![then];
            match other {
                None => {}
                Some(Else::Block(b)) => out.push(b),
                Some(Else::If(next)) => out.extend(lists(next)),
            }
            out
        }
        StmtKind::Guard { then, .. } => lists(then),
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Block(body) => vec![body],
        StmtKind::Switch { arms, .. } => arms
            .iter_mut()
            .flat_map(|a| match &mut a.body {
                ArmBody::Inline(x) => lists(x),
                ArmBody::Block(b) => vec![b],
            })
            .collect(),
        StmtKind::Try { body, handlers, .. } => {
            let mut out = vec![body];
            out.extend(handlers.iter_mut().map(|h| &mut h.body));
            out
        }
        StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank
        | StmtKind::Raw(_) => Vec::new(),
    }
}

/// Counts the jumps a statement itself makes, by label.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `out` - Receives one count per jump.
pub(super) fn jumps(s: &Stmt, out: &mut BTreeMap<Label, usize>) {
    match &s.kind {
        StmtKind::Goto(l) => *out.entry(*l).or_default() += 1,
        StmtKind::Raw(text) => {
            let mut named = BTreeSet::new();
            crate::analysis::decompile::structure::note_jumps(text, &mut named);
            for va in named {
                *out.entry(Label(va)).or_default() += 1;
            }
        }
        StmtKind::Expr(_)
        | StmtKind::Return(_)
        | StmtKind::Label(_)
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::If { .. }
        | StmtKind::Guard { .. }
        | StmtKind::While { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Block(_)
        | StmtKind::Try { .. }
        | StmtKind::Comment(_)
        | StmtKind::Asm(_)
        | StmtKind::Blank => {}
    }
}

/// Removes the run of statements a label begins and returns it.
///
/// The run is the label and the statements after it in the same list that
/// `fits` holds for.
///
/// # Arguments
///
/// * `list` - The statements to search, nested lists included.
/// * `label` - The label the run begins with.
/// * `fits` - Whether a statement belongs to the run.
///
/// # Returns
///
/// The run, or `None` when the label is nowhere.
fn take_run(list: &mut Vec<Stmt>, label: Label, fits: &dyn Fn(&Stmt) -> bool) -> Option<Vec<Stmt>> {
    if let Some(k) = list
        .iter()
        .position(|s| matches!(s.kind, StmtKind::Label(l) if l == label))
    {
        let end = list[k..]
            .iter()
            .position(|s| !fits(s))
            .map_or(list.len(), |n| k + n);
        return Some(list.drain(k..end).collect());
    }
    list.iter_mut()
        .flat_map(lists)
        .find_map(|inner| take_run(inner, label, fits))
}

/// Removes every statement, nested ones included, that `gone` holds for.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `gone` - Whether a statement goes.
fn drop_all(list: &mut Vec<Stmt>, gone: &dyn Fn(&Stmt) -> bool) {
    list.retain(|s| !gone(s));
    for s in list.iter_mut() {
        for inner in lists(s) {
            drop_all(inner, gone);
        }
    }
}

/// Replaces the run of statements a region protects with one `try`.
///
/// The run is found in the outermost list holding every statement that
/// touches the region; one statement that touches it but also holds code
/// from outside is looked into instead. Labels opening the run stay
/// before the `try`, where a jump from outside may still land. A jump
/// that ends the body or a handler to the label right after the `try` is
/// dropped: leaving the `try` falls through to it.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `touches` - Whether a statement holds code of the region.
/// * `fits` - Whether a statement holds code of the region only.
/// * `seh` - Whether the `try` is written `__try`.
/// * `handlers` - Its handlers.
///
/// # Returns
///
/// A copy of the `try` statement put in, or `None` when the touching
/// statements do not form one run of fitting ones.
fn enclose(
    list: &mut Vec<Stmt>,
    touches: &dyn Fn(&Stmt) -> bool,
    fits: &dyn Fn(&Stmt) -> bool,
    seh: bool,
    handlers: Vec<Handler>,
) -> Option<Stmt> {
    let hit: Vec<usize> = (0..list.len()).filter(|&k| touches(&list[k])).collect();
    let (&first, &last) = (hit.first()?, hit.last()?);
    if first == last && !fits(&list[first]) {
        return lists(&mut list[first])
            .into_iter()
            .filter(|inner| inner.iter().any(touches))
            .take(1)
            .find_map(|inner| enclose(inner, touches, fits, seh, handlers.clone()));
    }
    if !list[first..=last].iter().all(fits) {
        return None;
    }
    let mut start = first;
    while start <= last && matches!(list[start].kind, StmtKind::Label(_)) {
        start += 1;
    }
    if start > last {
        return None;
    }
    let mut handlers = handlers;
    let mut guarded: Vec<Stmt> = list.drain(start..=last).collect();
    if let Some(&Stmt {
        kind: StmtKind::Label(next),
        ..
    }) = list.get(start)
    {
        let falls = |body: &mut Vec<Stmt>| {
            if body
                .last()
                .is_some_and(|s| matches!(s.kind, StmtKind::Goto(l) if l == next))
            {
                body.pop();
            }
        };
        falls(&mut guarded);
        for h in &mut handlers {
            falls(&mut h.body);
        }
    }
    let prov = guarded.first().map_or(super::Prov::ENTRY, |s| s.prov);
    let stmt = Stmt {
        kind: StmtKind::Try {
            seh,
            body: guarded,
            handlers,
        },
        prov,
    };
    list.insert(start, stmt.clone());
    Some(stmt)
}

/// Writes a comment naming a region's handlers before the first statement
/// it protects and the labels opening it, or at the top when none is in the
/// text.
///
/// # Arguments
///
/// * `body` - The body.
/// * `r` - The region left unwrapped.
fn note_unwrapped(body: &mut Body, r: &Region) {
    let ranges: Vec<String> = r
        .ranges
        .iter()
        .map(|(s, e)| format!("{s:#x}..{e:#x}"))
        .collect();
    let heads: Vec<String> = r
        .handlers
        .iter()
        .map(|h| {
            let head = match &h.head {
                Head::Catch(decl) => format!("catch ({decl})"),
                Head::Except(filter) => {
                    let mut text = String::new();
                    super::print::expr(filter, &mut text);
                    format!("__except ({text})")
                }
                Head::Finally => "__finally".to_owned(),
            };
            let at = h.entry.map(|e| format!(" at {e:#x}"));
            let runs = h.note.as_ref().map(|n| format!(", {n}"));
            format!(
                "{head}{}{}",
                at.unwrap_or_default(),
                runs.unwrap_or_default()
            )
        })
        .collect();
    let text = format!(
        " {} {} not structured, its bounds are not exact: {}",
        if r.seh { "__try" } else { "try" },
        ranges.join(", "),
        heads.join("; ")
    );
    let sets = &body.prov;
    let mut at = body
        .stmts
        .iter()
        .position(|s| {
            let mut hit = false;
            each(s, &mut |x| hit |= own(x, sets, &r.protected));
            hit
        })
        .unwrap_or(0);
    while at > 0 && matches!(body.stmts[at - 1].kind, StmtKind::Label(_)) {
        at -= 1;
    }
    body.stmts.insert(
        at,
        Stmt {
            kind: StmtKind::Comment(text),
            prov: super::Prov::ENTRY,
        },
    );
}
