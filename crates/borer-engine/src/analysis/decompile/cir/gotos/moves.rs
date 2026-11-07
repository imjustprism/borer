//! The fold's rule that moves or copies a labelled block to the jumps that
//! reach it ([`relocate`]), with the survey of where every label and jump
//! stands that it reads.

use std::collections::{BTreeMap, BTreeSet};

use super::super::wrap::{each, jumps, lists, weighs};
use super::super::{ArmBody, Label, Stmt, StmtKind};
use super::{
    Facts, Kind, TAIL_MAX, ends, idle, labelled, larger, loose, stops, target, walk, word,
};

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
    /// The labels the block jumps to.
    jumps: BTreeSet<Label>,
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
                let back = weighs(block, 1, &|x| usize::from(target(x) == Some(l)));
                let returns = block
                    .iter()
                    .rfind(|x| !idle(x))
                    .is_some_and(|x| matches!(x.kind, StmtKind::Return(_) | StmtKind::Expr(_)));
                let loose = loose(block);
                let mut to = BTreeMap::new();
                for x in block {
                    each(x, &mut |y| jumps(y, &mut to));
                }
                let spot = Spot {
                    frames: frames.clone(),
                    len: block.len(),
                    entered: prev.is_none_or(|p| !stops(inner, p, f)),
                    whole: !back && ends(block, f),
                    loose,
                    tail: returns && !loose && !labelled(block) && !larger(block, TAIL_MAX),
                    jumps: to.into_keys().collect(),
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
/// The blocks that may move all move in one call, the hundreds of arms of
/// a `switch` written as jumps among them: one a call left a big `switch`
/// half written when the rounds ran out. A block that holds a label moves
/// alone, and one that holds another's jump or stands in a block that
/// moved waits for the next call, so no move touches what another read.
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
pub(super) fn relocate(list: &mut Vec<Stmt>, f: &Facts<'_>, copy: bool) -> bool {
    let (spots, sites) = survey(list, f);
    let mut moved = BTreeSet::new();
    let mut held = BTreeSet::new();
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
        let tangled = || held.contains(l) || !spot.jumps.is_disjoint(&moved);
        if !moved.is_empty() && (!moves || tangled()) {
            continue;
        }
        let Some(block) = block_of(list, *l, spot.len) else {
            continue;
        };
        if moves {
            if (!moved.is_empty() && labelled(&block)) || !place(list, *l, &block) {
                continue;
            }
            take(list, *l, spot.len);
            if labelled(&block) {
                return true;
            }
            moved.insert(*l);
            held.extend(spot.jumps.iter().copied());
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
    !moved.is_empty()
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
