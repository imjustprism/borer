//! Tail calls an ARM32 walk took for blocks of its own: the jumps that
//! leave a function, and the functions they reach that nothing else names.
//!
//! A compiler ends a function with a jump to another when the call is the
//! last thing it does. When no symbol, call or pointer names that other
//! function, the jumper's walk follows the jump and keeps the function as
//! its own blocks. [`outlines`] takes such a target back out as a function
//! of its own when the jump reads as a tail call: the jumper's frame is
//! gone at the jump, and the code it reaches is no part of the jumper.

use std::collections::{BTreeMap, BTreeSet};

use super::{Walked, Walks, guarded};
use crate::isa::a32::{self, Flow, Index, Insn, Offset, Op, PC};
use crate::program::Program;

/// Most instructions looked back over from a jump for the `pop` that
/// gave its frame back ([`frame_gone`]).
const FRAME_LOOK: usize = 64;
/// Most targets [`shared_tails`] weighs in one round of [`outlines`]; the
/// rest wait for the next round.
const SHARED_MAX: usize = 1 << 10;
/// Most instructions of a target's code [`tail_jump`] follows.
const BODY_MAX: usize = 1 << 14;

/// Promotes a tail call that was walked as a block of its caller.
///
/// Nothing but one unconditional jump reaches the block, and it lies
/// before the caller's entry or past another function's start. It is a
/// tail call when it is one straight run that returns without touching
/// the stack pointer, so not the caller's own epilogue
/// ([`straight_return`]), or when the jump comes right after a `pop`, so
/// the caller's frame is gone ([`after_pop`]), and no other walked
/// function holds it ([`owners`]): a jump into another function's body
/// splits nothing. A block several walks hold is promoted when each of
/// them reaches it that way ([`shared_tails`]). The caller is walked again
/// and the jump becomes a tail call.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks, updated in place.
///
/// # Returns
///
/// Whether a block was promoted.
pub(super) fn outlines(program: &Program, walks: &mut Walks<'_>) -> bool {
    let mut promote = Vec::new();
    let mut shared = BTreeSet::new();
    let mut held = None;
    for (&entry, w) in &walks.walked {
        let mut pred = None;
        for &t in &w.followed {
            if t == entry || walks.starts.contains(&t) {
                continue;
            }
            let stepped = t > entry && walks.starts.range((entry + 1)..t).next().is_some();
            if !stepped && t > entry {
                continue;
            }
            let pred = pred.get_or_insert_with(|| predecessors(w));
            if (stepped && straight_return(w, t, pred))
                || (after_pop(w, t, pred)
                    && held
                        .get_or_insert_with(|| owners(&walks.walked))
                        .get(&t)
                        .is_none_or(|owner| *owner == Some(entry)))
            {
                promote.push(t);
            } else {
                shared.insert(t);
            }
        }
    }
    let shared: Vec<u64> = shared.into_iter().take(SHARED_MAX).collect();
    promote.extend(shared_tails(program, walks, &shared));
    promote.sort_unstable();
    promote.dedup();
    let promoted = !promote.is_empty();
    for t in promote {
        walks.starts.insert(t);
        walks.guessed.insert(t);
    }
    promoted
}

/// Returns the targets among `cands` that every walk holding them reaches
/// by a tail call.
///
/// The code before a target ends a path or is data, so no walk falls into
/// it ([`super::guess::ends_before`]), and each walk holding it reaches it
/// as [`tail_jump`] says. That is how two thin wrappers jumping on to one
/// function they set arguments up for look, a frameless `mov r1, #1; b
/// f` as well as one that pops its frame first. Code several functions
/// jump to that way is shared, so a function wherever it lies; code one
/// function jumps to must lie away from it, as [`tail_jump`] says.
///
/// Each walk's [`Shape`] is built once, and the work is charged to the
/// walks' fuel: when it runs out, or the cancel flag in force is raised,
/// the targets not yet weighed stay blocks and the discovery is marked
/// incomplete.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks; their fuel is spent.
/// * `cands` - The targets, at most [`SHARED_MAX`].
fn shared_tails(program: &Program, walks: &mut Walks<'_>, cands: &[u64]) -> Vec<u64> {
    let cands: BTreeSet<u64> = cands
        .iter()
        .copied()
        .filter(|&t| super::guess::ends_before(program, walks, t))
        .collect();
    let mut holders: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (&entry, w) in &walks.walked {
        if let (Some((&lo, _)), Some((&hi, _))) =
            (w.seen.first_key_value(), w.seen.last_key_value())
        {
            for &t in cands.range(lo..=hi).filter(|t| w.seen.contains_key(t)) {
                holders.entry(t).or_default().push(entry);
            }
        }
    }
    let mut shapes: BTreeMap<u64, Shape> = BTreeMap::new();
    let mut spent = 0u64;
    let mut found = Vec::new();
    for (t, held) in holders {
        if spent >= walks.fuel || crate::cancel::Cancel::raised() {
            walks.incomplete = true;
            break;
        }
        let alone = held.len() == 1;
        let tail = held.iter().all(|entry| {
            let Some(w) = walks.walked.get(entry) else {
                return false;
            };
            let shape = shapes.entry(*entry).or_insert_with(|| {
                spent = spent.saturating_add(crate::num::from_usize(w.seen.len()));
                Shape::of(w)
            });
            tail_jump(&walks.starts, *entry, w, shape, t, alone, &mut spent)
        });
        if tail {
            found.push(t);
        }
    }
    walks.fuel = walks.fuel.saturating_sub(spent);
    found
}

/// What [`tail_jump`] reads off one walk, built once per round.
struct Shape {
    /// Every instruction that falls, jumps or dispatches to each address
    /// of the walk.
    preds: BTreeMap<u64, Vec<u64>>,
}

impl Shape {
    /// Builds a walk's shape.
    ///
    /// # Arguments
    ///
    /// * `w` - The walk.
    fn of(w: &Walked) -> Self {
        let mut preds: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        for i in w.seen.values() {
            edges(i, &mut |to| {
                if w.seen.contains_key(&to) {
                    preds.entry(to).or_default().push(i.va);
                }
            });
        }
        for t in &w.tables {
            for &target in &t.targets {
                preds.entry(target).or_default().push(t.site);
            }
        }
        Self { preds }
    }
}

/// Tells whether one walk reaches `t` only by jumps that leave the
/// function.
///
/// When no other walk holds `t`, it lies before the walk's entry or past
/// another start, so a block laid out after the jump stays the jumper's
/// own. Every way into `t` from outside the code `t` reaches is an
/// unconditional jump with the frame gone ([`frame_gone`]); no
/// instruction of that code is reached from outside it, and the entry is
/// not in it, so the code at `t` shares no block with the jumper. Code of
/// more than [`BODY_MAX`] instructions is not followed: the target stays.
///
/// # Arguments
///
/// * `starts` - The known function starts.
/// * `entry` - The walk's entry.
/// * `w` - The walk.
/// * `shape` - Its shape.
/// * `t` - The jump target.
/// * `alone` - Whether no other walk holds `t`.
/// * `spent` - The work done, increased by the instructions followed.
fn tail_jump(
    starts: &BTreeSet<u64>,
    entry: u64,
    w: &Walked,
    shape: &Shape,
    t: u64,
    alone: bool,
    spent: &mut u64,
) -> bool {
    let apart = t < entry || starts.range((entry + 1)..t).next().is_some();
    if t == entry || (alone && !apart) {
        return false;
    }
    let Some(body) = reach(w, t, BODY_MAX) else {
        *spent = spent.saturating_add(crate::num::from_usize(BODY_MAX));
        return false;
    };
    *spent = spent.saturating_add(crate::num::from_usize(body.len()));
    let preds = |va: u64| shape.preds.get(&va).map_or(&[][..], Vec::as_slice);
    let shut = body
        .iter()
        .all(|&b| b == t || preds(b).iter().all(|p| body.contains(p)));
    if body.contains(&entry) || !shut {
        return false;
    }
    let ins: Vec<u64> = preds(t)
        .iter()
        .copied()
        .filter(|p| !body.contains(p))
        .collect();
    !ins.is_empty()
        && ins.iter().all(|p| {
            w.seen.get(p).is_some_and(|j| {
                j.flow() == Flow::Jump
                    && j.target() == Some(t)
                    && !j.predicated()
                    && frame_gone(w, entry, *p, shape)
            })
        })
}

/// Tells whether the stack is as the function found it at the jump at
/// `jump`.
///
/// Walking back from it through instructions only one way reaches, a
/// `pop` comes before anything else touches the stack pointer, or the
/// entry does.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `entry` - The walk's entry.
/// * `jump` - The jump's address.
/// * `shape` - The walk's shape.
fn frame_gone(w: &Walked, entry: u64, jump: u64, shape: &Shape) -> bool {
    let mut va = jump;
    for _ in 0..FRAME_LOOK {
        if va == entry {
            return true;
        }
        let Some(p) = shape.preds.get(&va).and_then(|p| match p.as_slice() {
            [one] => w.seen.get(one),
            _ => None,
        }) else {
            return false;
        };
        if popped(p) {
            return true;
        }
        if touches_sp(p) {
            return false;
        }
        va = p.va;
    }
    false
}

/// Returns the addresses of a walk reached from `from`, `from` included,
/// or `None` past `cap` of them.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `from` - Where to start.
/// * `cap` - Most addresses gathered.
fn reach(w: &Walked, from: u64, cap: usize) -> Option<BTreeSet<u64>> {
    let mut seen = BTreeSet::from([from]);
    let mut pending = vec![from];
    while let Some(va) = pending.pop() {
        if seen.len() > cap {
            return None;
        }
        let Some(i) = w.seen.get(&va) else {
            continue;
        };
        let mut go = |to: u64| {
            if w.seen.contains_key(&to) && seen.insert(to) {
                pending.push(to);
            }
        };
        edges(i, &mut go);
        for t in w.tables.iter().filter(|t| t.site == va) {
            t.targets.iter().for_each(|&x| go(x));
        }
    }
    Some(seen)
}

/// Calls `edge` with each address an instruction passes control to inside
/// its function.
///
/// That is the next instruction it falls into and the target of a direct
/// jump. A conditional return or indirect jump still falls through
/// ([`guarded`]).
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `edge` - Called with each address.
fn edges(i: &Insn, edge: &mut impl FnMut(u64)) {
    match i.flow() {
        Flow::Next | Flow::Call => edge(i.next()),
        Flow::CondJump => {
            if let Some(t) = i.target() {
                edge(t);
            }
            edge(i.next());
        }
        Flow::Jump => {
            if let Some(t) = i.target() {
                edge(t);
            }
            if guarded(i) {
                edge(i.next());
            }
        }
        Flow::Return if guarded(i) => edge(i.next()),
        Flow::Return | Flow::Invalid => {}
    }
}

/// Returns, for each address the walks decoded, the one walk that holds it,
/// or `None` where several do.
///
/// Built once for a round of [`outlines`], so asking who holds a target
/// costs a lookup rather than a pass over every walk.
///
/// # Arguments
///
/// * `walked` - The walks, by entry.
fn owners(walked: &BTreeMap<u64, Walked>) -> BTreeMap<u64, Option<u64>> {
    let mut held: BTreeMap<u64, Option<u64>> = BTreeMap::new();
    for (&entry, w) in walked {
        for &va in w.seen.keys() {
            held.entry(va)
                .and_modify(|owner| *owner = None)
                .or_insert(Some(entry));
        }
    }
    held
}

/// Tells whether `t` is reached only by an unconditional jump that a
/// `pop` falls into.
///
/// A compiler pops a frame on the way out: a jump after the pop leaves the
/// function with the caller's stack and return address back in place, a
/// tail call (`pop {r4, lr}; b f`, or a leaf's `ldr r4, [sp], #4; b f`).
///
/// # Arguments
///
/// * `w` - The walk that contains `t`.
/// * `t` - The address the jump targets.
/// * `pred` - Each address's single predecessor ([`predecessors`]).
fn after_pop(w: &Walked, t: u64, pred: &BTreeMap<u64, Option<u64>>) -> bool {
    let single = |va: u64| {
        pred.get(&va)
            .copied()
            .flatten()
            .and_then(|p| w.seen.get(&p))
    };
    let Some(jump) = single(t) else {
        return false;
    };
    let Some(pop) = single(jump.va) else {
        return false;
    };
    popped(pop)
        && jump.flow() == Flow::Jump
        && jump.target() == Some(t)
        && !jump.predicated()
        && pop.next() == jump.va
}

/// Tells whether an instruction pops a frame without returning: an `ldm`
/// or `pop` of `sp` with writeback that leaves `pc` out, or a
/// post-indexed load from `sp` into another register.
///
/// # Arguments
///
/// * `pop` - The instruction.
fn popped(pop: &Insn) -> bool {
    !pop.predicated()
        && match pop.op {
            Op::Ldm {
                rn: a32::SP,
                regs,
                wback: true,
                ..
            } => regs & (1 << 15) == 0,
            Op::Load {
                rt,
                addr:
                    a32::Addr {
                        base: a32::SP,
                        offset: Offset::Imm(step),
                        index: Index::Post,
                    },
                ..
            } => rt != PC && step > 0,
            _ => false,
        }
}

/// The one instruction that falls or jumps to each address in a walk, or
/// `None` at an address more than one instruction reaches.
///
/// A conditional return or indirect jump still falls through
/// ([`guarded`]), and a resolved jump table still reaches its cases,
/// the same edges the walk follows.
///
/// # Arguments
///
/// * `w` - The walk.
fn predecessors(w: &Walked) -> BTreeMap<u64, Option<u64>> {
    let mut pred = BTreeMap::new();
    let mut note = |from: u64, to: u64| {
        if !w.seen.contains_key(&to) {
            return;
        }
        pred.entry(to)
            .and_modify(|seen| *seen = None)
            .or_insert(Some(from));
    };
    for i in w.seen.values() {
        edges(i, &mut |to| note(i.va, to));
    }
    for t in &w.tables {
        for &target in &t.targets {
            note(t.site, target);
        }
    }
    pred
}

/// Tells whether `t` is a straight run that returns without using the
/// stack pointer, reached by one unconditional jump.
///
/// A `pop` of the caller's saved registers is that caller's epilogue even
/// when another function sits between them. A run that reads or writes
/// `sp` stays in the caller. A conditional return falls through, so it is
/// not the end of the run.
///
/// # Arguments
///
/// * `w` - The walk that contains `t`.
/// * `t` - The address the jump targets.
/// * `pred` - Each address's single predecessor ([`predecessors`]).
fn straight_return(w: &Walked, t: u64, pred: &BTreeMap<u64, Option<u64>>) -> bool {
    let Some(from) = pred.get(&t).copied().flatten() else {
        return false;
    };
    if !w
        .seen
        .get(&from)
        .is_some_and(|i| i.flow() == Flow::Jump && i.target() == Some(t))
    {
        return false;
    }
    let mut va = t;
    let mut prev = None;
    for _ in 0..w.seen.len() {
        let Some(i) = w.seen.get(&va) else {
            return false;
        };
        if touches_sp(i) {
            return false;
        }
        if let Some(p) = prev
            && pred.get(&va).copied().flatten() != Some(p)
        {
            return false;
        }
        match i.flow() {
            Flow::Return => return !guarded(i),
            Flow::Next => {
                prev = Some(i.va);
                va = i.next();
            }
            Flow::Jump | Flow::CondJump | Flow::Call | Flow::Invalid => return false,
        }
    }
    false
}

/// Tells whether an instruction reads or writes the stack pointer.
///
/// # Arguments
///
/// * `i` - The instruction.
fn touches_sp(i: &Insn) -> bool {
    let regs = i.registers();
    regs.reads.contains(&a32::SP) || regs.writes.contains(&a32::SP)
}
