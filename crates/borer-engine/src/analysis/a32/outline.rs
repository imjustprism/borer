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
/// them reaches it that way ([`shared_tail`]). The caller is walked again
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
    promote.extend(
        shared
            .into_iter()
            .filter(|&t| shared_tail(program, walks, t)),
    );
    promote.sort_unstable();
    promote.dedup();
    let promoted = !promote.is_empty();
    for t in promote {
        walks.starts.insert(t);
        walks.guessed.insert(t);
    }
    promoted
}

/// Tells whether every walk that holds `t` reaches it by a tail call.
///
/// The code before `t` ends a path or is data, so no walk falls into it
/// ([`super::guess::ends_before`]), and each walk holding it reaches it
/// as [`tail_jump`] says. That is how two thin wrappers jumping on to one
/// function they set arguments up for look, a frameless `mov r1, #1; b
/// f` as well as one that pops its frame first. Code several functions
/// jump to that way is shared, so a function wherever it lies; code one
/// function jumps to must lie away from it, as [`tail_jump`] says.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks.
/// * `t` - The jump target.
fn shared_tail(program: &Program, walks: &Walks<'_>, t: u64) -> bool {
    if !super::guess::ends_before(program, walks, t) {
        return false;
    }
    let holders: Vec<(u64, &Walked)> = walks
        .walked
        .iter()
        .filter(|(_, w)| w.seen.contains_key(&t))
        .map(|(&e, w)| (e, w))
        .collect();
    let alone = holders.len() == 1;
    !holders.is_empty()
        && holders
            .iter()
            .all(|&(entry, w)| tail_jump(&walks.starts, entry, w, t, alone))
}

/// Tells whether one walk reaches `t` only by jumps that leave the
/// function.
///
/// Every way in is an unconditional jump with the frame gone
/// ([`frame_gone`]); when no other walk holds `t`, it lies before the
/// walk's entry or past another start, so a block laid out after the jump
/// stays the jumper's own; and nothing the entry reaches without passing
/// `t` is reached from `t` too, so the code at `t` shares no block with
/// the jumper.
///
/// # Arguments
///
/// * `starts` - The known function starts.
/// * `entry` - The walk's entry.
/// * `w` - The walk.
/// * `t` - The jump target.
/// * `alone` - Whether no other walk holds `t`.
fn tail_jump(starts: &BTreeSet<u64>, entry: u64, w: &Walked, t: u64, alone: bool) -> bool {
    if t == entry || (alone && t > entry && starts.range((entry + 1)..t).next().is_none()) {
        return false;
    }
    let pred = predecessors(w);
    let body = reach(w, t, t);
    let mut ins = Vec::new();
    for i in w.seen.values().filter(|i| !body.contains(&i.va)) {
        edges(i, &mut |to| {
            if to == t {
                ins.push(i);
            }
        });
    }
    let jumps = !ins.is_empty()
        && w.tables.iter().all(|tab| !tab.targets.contains(&t))
        && ins.iter().all(|j| {
            j.flow() == Flow::Jump
                && j.target() == Some(t)
                && !j.predicated()
                && frame_gone(w, entry, j.va, &pred)
        });
    if !jumps {
        return false;
    }
    let before = reach(w, entry, t);
    !body.iter().any(|va| before.contains(va))
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
/// * `pred` - Each address's single predecessor ([`predecessors`]).
fn frame_gone(w: &Walked, entry: u64, jump: u64, pred: &BTreeMap<u64, Option<u64>>) -> bool {
    let mut va = jump;
    for _ in 0..FRAME_LOOK {
        if va == entry {
            return true;
        }
        let Some(p) = pred
            .get(&va)
            .copied()
            .flatten()
            .and_then(|p| w.seen.get(&p))
        else {
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

/// Returns the addresses of a walk reached from `from` without passing
/// `avoid`, `from` included.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `from` - Where to start.
/// * `avoid` - An address not passed through (equal to `from` to avoid
///   nothing but returning to it).
fn reach(w: &Walked, from: u64, avoid: u64) -> BTreeSet<u64> {
    let mut seen = BTreeSet::from([from]);
    let mut pending = vec![from];
    while let Some(va) = pending.pop() {
        let Some(i) = w.seen.get(&va) else {
            continue;
        };
        let mut go = |to: u64| {
            if to != avoid && w.seen.contains_key(&to) && seen.insert(to) {
                pending.push(to);
            }
        };
        edges(i, &mut go);
        for t in w.tables.iter().filter(|t| t.site == va) {
            t.targets.iter().for_each(|&x| go(x));
        }
    }
    seen
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
