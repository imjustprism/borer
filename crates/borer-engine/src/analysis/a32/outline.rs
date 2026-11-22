//! Tail calls an ARM32 walk took for blocks of its own: the jumps that
//! leave a function, and the functions they reach that nothing else names.
//!
//! A compiler ends a function with a jump to another when the call is the
//! last thing it does. When no symbol, call or pointer names that other
//! function, the jumper's walk follows the jump and keeps the function as
//! its own blocks. [`outlines`] takes such a target back out as a function
//! of its own when the jump reads as a tail call.

use std::collections::BTreeMap;

use super::{Walked, Walks, guarded};
use crate::isa::a32::{self, Flow, Index, Insn, Offset, Op, PC};

/// Promotes a tail call that was walked as a block of its caller.
///
/// Nothing but one unconditional jump reaches the block, and it lies
/// before the caller's entry or past another function's start. It is a
/// tail call when it is one straight run that returns without touching
/// the stack pointer, so not the caller's own epilogue
/// ([`straight_return`]), or when the jump comes right after a `pop`, so
/// the caller's frame is gone ([`after_pop`]), and no other walked
/// function holds it ([`owners`]): a jump into another function's body
/// splits nothing. The caller is walked again and the jump becomes a tail
/// call.
///
/// # Arguments
///
/// * `walks` - The walks, updated in place.
///
/// # Returns
///
/// Whether a block was promoted.
pub(super) fn outlines(walks: &mut Walks<'_>) -> bool {
    let mut promote = Vec::new();
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
            }
        }
    }
    promote.sort_unstable();
    promote.dedup();
    let promoted = !promote.is_empty();
    for t in promote {
        walks.starts.insert(t);
        walks.guessed.insert(t);
    }
    promoted
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
    let popped = match pop.op {
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
    };
    popped
        && jump.flow() == Flow::Jump
        && jump.target() == Some(t)
        && !jump.predicated()
        && !pop.predicated()
        && pop.next() == jump.va
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
        match i.flow() {
            Flow::Next | Flow::Call => note(i.va, i.next()),
            Flow::CondJump => {
                if let Some(t) = i.target() {
                    note(i.va, t);
                }
                note(i.va, i.next());
            }
            Flow::Jump => {
                if let Some(t) = i.target() {
                    note(i.va, t);
                }
                if guarded(i) {
                    note(i.va, i.next());
                }
            }
            Flow::Return if guarded(i) => note(i.va, i.next()),
            Flow::Return | Flow::Invalid => {}
        }
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
