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
use crate::isa::a32::{self, DpKind, Flow, Index, Insn, Offset, Op, Operand, PC};
use crate::program::Program;

/// Most targets [`shared_tails`] weighs in one round of [`outlines`]; the
/// rest wait for the next round.
const SHARED_MAX: usize = 1 << 10;
/// Most walks holding one target that [`shared_tails`] weighs it for.
const HOLDERS_MAX: usize = 64;
/// Most instructions of a target's code [`tail_jump`] follows.
const BODY_MAX: usize = 1 << 14;

/// Promotes a tail call that was walked as a block of its caller.
///
/// Nothing but one unconditional jump reaches the block, and it lies
/// before the caller's entry or past another function's start. It is a
/// tail call when it is one straight run that returns without touching
/// the stack pointer, so not the caller's own epilogue
/// ([`straight_return`]), or when the jump comes right after a `pop` that
/// gives back all the caller pushed ([`after_pop`], [`Shape::depth`]), so
/// the caller's frame is gone, and no other walked
/// function holds it ([`owners`]): a jump into another function's body
/// splits nothing. A block several walks hold is promoted when each of
/// them reaches it that way ([`shared_tails`]). The caller is walked again
/// and the jump becomes a tail call.
///
/// Every start read and edge followed for a walk (its [`Apart`],
/// predecessors and [`Shape`]) is charged to the round's [`Budget`]; when
/// it runs out, or the cancel flag in force is raised, the round stops
/// there and the discovery is marked incomplete.
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
    let mut budget = Budget::new(walks.fuel);
    for (&entry, w) in &walks.walked {
        if !budget.charge(0) {
            break;
        }
        let mut pred = None;
        let mut shape = None;
        let mut apart: Option<Apart> = None;
        for &t in &w.followed {
            if t == entry || walks.starts.contains(&t) {
                continue;
            }
            if t > entry && apart.is_none() {
                apart = Apart::of(&walks.starts, w, &mut budget);
            }
            let stepped = t > entry && apart.as_ref().is_some_and(|a| a.steps_over(entry, t));
            if budget.out || (!stepped && t > entry) {
                continue;
            }
            if pred.is_none() {
                pred = predecessors(w, &mut budget);
            }
            let Some(pred) = pred.as_ref() else {
                continue;
            };
            let mut balanced = |budget: &mut Budget| {
                if shape.is_none() {
                    shape = Shape::of(w, entry, budget);
                }
                shape.as_ref().is_some_and(|shape| {
                    pred.get(&t)
                        .copied()
                        .flatten()
                        .is_some_and(|j| shape.depth.get(&j) == Some(&Some(0)))
                })
            };
            if (stepped && straight_return(w, t, pred))
                || (after_pop(w, t, pred)
                    && balanced(&mut budget)
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
    if !budget.out {
        promote.extend(shared_tails(program, walks, &shared, &mut budget));
    }
    walks.fuel = budget.left;
    walks.incomplete |= budget.out;
    promote.sort_unstable();
    promote.dedup();
    let promoted = !promote.is_empty();
    for t in promote {
        walks.starts.insert(t);
        walks.guessed.insert(t);
    }
    promoted
}

/// The work a round of [`outlines`] may still do. Every edge, start and
/// lookup the round's passes make is charged here, and the cancel flag in
/// force is read at each charge.
struct Budget {
    /// Steps left: the walks' fuel when the round began, less what it did.
    left: u64,
    /// Whether the steps ran out or the cancel flag was raised.
    out: bool,
}

impl Budget {
    /// Makes a budget of `left` steps.
    ///
    /// # Arguments
    ///
    /// * `left` - The steps.
    fn new(left: u64) -> Self {
        Self { left, out: false }
    }

    /// Charges `n` steps.
    ///
    /// # Arguments
    ///
    /// * `n` - The steps.
    ///
    /// # Returns
    ///
    /// Whether the work may go on: `false` once the steps ran out or the
    /// cancel flag in force was raised.
    fn charge(&mut self, n: u64) -> bool {
        if !self.out {
            if n > self.left || crate::cancel::Cancel::raised() {
                self.out = true;
                self.left = 0;
            } else {
                self.left -= n;
            }
        }
        !self.out
    }
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
/// A walk whose entry another holder runs through is that holder's own
/// code, not another function reaching `t`, and is not counted. A target
/// more than [`HOLDERS_MAX`] walks hold is not weighed: it stays a block,
/// the safe answer, rather than cost every holder against every other.
///
/// Every step is charged to `budget`; when it runs out the targets not yet
/// weighed stay blocks. Each holder's [`Shape`] is made for the one target
/// and dropped after it, so the heap held is one walk's, not a round's.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks.
/// * `cands` - The targets, at most [`SHARED_MAX`].
/// * `budget` - The round's budget.
fn shared_tails(
    program: &Program,
    walks: &Walks<'_>,
    cands: &[u64],
    budget: &mut Budget,
) -> Vec<u64> {
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
            for &t in cands.range(lo..=hi) {
                if !budget.charge(1) {
                    return Vec::new();
                }
                if w.seen.contains_key(&t) {
                    holders.entry(t).or_default().push(entry);
                }
            }
        }
    }
    let mut found = Vec::new();
    for (t, mut held) in holders {
        let pairs =
            crate::num::from_usize(held.len()).saturating_mul(crate::num::from_usize(held.len()));
        if held.len() > HOLDERS_MAX || !budget.charge(pairs) {
            continue;
        }
        let inner: Vec<u64> = held
            .iter()
            .copied()
            .filter(|e| {
                held.iter()
                    .any(|o| o != e && walks.walked.get(o).is_some_and(|w| w.seen.contains_key(e)))
            })
            .collect();
        held.retain(|e| !inner.contains(e));
        let alone = held.len() == 1;
        let tail = held.iter().all(|entry| {
            walks
                .walked
                .get(entry)
                .is_some_and(|w| tail_jump(&walks.starts, *entry, w, t, alone, budget))
        });
        if tail && !budget.out {
            found.push(t);
        }
    }
    found
}

/// What [`tail_jump`] and the pop rule of [`outlines`] read off one walk.
struct Shape {
    /// Every instruction that falls, jumps or dispatches to each address
    /// of the walk.
    preds: BTreeMap<u64, Vec<u64>>,
    /// The stack depth before each instruction, in bytes from the entry's
    /// (a push makes it negative), or `None` where two paths disagree or
    /// an instruction before it moves `sp` in a way [`sp_step`] does not
    /// read. A conditional return or jump (`popne {r4, pc}`) moves `sp`
    /// only on the path that leaves, so the path past it keeps the depth;
    /// any other conditional move of `sp` leaves the depth unknown.
    depth: BTreeMap<u64, Option<i64>>,
}

impl Shape {
    /// Builds a walk's shape.
    ///
    /// # Arguments
    ///
    /// * `w` - The walk.
    /// * `entry` - Its entry.
    /// * `budget` - Charged one step per edge followed.
    ///
    /// # Returns
    ///
    /// The shape, or `None` when the budget ran out.
    fn of(w: &Walked, entry: u64, budget: &mut Budget) -> Option<Self> {
        let preds = all_preds(w, budget)?;
        let mut depth: BTreeMap<u64, Option<i64>> = BTreeMap::from([(entry, Some(0))]);
        let mut pending = vec![entry];
        while let Some(va) = pending.pop() {
            let (Some(i), Some(&d)) = (w.seen.get(&va), depth.get(&va)) else {
                continue;
            };
            let step = match sp_step(i) {
                Some(0) => Some(0),
                _ if guarded(i) => Some(0),
                _ if i.predicated() => None,
                k => k,
            };
            let after = d.zip(step).map(|(d, k)| d.saturating_add(k));
            let mut edges = 0u64;
            let mut next = |to: u64| {
                edges += 1;
                let new = match depth.get(&to) {
                    None => after,
                    Some(old) if *old == after || old.is_none() => return,
                    Some(_) => None,
                };
                if w.seen.contains_key(&to) {
                    depth.insert(to, new);
                    pending.push(to);
                }
            };
            successors(w, i, &mut next);
            if !budget.charge(edges) {
                return None;
            }
        }
        Some(Self { preds, depth })
    }
}

/// Returns how far an instruction moves `sp`, in bytes (a push is
/// negative), or `None` when it writes `sp` in a way not read.
///
/// Zero for one that does not write it; read are a `push` or `pop`
/// (`stmdb` and `ldmia` with writeback), a `vpush` or `vpop`, a load or
/// store that writes `sp` back by a constant, and an `add` or `sub` of a
/// constant to `sp`.
///
/// # Arguments
///
/// * `i` - The instruction.
fn sp_step(i: &Insn) -> Option<i64> {
    if !i.registers().writes.contains(&a32::SP) {
        return Some(0);
    }
    let words = |regs: u16| i64::from(regs.count_ones()) * 4;
    let vwords = |first: a32::Reg, count: u8| {
        let size = if matches!(first, a32::Reg::D(_)) {
            8
        } else {
            4
        };
        i64::from(count) * size
    };
    let sp_by = |addr: a32::Addr| match addr {
        a32::Addr {
            base: a32::SP,
            offset: Offset::Imm(step),
            index: Index::Pre | Index::Post,
        } => Some(i64::from(step)),
        _ => None,
    };
    match i.op {
        Op::Stm {
            rn: a32::SP,
            regs,
            wback: true,
            block: a32::Block::Db,
        } => Some(-words(regs)),
        Op::Ldm {
            rn: a32::SP,
            regs,
            wback: true,
            block: a32::Block::Ia,
        } => Some(words(regs)),
        Op::VStm {
            rn: a32::SP,
            first,
            count,
            wback: true,
            db: true,
        } => Some(-vwords(first, count)),
        Op::VLdm {
            rn: a32::SP,
            first,
            count,
            wback: true,
            db: false,
        } => Some(vwords(first, count)),
        Op::Load { rt, addr, .. } | Op::Store { rt, addr, .. } if rt != a32::SP => sp_by(addr),
        Op::Dp {
            kind,
            rd: a32::SP,
            rn: a32::SP,
            src: Operand::Imm { value, .. },
        } => match kind {
            DpKind::Add => Some(i64::from(value)),
            DpKind::Sub => Some(-i64::from(value)),
            _ => None,
        },
        _ => None,
    }
}

/// Tells whether one walk reaches `t` only by jumps that leave the
/// function.
///
/// When no other walk holds `t`, it lies before the walk's entry or past
/// the start of a function the walk does not run through ([`steps_over`]),
/// so a block laid out after the jump stays the jumper's own. Every way
/// into `t` from outside the code `t` reaches is an unconditional jump at
/// the entry's stack depth, the frame given back or never built
/// ([`Shape::depth`]); no instruction of that code is reached from outside
/// it, and the entry is not in it, so the code at `t` shares no block with
/// the jumper. Code of more than [`BODY_MAX`] instructions is not
/// followed: the target stays. The walk's [`Shape`] is made only once
/// those cheaper tests pass, and dropped on return.
///
/// # Arguments
///
/// * `starts` - The known function starts.
/// * `entry` - The walk's entry.
/// * `w` - The walk.
/// * `t` - The jump target.
/// * `alone` - Whether no other walk holds `t`.
/// * `budget` - Charged for every start read and edge followed.
fn tail_jump(
    starts: &BTreeSet<u64>,
    entry: u64,
    w: &Walked,
    t: u64,
    alone: bool,
    budget: &mut Budget,
) -> bool {
    if t == entry || (alone && t > entry && !steps_over(starts, w, entry, t, budget)) {
        return false;
    }
    let Some(body) = reach(w, t, BODY_MAX, budget) else {
        return false;
    };
    if body.contains(&entry) {
        return false;
    }
    let Some(shape) = Shape::of(w, entry, budget) else {
        return false;
    };
    let preds = |va: u64| shape.preds.get(&va).map_or(&[][..], Vec::as_slice);
    let mut shut = true;
    for &b in body.iter().filter(|&&b| b != t) {
        let from = preds(b);
        if !budget.charge(crate::num::from_usize(from.len()))
            || !from.iter().all(|p| body.contains(p))
        {
            shut = false;
            break;
        }
    }
    let ins: Vec<u64> = preds(t)
        .iter()
        .copied()
        .filter(|p| !body.contains(p))
        .collect();
    shut && !ins.is_empty()
        && ins.iter().all(|p| {
            w.seen.get(p).is_some_and(|j| {
                j.flow() == Flow::Jump
                    && j.target() == Some(t)
                    && !j.predicated()
                    && shape.depth.get(p) == Some(&Some(0))
            })
        })
}

/// Tells whether a start the walk does not run through lies between its
/// entry and `t`, a target past the entry.
///
/// The starts between them are read one by one: this answers the one pair
/// [`tail_jump`] asks about, where [`Apart`] would hold a walk's whole
/// span.
///
/// # Arguments
///
/// * `starts` - The known function starts.
/// * `w` - The walk.
/// * `entry` - Its entry.
/// * `t` - The target, past `entry`.
/// * `budget` - Charged one step per start read.
fn steps_over(starts: &BTreeSet<u64>, w: &Walked, entry: u64, t: u64, budget: &mut Budget) -> bool {
    for s in starts.range(entry.saturating_add(1)..t) {
        if !budget.charge(1) {
            return false;
        }
        if !w.seen.contains_key(s) {
            return true;
        }
    }
    false
}

/// The function starts within a walk's span the walk does not run
/// through: a start the jumper's own code falls into is no other function
/// it steps over.
#[derive(Default)]
struct Apart {
    /// Those starts, from the walk's lowest address to its highest.
    starts: BTreeSet<u64>,
    /// The first start past the walk's highest address: apart too.
    past: Option<u64>,
}

impl Apart {
    /// Finds the starts within a walk's span it does not run through.
    ///
    /// # Arguments
    ///
    /// * `starts` - The known function starts.
    /// * `w` - The walk.
    /// * `budget` - Charged one step per start read.
    ///
    /// # Returns
    ///
    /// The starts, or `None` when the budget ran out.
    fn of(starts: &BTreeSet<u64>, w: &Walked, budget: &mut Budget) -> Option<Self> {
        let (Some((&lo, _)), Some((&hi, _))) = (w.seen.first_key_value(), w.seen.last_key_value())
        else {
            return Some(Self::default());
        };
        let mut apart = Self {
            starts: BTreeSet::new(),
            past: starts.range(hi.saturating_add(1)..).next().copied(),
        };
        for &s in starts.range(lo..=hi) {
            if !budget.charge(1) {
                return None;
            }
            if !w.seen.contains_key(&s) {
                apart.starts.insert(s);
            }
        }
        Some(apart)
    }

    /// Tells whether a start the walk does not run through lies between
    /// its entry and `t`, a target past the entry.
    ///
    /// # Arguments
    ///
    /// * `entry` - The walk's entry.
    /// * `t` - The target, past `entry`.
    fn steps_over(&self, entry: u64, t: u64) -> bool {
        let from = entry.saturating_add(1);
        self.starts.range(from..t).next().is_some() || self.past.is_some_and(|p| p < t)
    }
}

/// Returns the addresses of a walk reached from `from`, `from` included,
/// or `None` past `cap` of them or once the budget runs out.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `from` - Where to start.
/// * `cap` - Most addresses gathered.
/// * `budget` - Charged one step per edge followed.
fn reach(w: &Walked, from: u64, cap: usize, budget: &mut Budget) -> Option<BTreeSet<u64>> {
    let mut seen = BTreeSet::from([from]);
    let mut pending = vec![from];
    while let Some(va) = pending.pop() {
        if seen.len() > cap {
            return None;
        }
        let Some(i) = w.seen.get(&va) else {
            continue;
        };
        let mut edges = 0u64;
        let mut go = |to: u64| {
            edges += 1;
            if w.seen.contains_key(&to) && seen.insert(to) {
                pending.push(to);
            }
        };
        successors(w, i, &mut go);
        if !budget.charge(edges) {
            return None;
        }
    }
    Some(seen)
}

/// Calls `edge` with each address an instruction of a walk passes control
/// to inside its function.
///
/// Those are the edges [`edges`] names, and the cases of the jump table
/// it dispatches through, if the walk resolved one.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `i` - One of its instructions.
/// * `edge` - Called with each address.
fn successors(w: &Walked, i: &Insn, edge: &mut impl FnMut(u64)) {
    edges(i, edge);
    if let Some(t) = w.tables.get(&i.va) {
        t.targets.iter().for_each(|&x| edge(x));
    }
}

/// Returns, for each address of a walk, every instruction of it that
/// falls, jumps or dispatches there ([`successors`]).
///
/// # Arguments
///
/// * `w` - The walk.
/// * `budget` - Charged one step per edge.
///
/// # Returns
///
/// The map, or `None` when the budget ran out.
fn all_preds(w: &Walked, budget: &mut Budget) -> Option<BTreeMap<u64, Vec<u64>>> {
    let mut preds: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for i in w.seen.values() {
        let mut edges = 0u64;
        successors(w, i, &mut |to| {
            edges += 1;
            if w.seen.contains_key(&to) {
                preds.entry(to).or_default().push(i.va);
            }
        });
        if !budget.charge(edges) {
            return None;
        }
    }
    Some(preds)
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
/// * `budget` - Charged one step per edge.
///
/// # Returns
///
/// The map, or `None` when the budget ran out.
fn predecessors(w: &Walked, budget: &mut Budget) -> Option<BTreeMap<u64, Option<u64>>> {
    let all = all_preds(w, budget)?;
    Some(
        all.into_iter()
            .map(|(to, from)| {
                let one = match from.as_slice() {
                    [one] => Some(*one),
                    _ => None,
                };
                (to, one)
            })
            .collect(),
    )
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
