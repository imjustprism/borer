//! Function discovery for ARM32 (A32 and T32) code.
//!
//! [`discover()`] finds an ARM32 program's functions from the entry point,
//! the symbols and the extents the file declares, as the arm64 walk does:
//! it follows every branch, takes a `bl` or `blx` target as a new function
//! and a jump into a known start as a tail call, ends a path at a call to
//! a function named as never returning, and walks the cases of a jump
//! table it can bound ([`table`]): a `tbb` or `tbh`, the A32 `adr` and
//! `add pc` of a position-independent table, and an indexed load of `pc`
//! from a table after it or at an `adr`. Each instruction is decoded in
//! the instruction set the program says its address is in, an `IT`
//! block's conditions carried along a fall-through.
//!
//! The entry point, the symbols and the calls miss what only a pointer
//! names (an interrupt handler, a callback) and what nothing names; the
//! [`guess`] module finds those from the image's words and from the gaps
//! between the functions found. A straight run of instructions that
//! returns, reached by one unconditional jump from a function that
//! already stepped over another function, is that jump's target
//! ([`outlines`]), not a block of the jumper.
//!
//! An instruction under a condition that moves control (`bxeq lr`,
//! `popne {r4, pc}`, `blne f`) is a block of its own. When the block before
//! it falls into it and nothing else jumps to it, that block ends in the
//! test of the condition, a [`BlockTerm::Cond`] whose successors are the
//! instruction after it (the condition fails) and the instruction itself
//! (it holds); the decompiler reads that test as the branch at
//! [`a32::SKIP`]. The instruction's own block then has the successors of
//! what it does. A linkage stub (a PLT entry, an import thunk) is named
//! after the import its slot holds ([`stub_slot`]).

use std::collections::{BTreeMap, BTreeSet};

mod guess;
mod returns;

use super::functions::helpers::is_noreturn_name;
use super::functions::{build_callers_and_names, fuel_for, mix, push_site};
use super::{Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, bare_name, seeds};
use crate::isa::a32::{
    self, Cond, DpKind, Flow, Index, Insn, ItState, Mode, Offset, Op, Operand, PC,
};
use crate::program::{Program, SymbolKind};

/// Rounds of gap guessing: a guess the walks found after it show to be
/// data is dropped, and the code it hid is guessed at again.
const GAP_ROUNDS: usize = 2;
/// Most instructions one walk decodes.
const WALK_MAX: usize = 1 << 18;
/// Most instructions one walk from a guess decodes: a guess into data can
/// decode a long way, and nothing it decodes is kept when it is rejected.
const GUESS_MAX: usize = 1 << 14;
/// Most jump-table entries read for one dispatch.
const TABLE_MAX: u64 = 1024;
/// Instructions looked back over for a dispatch's bound and base.
const LOOK_BACK: usize = 16;
/// Instructions a linkage stub spends reaching its slot.
const STUB_MAX: usize = 4;
/// Where every fingerprint starts: the FNV-1a offset basis.
const HASH_SEED: u64 = 0xcbf2_9ce4_8422_2325;

/// Decodes the instruction at `va` in the instruction set the program says
/// it is in.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
/// * `it` - The `IT` state before it; advanced past it.
///
/// # Returns
///
/// The instruction, or `None` when the address is not executable or holds
/// too few bytes.
pub(crate) fn decode(program: &Program, va: u64, it: &mut ItState) -> Option<Insn> {
    if !super::is_executable_va(program, va) {
        return None;
    }
    let bytes = program.read_va_upto(va, 4)?;
    a32::decode(bytes, va, program.modes.at(va), it)
}

/// Tells whether an instruction moves control under a condition: a
/// conditional return, call or jump that is no conditional branch.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(crate) fn guarded(i: &Insn) -> bool {
    i.predicated() && i.flow() != Flow::Next
}

/// Returns the test in front of a run of instructions under one condition.
///
/// The run ends in a guarded instruction ([`guarded`]), and the block
/// before it ends in the test: a conditional branch past the run, under
/// the inverse of its condition, at the run's first address tagged
/// [`a32::SKIP`].
///
/// # Arguments
///
/// * `first` - The run's first instruction.
/// * `end` - The address after the run.
pub(crate) fn skip(first: &Insn, end: u64) -> Insn {
    Insn {
        va: first.va | a32::SKIP,
        len: 0,
        mode: first.mode,
        cond: a32::invert(first.cond),
        sets: false,
        op: Op::B { target: end },
        word: 0,
    }
}

/// The slot a linkage stub at `va` jumps through: a PLT entry (`add ip,
/// pc, #a; add ip, ip, #b; ldr pc, [ip, #c]!`) or a Windows import thunk
/// (`movw ip, #lo; movt ip, #hi; ldr pc, [ip]`).
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The stub's first instruction.
///
/// # Returns
///
/// The slot's address, or `None` when the code is no such stub.
pub(crate) fn stub_slot(program: &Program, va: u64) -> Option<u64> {
    let mut regs: BTreeMap<a32::Reg, u64> = BTreeMap::new();
    let mut it = ItState::default();
    let mut at = va;
    for _ in 0..STUB_MAX {
        let i = decode(program, at, &mut it)?;
        if let Op::Adr { rd, target } = i.op {
            regs.insert(rd, target);
        } else if let Op::Movw { rd, imm } = i.op {
            regs.insert(rd, u64::from(imm));
        } else if let Op::Movt { rd, imm } = i.op {
            let lo = regs.get(&rd).copied()? & 0xffff;
            regs.insert(rd, lo | (u64::from(imm) << 16));
        } else if let Op::Dp {
            kind: DpKind::Add,
            rd,
            rn,
            src: Operand::Imm { value, .. },
        } = i.op
        {
            let base = if rn == PC {
                i.pc()
            } else {
                regs.get(&rn).copied()?
            };
            regs.insert(rd, base.wrapping_add(u64::from(value)) & 0xffff_ffff);
        } else if let Op::Load {
            rt: PC,
            addr:
                a32::Addr {
                    base,
                    offset: Offset::Imm(d),
                    index: Index::Offset | Index::Pre,
                },
            ..
        } = i.op
        {
            return Some(regs.get(&base)?.wrapping_add_signed(i64::from(d)) & 0xffff_ffff);
        } else {
            return None;
        }
        at = i.next();
    }
    None
}

/// A resolved jump table: the dispatch, its cases and where the table
/// lies.
#[derive(Debug, Clone)]
struct Table {
    /// The dispatching instruction.
    site: u64,
    /// The case targets, in table order.
    targets: Vec<u64>,
    /// The bytes the table's entries occupy.
    bytes: std::ops::Range<u64>,
}

/// The straight-line instructions before `at`, nearest first.
///
/// # Arguments
///
/// * `seen` - The walk's instructions by address.
/// * `at` - The dispatch.
fn before(seen: &BTreeMap<u64, Insn>, at: u64) -> Vec<&Insn> {
    let mut out = Vec::new();
    let mut cur = at;
    while out.len() < LOOK_BACK {
        let Some((_, p)) = seen.range(..cur).next_back() else {
            break;
        };
        if p.next() != cur {
            break;
        }
        out.push(p);
        cur = p.va;
    }
    out
}

/// Returns the number of cases a dispatch's guard admits.
///
/// The guard is a `cmp` with an immediate followed by a `bhi` to the
/// default or a return under `hi` (one more than the immediate) or the
/// same under `hs` (the immediate), or an `and` with a mask one short of a
/// power of two. A dispatch under `ls` or `lo` is its own guard: it runs
/// only when the `cmp` admits the case.
///
/// # Arguments
///
/// * `older` - The instructions before the dispatch, nearest first.
/// * `own` - The dispatch's own condition.
fn bound(older: &[&Insn], own: Cond) -> Option<u64> {
    let mut guard = if own == Cond::Ls {
        Some(Cond::Hi)
    } else if own == Cond::Lo {
        Some(Cond::Hs)
    } else {
        None
    };
    for i in older {
        if matches!(i.flow(), Flow::CondJump | Flow::Jump | Flow::Return)
            && matches!(i.cond, Cond::Hi | Cond::Hs)
        {
            guard = Some(i.cond);
        } else if let Op::Dp {
            kind: DpKind::Cmp,
            src: Operand::Imm { value, .. },
            ..
        } = i.op
        {
            let more = u64::from(guard? == Cond::Hi);
            return Some(u64::from(value) + more);
        } else if let Op::Dp {
            kind: DpKind::And,
            src: Operand::Imm { value, .. },
            ..
        } = i.op
            && value.checked_add(1).is_some_and(u32::is_power_of_two)
            && guard.is_none()
        {
            return Some(u64::from(value) + 1);
        }
    }
    None
}

/// Resolves the jump table an indirect jump dispatches through.
///
/// # Arguments
///
/// * `program` - The image.
/// * `seen` - The walk's instructions by address.
/// * `j` - The indirect jump.
///
/// # Returns
///
/// The table, or `None` when the jump is no dispatch the walk can bound.
fn table(program: &Program, seen: &BTreeMap<u64, Insn>, j: &Insn) -> Option<Table> {
    let older = before(seen, j.va);
    let count = bound(&older, j.cond)?.min(TABLE_MAX);
    let word = |at: u64, n: usize| -> Option<u64> {
        let b = program.read_va(at, n)?;
        Some(
            b.iter()
                .rev()
                .fold(0u64, |acc, x| (acc << 8) | u64::from(*x)),
        )
    };
    let adr = |reg: a32::Reg| {
        older.iter().find_map(|i| {
            if let Op::Adr { rd, target } = i.op
                && rd == reg
            {
                Some(target)
            } else {
                None
            }
        })
    };
    let (targets, bytes): (Option<Vec<u64>>, _) = if let Op::Tb { half, rn, .. } = j.op {
        let base = if rn == PC { j.pc() } else { adr(rn)? };
        let size = if half { 2 } else { 1 };
        let targets = (0..count)
            .map(|k| {
                let e = word(base + k * size, usize::try_from(size).ok()?)?;
                Some((j.pc() + 2 * e) & 0xffff_ffff)
            })
            .collect();
        (targets, base..base + count * size)
    } else if let Op::Dp {
        kind: DpKind::Add,
        rd: PC,
        rn: rb,
        src:
            Operand::Reg {
                rm: re,
                shift: a32::Shift::Lsl,
                amount: 0,
            },
    } = j.op
    {
        older.iter().find(|i| {
            matches!(i.op, Op::Load { rt, addr: a32::Addr { base, offset: Offset::Reg { amount: 2, .. }, .. }, .. } if rt == re && base == rb)
        })?;
        let base = adr(rb)?;
        let targets = (0..count)
            .map(|k| {
                let e = word(base + k * 4, 4)?;
                Some((base.wrapping_add(e) & 0xffff_ffff) & !1)
            })
            .collect();
        (targets, base..base + count * 4)
    } else if let Op::Load {
        rt: PC,
        addr:
            a32::Addr {
                base: rb,
                offset: Offset::Reg { amount: 2, .. },
                index: Index::Offset,
            },
        ..
    } = j.op
    {
        let base = if rb == PC { j.pc() } else { adr(rb)? };
        let targets = (0..count)
            .map(|k| word(base + k * 4, 4).map(|t| t & !1))
            .collect();
        (targets, base..base + count * 4)
    } else {
        return None;
    };
    let targets = targets?;
    targets
        .iter()
        .all(|t| super::is_executable_va(program, *t))
        .then_some(Table {
            site: j.va,
            targets,
            bytes,
        })
}

/// What one walk found.
struct Walked {
    /// The instructions by address.
    seen: BTreeMap<u64, Insn>,
    /// The functions it calls or tail-calls.
    callees: BTreeSet<u64>,
    /// Jump targets it followed.
    followed: BTreeSet<u64>,
    /// The jump tables it resolved.
    tables: Vec<Table>,
    /// Whether a path ran into bytes that decode to no instruction.
    bad: bool,
    /// Whether a path leaves the function: a return, a jump through a
    /// register or to another function, or a call that does not return.
    exits: bool,
    /// The covered addresses a guessed walk ran into.
    into: BTreeSet<u64>,
    /// The known starts its jumps reach: tail calls.
    tails: BTreeSet<u64>,
}

/// Walks one function from its entry.
///
/// A call falling through to a known start never returns: no function
/// runs on into another's entry. A jump below the entry stays inside the
/// function unless it reaches a known start: a cold block laid out before
/// the entry is still the function's own code.
///
/// # Arguments
///
/// * `program` - The image.
/// * `entry` - Where to start.
/// * `starts` - Known function starts: a jump into one is a tail call.
/// * `noreturn` - Functions that never return.
/// * `guess` - The bytes already covered ([`Walks::covered`]) when
///   nothing says code starts at `entry`: the walk then stops at the first
///   word that decodes to no instruction or lies in them, and after
///   [`GUESS_MAX`] instructions, which rejects the guess: a function cut
///   short would leave reachable code out.
fn walk(
    program: &Program,
    entry: u64,
    starts: &BTreeSet<u64>,
    noreturn: &BTreeSet<u64>,
    guess: Option<&BTreeMap<u64, (u64, bool)>>,
) -> Walked {
    let mut w = Walked {
        seen: BTreeMap::new(),
        callees: BTreeSet::new(),
        followed: BTreeSet::new(),
        tables: Vec::new(),
        bad: false,
        exits: false,
        into: BTreeSet::new(),
        tails: BTreeSet::new(),
    };
    let limit = if guess.is_some() { GUESS_MAX } else { WALK_MAX };
    let mut pending: Vec<(u64, ItState)> = vec![(entry, ItState::default())];
    let leaves = |t: u64| t != entry && starts.contains(&t);
    while let Some((va, mut it)) = pending.pop() {
        if w.seen.contains_key(&va)
            || w.seen.len() >= limit
            || (guess.is_some() && (w.bad || !w.into.is_empty()))
        {
            continue;
        }
        if guess.is_some_and(|c| guess::covers(c, va).is_some()) {
            w.into.insert(va);
            continue;
        }
        let Some(i) = decode(program, va, &mut it).filter(|i| i.op != Op::Invalid) else {
            w.bad = true;
            continue;
        };
        w.seen.insert(va, i);
        let next = i.next();
        let falls = guarded(&i);
        let follow = |t: u64, w: &mut Walked, pending: &mut Vec<(u64, ItState)>| {
            if leaves(t) {
                w.callees.insert(t);
                w.tails.insert(t);
                w.exits = true;
            } else {
                w.followed.insert(t);
                pending.push((t, ItState::default()));
            }
        };
        match i.flow() {
            Flow::Next => pending.push((next, it)),
            Flow::CondJump => {
                if let Some(t) = i.target() {
                    follow(t, &mut w, &mut pending);
                }
                pending.push((next, it));
            }
            Flow::Jump => {
                match i.target() {
                    Some(t) => follow(t, &mut w, &mut pending),
                    None => match table(program, &w.seen, &i) {
                        Some(tab) => {
                            for &t in &tab.targets {
                                w.followed.insert(t);
                                pending.push((t, ItState::default()));
                            }
                            w.tables.push(tab);
                        }
                        None => w.exits = true,
                    },
                }
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Call => {
                let target = i.target().filter(|t| super::is_executable_va(program, *t));
                w.callees.extend(target);
                let returns =
                    !target.is_some_and(|t| noreturn.contains(&t)) && !starts.contains(&next);
                if falls || returns {
                    pending.push((next, it));
                }
                w.exits |= !returns;
            }
            Flow::Return => {
                w.exits = true;
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Invalid => {}
        }
    }
    w.bad |= guess.is_some() && w.seen.len() >= limit;
    w
}

/// Walks from an address a caller asked for that no discovered function
/// contains.
///
/// The same walk as [`walk`], with two stops a gap guess treats as
/// failure. A fall into this walk's own literal pool, or into code
/// another function already owns, ends the path: the pool is data, and
/// the neighbor is not part of this function. A jump into either is the
/// same stop, so the bytes already found stay a function of their own.
/// Padding that falls out of the walk, a `nop` before that pool or the
/// next function, is dropped: a block ending on it would fall out of
/// the function. A call to a function that never returns ends the path,
/// the same way [`walk`] ends one.
///
/// # Arguments
///
/// * `program` - The image.
/// * `entry` - The requested address, even.
/// * `starts` - Entries already discovered. A jump to one is a tail call.
/// * `noreturn` - Functions that never return ([`gap_noreturn`]).
/// * `covered` - Ranges those functions own.
fn walk_gap(
    program: &Program,
    entry: u64,
    starts: &BTreeSet<u64>,
    noreturn: &BTreeSet<u64>,
    covered: &BTreeMap<u64, (u64, bool)>,
) -> Walked {
    let mut w = Walked {
        seen: BTreeMap::new(),
        callees: BTreeSet::new(),
        followed: BTreeSet::new(),
        tables: Vec::new(),
        bad: false,
        exits: false,
        into: BTreeSet::new(),
        tails: BTreeSet::new(),
    };
    let mut pool: BTreeSet<u64> = BTreeSet::new();
    let mut pending: Vec<(u64, ItState)> = vec![(entry, ItState::default())];
    while let Some((va, mut it)) = pending.pop() {
        if w.seen.contains_key(&va) || w.seen.len() >= GUESS_MAX || w.bad {
            continue;
        }
        if pool.contains(&va) || guess::covers(covered, va).is_some() {
            w.exits = true;
            continue;
        }
        let Some(i) = decode(program, va, &mut it).filter(|i| i.op != Op::Invalid) else {
            w.bad = true;
            continue;
        };
        if let Some(lit) = i.literal() {
            pool.extend(lit..lit.saturating_add(4));
        }
        w.seen.insert(va, i);
        let next = i.next();
        let falls = guarded(&i);
        let follow = |t: u64, w: &mut Walked, pending: &mut Vec<(u64, ItState)>| {
            if t != entry && starts.contains(&t) {
                w.callees.insert(t);
                w.tails.insert(t);
                w.exits = true;
            } else {
                w.followed.insert(t);
                pending.push((t, ItState::default()));
            }
        };
        match i.flow() {
            Flow::Next => pending.push((next, it)),
            Flow::CondJump => {
                if let Some(t) = i.target() {
                    follow(t, &mut w, &mut pending);
                }
                pending.push((next, it));
            }
            Flow::Jump => {
                match i.target() {
                    Some(t) => follow(t, &mut w, &mut pending),
                    None => match table(program, &w.seen, &i) {
                        Some(tab) => {
                            for &t in &tab.targets {
                                w.followed.insert(t);
                                pending.push((t, ItState::default()));
                            }
                            w.tables.push(tab);
                        }
                        None => w.exits = true,
                    },
                }
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Call => {
                let target = i.target().filter(|t| super::is_executable_va(program, *t));
                w.callees.extend(target);
                let returns =
                    !target.is_some_and(|t| noreturn.contains(&t)) && !starts.contains(&next);
                if falls || returns {
                    pending.push((next, it));
                }
                w.exits |= !returns;
            }
            Flow::Return => {
                w.exits = true;
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Invalid => {}
        }
    }
    while w
        .seen
        .last_key_value()
        .is_some_and(|(_, i)| gap_padding(i) && !w.seen.contains_key(&i.next()))
    {
        w.seen.pop_last();
        w.exits = true;
    }
    w.bad |= w.seen.len() >= GUESS_MAX;
    w
}

/// Whether an instruction is padding a compiler inserted between code and
/// the bytes after it: zero, or a `nop` in either instruction set.
///
/// # Arguments
///
/// * `insn` - The instruction.
fn gap_padding(insn: &Insn) -> bool {
    match insn.mode {
        Mode::Thumb => insn.len == 2 && matches!(insn.word & 0xffff, 0 | 0xbf00 | 0x46c0),
        Mode::Arm => insn.len == 4 && matches!(insn.word, 0 | 0xe1a0_0000 | 0xe320_f000),
    }
}

/// Whether a decoded block contains `va`.
///
/// A function's `[start, end)` is the lowest and highest byte it decoded,
/// so a later entry that reached backward leaves a hole in that span.
/// An address in the hole is not inside the function. One in a block is.
///
/// # Arguments
///
/// * `functions` - The functions discovery kept.
/// * `va` - The address, even.
/// * `earlier_only` - Count only a function whose entry is at or below `va`.
fn gap_owned(functions: &[Function], va: u64, earlier_only: bool) -> bool {
    functions.iter().any(|f| {
        (!earlier_only || f.entry <= va) && f.blocks.iter().any(|b| va >= b.start && va < b.end)
    })
}

/// The bytes discovery already decoded, merged, leaving out the body a
/// later function entered by jumping backward.
///
/// A block that starts at `va` belongs to a function whose entry is after
/// `va`: a thunk in front of that body. The walk claims that block and
/// every other block of that function except the one that holds the
/// thunk's entry, so a branch inside the body stays in the recovered
/// function. The thunk's block stays covered, and so does every block of
/// every other function.
///
/// # Arguments
///
/// * `functions` - The functions discovery kept.
/// * `va` - The address the walk starts at.
fn gap_covered(functions: &[Function], va: u64) -> BTreeMap<u64, (u64, bool)> {
    let mut spans: Vec<(u64, u64)> = Vec::new();
    for f in functions {
        let stolen = f.entry > va && f.blocks.iter().any(|b| b.start == va);
        for b in &f.blocks {
            if b.end <= b.start {
                continue;
            }
            let thunk = b.start <= f.entry && f.entry < b.end;
            if stolen && !thunk {
                continue;
            }
            spans.push((b.start, b.end));
        }
    }
    spans.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (start, end) in spans {
        if let Some(last) = merged.last_mut()
            && start <= last.1
        {
            last.1 = last.1.max(end);
            continue;
        }
        merged.push((start, end));
    }
    merged
        .into_iter()
        .map(|(start, end)| (start, (end, true)))
        .collect()
}

/// Walks from `va` and returns the walk when it is a clean ARM32 gap.
///
/// The walk uses the same rules as [`guess::try_seed`] for a pointer seed:
/// `va` is in an executable section, does not read as a string, is not inside
/// an existing function's blocks, decodes without running into covered bytes
/// or calling into the middle of a function, does not open like data, and
/// either exits or is a closed loop.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `functions` - The functions discovery kept.
/// * `va` - The address a decompile asked for, with its Thumb bit cleared.
///
/// # Returns
///
/// The walk, or `None` when `va` is not a clean ARM32 gap.
fn function_at_gap(program: &Program, functions: &[Function], va: u64) -> Option<Walked> {
    if program.arch != crate::program::Arch::Arm {
        return None;
    }
    if program.section_at(va).is_none_or(|s| !s.executable) || guess::texty(program, va) {
        return None;
    }
    if gap_owned(functions, va, true) {
        return None;
    }
    let opens_block = functions
        .iter()
        .any(|f| f.blocks.iter().any(|b| b.start == va));
    if gap_owned(functions, va, false) && !opens_block {
        return None;
    }
    let covered = gap_covered(functions, va);
    let starts: BTreeSet<u64> = functions.iter().map(|f| f.entry).collect();
    let noreturn = gap_noreturn(program, functions);
    let w = walk_gap(program, va, &starts, &noreturn, &covered);
    let free = |a: u64| guess::covers(&covered, a).is_none();
    let ok = !w.bad
        && w.into.is_empty()
        && (w.exits || guess::closed(&w))
        && !guess::dead_start(&w, va)
        && !w.seen.is_empty()
        && w.seen
            .values()
            .all(|i| free(i.va) && free(i.next().saturating_sub(1)));
    ok.then_some(w)
}

/// Adds a function at `va` to `analysis` when no discovered function
/// contains it ([`Analysis::start_gap_function`]).
///
/// # Arguments
///
/// * `program` - The image the analysis was computed from.
/// * `analysis` - That analysis, updated in place.
/// * `va` - The address asked for.
///
/// # Returns
///
/// The new function's entry, or `None` when `va` is not a clean ARM32 gap.
pub(crate) fn start_gap_function(
    program: &Program,
    analysis: &mut Analysis,
    va: u64,
) -> Option<u64> {
    let entry = va & !1;
    let mut work = vec![entry];
    let mut added = Vec::new();
    while let Some(next) = work.pop() {
        let Some(w) = function_at_gap(program, &analysis.functions, next) else {
            if next == entry {
                return None;
            }
            continue;
        };
        let (func, mut sites) = assemble(next, &w);
        data_refs(program, &w, &mut |t, site| {
            sites.push((t, site, RefKind::Data));
        });
        for &c in &func.callees {
            if !analysis.functions.iter().any(|f| f.entry == c) {
                work.push(c);
            }
        }
        added.push((next, func.callees.clone()));
        let pos = analysis.functions.partition_point(|f| f.entry < next);
        analysis.functions.insert(pos, func);
        for t in &w.tables {
            analysis.jump_tables.insert(t.site, t.targets.clone());
        }
        for (target, site, kind) in sites {
            push_site(&mut analysis.xrefs, target, site, kind, Some(next));
            if let Some(list) = analysis.xrefs.get_mut(&target) {
                list.sort_by_key(|s| s.va);
            }
        }
    }
    analysis.entry_index.clear();
    for (i, f) in analysis.functions.iter().enumerate() {
        analysis.entry_index.insert(f.entry, i);
    }
    for (caller, callees) in added {
        for callee in callees {
            if let Some(f) = analysis.function_mut(callee)
                && let Err(at) = f.callers.binary_search(&caller)
            {
                f.callers.insert(at, caller);
            }
        }
    }
    analysis.index_refs();
    infer_returns(program, analysis);
    analysis.derived.forget_all();
    Some(entry)
}

/// Addresses a gap walk treats as never returning.
///
/// Discovery walks with this same set: a symbol that is not an import and
/// whose name never returns, a function already found with such a name,
/// and an import thunk whose slot names one ([`stub_slot`]). A call to
/// one of them ends the path.
///
/// # Arguments
///
/// * `program` - The image.
/// * `functions` - The functions discovery kept.
fn gap_noreturn(program: &Program, functions: &[Function]) -> BTreeSet<u64> {
    let mut noreturn: BTreeSet<u64> = program
        .symbols
        .iter()
        .filter(|s| s.kind != SymbolKind::Import && s.addr != 0 && noreturn_name(&s.name))
        .map(|s| s.addr)
        .collect();
    let imports: BTreeMap<u64, &str> = program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect();
    for f in functions {
        if f.name.as_deref().is_some_and(noreturn_name) {
            noreturn.insert(f.entry);
        }
        if let Some(slot) = stub_slot(program, f.entry)
            && imports.get(&slot).is_some_and(|n| noreturn_name(n))
        {
            noreturn.insert(f.entry);
        }
    }
    noreturn
}

/// Finds the guarded instructions ([`guarded`]) whose condition the block
/// before them can test, each with the run of instructions under the same
/// condition leading up to it.
///
/// A run starts after an instruction that falls through to it, is no
/// branch target nor the entry, and holds instructions under the guarded
/// one's condition that set no flags.
///
/// # Arguments
///
/// * `entry` - The function's entry.
/// * `w` - The walk.
/// * `targets` - The branch and table targets.
///
/// # Returns
///
/// Each run's first address, with its guarded instruction's.
fn groups(entry: u64, w: &Walked, targets: &BTreeSet<u64>) -> BTreeMap<u64, u64> {
    let mut out = BTreeMap::new();
    for g in w.seen.values().filter(|g| guarded(g)) {
        let free = |va: u64| va != entry && !targets.contains(&va);
        let mut start = g.va;
        let mut held = 1;
        while let Some((_, p)) = w.seen.range(..start).next_back() {
            held += 1;
            let joins = held <= a32::RUN_MAX
                && free(start)
                && p.next() == start
                && p.predicated()
                && p.cond == g.cond
                && p.flow() == Flow::Next
                && !p.sets;
            if !joins {
                break;
            }
            start = p.va;
        }
        let opens = free(start)
            && w.seen
                .range(..start)
                .next_back()
                .is_some_and(|(_, p)| p.next() == start && p.flow() == Flow::Next && !guarded(p));
        if opens {
            out.insert(start, g.va);
        }
    }
    out
}

/// Builds a function's record and its references from its walk.
///
/// # Arguments
///
/// * `entry` - The entry.
/// * `w` - The walk.
///
/// # Returns
///
/// The function (callers empty, name unset) and its references.
fn assemble(entry: u64, w: &Walked) -> (Function, Vec<(u64, u64, RefKind)>) {
    let insns: Vec<&Insn> = w.seen.values().collect();
    let present = |va: u64| w.seen.contains_key(&va);
    let mut targets: BTreeSet<u64> = BTreeSet::new();
    for i in &insns {
        if matches!(i.flow(), Flow::CondJump | Flow::Jump) {
            targets.extend(i.target().filter(|t| present(*t)));
        }
    }
    for t in &w.tables {
        targets.extend(t.targets.iter().copied().filter(|t| present(*t)));
    }
    let groups = groups(entry, w, &targets);
    let checked: BTreeSet<u64> = groups.values().copied().collect();
    let mut leaders: BTreeSet<u64> = targets;
    leaders.insert(entry);
    leaders.extend(groups.keys().copied());
    for i in &insns {
        if i.flow() != Flow::Next || guarded(i) {
            leaders.insert(i.next());
        }
        if guarded(i) && !checked.contains(&i.va) {
            leaders.insert(i.va);
        }
    }
    let table_of: BTreeMap<u64, &Table> = w.tables.iter().map(|t| (t.site, t)).collect();
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut current: Option<BasicBlock> = None;
    let mut last: Option<&Insn> = None;
    let close = |b: &mut BasicBlock, l: &Insn, blocks: &mut Vec<BasicBlock>| {
        let next = l.next();
        let unguarded_fall = || {
            if present(next) {
                vec![next]
            } else {
                Vec::new()
            }
        };
        let (term, mut succs) = match l.flow() {
            Flow::Next if groups.contains_key(&next) => {
                let after = groups
                    .get(&next)
                    .and_then(|g| w.seen.get(g))
                    .map_or(next, Insn::next);
                (BlockTerm::Cond, vec![after, next])
            }
            Flow::Next => (BlockTerm::Fall, unguarded_fall()),
            Flow::CondJump => {
                let mut s: Vec<u64> = l.target().into_iter().collect();
                s.extend(unguarded_fall());
                (BlockTerm::Cond, s)
            }
            Flow::Jump => match l.target() {
                Some(t) => (BlockTerm::Jmp, vec![t]),
                None => (
                    BlockTerm::Indirect,
                    table_of
                        .get(&l.va)
                        .map(|t| t.targets.clone())
                        .unwrap_or_default(),
                ),
            },
            Flow::Call => (BlockTerm::Call, unguarded_fall()),
            Flow::Return => (BlockTerm::Ret, Vec::new()),
            Flow::Invalid => (BlockTerm::Invalid, Vec::new()),
        };
        if guarded(l) && !checked.contains(&l.va) && l.flow() != Flow::Call && present(next) {
            succs.push(next);
        }
        b.term = term;
        b.successors = succs;
        blocks.push(b.clone());
    };
    for i in &insns {
        let continues = last.is_some_and(|l| {
            l.next() == i.va && l.flow() == Flow::Next && !guarded(l) && !leaders.contains(&i.va)
        });
        if !continues {
            if let (Some(mut b), Some(l)) = (current.take(), last) {
                close(&mut b, l, &mut blocks);
            }
            current = Some(BasicBlock {
                start: i.va,
                end: i.next(),
                term: BlockTerm::Fall,
                successors: Vec::new(),
            });
        }
        if let Some(b) = current.as_mut() {
            b.end = i.next();
        }
        last = Some(i);
    }
    if let (Some(mut b), Some(l)) = (current.take(), last) {
        close(&mut b, l, &mut blocks);
    }
    let start = insns.first().map_or(entry, |i| i.va);
    let end = insns.last().map_or(entry, |i| i.next());
    let mut sites = Vec::new();
    let (mut body_hash, mut shape_hash) = (HASH_SEED, HASH_SEED);
    for i in &insns {
        let fixed = if i.target().is_some() || i.literal().is_some() {
            u64::from(i.word >> 24)
        } else {
            u64::from(i.word)
        };
        body_hash = mix(body_hash, fixed);
        shape_hash = mix(shape_hash, u64::from(i.word >> 24));
        let Some(t) = i.target() else { continue };
        body_hash = if (start..end).contains(&t) {
            mix(body_hash, t.wrapping_sub(i.va))
        } else {
            mix(body_hash, t)
        };
        let kind = match i.flow() {
            Flow::Call => RefKind::Call,
            Flow::Jump => RefKind::Jmp,
            Flow::CondJump if !present(t) => RefKind::Jmp,
            Flow::CondJump | Flow::Next | Flow::Return | Flow::Invalid => continue,
        };
        sites.push((t, i.va, kind));
    }
    let func = Function {
        entry,
        start,
        end,
        instr_count: insns.len(),
        blocks,
        callees: w.callees.iter().copied().collect(),
        callers: Vec::new(),
        name: None,
        name_inferred: false,
        name_source: NameSource::None,
        thunk: None,
        bound: None,
        funclet: None,
        signature: None,
        body_hash,
        shape_hash,
        returns_value: None,
        ret_width: None,
        ret_partial: None,
        ret_float: None,
        preserves_rax: false,
        hands_back_rdx: false,
        param_hints: BTreeMap::new(),
        ret_hint: None,
        stack_args: 0,
        stack_pop: 0,
    };
    (func, sites)
}

/// The data references of a function's instructions: a literal load's
/// address and the address the literal holds, an `adr` into data, and a
/// `movw`/`movt` pair's constant.
///
/// # Arguments
///
/// * `program` - The image.
/// * `w` - The walk.
/// * `found` - Takes each target and site.
fn data_refs(program: &Program, w: &Walked, found: &mut dyn FnMut(u64, u64)) {
    let mapped = |a: u64| program.section_at(a).is_some();
    let mut wide: BTreeMap<a32::Reg, (u64, u64)> = BTreeMap::new();
    for i in w.seen.values() {
        if let Some(lit) = i.literal() {
            found(lit, i.va);
            if let Some(v) = program
                .read_va(lit, 4)
                .and_then(|b| crate::num::u32_le(b, 0))
                .map(u64::from)
                .filter(|v| *v != 0 && mapped(*v))
            {
                found(v, i.va);
            }
        }
        if let Op::Adr { target, .. } = i.op
            && mapped(target)
            && !super::is_executable_va(program, target)
        {
            found(target, i.va);
        } else if let Op::Movw { rd, imm } = i.op {
            wide.insert(rd, (i.va, u64::from(imm)));
        } else if let Op::Movt { rd, imm } = i.op
            && let Some((_, lo)) = wide.remove(&rd)
        {
            let v = lo | (u64::from(imm) << 16);
            if mapped(v) {
                found(v, i.va);
            }
        }
    }
}

/// Tells whether a function of this name never returns.
///
/// # Arguments
///
/// * `n` - The symbol's name, mangled or not.
fn noreturn_name(n: &str) -> bool {
    is_noreturn_name(bare_name(&crate::search::demangled_name(n)))
}

/// The functions walked so far and what their walks share.
struct Walks<'a> {
    /// Every known function start.
    starts: BTreeSet<u64>,
    /// The starts only a guess gave ([`guess`]).
    guessed: BTreeSet<u64>,
    /// Each jump target the walks followed, with the lowest entry of a
    /// function that jumps to it.
    labels: BTreeMap<u64, u64>,
    /// The functions that never return.
    noreturn: BTreeSet<u64>,
    /// Each walked function's walk, by entry.
    walked: BTreeMap<u64, Walked>,
    /// The bytes the walks account for, by first address: the end, and
    /// whether an instruction (rather than a literal or a jump table)
    /// lies there.
    covered: BTreeMap<u64, (u64, bool)>,
    /// The literals and jump tables the walks read, by first address,
    /// with the end; the same `false` value as in [`Walks::covered`].
    data: BTreeMap<u64, (u64, bool)>,
    /// Instructions left to decode.
    fuel: u64,
    /// Whether the fuel ran out.
    incomplete: bool,
    /// The imports by slot address.
    imports: &'a BTreeMap<u64, &'a str>,
}

impl Walks<'_> {
    /// Walks every queued entry not yet walked and every function those
    /// walks call.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    /// * `queue` - The entries.
    fn drain(&mut self, program: &Program, mut queue: Vec<u64>) {
        while let Some(e) = queue.pop() {
            if self.walked.contains_key(&e) {
                continue;
            }
            if self.fuel == 0 {
                self.incomplete = true;
                break;
            }
            if let Some(slot) = stub_slot(program, e)
                && self.imports.get(&slot).is_some_and(|n| noreturn_name(n))
            {
                self.noreturn.insert(e);
            }
            let w = walk(program, e, &self.starts, &self.noreturn, None);
            self.keep(e, w, &mut queue);
        }
    }

    /// Records a walk: spends its fuel, marks its bytes covered and queues
    /// the functions it calls.
    ///
    /// # Arguments
    ///
    /// * `e` - The walk's entry.
    /// * `w` - The walk.
    /// * `queue` - Takes the callees not yet walked.
    fn keep(&mut self, e: u64, w: Walked, queue: &mut Vec<u64>) {
        self.fuel = self
            .fuel
            .saturating_sub(crate::num::from_usize(w.seen.len()));
        for &c in &w.callees {
            if self.starts.insert(c) || !self.walked.contains_key(&c) {
                queue.push(c);
            }
        }
        for &t in &w.followed {
            let low = self.labels.entry(t).or_insert(e);
            *low = (*low).min(e);
        }
        Self::mark(&mut self.covered, &mut self.data, &w);
        self.walked.insert(e, w);
    }

    /// Marks a walk's bytes covered: its instructions, the literals they
    /// load and its jump tables, the last two also as data.
    ///
    /// # Arguments
    ///
    /// * `covered` - The covered stretches ([`Walks::covered`]).
    /// * `data` - The data stretches ([`Walks::data`]).
    /// * `w` - The walk.
    fn mark(
        covered: &mut BTreeMap<u64, (u64, bool)>,
        data: &mut BTreeMap<u64, (u64, bool)>,
        w: &Walked,
    ) {
        let mut stretches = Vec::new();
        for i in w.seen.values() {
            covered.insert(i.va, (i.next(), true));
            if let Some(lit) = i.literal() {
                let len = if matches!(i.op, Op::LoadDual { .. }) {
                    8
                } else {
                    4
                };
                stretches.push(lit..lit + len);
            }
        }
        stretches.extend(w.tables.iter().map(|t| t.bytes.clone()));
        for r in stretches {
            covered.entry(r.start).or_insert((r.end, false));
            data.insert(r.start, (r.end, false));
        }
    }

    /// Marks covered again what the walks hold, after some were dropped.
    fn cover(&mut self) {
        self.covered.clear();
        self.data.clear();
        for w in self.walked.values() {
            Self::mark(&mut self.covered, &mut self.data, w);
        }
    }
}

/// Discovers an ARM32 program's functions, blocks, references and jump
/// tables.
///
/// # Arguments
///
/// * `program` - The loaded image, ARM32.
///
/// # Returns
///
/// The analysis, indexed ([`Analysis::finish_index`]).
pub(crate) fn discover(program: &Program) -> Analysis {
    let seeds = seeds(program);
    let imports: BTreeMap<u64, &str> = program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect();
    let mut walks = Walks {
        starts: seeds.iter().copied().collect(),
        guessed: BTreeSet::new(),
        labels: BTreeMap::new(),
        noreturn: program
            .symbols
            .iter()
            .filter(|s| s.kind != SymbolKind::Import && s.addr != 0 && noreturn_name(&s.name))
            .map(|s| s.addr)
            .collect(),
        walked: BTreeMap::new(),
        covered: BTreeMap::new(),
        data: BTreeMap::new(),
        fuel: fuel_for(program),
        incomplete: false,
        imports: &imports,
    };
    walks.drain(program, seeds);
    guess::pointers(program, &mut walks);
    for _ in 0..GAP_ROUNDS {
        guess::gaps(program, &mut walks);
        guess::drop_inner(program, &mut walks);
    }
    outlines(&mut walks);
    let redo: Vec<u64> = walks
        .walked
        .iter()
        .filter(|(e, w)| {
            w.followed
                .iter()
                .any(|t| t != *e && walks.starts.contains(t))
        })
        .map(|(e, _)| *e)
        .collect();
    for e in &redo {
        walks.walked.remove(e);
    }
    walks.drain(program, redo);
    let Walks {
        walked, incomplete, ..
    } = walks;
    let mut analysis = Analysis {
        incomplete,
        ..Analysis::default()
    };
    let mut functions = Vec::with_capacity(walked.len());
    for (&entry, w) in &walked {
        if w.seen.is_empty() {
            continue;
        }
        let (f, sites) = assemble(entry, w);
        for (t, va, kind) in sites {
            push_site(&mut analysis.xrefs, t, va, kind, Some(entry));
        }
        data_refs(program, w, &mut |t, va| {
            push_site(&mut analysis.xrefs, t, va, RefKind::Data, Some(entry));
        });
        for t in &w.tables {
            analysis.jump_tables.insert(t.site, t.targets.clone());
        }
        functions.push(f);
    }
    build_callers_and_names(program, &mut functions);
    for f in &mut functions {
        if let Some(slot) = stub_slot(program, f.entry)
            && let Some(name) = imports.get(&slot)
        {
            f.name = Some(crate::search::demangled_name(name));
            f.name_source = NameSource::Symbol;
            f.thunk = Some(slot);
        }
    }
    analysis.functions = functions;
    analysis.finish_index(program);
    analysis
}

/// Promotes a tail call that was walked as a block of its caller.
///
/// The block is one straight run that returns without touching the stack
/// pointer, so it is not the caller's own epilogue. Nothing but one
/// unconditional jump reaches it, and another function already starts
/// between the caller and the block. The caller is walked again and the
/// jump becomes a tail call.
///
/// # Arguments
///
/// * `walks` - The walks, updated in place.
fn outlines(walks: &mut Walks<'_>) {
    let mut promote = Vec::new();
    for (&entry, w) in &walks.walked {
        let pred = predecessors(w);
        for &t in &w.followed {
            if t > entry
                && !walks.starts.contains(&t)
                && walks.starts.range((entry + 1)..t).next().is_some()
                && straight_return(w, t, &pred)
            {
                promote.push(t);
            }
        }
    }
    promote.sort_unstable();
    promote.dedup();
    for t in promote {
        walks.starts.insert(t);
        walks.guessed.insert(t);
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

/// Most jumps on from function to function a float result is followed
/// through.
const TAIL_LINKS: usize = 4;

/// What the last write of a result register in a stretch of code was.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Last {
    /// `r0`.
    Int,
    /// `s0` or `d0`, with the width in bits.
    Float(u8),
}

/// The result register an instruction other than a call writes, a base
/// register a transfer writes back left out.
///
/// # Arguments
///
/// * `i` - The instruction.
fn last_write(i: &Insn) -> Option<Last> {
    if i.flow() == Flow::Call {
        return None;
    }
    let base = if let Op::Load { addr, .. }
    | Op::Store { addr, .. }
    | Op::LoadDual { addr, .. }
    | Op::StoreDual { addr, .. } = i.op
        && addr.index != Index::Offset
    {
        Some(addr.base)
    } else if let Op::Ldm { rn, wback, .. }
    | Op::Stm { rn, wback, .. }
    | Op::VLdm { rn, wback, .. }
    | Op::VStm { rn, wback, .. } = i.op
    {
        wback.then_some(rn)
    } else if let Op::Neon { base, .. } = i.op {
        base
    } else {
        None
    };
    let mut w = i.registers().writes;
    w.retain(|r| Some(*r) != base);
    if w.contains(&a32::Reg::R(0)) {
        Some(Last::Int)
    } else if w.contains(&a32::Reg::D(0)) {
        Some(Last::Float(64))
    } else if w.contains(&a32::Reg::S(0)) {
        Some(Last::Float(32))
    } else {
        None
    }
}

/// Says which ARM32 functions hand back a result, and which a float.
///
/// Whether `r0` holds a result is [`returns::infer`]'s answer. A float
/// result then makes the function return a value whatever that said: one
/// does whose returning blocks last write `s0` or `d0` rather than
/// `r0`, or, when no returning block writes either and none jumps on to
/// another function, that writes `s0` or `d0` outside a call and never
/// `r0`; one that only jumps on hands back what the function it jumps to
/// does, up to [`TAIL_LINKS`] jumps away. The width goes into
/// [`Function::ret_float`].
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, updated in place.
pub(crate) fn infer_returns(program: &Program, analysis: &mut Analysis) {
    returns::infer(program, analysis);
    let float_of = |ls: &[Last]| {
        ls.iter().find_map(|l| {
            if let Last::Float(w) = l {
                Some(*w)
            } else {
                None
            }
        })
    };
    let mut onward: Vec<(usize, u64)> = Vec::new();
    for (k, f) in analysis.functions.iter_mut().enumerate() {
        let mut at_return: Vec<Last> = Vec::new();
        let mut any: Vec<Last> = Vec::new();
        for b in &f.blocks {
            let mut it = ItState::default();
            let mut va = b.start;
            let mut in_block = None;
            while va < b.end {
                let Some(i) = decode(program, va, &mut it) else {
                    break;
                };
                if let Some(l) = last_write(&i) {
                    in_block = Some(l);
                    any.push(l);
                }
                va = i.next();
            }
            if b.term == BlockTerm::Ret {
                at_return.extend(in_block);
            }
        }
        let inside = |t: &u64| f.blocks.iter().any(|x| x.start == *t);
        let tail = f
            .blocks
            .iter()
            .find(|b| b.term == BlockTerm::Jmp && !b.successors.iter().any(inside));
        if at_return.is_empty()
            && let Some(&t) = tail.and_then(|b| b.successors.first())
        {
            onward.push((k, t));
        }
        let tail = tail.is_some();
        let float = if at_return.is_empty() {
            float_of(&any).filter(|_| !tail && !any.contains(&Last::Int))
        } else {
            float_of(&at_return).filter(|_| !at_return.contains(&Last::Int))
        };
        if float.is_some() {
            f.ret_float = float;
            f.returns_value = Some(true);
        }
    }
    for _ in 0..TAIL_LINKS {
        for &(k, t) in &onward {
            let float = analysis
                .function(t)
                .filter(|g| g.entry == t)
                .and_then(|g| g.ret_float);
            if let Some(f) = analysis.functions.get_mut(k)
                && f.ret_float.is_none()
                && float.is_some()
            {
                f.ret_float = float;
                f.returns_value = Some(true);
            }
        }
    }
}
