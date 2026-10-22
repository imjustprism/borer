//! Function starts nothing names outright, for ARM32: the code pointers in
//! the image's words, and the code in the gaps the walks leave.
//!
//! An interrupt handler is named only by its vector table, a callback only
//! by the table or the literal pool holding its address, and a function
//! only ever reached through a pointer computed at run time by nothing at
//! all. [`pointers`] takes each word that reads as a code address in the
//! instruction set there (odd for T32, aligned for A32 outside code);
//! [`gaps`] takes the first instruction after each stretch the walks cover
//! and every frame-opening `push` in what is left. Either is a guess, and
//! a walk from a guess is kept only when it looks like a function: every
//! path decodes, one leaves (a pointer's handler may loop forever), and it
//! shares no byte with code or data already found nor calls into the
//! middle of a function.

use std::collections::{BTreeMap, BTreeSet};

use super::super::functions::seeds::describes_addresses;
use super::{Walks, decode, guarded, walk};
use crate::isa::a32::{Flow, ItState, Mode};
use crate::program::Program;

/// Fewest instructions a walk from a bare gap (no frame-opening `push`)
/// must decode: `ldr r0, [pc]; bx lr` is the shortest function that
/// reads as one.
const BARE_MIN: usize = 2;
/// Most times a guessed walk is made again with the starts it ran into.
const INTO_MAX: usize = 4;
/// Most padding units looked back over for the end of the code before a
/// start.
const PAD_MAX: usize = 8;
/// Most rounds of dropping guesses: a block of a function followed by
/// another block of it is found only once the first is dropped.
const DROP_ROUNDS: usize = 8;
/// Most pointer candidates tried.
const POINTERS_MAX: usize = 1 << 16;
/// Leading printable bytes that make a gap's start a string.
const TEXT_RUN: usize = 8;
/// Leading printable bytes that, ended by a zero, make a gap's start a
/// string.
const TEXT_SHORT: usize = 4;

/// Returns what covers `va`: the end of the covered stretch and whether
/// an instruction lies there.
///
/// # Arguments
///
/// * `covered` - The covered stretches by first address.
/// * `va` - The address.
pub(super) fn covers(covered: &BTreeMap<u64, (u64, bool)>, va: u64) -> Option<(u64, bool)> {
    covered
        .range(..=va)
        .next_back()
        .filter(|(_, (end, _))| va < *end)
        .map(|(_, v)| *v)
}

/// Tells whether covered code at `x` reads as a function's start.
///
/// That is the start of code another function fell into: an instruction
/// lies there, the code before it (past any padding) ends a path or is
/// data, and no function that starts before it jumps to it.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks so far.
/// * `x` - The address.
fn opens_after_end(program: &Program, walks: &Walks<'_>, x: u64) -> bool {
    if walks.covered.get(&x).is_none_or(|(_, insn)| !insn)
        || walks.labels.get(&x).is_some_and(|e| *e < x)
    {
        return false;
    }
    let mode = program.modes.at(x);
    let mut at = x;
    for _ in 0..PAD_MAX {
        let Some((&start, &(end, insn))) = walks.covered.range(..at).next_back() else {
            return false;
        };
        if end == at {
            let mut it = ItState::default();
            return !insn
                || decode(program, start, &mut it).is_some_and(|i| {
                    matches!(i.flow(), Flow::Return | Flow::Jump) && !guarded(&i)
                });
        }
        let unit = if mode == Mode::Thumb { 2 } else { 4 };
        at = at.saturating_sub(unit);
        if !padding(program, at, mode) {
            return false;
        }
    }
    false
}

/// Walks from a guessed start and keeps the walk, with the functions it
/// calls, when it looks like a function.
///
/// A walk that runs or calls into code already found is kept only when
/// that code opens a function another fell into ([`opens_after_end`]):
/// the walk is then made again with it as a start, so that reaching it is
/// a tail call.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks so far, updated in place.
/// * `va` - The guessed start.
/// * `min` - Fewest instructions the walk must decode.
/// * `exits` - Whether a path must leave the function: a pointer is
///   evidence enough for a handler that loops forever. So is a gap whose
///   walk never leaves its own instructions ([`closed`]): the bytes after
///   a gap are not, on their own.
///
/// # Returns
///
/// Whether the walk was kept.
fn try_seed(program: &Program, walks: &mut Walks<'_>, va: u64, min: usize, exits: bool) -> bool {
    if walks.fuel == 0 || walks.walked.contains_key(&va) || covers(&walks.covered, va).is_some() {
        return false;
    }
    let mut more: Option<BTreeSet<u64>> = None;
    for _ in 0..=INTO_MAX {
        let known = more.as_ref().unwrap_or(&walks.starts);
        let w = walk(program, va, known, &walks.noreturn, Some(&walks.covered));
        let free = |a: u64| covers(&walks.covered, a).is_none();
        let entered: BTreeSet<u64> = w
            .callees
            .iter()
            .copied()
            .filter(|c| !known.contains(c) && !free(*c))
            .chain(w.into.iter().copied())
            .collect();
        let plausible = !w.bad
            && entered.is_empty()
            && (w.exits || !exits || closed(&w))
            && !dead_start(&w, va)
            && w.seen.len() >= min
            && w.seen.values().all(|i| free(i.next() - 1));
        if plausible {
            if let Some(m) = more {
                walks.starts = m;
            }
            walks.starts.insert(va);
            walks.guessed.insert(va);
            let mut queue = Vec::new();
            walks.keep(va, w, &mut queue);
            walks.drain(program, queue);
            return true;
        }
        walks.fuel = walks
            .fuel
            .saturating_sub(crate::num::from_usize(w.seen.len()));
        if w.bad
            || entered.is_empty()
            || !entered.iter().all(|x| opens_after_end(program, walks, *x))
        {
            return false;
        }
        let mut m = more.take().unwrap_or_else(|| walks.starts.clone());
        m.extend(entered);
        more = Some(m);
    }
    false
}

/// Tells whether a walk never leaves its own instructions.
///
/// A handler that spins (`b .` after its prologue) has no return and no
/// jump out, which is why a gap rejected it while a pointer to the same
/// bytes was kept. A walk that falls off the end, or that returns, is not
/// one of these.
///
/// # Arguments
///
/// * `w` - The walk.
fn closed(w: &super::Walked) -> bool {
    if w.bad || w.seen.is_empty() {
        return false;
    }
    let mut branched = false;
    for i in w.seen.values() {
        match i.flow() {
            Flow::Next | Flow::Call => {
                if !w.seen.contains_key(&i.next()) {
                    return false;
                }
            }
            Flow::CondJump => {
                let Some(t) = i.target() else {
                    return false;
                };
                if !w.seen.contains_key(&t) || !w.seen.contains_key(&i.next()) {
                    return false;
                }
                branched = true;
            }
            Flow::Jump => {
                let Some(t) = i.target() else {
                    return false;
                };
                if !w.seen.contains_key(&t) {
                    return false;
                }
                branched = true;
            }
            Flow::Return | Flow::Invalid => return false,
        }
    }
    branched
}

/// Tells whether a walk opens the way data read as code does.
///
/// Compiled code never opens under a condition, with the same instruction
/// twice (a table of small numbers reads as `movs r0, #n` or `cmp r0, #n`
/// over and over), or by writing a register its next instruction
/// overwrites unread.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `entry` - Its entry.
fn dead_start(w: &super::Walked, entry: u64) -> bool {
    let Some(a) = w.seen.get(&entry) else {
        return true;
    };
    if a.predicated() {
        return true;
    }
    let Some(b) = w.seen.get(&a.next()).filter(|_| a.flow() == Flow::Next) else {
        return false;
    };
    let (ra, rb) = (a.registers(), b.registers());
    a.word == b.word
        || (!ra.writes.is_empty()
            && ra
                .writes
                .iter()
                .all(|r| rb.writes.contains(r) && !rb.reads.contains(r)))
}

/// Drops each guessed function that reads as a part of another.
///
/// That is one whose entry another walk runs through (a label inside code found later from
/// a fact), one another function jumps to from around it or right after
/// its last instruction (a block of that function, which its walk took for
/// a tail call), or one whose entry a
/// walk found later reads as data (a literal pool or a jump table read as
/// code). The functions that jumped to one are walked again, and what the
/// walks then hold is marked covered anew.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks, updated in place.
pub(super) fn drop_inner(program: &Program, walks: &mut Walks<'_>) {
    for _ in 0..DROP_ROUNDS {
        if !drop_once(program, walks) {
            break;
        }
    }
    walks.cover();
}

/// Drops the guesses [`drop_inner`] names once, and walks again the
/// functions that jumped to them.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks, updated in place.
///
/// # Returns
///
/// Whether a guess was dropped.
fn drop_once(program: &Program, walks: &mut Walks<'_>) -> bool {
    let mut held: BTreeMap<u64, usize> = BTreeMap::new();
    let mut owners: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (&e, w) in &walks.walked {
        for va in w.seen.keys() {
            *held.entry(*va).or_default() += 1;
        }
        let end = w.seen.values().next_back().map_or(e, |i| i.next());
        for &t in w.tails.iter().filter(|t| (e + 1..=end).contains(*t)) {
            owners.entry(t).or_default().push(e);
        }
    }
    let inner: Vec<u64> = walks
        .guessed
        .iter()
        .copied()
        .filter(|g| {
            held.get(g).is_some_and(|n| *n > 1)
                || owners.contains_key(g)
                || covers(&walks.data, *g).is_some()
        })
        .collect();
    let dropped = !inner.is_empty();
    let mut again = Vec::new();
    for g in inner {
        walks.walked.remove(&g);
        walks.starts.remove(&g);
        walks.guessed.remove(&g);
        again.extend(owners.remove(&g).unwrap_or_default());
    }
    for e in &again {
        walks.walked.remove(e);
    }
    walks.drain(program, again);
    dropped
}

/// Walks the code addresses the image's aligned words hold.
///
/// A word is one when it names T32 code with its low bit set, or, outside
/// executable sections, A32 code at an aligned address. A word inside an
/// instruction already walked is code, not a pointer, and one in a
/// section that describes addresses (a relocation names the word it
/// patches) names no function.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks so far, updated in place.
pub(super) fn pointers(program: &Program, walks: &mut Walks<'_>) {
    let mut found = Vec::new();
    for s in &program.sections {
        if describes_addresses(&s.name) {
            continue;
        }
        let Some(data) = program.section_bytes(s) else {
            continue;
        };
        let skew = crate::num::saturating_usize(s.va.0.wrapping_neg() & 3);
        for (k, chunk) in data
            .get(skew..)
            .unwrap_or_default()
            .chunks_exact(4)
            .enumerate()
        {
            let site = s.va.0 + crate::num::from_usize(skew + 4 * k);
            let Some(v) = crate::num::u32_le(chunk, 0).map(u64::from) else {
                continue;
            };
            let t = v & !1;
            let named = super::super::is_executable_va(program, t)
                && match program.modes.at(t) {
                    Mode::Thumb => v & 1 == 1,
                    Mode::Arm => v & 3 == 0 && !s.executable,
                };
            if named && covers(&walks.covered, site).is_none_or(|(_, insn)| !insn) {
                found.push(t);
            }
        }
    }
    found.sort_unstable();
    found.dedup();
    for t in found.into_iter().take(POINTERS_MAX) {
        try_seed(program, walks, t, 1, false);
    }
}

/// Tells whether the instruction at `va` fills space between functions:
/// zero, or a `nop` in either instruction set.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
/// * `mode` - Its instruction set.
fn padding(program: &Program, va: u64, mode: Mode) -> bool {
    let bytes = program.read_va(va, 4).unwrap_or_default();
    match mode {
        Mode::Thumb => {
            crate::num::u16_le(bytes, 0).is_some_and(|h| matches!(h, 0 | 0xbf00 | 0x46c0))
        }
        Mode::Arm => {
            crate::num::u32_le(bytes, 0).is_some_and(|w| matches!(w, 0 | 0xe1a0_0000 | 0xe320_f000))
        }
    }
}

/// Tells whether the code at `va` opens a frame as a compiled function does.
///
/// That is a `push` holding `lr` (after the `push` of a variadic
/// function's register arguments), or the `push {r7}; sub sp` of a leaf
/// built without optimization; in A32, an `stmdb sp!` or `str` of `lr`.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
/// * `mode` - Its instruction set.
fn opens_frame(program: &Program, va: u64, mode: Mode) -> bool {
    let bytes = program.read_va(va, 4).unwrap_or_default();
    match mode {
        Mode::Thumb => {
            let (Some(h0), Some(h1)) = (crate::num::u16_le(bytes, 0), crate::num::u16_le(bytes, 2))
            else {
                return false;
            };
            h0 & 0xff00 == 0xb500
                || (h0 & 0xff00 == 0xb400 && (h1 & 0xff00 == 0xb500 || h1 & 0xff80 == 0xb080))
                || (h0 == 0xe92d && h1 & 0x4000 != 0)
        }
        Mode::Arm => crate::num::u32_le(bytes, 0)
            .is_some_and(|w| w & 0xffff_4000 == 0xe92d_4000 || w == 0xe52d_e004),
    }
}

/// Tells whether the bytes at `va` read as a string: [`TEXT_RUN`]
/// printable bytes, or [`TEXT_SHORT`] ended by a zero.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
fn texty(program: &Program, va: u64) -> bool {
    let bytes = program.read_va_upto(va, TEXT_RUN).unwrap_or_default();
    let run = bytes
        .iter()
        .take_while(|b| (0x20..0x7f).contains(*b) || matches!(b, b'\t' | b'\n' | b'\r'))
        .count();
    run >= TEXT_RUN || (run >= TEXT_SHORT && bytes.get(run) == Some(&0))
}

/// Walks the code in the gaps of the executable sections: the first
/// instruction past each covered stretch and its padding, and every
/// frame-opening instruction ([`opens_frame`]) after it.
///
/// A section the walk budget runs out in before its end marks the
/// discovery incomplete, so the lists say functions may be missing.
///
/// # Arguments
///
/// * `program` - The image.
/// * `walks` - The walks so far, updated in place.
pub(super) fn gaps(program: &Program, walks: &mut Walks<'_>) {
    for s in program.sections.iter().filter(|s| s.executable) {
        let end = s.va.0.saturating_add(s.file_size.min(s.vsize));
        let mut va = s.va.0;
        let mut fresh = true;
        while va < end && walks.fuel > 0 {
            if let Some((e, _)) = covers(&walks.covered, va) {
                va = e;
                fresh = true;
                continue;
            }
            let mode = program.modes.at(va);
            let unit = match mode {
                Mode::Thumb => 2,
                Mode::Arm => 4,
            };
            if va % unit != 0 {
                va = va.next_multiple_of(unit);
                continue;
            }
            if padding(program, va, mode) {
                va += unit;
                continue;
            }
            let frame = opens_frame(program, va, mode);
            let min = if frame { 1 } else { BARE_MIN };
            if (fresh || frame) && !texty(program, va) && try_seed(program, walks, va, min, true) {
                continue;
            }
            fresh = false;
            va += unit;
        }
        if va < end && walks.fuel == 0 {
            walks.incomplete = true;
        }
    }
}
