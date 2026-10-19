//! The arm64 walk: seeds, waves of walks, the split rounds that walk a
//! function again once something it followed proves to be another
//! function, and the gap rounds that guess at code nothing reaches.
//!
//! Phase 1 walks the facts: the entry point, the symbols and the extents
//! the file declares. A walk follows every branch, takes a `bl` target as a
//! new function, takes a `b` as a tail call when it enters a known start or
//! leaves the extent the file declares for the function ([`jump_kind`]),
//! and stops after a call that never returns: one to a function named as
//! never returning (or to an import named so, through its stub or its
//! slot), or one followed by another function's start or by a word only a
//! function opens with. An indirect `br` ends the path; once the path ends,
//! a `br` that dispatches through a bounded jump table ([`switch`]) has its
//! cases walked, round after round, since a case may reach another switch.
//! A jump to a stub after an import is a tail call. A function whose walk
//! followed a jump into what later proved a start, a call into what later
//! proved never to return, or the fall-through of a call to where another
//! function later proved to start, is walked again, round after round.
//! Phase 2 guesses: every gap no block covers is swept a word at a time,
//! and where it opens (its first word, or the word after padding or after
//! an instruction control does not fall through) on a word a function opens
//! with ([`prologue::opens`]), or on any word outside the extents of a file
//! that declares them, the word is walked as a guess
//! ([`Discovery::gap_seeds`]), kept only when the walk decodes nothing that
//! is not code, finds a way out, does not run into another function or into
//! code one covers, and does not lie inside a guess kept before it. Each
//! accepted guess shrinks its gap, so rounds go on until one adds nothing.
//!
//! Every walk of a wave reads the starts and the functions known never to
//! return as they stood when the wave began, so the walks of a wave run
//! across the cores and their results are the same whatever the order;
//! they are committed in address order. A walk is held to [`WALK_MAX`]
//! instructions, a guess to [`GUESS_WALK_MAX`], and all of them together
//! to the fuel [`fuel_for`] gives the program.

use std::collections::{BTreeMap, BTreeSet};

use super::refs::{self, Tracker};
use super::switch::{self, Shape, Table};
use super::{prologue, stubs};
use crate::analysis::functions::helpers::is_noreturn_name;
use crate::analysis::functions::{
    GAP_ROUNDS_MAX, GUESS_WALK_MAX, SEEDS_MAX, SPLIT_ROUNDS_MAX, build_callers_and_names, fuel_for,
    mix, push_site,
};
use crate::analysis::{
    Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, bare_name, seeds, striped,
};
use crate::fxmap::FxHashSet;
use crate::isa::a64::{self, Flow, Insn, Mode, Op, Opnd};
use crate::num::from_usize;
use crate::program::{Program, SymbolKind};

/// Bytes from one instruction to the next: [`a64::INSN_LEN`].
const STEP: u64 = 4;
/// Most instructions one walk from a fact decodes: a quarter of a million,
/// past any function a compiler emits, so a walk through a sled of
/// hostile words ends.
const WALK_MAX: u64 = 1 << 18;
/// Most rounds of jump-table resolution one walk makes: each resolves the
/// `br`s the code walked so far reaches, and walks their cases, which may
/// reach a nested switch's `br`.
const TABLE_ROUNDS_MAX: usize = 32;
/// Walks committed per batch of a wave; only one batch's results are held
/// at a time.
const WAVE_BATCH: usize = 4096;
/// Fewest instructions a guessed function holds: a single word between
/// gaps is a stray, not a function.
const GUESS_INSTRS_MIN: usize = 2;
/// Where every fingerprint starts: the FNV-1a offset basis the x86 walk
/// folds from.
const HASH_SEED: u64 = 0xcbf2_9ce4_8422_2325;
/// The fixed bits of `b` and `bl`: the 26-bit offset left out.
const BRANCH_FIXED: u32 = 0xfc00_0000;
/// The fixed bits of `b.cond`, `cbz`, `cbnz` and a literal load: the
/// 19-bit offset left out.
const IMM19_FIXED: u32 = 0xff00_001f;
/// The fixed bits of `tbz` and `tbnz`: the 14-bit offset left out.
const TEST_FIXED: u32 = 0xfff8_001f;
/// The fixed bits of `adr` and `adrp`: the 21-bit offset left out.
const ADR_FIXED: u32 = 0x9f00_001f;
/// The bits that, then their value, make a word a literal load
/// (`ldr`, `ldrsw`, `prfm` from a PC-relative address).
const LITERAL: (u32, u32) = (0x3b00_0000, 0x1800_0000);

/// The executable bytes of a program, section by section, read a word at a
/// time.
pub(super) struct Text<'a> {
    /// `(address, bytes)` of every executable section the file backs,
    /// sorted by address.
    sections: Vec<(u64, &'a [u8])>,
}

impl<'a> Text<'a> {
    /// Collects the executable sections the file backs.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    pub(super) fn new(program: &'a Program) -> Self {
        let mut sections: Vec<(u64, &'a [u8])> = program
            .sections
            .iter()
            .filter(|s| s.executable && s.file_size > 0)
            .filter_map(|s| {
                let off = usize::try_from(s.file_off.0).ok()?;
                let len = usize::try_from(s.file_size).ok()?;
                Some((s.va.0, program.bytes.get(off..off.checked_add(len)?)?))
            })
            .collect();
        sections.sort_by_key(|s| s.0);
        Text { sections }
    }

    /// Reads the instruction word at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    ///
    /// # Returns
    ///
    /// The word, or `None` when `va` is not aligned to an instruction or no
    /// executable section the file backs holds four bytes there.
    pub(super) fn word(&self, va: u64) -> Option<u32> {
        if !va.is_multiple_of(STEP) {
            return None;
        }
        let k = self
            .sections
            .partition_point(|s| s.0 <= va)
            .checked_sub(1)?;
        let &(start, bytes) = self.sections.get(k)?;
        let off = usize::try_from(va - start).ok()?;
        let word = bytes.get(off..off.checked_add(a64::INSN_LEN)?)?;
        Some(u32::from_le_bytes(word.try_into().ok()?))
    }
}

/// What every walk of a wave reads and none writes.
#[derive(Clone, Copy)]
struct Known<'a> {
    /// The loaded image, for the bytes of a jump table.
    program: &'a Program,
    /// The code.
    text: &'a Text<'a>,
    /// The slots the file names imports in.
    import_slots: &'a FxHashSet<u64>,
    /// The slots of the imports named as never returning.
    noreturn_slots: &'a FxHashSet<u64>,
    /// Function starts known when the wave began.
    starts: &'a FxHashSet<u64>,
    /// Functions known never to return when the wave began.
    noreturn: &'a FxHashSet<u64>,
    /// The extents the file declares, sorted ([`Program::function_ranges`]).
    declared: &'a [(u64, u64)],
    /// The fragments the file declares, sorted: chunks of a function, no
    /// function of their own ([`crate::headers::Headers::chained_chunks`]).
    fragments: &'a [(u64, u64)],
    /// The code the functions kept so far cover, as sorted, disjoint
    /// extents ([`Discovery::covered`]); empty for a wave of facts.
    covered: &'a [(u64, u64)],
    /// Each function's Itanium landing pads, by entry: labels of its own
    /// that only the unwinder reaches ([`crate::lsda`]).
    pads: &'a BTreeMap<u64, Vec<u64>>,
}

impl Known<'_> {
    /// Tells whether a kept function's block covers `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    fn covers(&self, va: u64) -> bool {
        inside(self.covered, va)
    }

    /// Tells whether a function opens at `va`: a known start, or a word
    /// only a function opens with ([`prologue::opens_surely`]).
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    fn start_at(&self, va: u64) -> bool {
        self.starts.contains(&va) || self.text.word(va).is_some_and(prologue::opens_surely)
    }

    /// Tells whether `t` lies inside the extent the file declares for the
    /// function at `entry`, or in a fragment of one.
    ///
    /// Of two extents declared at one entry (a sized symbol and an unwind
    /// entry), the longer is the function's.
    ///
    /// # Arguments
    ///
    /// * `entry` - The walked function's entry.
    /// * `t` - A branch target.
    ///
    /// # Returns
    ///
    /// `None` when the file declares no extent starting at `entry`.
    fn within_extent(&self, entry: u64, t: u64) -> Option<bool> {
        let &(start, end) = self
            .declared
            .partition_point(|r| r.0 <= entry)
            .checked_sub(1)
            .and_then(|k| self.declared.get(k))
            .filter(|r| r.0 == entry)?;
        let in_fragment = {
            let f = self.fragments.partition_point(|r| r.0 <= t);
            f.checked_sub(1)
                .and_then(|f| self.fragments.get(f))
                .is_some_and(|&(lo, hi)| t >= lo && t < hi)
        };
        Some((start..end).contains(&t) || in_fragment)
    }

    /// Tells whether the file declares a function starting between `entry`
    /// and `t`: past `entry` up to `t` for a forward branch, from `t` up to
    /// `entry` for a backward one. A function's code does not straddle
    /// another's start, so a branch across one leaves the function.
    ///
    /// # Arguments
    ///
    /// * `entry` - The walked function's entry.
    /// * `t` - A branch target.
    fn declared_between(&self, entry: u64, t: u64) -> bool {
        let (lo, hi) = match t.cmp(&entry) {
            std::cmp::Ordering::Greater => (entry.saturating_add(1), t),
            std::cmp::Ordering::Less => (t, entry.saturating_sub(1)),
            std::cmp::Ordering::Equal => return false,
        };
        let k = self.declared.partition_point(|r| r.0 < lo);
        self.declared.get(k).is_some_and(|r| r.0 <= hi)
    }

    /// Tells whether a stub after an import starts at `t` ([`stubs::slot`]).
    ///
    /// # Arguments
    ///
    /// * `t` - The address.
    fn stub(&self, t: u64) -> bool {
        !self.import_slots.is_empty()
            && stubs::slot(self.text, t).is_some_and(|s| self.import_slots.contains(&s))
    }

    /// Tells whether a call to `t`, or the call `insn` through a register,
    /// reaches an import named as never returning through its slot: a stub
    /// at `t` ([`stubs::slot`]), or the slot the call's register was loaded
    /// from ([`stubs::slot_call`]).
    ///
    /// # Arguments
    ///
    /// * `insn` - The call.
    /// * `t` - Its direct target, when it has one.
    fn noreturn_import(&self, insn: &Insn, t: Option<u64>) -> bool {
        !self.noreturn_slots.is_empty()
            && t.map_or_else(
                || stubs::slot_call(self.text, insn),
                |t| stubs::slot(self.text, t),
            )
            .is_some_and(|s| self.noreturn_slots.contains(&s))
    }

    /// Tells whether a branch from the function at `entry` to `t` leaves
    /// it: `t` is a known start or a stub after an import, lies outside the
    /// extent the file declares for the function, or, where it declares
    /// none, past another function the file declares
    /// ([`Known::declared_between`]).
    ///
    /// # Arguments
    ///
    /// * `entry` - The walked function's entry.
    /// * `t` - A branch target.
    fn leaves(&self, entry: u64, t: u64) -> bool {
        self.starts.contains(&t)
            || self.stub(t)
            || self
                .within_extent(entry, t)
                .map_or_else(|| self.declared_between(entry, t), |inside| !inside)
    }
}

/// What a direct `b` is, as far as the walk can tell at the jump.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Jump {
    /// A jump within the function: followed.
    Within,
    /// A tail call: the target is a callee, not followed.
    Tail,
    /// A tail call unless the walk reaches the target another way: the
    /// frame was torn down right before it, which a tail call does, and
    /// which a function that shrink-wraps its frame also does before
    /// jumping back to the tail its other paths share.
    Unless,
}

/// How a pending address was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Via {
    /// A fall-through: a word that is not code there means the walk was
    /// reading data.
    Fall,
    /// A branch: a word that is not code there is only a branch not taken.
    Branch,
}

/// Everything one [`walk`] produced.
struct Walked {
    /// The function record (callers empty, name unset).
    func: Function,
    /// Its references: target, site and kind.
    sites: Vec<(u64, u64, RefKind)>,
    /// Jump targets the walk followed into: should one prove a start, the
    /// jump was a tail call.
    followed: Vec<u64>,
    /// Callees whose fall-through the walk followed: should one prove never
    /// to return, the code after the call is not this function's.
    followed_calls: Vec<u64>,
    /// The addresses right after those calls: should one prove a start,
    /// the call never returns.
    after_calls: Vec<u64>,
    /// Callees found never to return here: another function starts right
    /// after the call.
    found_noreturn: Vec<u64>,
    /// The jump tables its `br`s dispatch through, resolved.
    tables: Vec<Table>,
    /// Instructions decoded, charged to the fuel.
    spent: u64,
    /// A fall-through landed on a word that is not code.
    junk: bool,
    /// The walk reached a way out: a return, a tail call, an indirect jump,
    /// a trap or a call that never returns.
    terminated: bool,
    /// A fall-through reached another function's start.
    fell_into_start: bool,
    /// A guess's fall-through or jump reached code a kept function covers:
    /// the unreached rest of that function (a jump table's case), not a
    /// function of its own.
    enters_covered: bool,
    /// The entry's own word is not code.
    bad_entry: bool,
    /// The walk reached its instruction cap.
    overlong: bool,
}

/// What a committed walk left that later rounds read back.
struct Kept {
    /// The function.
    func: Function,
    /// Its references: target, site and kind.
    sites: Vec<(u64, u64, RefKind)>,
    /// [`Walked::followed`].
    followed: Vec<u64>,
    /// [`Walked::followed_calls`].
    followed_calls: Vec<u64>,
    /// [`Walked::after_calls`].
    after_calls: Vec<u64>,
    /// [`Walked::tables`].
    tables: Vec<Table>,
}

/// Tells what a direct `b` to `t` in the function at `entry` is.
///
/// A jump into a known start is a tail call. Where the file declares the
/// function's extent, the extent decides: a target outside it (and outside
/// the function's fragments) is a tail call, one inside a jump. Where it
/// declares none, a target past another declared function, right after
/// zero padding (which only separates functions) or on a word only a
/// function opens with is a tail call, and
/// one right after the frame was torn down is one unless the walk reaches
/// it another way ([`Jump::Unless`]). A conditional branch is held to the
/// start, the extent and the declared functions alone
/// ([`Known::leaves`]): a function that shrink-wraps its prologue
/// branches to it past an early return.
///
/// # Arguments
///
/// * `known` - What the wave reads.
/// * `entry` - The walked function's entry.
/// * `t` - The target.
/// * `torn_down` - Whether the instruction before the jump undid the frame.
fn jump_kind(known: &Known<'_>, entry: u64, t: u64, torn_down: bool) -> Jump {
    if known.leaves(entry, t) {
        return Jump::Tail;
    }
    match known.within_extent(entry, t) {
        Some(true) => Jump::Within,
        Some(false) => Jump::Tail,
        None if known.start_at(t)
            || t.checked_sub(STEP)
                .and_then(|before| known.text.word(before))
                == Some(0) =>
        {
            Jump::Tail
        }
        None if torn_down => Jump::Unless,
        None => Jump::Within,
    }
}

/// Walks one function from its entry.
///
/// # Arguments
///
/// * `known` - What the wave reads.
/// * `entry` - Where to start.
/// * `cap` - Most instructions to decode.
/// * `guess` - Whether the entry is a guess, whose walk stops at code a
///   kept function covers ([`Walked::enters_covered`]).
fn walk(known: &Known<'_>, entry: u64, cap: u64, guess: bool) -> Walked {
    let mut seen: FxHashSet<u64> = FxHashSet::default();
    let mut words: Vec<(u64, u32)> = Vec::new();
    let mut pending: Vec<(u64, Via)> = vec![(entry, Via::Fall)];
    pending.extend(
        known
            .pads
            .get(&entry)
            .into_iter()
            .flatten()
            .map(|&pad| (pad, Via::Branch)),
    );
    let mut torn_down: FxHashSet<u64> = FxHashSet::default();
    let mut callees: BTreeSet<u64> = BTreeSet::new();
    let mut followed: BTreeSet<u64> = BTreeSet::new();
    let mut followed_calls: BTreeSet<u64> = BTreeSet::new();
    let mut after_calls: BTreeSet<u64> = BTreeSet::new();
    let mut found_noreturn: BTreeSet<u64> = BTreeSet::new();
    let mut unless_reached: Vec<u64> = Vec::new();
    let (mut junk, mut terminated, mut fell_into_start, mut bad_entry, mut overlong) =
        (false, false, false, false, false);
    let mut enters_covered = false;
    let mut dispatches: Vec<Shape> = Vec::new();
    let mut tables: Vec<Table> = Vec::new();
    let mut rounds = 0;
    loop {
        while let Some((va, via)) = pending.pop() {
            if seen.contains(&va) {
                continue;
            }
            if from_usize(words.len()) >= cap {
                overlong = true;
                break;
            }
            let insn = known
                .text
                .word(va)
                .filter(|&w| w != 0)
                .map(|w| a64::decode(w, va))
                .filter(|i| i.op != Op::Invalid);
            let Some(insn) = insn else {
                junk |= via == Via::Fall;
                bad_entry |= words.is_empty();
                continue;
            };
            seen.insert(va);
            words.push((va, insn.word));
            let next = va.wrapping_add(STEP);
            if prologue::tears_down(insn.word) {
                torn_down.insert(next);
            }
            let falls_into_start = next != entry && known.starts.contains(&next);
            let falls_into_covered = guess && known.covers(next);
            match insn.flow {
                Flow::Next => {
                    if falls_into_start {
                        fell_into_start = true;
                    } else if falls_into_covered {
                        enters_covered = true;
                    } else {
                        pending.push((next, Via::Fall));
                    }
                }
                Flow::CondJump => {
                    if let Some(t) = insn.target() {
                        if t == entry {
                            pending.push((t, Via::Branch));
                        } else if known.leaves(entry, t) {
                            callees.insert(t);
                        } else if guess && known.covers(t) {
                            enters_covered = true;
                        } else {
                            followed.insert(t);
                            pending.push((t, Via::Branch));
                        }
                    }
                    if falls_into_start {
                        fell_into_start = true;
                    } else if falls_into_covered {
                        enters_covered = true;
                    } else {
                        pending.push((next, Via::Fall));
                    }
                }
                Flow::Jump => match insn.target() {
                    None => {
                        terminated = true;
                        if insn.op == Op::Br {
                            dispatches.extend(switch::shape(known.text, &insn));
                        }
                    }
                    Some(t) if t == entry => pending.push((t, Via::Branch)),
                    Some(t) => match jump_kind(known, entry, t, torn_down.contains(&va)) {
                        Jump::Within if guess && known.covers(t) => enters_covered = true,
                        Jump::Within => {
                            followed.insert(t);
                            pending.push((t, Via::Branch));
                        }
                        Jump::Tail => {
                            callees.insert(t);
                            terminated = true;
                        }
                        Jump::Unless => {
                            unless_reached.push(t);
                            terminated = true;
                        }
                    },
                },
                Flow::Call => {
                    let callee = insn.target().filter(|&t| known.text.word(t).is_some());
                    if let Some(t) = callee {
                        callees.insert(t);
                    }
                    if next != entry && known.start_at(next) {
                        found_noreturn.extend(callee);
                        terminated = true;
                    } else if callee.is_some_and(|t| known.noreturn.contains(&t))
                        || known.noreturn_import(&insn, insn.target())
                    {
                        terminated = true;
                    } else {
                        followed_calls.extend(callee);
                        after_calls.insert(next);
                        pending.push((next, Via::Fall));
                    }
                }
                Flow::Return | Flow::Invalid => terminated = true,
            }
        }
        if dispatches.is_empty() || overlong || rounds == TABLE_ROUNDS_MAX {
            break;
        }
        rounds += 1;
        let mut sorted = words.clone();
        sorted.sort_unstable_by_key(|w| w.0);
        let insns: Vec<Insn> = sorted.iter().map(|&(va, w)| a64::decode(w, va)).collect();
        let present = |va: u64| insns.binary_search_by_key(&va, |i| i.va).is_ok();
        let graph = blocks(entry, &insns, &present, &tables);
        let tracker = Tracker::new(&insns, &graph);
        let before = tables.len();
        dispatches.retain(|d| {
            let Some(table) = switch::resolve(known.program, known.text, &tracker, d) else {
                return true;
            };
            for &t in &table.targets {
                if t == entry {
                    pending.push((t, Via::Branch));
                } else if known.leaves(entry, t) {
                    callees.insert(t);
                } else if guess && known.covers(t) {
                    enters_covered = true;
                } else {
                    followed.insert(t);
                    pending.push((t, Via::Branch));
                }
            }
            tables.push(table);
            false
        });
        if tables.len() == before {
            break;
        }
        tables.sort_unstable_by_key(|t| t.site);
    }
    callees.extend(unless_reached.into_iter().filter(|t| !seen.contains(t)));
    let spent = from_usize(words.len());
    let (func, sites) = assemble(entry, words, callees, &tables);
    Walked {
        func,
        sites,
        followed: followed.into_iter().collect(),
        followed_calls: followed_calls.into_iter().collect(),
        after_calls: after_calls.into_iter().collect(),
        found_noreturn: found_noreturn.into_iter().collect(),
        tables,
        spent,
        junk,
        terminated,
        fell_into_start,
        enters_covered,
        bad_entry,
        overlong,
    }
}

/// Tells whether `va` lies in one of `extents`, sorted and disjoint.
///
/// # Arguments
///
/// * `extents` - `(start, end)` pairs, `end` exclusive.
/// * `va` - The address.
fn inside(extents: &[(u64, u64)], va: u64) -> bool {
    extents
        .partition_point(|e| e.0 <= va)
        .checked_sub(1)
        .and_then(|k| extents.get(k))
        .is_some_and(|&(_, end)| va < end)
}

/// Merges extents into sorted, disjoint ones.
///
/// # Arguments
///
/// * `extents` - `(start, end)` pairs in any order, `end` exclusive.
fn merged(mut extents: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
    extents.sort_unstable();
    let mut out: Vec<(u64, u64)> = Vec::with_capacity(extents.len());
    for (lo, hi) in extents {
        match out.last_mut() {
            Some(last) if lo <= last.1 => last.1 = last.1.max(hi),
            Some(_) | None => out.push((lo, hi)),
        }
    }
    out
}

/// Builds the function record and its references from the words a walk
/// decoded.
///
/// # Arguments
///
/// * `entry` - The function's entry.
/// * `words` - The decoded words and their addresses, in walk order.
/// * `callees` - The functions it calls or tail-calls.
/// * `tables` - The jump tables its `br`s dispatch through, by site.
///
/// # Returns
///
/// The function (callers empty, name unset) and its references.
fn assemble(
    entry: u64,
    mut words: Vec<(u64, u32)>,
    callees: BTreeSet<u64>,
    tables: &[Table],
) -> (Function, Vec<(u64, u64, RefKind)>) {
    words.sort_unstable_by_key(|w| w.0);
    let insns: Vec<Insn> = words.iter().map(|&(va, w)| a64::decode(w, va)).collect();
    let present = |va: u64| insns.binary_search_by_key(&va, |i| i.va).is_ok();
    let start = insns.first().map_or(entry, |i| i.va);
    let end = insns.last().map_or(entry, |i| i.va.wrapping_add(STEP));
    let mut sites = Vec::new();
    let (mut body_hash, mut shape_hash) = (HASH_SEED, HASH_SEED);
    for i in &insns {
        let (print, shape) = fingerprint(i);
        body_hash = mix(body_hash, print);
        shape_hash = mix(shape_hash, shape);
        let Some(t) = i.target() else {
            continue;
        };
        body_hash = if (start..end).contains(&t) {
            mix(body_hash, t.wrapping_sub(i.va))
        } else {
            mix(body_hash, t)
        };
        let kind = match i.flow {
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
        blocks: blocks(entry, &insns, &present, tables),
        callees: callees.into_iter().collect(),
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

/// Splits a function's instructions into basic blocks.
///
/// A block starts at the entry, at every branch target and jump-table
/// case the walk decoded, after every instruction control does not simply
/// fall through, and wherever the instructions stop being contiguous. A
/// call ends a block, and its fall-through is a successor only when the
/// walk followed it; a branch's target is a successor wherever it lies, a
/// tail call's included, and a `br` through a resolved table has its cases
/// as successors, in table order.
///
/// # Arguments
///
/// * `entry` - The function's entry.
/// * `insns` - Its instructions, in address order.
/// * `present` - Whether the walk decoded an address.
/// * `tables` - The resolved jump tables, sorted by site.
///
/// # Returns
///
/// The blocks in address order.
fn blocks(
    entry: u64,
    insns: &[Insn],
    present: &dyn Fn(u64) -> bool,
    tables: &[Table],
) -> Vec<BasicBlock> {
    let mut leaders: Vec<u64> = vec![entry];
    for i in insns {
        if matches!(i.flow, Flow::CondJump | Flow::Jump) {
            leaders.extend(i.target().filter(|&t| present(t)));
        }
    }
    for t in tables {
        leaders.extend(t.targets.iter().copied().filter(|&t| present(t)));
    }
    leaders.sort_unstable();
    leaders.dedup();
    let mut out: Vec<BasicBlock> = Vec::new();
    let mut current: Option<BasicBlock> = None;
    for i in insns {
        let next = i.va.wrapping_add(STEP);
        let continues = current.as_ref().is_some_and(|b| {
            b.end == i.va && b.term == BlockTerm::Fall && leaders.binary_search(&i.va).is_err()
        });
        if !continues {
            if let Some(mut b) = current.take() {
                if b.term == BlockTerm::Fall && b.end == i.va {
                    b.successors.push(i.va);
                }
                out.push(b);
            }
            current = Some(BasicBlock {
                start: i.va,
                end: next,
                term: BlockTerm::Fall,
                successors: Vec::new(),
            });
        }
        let Some(b) = current.as_mut() else {
            continue;
        };
        b.end = next;
        match i.flow {
            Flow::Next => {}
            Flow::CondJump => {
                b.term = BlockTerm::Cond;
                b.successors.extend(i.target());
                if present(next) {
                    b.successors.push(next);
                }
            }
            Flow::Jump => match i.target() {
                Some(t) => {
                    b.term = BlockTerm::Jmp;
                    b.successors.push(t);
                }
                None => {
                    b.term = BlockTerm::Indirect;
                    if let Some(t) = tables
                        .binary_search_by_key(&i.va, |t| t.site)
                        .ok()
                        .and_then(|k| tables.get(k))
                    {
                        b.successors.extend(t.targets.iter().copied());
                    }
                }
            },
            Flow::Call => {
                b.term = BlockTerm::Call;
                if present(next) {
                    b.successors.push(next);
                }
            }
            Flow::Return => b.term = BlockTerm::Ret,
            Flow::Invalid => b.term = BlockTerm::Invalid,
        }
    }
    out.extend(current);
    out
}

/// Fingerprints one instruction: everything but the addresses it names,
/// paired with its shape.
///
/// The fingerprint is the word with its PC-relative offset left out (a
/// branch's, an `adr`'s, an `adrp`'s page, a literal load's), so two copies
/// of one function at different addresses agree; the caller folds a
/// branch's target in as an offset when it stays inside the function. The
/// shape is the top byte of that word, which names its encoding group, and
/// its operands' kinds, so functions differing only in registers, constants
/// or offsets agree.
///
/// # Arguments
///
/// * `insn` - The instruction.
///
/// # Returns
///
/// `(fingerprint, shape)`.
fn fingerprint(insn: &Insn) -> (u64, u64) {
    let w = insn.word;
    let fixed = match insn.op {
        Op::B | Op::Bl => w & BRANCH_FIXED,
        Op::BCond(_) | Op::Cbz | Op::Cbnz => w & IMM19_FIXED,
        Op::Tbz | Op::Tbnz => w & TEST_FIXED,
        Op::Adr | Op::Adrp => w & ADR_FIXED,
        Op::Other if w & LITERAL.0 == LITERAL.1 => w & IMM19_FIXED,
        Op::Br
        | Op::Blr
        | Op::Ret
        | Op::Eret
        | Op::Trap
        | Op::Syscall
        | Op::Nop
        | Op::Bti
        | Op::Pac
        | Op::Sve
        | Op::Sme
        | Op::Invalid
        | Op::Other => w,
    };
    let shape = insn
        .operands
        .iter()
        .fold(mix(HASH_SEED, u64::from(fixed >> 24)), |h, o| {
            mix(h, operand_kind(o))
        });
    (mix(HASH_SEED, u64::from(fixed)), shape)
}

/// Names an operand's kind as a number, for a shape.
///
/// # Arguments
///
/// * `o` - The operand.
fn operand_kind(o: &Opnd) -> u64 {
    match o {
        Opnd::None => 0,
        Opnd::Reg { bits, .. } => 1 | u64::from(*bits) << 8,
        Opnd::Shifted { .. } => 2,
        Opnd::Imm(_) => 3,
        Opnd::PcRel(_) => 4,
        Opnd::Mem(m) => {
            5 | match m.mode {
                Mode::Offset => 0,
                Mode::PreIndex => 1 << 8,
                Mode::PostIndex => 2 << 8,
            }
        }
        Opnd::Cond(_) => 6,
        Opnd::Other => 7,
    }
}

/// Says why a walk is not a function, when it is not.
///
/// A walk whose entry is not code is never one. Every other walk from a
/// fact is; a guess must also decode nothing that is not code, reach a way
/// out, run into no other function and no code a kept function covers,
/// hold more than one instruction (or be one jump to another function, a
/// thunk) and stay under its cap.
///
/// # Arguments
///
/// * `w` - The walk.
/// * `guess` - Whether its entry was a guess.
fn rejected(w: &Walked, guess: bool) -> bool {
    let thunk = w.func.instr_count == 1
        && !w.func.callees.is_empty()
        && w.func
            .blocks
            .first()
            .is_some_and(|b| b.term == BlockTerm::Jmp);
    w.bad_entry
        || (guess
            && (w.overlong
                || w.junk
                || !w.terminated
                || w.fell_into_start
                || w.enters_covered
                || (w.func.instr_count < GUESS_INSTRS_MIN && !thunk)))
}

/// The state of one discovery pass.
struct Discovery<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Each function's Itanium landing pads, by entry.
    pads: &'a BTreeMap<u64, Vec<u64>>,
    /// Instructions left to decode across every walk.
    fuel: u64,
    /// The fuel ran out, or a walk reached its cap, before discovery
    /// finished.
    incomplete: bool,
    /// Function starts: the seeds and every callee found so far. A `b`
    /// into one is a tail call.
    starts: FxHashSet<u64>,
    /// Functions that never return: named ones, and callees another
    /// function's start follows that their own code does not show
    /// returning.
    noreturn: FxHashSet<u64>,
    /// The slots the file names imports in.
    import_slots: &'a FxHashSet<u64>,
    /// The slots of the imports named as never returning.
    noreturn_slots: &'a FxHashSet<u64>,
    /// Callees another function's start followed, held until the round
    /// ends ([`Discovery::promote_noreturn`]).
    claimed: BTreeSet<u64>,
    /// Entries still to walk.
    queue: Vec<u64>,
    /// Entries walked and kept.
    done: FxHashSet<u64>,
    /// Entries walked and rejected; a guess is not made at one again.
    rejected: FxHashSet<u64>,
    /// The entries of the guesses now being walked.
    guessed: FxHashSet<u64>,
    /// The kept walks, by entry.
    walked: BTreeMap<u64, Kept>,
    /// The extents the file declares, merged: no guess is made inside one,
    /// where the code is the declared function's own.
    declared: Vec<(u64, u64)>,
    /// The blocks of the guesses kept in this gap round, start to end: a
    /// guess inside one is the rest of that function (code after an early
    /// return), not a function of its own.
    guessed_blocks: BTreeMap<u64, u64>,
}

impl Discovery<'_> {
    /// Walks every queued entry, then walks again each function that
    /// followed what later proved another function, until none did.
    ///
    /// A function is walked again when a jump it followed entered what
    /// proved a start, a call whose fall-through it followed proved never
    /// to return, or the address after such a call proved a start. A
    /// second walk is a fact, whatever made the first.
    ///
    /// # Arguments
    ///
    /// * `text` - The code.
    fn run(&mut self, text: &Text<'_>) {
        for round in 0..SPLIT_ROUNDS_MAX {
            self.drain(text);
            self.promote_noreturn();
            if round + 1 == SPLIT_ROUNDS_MAX {
                break;
            }
            let redo: Vec<u64> = self
                .walked
                .iter()
                .filter(|&(&e, k)| {
                    k.followed
                        .iter()
                        .chain(&k.after_calls)
                        .any(|&t| t != e && self.starts.contains(&t))
                        || k.followed_calls.iter().any(|t| self.noreturn.contains(t))
                })
                .map(|(&e, _)| e)
                .collect();
            if redo.is_empty() {
                break;
            }
            for e in &redo {
                self.walked.remove(e);
                self.done.remove(e);
                self.guessed.remove(e);
            }
            self.queue = redo;
        }
    }

    /// Walks every queued entry once, wave after wave, queueing the callees
    /// each kept walk finds.
    ///
    /// # Arguments
    ///
    /// * `text` - The code.
    fn drain(&mut self, text: &Text<'_>) {
        loop {
            let mut wave = std::mem::take(&mut self.queue);
            wave.sort_unstable();
            wave.dedup();
            wave.retain(|e| !self.done.contains(e));
            if wave.is_empty() {
                return;
            }
            if self.fuel == 0 {
                self.incomplete = true;
                return;
            }
            let starts = self.starts.clone();
            let noreturn = self.noreturn.clone();
            let covered = if wave.iter().any(|e| self.guessed.contains(e)) {
                self.covered()
            } else {
                Vec::new()
            };
            let program = self.program;
            let known = Known {
                program,
                text,
                import_slots: self.import_slots,
                noreturn_slots: self.noreturn_slots,
                starts: &starts,
                noreturn: &noreturn,
                declared: &program.function_ranges,
                fragments: &program.headers.chained_chunks,
                covered: &covered,
                pads: self.pads,
            };
            for batch in wave.chunks(WAVE_BATCH) {
                let guessed = &self.guessed;
                let cap = |e: u64| {
                    if guessed.contains(&e) {
                        GUESS_WALK_MAX
                    } else {
                        WALK_MAX
                    }
                };
                let walks = striped(batch, |&e| walk(&known, e, cap(e), guessed.contains(&e)));
                let walks: Vec<Walked> = batch
                    .iter()
                    .zip(walks)
                    .map(|(&e, w)| {
                        w.unwrap_or_else(|| walk(&known, e, cap(e), guessed.contains(&e)))
                    })
                    .collect();
                for (&e, w) in batch.iter().zip(walks) {
                    self.fuel = self.fuel.saturating_sub(w.spent);
                    self.commit(e, w);
                }
                if self.fuel == 0 {
                    self.incomplete = true;
                    return;
                }
            }
        }
    }

    /// Records one walk: rejected, or kept with its callees made starts
    /// and queued. A guess is rejected too when it lies inside a guess
    /// kept before it in the round ([`Discovery::guessed_blocks`]); the
    /// guesses commit in address order, so a function's own start comes
    /// first.
    ///
    /// # Arguments
    ///
    /// * `entry` - The walk's entry.
    /// * `w` - The walk.
    fn commit(&mut self, entry: u64, w: Walked) {
        let guess = self.guessed.contains(&entry);
        let inside_guess = guess
            && self
                .guessed_blocks
                .range(..=entry)
                .next_back()
                .is_some_and(|(_, &end)| entry < end);
        if rejected(&w, guess) || inside_guess {
            self.rejected.insert(entry);
            return;
        }
        if guess {
            self.guessed_blocks
                .extend(w.func.blocks.iter().map(|b| (b.start, b.end)));
        }
        self.incomplete |= w.overlong;
        self.done.insert(entry);
        self.claimed.extend(w.found_noreturn);
        for &c in &w.func.callees {
            self.starts.insert(c);
            self.queue.push(c);
        }
        self.walked.insert(
            entry,
            Kept {
                func: w.func,
                sites: w.sites,
                followed: w.followed,
                followed_calls: w.followed_calls,
                after_calls: w.after_calls,
                tables: w.tables,
            },
        );
    }

    /// Makes the claimed callees known never to return, each unless its
    /// own code shows a way back: a return, an indirect jump (a dispatcher,
    /// or a jump table not resolved) or a tail call, which returns as its
    /// callee does. A call followed by another function's start proves the
    /// call site never returns, not always the callee.
    fn promote_noreturn(&mut self) {
        for t in std::mem::take(&mut self.claimed) {
            let returns = self.walked.get(&t).is_some_and(|k| {
                k.func.blocks.iter().any(|b| match b.term {
                    BlockTerm::Ret | BlockTerm::Indirect => true,
                    BlockTerm::Jmp => b
                        .successors
                        .iter()
                        .any(|s| k.func.blocks.binary_search_by_key(s, |x| x.start).is_err()),
                    BlockTerm::Cond | BlockTerm::Call | BlockTerm::Fall | BlockTerm::Invalid => {
                        false
                    }
                })
            });
            if !returns {
                self.noreturn.insert(t);
            }
        }
    }

    /// The code the kept functions' blocks cover and the jump tables they
    /// dispatch through, as sorted, disjoint extents: a table kept in the
    /// code is no gap to guess at.
    fn covered(&self) -> Vec<(u64, u64)> {
        merged(
            self.walked
                .values()
                .flat_map(|k| {
                    k.func
                        .blocks
                        .iter()
                        .map(|b| (b.start, b.end))
                        .chain(k.tables.iter().map(|t| (t.at, t.at.saturating_add(t.len))))
                })
                .collect(),
        )
    }

    /// Collects the guesses of one gap round.
    ///
    /// Every gap no block covers in an executable section is swept a word
    /// at a time. A word opens the gap when it is the gap's first, or
    /// follows padding or an instruction control does not fall through (a
    /// jump, a return, a trap); one that opens it the way a function opens
    /// ([`prologue::opens`]) is a guess, unless it was walked or lies inside
    /// an extent the file declares. Where the file declares extents (an
    /// arm64 PE's `.pdata` leaves out the leaf functions that keep no
    /// frame), any word opening a gap outside them is a guess, since the
    /// unreached blocks of a declared function lie inside its extent. In a
    /// file that declares nothing, a word opening like no function is not
    /// guessed at: the unreached blocks of a function never found open that
    /// way too.
    ///
    /// # Arguments
    ///
    /// * `text` - The code.
    ///
    /// # Returns
    ///
    /// The guesses in address order, at most [`SEEDS_MAX`].
    fn gap_seeds(&self, text: &Text<'_>) -> Vec<u64> {
        let covered = self.covered();
        let mut seeds = Vec::new();
        for &(start, bytes) in &text.sections {
            let end = start.saturating_add(from_usize(bytes.len()));
            let mut cursor = start;
            let first = covered.partition_point(|c| c.1 <= start);
            for &(lo, hi) in covered.get(first..).unwrap_or_default() {
                if lo >= end {
                    break;
                }
                if lo > cursor {
                    self.sweep_gap(text, cursor, lo, &mut seeds);
                }
                cursor = cursor.max(hi);
            }
            if cursor < end {
                self.sweep_gap(text, cursor, end, &mut seeds);
            }
            if seeds.len() >= SEEDS_MAX {
                break;
            }
        }
        seeds.truncate(SEEDS_MAX);
        seeds
    }

    /// Sweeps one gap for guesses ([`Discovery::gap_seeds`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The code.
    /// * `lo` - The gap's first byte.
    /// * `hi` - Its end (exclusive).
    /// * `seeds` - Collects the guesses.
    fn sweep_gap(&self, text: &Text<'_>, lo: u64, hi: u64, seeds: &mut Vec<u64>) {
        let Some(first) = lo.checked_next_multiple_of(STEP) else {
            return;
        };
        let mut va = first;
        let mut opening = true;
        while va.checked_add(STEP).is_some_and(|after| after <= hi) && seeds.len() < SEEDS_MAX {
            let Some(word) = text.word(va) else {
                break;
            };
            if opening
                && !prologue::is_padding(word)
                && (prologue::opens(word) || !self.declared.is_empty())
                && !self.done.contains(&va)
                && !self.rejected.contains(&va)
                && !inside(&self.declared, va)
            {
                seeds.push(va);
            }
            opening = prologue::is_padding(word)
                || matches!(
                    a64::decode(word, va).flow,
                    Flow::Jump | Flow::Return | Flow::Invalid
                );
            va += STEP;
        }
    }
}

/// Discovers an arm64 program's functions, blocks and call references.
///
/// # Arguments
///
/// * `program` - The loaded image, arm64.
///
/// # Returns
///
/// The analysis, indexed ([`Analysis::finish_index`]).
pub(crate) fn discover(program: &Program) -> Analysis {
    let text = Text::new(program);
    let seeds = seeds(program);
    let noreturn: FxHashSet<u64> = program
        .symbols
        .iter()
        .filter(|s| s.kind != SymbolKind::Import && s.addr != 0)
        .filter(|s| is_noreturn_name(bare_name(&crate::search::demangled_name(&s.name))))
        .map(|s| s.addr)
        .collect();
    let imports = || {
        program
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
    };
    let import_slots: FxHashSet<u64> = imports().map(|s| s.addr).collect();
    let noreturn_slots: FxHashSet<u64> = imports()
        .filter(|s| is_noreturn_name(bare_name(&crate::search::demangled_name(&s.name))))
        .map(|s| s.addr)
        .collect();
    let throw_sites = crate::lsda::throw_sites(program);
    let pads: BTreeMap<u64, Vec<u64>> = throw_sites
        .iter()
        .map(|(&f, sites)| (f, sites.iter().filter_map(|s| s.landing_pad).collect()))
        .collect();
    let mut d = Discovery {
        program,
        pads: &pads,
        fuel: fuel_for(program),
        incomplete: false,
        starts: seeds.iter().copied().collect(),
        noreturn,
        import_slots: &import_slots,
        noreturn_slots: &noreturn_slots,
        claimed: BTreeSet::new(),
        queue: seeds,
        done: FxHashSet::default(),
        rejected: FxHashSet::default(),
        guessed: FxHashSet::default(),
        walked: BTreeMap::new(),
        declared: merged(program.function_ranges.clone()),
        guessed_blocks: BTreeMap::new(),
    };
    d.run(&text);
    for _ in 0..GAP_ROUNDS_MAX {
        let guesses = d.gap_seeds(&text);
        if guesses.is_empty() {
            break;
        }
        let before = d.walked.len();
        d.guessed = guesses.iter().copied().collect();
        d.queue = guesses;
        d.run(&text);
        d.guessed.clear();
        d.guessed_blocks.clear();
        if d.walked.len() == before {
            break;
        }
    }
    let mut analysis = Analysis {
        incomplete: d.incomplete,
        throw_sites,
        ..Analysis::default()
    };
    for (&entry, k) in &d.walked {
        for &(target, va, kind) in &k.sites {
            push_site(&mut analysis.xrefs, target, va, kind, Some(entry));
        }
        for t in &k.tables {
            analysis.jump_tables.insert(t.site, t.targets.clone());
        }
    }
    analysis.functions = d
        .walked
        .into_values()
        .map(|k| k.func)
        .filter(|f| f.instr_count > 0)
        .collect();
    build_callers_and_names(program, &mut analysis.functions);
    stubs::name(program, &text, &mut analysis.functions);
    refs::index(program, &text, &analysis.functions, &mut analysis.xrefs);
    analysis.finish_index(program);
    analysis
}

/// Tells whether an instruction lets the one after it run next: it falls
/// through, branches only conditionally, or calls.
///
/// # Arguments
///
/// * `insn` - The instruction.
pub(super) fn falls_through(insn: &Insn) -> bool {
    matches!(insn.flow, Flow::Next | Flow::CondJump | Flow::Call)
}
