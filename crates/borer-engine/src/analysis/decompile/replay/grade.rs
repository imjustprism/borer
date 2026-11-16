//! Each block's check as a record: its grade, what the replay compared
//! there and the claims the machine does not bear out.
//!
//! The replay decides every block ([`Function::check`](super::Function)):
//! not checked and why, proved over every state, compared on the states
//! tried, or contradicted by one. The record keeps that decision and the
//! disagreements its check found, and the header line an answer carries
//! ([`TextCheck::header`]) counts the records, so the two cannot
//! disagree. A disagreement is charged to the block whose check found it:
//! the run into a block that starts under an equality tries the
//! predecessor ([`edge`]), and what that run finds is why the block is
//! not checked, not a grade of the predecessor, whose own check graded it
//! already. A block can be tried harder on request ([`recheck_block`]).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{
    BARE_RETURN, CONTRADICTED, DISAGREE_SHOWN, Disagreement, OUTSIDE_FLOAT, OVER_BUDGET, Replay,
    Replayed, SHORT_CALL, TRIALS, edge, effects_of, replay_effects,
};
use crate::analysis::decompile::{arch, decompile_with};
use crate::analysis::{Analysis, Overlay};
use crate::cancel::Cancel;
use crate::isa::Isa;
use crate::program::Program;

/// Why a block compared is not proved: a state tried disagrees with the
/// text, which the proof does not take up.
pub(super) const DIFFERED: &str = "a state tried disagrees";
/// Why a block compared is not proved: a state the proof chose to tell a
/// claim's two sides apart disagrees on the emulator.
pub(super) const REFUTED: &str = "a state the proof chose disagrees";
/// Disagreements a block's record keeps; past them it counts.
pub const KEPT_MAX: usize = 16;
/// Most states a recheck tries a block from; more asked for are clamped
/// to it.
pub const RECHECK_MAX: u32 = 256;

/// Which states a block is tried from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Sampling {
    /// [`TRIALS`] states each: a sweep's report counts the states and the
    /// claims compared.
    Every,
    /// [`TRIALS`] states each, no more once the block is proved: an
    /// answer's header grades the blocks and counts no state.
    UntilProved,
    /// One block only, from as many states as asked: a recheck
    /// ([`recheck_block`]).
    Recheck {
        /// The block's start.
        block: u64,
        /// States to try it from, at most [`RECHECK_MAX`].
        trials: u32,
    },
}

impl Sampling {
    /// Returns the states each block is tried from.
    pub(super) fn trials(self) -> u64 {
        match self {
            Self::Every | Self::UntilProved => TRIALS,
            Self::Recheck { trials, .. } => u64::from(trials),
        }
    }

    /// Returns the one block a recheck tries, `None` when every block is
    /// tried.
    pub(super) fn only(self) -> Option<u64> {
        match self {
            Self::Every | Self::UntilProved => None,
            Self::Recheck { block, .. } => Some(block),
        }
    }
}

/// What the replay showed of one block.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Grade {
    /// Compared, and every claim holds over every state against the
    /// lifter's semantics of its instructions.
    Proved,
    /// Compared, and the states tried agree; not proved.
    Tested,
    /// Compared, and its check found a claim the machine does not bear
    /// out, lane roughness aside, on a state tried or one the proof chose.
    Wrong,
    /// Not compared, whatever its check found on the way; a block with no
    /// record is this too.
    #[default]
    Unchecked,
}

/// One block's check: its grade and the evidence behind it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BlockCheck {
    /// The block's start.
    pub start: u64,
    /// What the replay showed.
    pub grade: Grade,
    /// States compared.
    pub states: u32,
    /// Claims compared, over those states.
    pub claims: usize,
    /// Why the block was not checked, or not proved; `None` for one proved.
    pub why: Option<&'static str>,
    /// The disagreements its check found, lane roughness aside, then those
    /// the proof found, the first [`KEPT_MAX`].
    pub disagreements: Vec<Disagreement>,
    /// Disagreements past [`KEPT_MAX`].
    pub past_cap: usize,
    /// The states a recheck asked for, past [`RECHECK_MAX`] when it was
    /// clamped; `None` for an answer's check, [`TRIALS`] per block.
    pub asked: Option<u32>,
}

/// What a replay had compared and found before one block's check.
pub(super) struct Mark {
    /// States compared.
    trials: usize,
    /// Claims compared.
    claims: usize,
    /// Disagreements found.
    disagreements: usize,
    /// Disagreements the proof found.
    refuted: usize,
}

/// Returns what a replay has compared and found so far.
///
/// # Arguments
///
/// * `out` - The replay so far.
pub(super) fn mark(out: &Replayed) -> Mark {
    Mark {
        trials: out.trials,
        claims: claims(out),
        disagreements: out.disagreements.len(),
        refuted: out.refuted.len(),
    }
}

impl BlockCheck {
    /// Returns the record of a block as its check decided it, with the
    /// disagreements that check found.
    ///
    /// The grade is the check's own: a block compared and found to
    /// disagree, lane roughness aside, is wrong; one not compared stays
    /// unchecked whatever its check found, as the replay counts it.
    ///
    /// # Arguments
    ///
    /// * `start` - The block's start.
    /// * `checked` - What the check returned: `None` for a block proved,
    ///   else why not proved, or the error why not checked.
    /// * `before` - What the replay had before this block's check.
    /// * `out` - The replay so far, this block's check included.
    pub(super) fn of(
        start: u64,
        checked: Result<Option<&'static str>, &'static str>,
        before: &Mark,
        out: &Replayed,
    ) -> Self {
        let wrong = out.disagreements.get(before.disagreements..);
        let refuted = out.refuted.get(before.refuted..);
        let found: Vec<Disagreement> = (wrong.unwrap_or_default().iter())
            .filter(|d| !d.lane)
            .chain(refuted.unwrap_or_default())
            .cloned()
            .collect();
        let (grade, why) = match checked {
            Ok(None) => (Grade::Proved, None),
            Ok(Some(why)) if found.is_empty() => (Grade::Tested, Some(why)),
            Ok(Some(why)) => (Grade::Wrong, Some(why)),
            Err(why) => (Grade::Unchecked, Some(why)),
        };
        let past_cap = found.len().saturating_sub(KEPT_MAX);
        let mut disagreements = found;
        disagreements.truncate(KEPT_MAX);
        Self {
            start,
            grade,
            states: u32::try_from(out.trials.saturating_sub(before.trials)).unwrap_or(u32::MAX),
            claims: claims(out).saturating_sub(before.claims),
            why,
            disagreements,
            past_cap,
            asked: None,
        }
    }

    /// Returns the evidence behind the grade, as plain lines a person
    /// reads.
    ///
    /// The first line names the block and its grade with what the grade
    /// means; a block compared then has the states tried and the claims
    /// compared, a block found wrong each disagreement kept (its claim,
    /// place and instruction, the text's value, the machine's, the width
    /// compared and the text's expression) and how many more there were,
    /// and a block not checked or not proved why. The last line says the
    /// text passes after the emission are not checked.
    #[must_use]
    pub fn spell(&self) -> String {
        let meaning = match self.grade {
            Grade::Proved => {
                "proved vs lift: every claim holds on every state against the lifter's semantics of its instructions, and the emulator agreed on each state tried"
            }
            Grade::Tested => {
                "tested: the emulator agreed on each state tried; not proved over every state"
            }
            Grade::Wrong => "wrong: the machine does not bear out the text",
            Grade::Unchecked => "unchecked: not compared from any state",
        };
        let mut out = format!("block {:#x}: {meaning}\n", self.start);
        if self.grade != Grade::Unchecked {
            let (states, claims) = (self.states, self.claims);
            let _ = writeln!(out, "states tried: {states}, claims compared: {claims}");
        }
        for d in &self.disagreements {
            let _ = writeln!(
                out,
                "{} {} at {:#x}: text {:#x}, machine {:#x}, {} bits, expression {}",
                d.claim, d.place, d.at, d.text, d.machine, d.bits, d.expr
            );
        }
        if self.past_cap > 0 {
            let _ = writeln!(out, "{} more past the first {KEPT_MAX}", self.past_cap);
        }
        if let Some(why) = self.why {
            let not = match self.grade {
                Grade::Unchecked => "not checked",
                Grade::Proved | Grade::Tested | Grade::Wrong => "not proved",
            };
            let _ = writeln!(out, "{not}: {why}");
        }
        if let Some(asked) = self.asked {
            let tried = asked.min(RECHECK_MAX);
            let _ = write!(out, "rechecked from up to {tried} states");
            if asked > RECHECK_MAX {
                let _ = write!(out, ": {asked} asked for, clamped to {RECHECK_MAX}");
            }
            out.push('\n');
        }
        out.push_str("the text passes after the emission are not checked");
        out
    }

    /// Returns the bytes the record holds beyond its own size.
    fn heap(&self) -> usize {
        self.disagreements.capacity() * size_of::<Disagreement>()
            + self
                .disagreements
                .iter()
                .map(|d| d.place.capacity() + d.expr.capacity())
                .sum::<usize>()
    }
}

/// Returns the claims a replay compared, over every kind.
///
/// # Arguments
///
/// * `r` - The replay so far.
fn claims(r: &Replayed) -> usize {
    r.compared.values().sum()
}

/// Replays one block of a function's text from more states than an
/// answer's check tries, as that check does and from the same seeds.
///
/// The text is decompiled afresh under `overlay` and its block tried from
/// states seeded by `seed`, the block's address and the trial, as
/// [`replay`](super::replay) seeds them, so the first [`TRIALS`] are the
/// check's own; each state runs within the replay's step budget and the
/// proof within its term budget. Not memoized: a caller asks once per
/// request. The same arguments give the same record at any thread count.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the text is decompiled under.
/// * `entry` - The function's entry.
/// * `block` - The block's start.
/// * `seed` - The states' seed; [`ANSWER_SEED`](super::ANSWER_SEED) is the
///   answer check's.
/// * `trials` - States to try the block from, clamped to [`RECHECK_MAX`].
///
/// # Returns
///
/// The block's record, `None` when the function does not decompile, the
/// image has no emulator, no block of the function starts at `block`, or
/// the caller's [`Cancel`] was raised.
#[must_use]
pub fn recheck_block(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    block: u64,
    seed: u64,
    trials: u32,
) -> Option<BlockCheck> {
    let asked = Sampling::Recheck {
        block,
        trials: trials.min(RECHECK_MAX),
    };
    let mut record = match program.arch.isa()? {
        Isa::X86 { .. } => recheck_in::<arch::X86>(program, analysis, overlay, entry, seed, asked),
        Isa::A64 => recheck_in::<arch::A64>(program, analysis, overlay, entry, seed, asked),
        Isa::A32 => recheck_in::<arch::A32>(program, analysis, overlay, entry, seed, asked),
        Isa::Rv(_) => None,
    }?;
    record.asked = Some(trials);
    (!Cancel::raised()).then_some(record)
}

/// [`recheck_block`] for one instruction set.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the text is decompiled under.
/// * `entry` - The function's entry.
/// * `seed` - The states' seed.
/// * `sampling` - The block and the states to try it from.
fn recheck_in<L: Replay>(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    seed: u64,
    sampling: Sampling,
) -> Option<BlockCheck> {
    let f = analysis.function(entry)?;
    let d = decompile_with(program, analysis, overlay, entry, true, &[], true)?;
    let w = d.take_witness()?;
    let template = L::rig(program, analysis)?;
    let effects = effects_of(&d, f);
    let r = replay_effects::<L>(
        program,
        analysis,
        overlay,
        &template,
        entry,
        seed,
        (&w, &d.live.succs),
        &effects,
        usize::MAX,
        sampling,
    );
    r.records.into_iter().next()
}

/// What the check of one function's answer found: the header line the
/// `decompile` tool prints.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TextCheck {
    /// Each block's check, in block address order.
    pub blocks: Vec<BlockCheck>,
    /// The instructions of the statements the machine does not bear out,
    /// lane roughness aside, in address order: from a state tried or one
    /// the proof chose.
    pub disagree: Vec<u64>,
}

impl TextCheck {
    /// Sums a replay up.
    ///
    /// # Arguments
    ///
    /// * `r` - One function's replay.
    pub(super) fn of(r: Replayed) -> Self {
        let mut disagree: Vec<u64> = r
            .wrong()
            .iter()
            .map(|d| d.at)
            .chain(r.refuted.iter().map(|d| d.at))
            .collect();
        disagree.sort_unstable();
        disagree.dedup();
        Self {
            blocks: r.records,
            disagree,
        }
    }

    /// Returns how many blocks have a grade.
    ///
    /// # Arguments
    ///
    /// * `grade` - The grade counted.
    #[must_use]
    pub fn count(&self, grade: Grade) -> usize {
        self.blocks.iter().filter(|b| b.grade == grade).count()
    }

    /// Returns the blocks not compared, by the header's words for what
    /// kept them out, most first.
    #[must_use]
    pub fn unchecked(&self) -> Vec<(&'static str, usize)> {
        let mut why: BTreeMap<&'static str, usize> = BTreeMap::new();
        for b in self.blocks.iter().filter(|b| b.grade == Grade::Unchecked) {
            let label = unchecked_label(b.why.unwrap_or_default());
            *why.entry(label).or_default() += 1;
        }
        let mut unchecked: Vec<(&'static str, usize)> = why.into_iter().collect();
        unchecked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        unchecked
    }

    /// The bytes the result holds, which the memo keeping it counts.
    #[must_use]
    pub fn bytes(&self) -> usize {
        size_of::<Self>()
            + self.blocks.capacity() * size_of::<BlockCheck>()
            + self.blocks.iter().map(BlockCheck::heap).sum::<usize>()
            + self.disagree.capacity() * size_of::<u64>()
    }

    /// The header line: what of the answer was checked against the binary,
    /// what the binary contradicts, and what was not checked.
    ///
    /// Checked means the statements as the lifter emitted them were
    /// replayed from [`TRIALS`] states per block (one random, the others
    /// drawn from the block's own constants and their neighbors) and
    /// compared with the emulator. Each checked block is graded: proved
    /// when its claims hold over every state, symbolically against the
    /// lifter's semantics of its instructions, tested when only the states
    /// tried agree, or when one disagrees; blocks not checked are unknown.
    /// The counts are the records' ([`BlockCheck`]). The proof's machine is
    /// the lifter itself ([`prove`](super::prove)), so the line says
    /// `proved vs lift`: the text equals the lift on every state, and met
    /// the emulator on the one state tried before the proof, not on every
    /// state. A misreading of an instruction the lifter makes is proved,
    /// and only the states tried and [`verify`](super::super::verify) hold
    /// the lift to the emulator, which may share it. A statement the
    /// machine does not bear out, on a state tried or on one the proof
    /// chose to tell a claim's sides apart, is named by its instruction,
    /// the first [`DISAGREE_SHOWN`] of them, so a block that was compared
    /// and found wrong never reads as agreement; the blocks left out are
    /// counted by why. What a statement computes is checked, not how its C
    /// is spelled (a cast that makes C's `>>` the signed one, a constant
    /// written as a literal), and the text passes after the emission are
    /// not checked either, which the line says too. One line on every
    /// answer costs tokens, so it is terse, and a grade no block has is
    /// left out: `// checked vs binary: statements as emitted, 41/44
    /// blocks: 30 proved vs lift, 11 tested x3 states, 3 unknown; disagree
    /// at 0x401a2c; unchecked: 2 float/vector, 1 over budget, C spelling,
    /// later text passes`.
    #[must_use]
    pub fn header(&self) -> String {
        let blocks = self.blocks.len();
        let unknown = self.count(Grade::Unchecked);
        let checked = blocks.saturating_sub(unknown);
        let proved = self.count(Grade::Proved);
        let mut out = format!(
            "// checked vs binary: statements as emitted, {checked}/{blocks} blocks: {proved} proved vs lift"
        );
        let tested = checked.saturating_sub(proved);
        if tested > 0 {
            let _ = write!(out, ", {tested} tested x{TRIALS} states");
        }
        if unknown > 0 {
            let _ = write!(out, ", {unknown} unknown");
        }
        out.push_str("; ");
        if !self.disagree.is_empty() {
            let shown: Vec<String> = self
                .disagree
                .iter()
                .take(DISAGREE_SHOWN)
                .map(|a| format!("{a:#x}"))
                .collect();
            let _ = write!(out, "disagree at {}", shown.join(", "));
            let more = self.disagree.len().saturating_sub(DISAGREE_SHOWN);
            if more > 0 {
                let _ = write!(out, " (+{more} more)");
            }
            out.push_str("; ");
        }
        out.push_str("unchecked: ");
        for (label, n) in &self.unchecked() {
            let _ = write!(out, "{n} {label}, ");
        }
        out.push_str("C spelling, later text passes");
        out
    }
}

/// The few words the header line gives a reason a block was not checked.
///
/// # Arguments
///
/// * `reason` - Why the replay did not compare the block.
fn unchecked_label(reason: &str) -> &'static str {
    match reason {
        "not in the text" => "not in text",
        OUTSIDE_FLOAT => "float/vector",
        "a read or write through the thread block" => "fs/gs access",
        OVER_BUDGET => "over budget",
        "a call the text leaves out or reads in place" => "call left out",
        SHORT_CALL => "call args dropped",
        CONTRADICTED => "declaration contradicted",
        BARE_RETURN => "result dropped",
        "a statement no effect models"
        | "an instruction the emulator does not model"
        | "an instruction outside every checked form"
        | "a trap or a branch with no model" => "unmodeled",
        "flags set in another block" => "flags across blocks",
        edge::ASSUMED => "entry equality",
        "the stack pointer unknown at its start" | "a frame alignment" => "stack unknown",
        _ => "other",
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;
