//! Each block's check as a record: its grade, what the replay compared
//! there and the claims the machine does not bear out.
//!
//! The replay decides every block ([`Function::check`](super::Function)):
//! not checked and why, proved over every state, compared on the states
//! tried, or contradicted by one. The record keeps that decision, and the
//! header line an answer carries ([`TextCheck::header`]) counts the
//! records, so the two cannot disagree.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{
    BARE_RETURN, CONTRADICTED, DISAGREE_SHOWN, Disagreement, OUTSIDE_FLOAT, OVER_BUDGET, Replayed,
    SHORT_CALL, TRIALS, edge,
};

/// Why a block compared is not proved: a state tried disagrees with the
/// text, which the proof does not take up.
pub(super) const DIFFERED: &str = "a state tried disagrees";
/// Why a block compared is not proved: a state the proof chose to tell a
/// claim's two sides apart disagrees on the emulator.
pub(super) const REFUTED: &str = "a state the proof chose disagrees";
/// Disagreements a block's record keeps; past them it counts.
pub const KEPT_MAX: usize = 16;

/// What the replay showed of one block.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Grade {
    /// Compared, and every claim holds over every state against the
    /// lifter's semantics of its instructions.
    Proved,
    /// Compared, and the states tried agree; not proved.
    Tested,
    /// A claim the machine does not bear out, lane roughness aside, on a
    /// state tried or one the proof chose, whatever else held.
    Wrong,
    /// Not compared; a block with no record is this too.
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
    /// The block's disagreements, lane roughness aside, then those the
    /// proof found, the first [`KEPT_MAX`].
    pub disagreements: Vec<Disagreement>,
    /// Disagreements past [`KEPT_MAX`].
    pub past_cap: usize,
}

impl BlockCheck {
    /// Returns the record of a block as its check decided it.
    ///
    /// # Arguments
    ///
    /// * `start` - The block's start.
    /// * `checked` - What the check returned: `None` for a block proved,
    ///   else why not proved, or the error why not checked.
    /// * `before` - The states and the claims the replay had compared
    ///   before this block.
    /// * `out` - The replay so far, this block included.
    pub(super) fn of(
        start: u64,
        checked: Result<Option<&'static str>, &'static str>,
        before: (usize, usize),
        out: &Replayed,
    ) -> Self {
        let (grade, why) = match checked {
            Ok(None) => (Grade::Proved, None),
            Ok(Some(why)) => (Grade::Tested, Some(why)),
            Err(why) => (Grade::Unchecked, Some(why)),
        };
        Self {
            start,
            grade,
            states: u32::try_from(out.trials.saturating_sub(before.0)).unwrap_or(u32::MAX),
            claims: claims(out).saturating_sub(before.1),
            why,
            disagreements: Vec::new(),
            past_cap: 0,
        }
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
pub(super) fn claims(r: &Replayed) -> usize {
    r.compared.values().sum()
}

/// Grades wrong each block of one function's replay that a disagreement,
/// lane roughness aside, or a refutation names, and keeps it in the
/// block's record.
///
/// # Arguments
///
/// * `out` - One function's replay, its records in block address order.
pub(super) fn blame(out: &mut Replayed) {
    let Replayed {
        disagreements,
        refuted,
        records,
        ..
    } = out;
    for d in disagreements
        .iter()
        .filter(|d| !d.lane)
        .chain(refuted.iter())
    {
        let Ok(i) = records.binary_search_by_key(&d.block, |r| r.start) else {
            continue;
        };
        let Some(r) = records.get_mut(i) else {
            continue;
        };
        r.grade = Grade::Wrong;
        if r.disagreements.len() < KEPT_MAX {
            r.disagreements.push(d.clone());
        } else {
            r.past_cap += 1;
        }
    }
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
    pub(super) fn of(r: &Replayed) -> Self {
        let mut disagree: Vec<u64> = r
            .wrong()
            .iter()
            .map(|d| d.at)
            .chain(r.refuted.iter().map(|d| d.at))
            .collect();
        disagree.sort_unstable();
        disagree.dedup();
        Self {
            blocks: r.records.clone(),
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
