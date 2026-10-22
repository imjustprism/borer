//! A replay as a report: the summary lines, then a row per disagreement.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::{Claim, LISTED_MAX, Replayed, low};

/// Renders a replay as a report.
///
/// A `#` summary, a line per kind of claim with what was compared, the
/// reasons blocks were not checked, then a row per disagreement, at most
/// [`LISTED_MAX`]; rows whose values differ only above the low 32 bits
/// or whose claim is a lane's say so in their `lane` column and come last,
/// so the whole disagreements are never cut off behind them.
///
/// # Arguments
///
/// * `r` - What [`replay`](super::replay) found.
#[must_use]
pub fn replay_tsv(r: &Replayed) -> String {
    let skipped: usize = r.skipped.values().sum();
    let lane = r.disagreements.iter().filter(|d| d.lane).count();
    let mut out = format!(
        "# replayed {} functions, {} blocks: {} checked from {} states, {skipped} not checked, {} disagreements ({lane} of a lane only)\n",
        r.functions,
        r.blocks,
        r.checked,
        r.trials,
        r.disagreements.len()
    );
    for claim in Claim::ALL {
        let _ = writeln!(
            out,
            "# {claim}: {} compared, {} not readable, {} disagree",
            r.compared.get(&claim).copied().unwrap_or(0),
            r.unreadable.get(&claim).copied().unwrap_or(0),
            r.disagreements
                .iter()
                .filter(|d| d.claim == claim && !d.lane)
                .count()
        );
    }
    for (reason, n) in &r.skipped {
        let _ = writeln!(out, "# not checked: {n} for {reason}");
    }
    let refuted: BTreeSet<(u64, u64)> = r.refuted.iter().map(|d| (d.function, d.block)).collect();
    let _ = writeln!(
        out,
        "# proved over every state: {} of {} checked blocks; {} refuted by a state the proof chose",
        r.proved,
        r.checked,
        refuted.len()
    );
    for (reason, n) in &r.unproved {
        let _ = writeln!(out, "# not proved: {n} for {reason}");
    }
    if r.disagreements.len() > LISTED_MAX {
        let _ = writeln!(
            out,
            "# showing {LISTED_MAX} of {} disagreements",
            r.disagreements.len()
        );
    }
    out.push_str("function\tblock\tat\tclaim\tplace\ttext\tmachine\tbits\tlane\texpression\n");
    let (whole, lanes): (Vec<_>, Vec<_>) = r.disagreements.iter().partition(|d| !d.lane);
    for d in whole
        .into_iter()
        .chain(&r.refuted)
        .chain(lanes)
        .take(LISTED_MAX)
    {
        let _ = writeln!(
            out,
            "{:#x}\t{:#x}\t{:#x}\t{}\t{}\t{:#x}\t{:#x}\t{}\t{}\t{}",
            d.function, d.block, d.at, d.claim, d.place, d.text, d.machine, d.bits, d.lane, d.expr
        );
    }
    out
}

/// The width a byte or word write left of a register whose bits above it
/// the expression keeps, when it is that merge.
///
/// `mov cx, [rsp+0x60]` keeps bits 16 to 63 of rcx, so the text spells
/// the register as `(rcx & ~0xffff) | (word & 0xffff)`. Those kept bits are
/// what the register held when the block began, which the replay seeds
/// without the text's history, so a difference confined to them is a
/// lane's, as a difference above bit 32 is.
///
/// # Arguments
///
/// * `expr` - The claim's expression as a row renders it.
fn kept_above(expr: &str) -> Option<u8> {
    let merge = expr.strip_prefix("Bin(Or, Bin(And, ")?;
    [(!0xffu64, 8), (!0xffffu64, 16)]
        .into_iter()
        .find(|(mask, _)| merge.contains(&format!("Const({mask})")))
        .map(|(_, w)| w)
}

/// Tells whether a disagreement is a lane's only: a narrowing claim, a
/// difference above bit 32, or one confined to the bits a byte or word
/// write kept ([`kept_above`]).
///
/// # Arguments
///
/// * `claim` - What kind of claim.
/// * `bits` - The width compared.
/// * `diff` - The text's value xor the machine's.
/// * `expr` - The claim's expression as a row renders it.
pub(super) fn lane_only(claim: Claim, bits: u8, diff: u64, expr: &str) -> bool {
    claim == Claim::Narrow
        || (bits > 32 && diff & low(32) == 0)
        || kept_above(expr).is_some_and(|w| diff & low(w) == 0)
}
