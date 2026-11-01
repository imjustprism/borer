//! Checked answers: each function's text replayed against the machine,
//! kept in [`Analysis::derived`] beside the text, and the header line a
//! `decompile` answer prints from it.

use super::{decompile_witnessed, finished, name_fields, render_all, replay};
use crate::analysis::{Analysis, Overlay};
use crate::program::Program;

/// Returns [`decompile_named_all`](super::decompile_named_all)'s texts,
/// checking each from its own decompilation.
///
/// The checks run across the cores and stay in the memo
/// [`checked_header`] reads, so a caller printing them decompiles nothing
/// again.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
/// * `entries` - Function entries, in any order.
///
/// # Returns
///
/// One result per entry, in the order of `entries`.
pub fn decompile_checked_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
) -> Vec<Option<String>> {
    render_all(
        program,
        analysis,
        overlay,
        entries,
        decompile_checked_afresh,
    )
}

/// What the check of a function's answer found ([`replay::TextCheck`]),
/// once per overlay, through [`Analysis::derived`] beside the text.
///
/// The statements the lifter emitted for the function under `overlay` are
/// replayed against the emulator from fixed states within a fixed block
/// budget, so the result is a function of the binary, the names and the
/// entry alone. It is an item result, let go with the names it was read
/// under, like the text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The check, `None` inside when the function does not decompile or the
/// image has no emulator.
pub fn text_check(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> std::sync::Arc<Option<replay::TextCheck>> {
    text_check_with(analysis, overlay, entry, || {
        replay::check_answer(program, analysis, overlay, entry)
    })
}

/// [`text_check`] with the check `build` makes when the memo has none.
///
/// # Arguments
///
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `build` - Checks the function's answer.
fn text_check_with(
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    build: impl FnOnce() -> Option<replay::TextCheck>,
) -> std::sync::Arc<Option<replay::TextCheck>> {
    analysis.derived.get_or_build_item(
        "text_check",
        overlay.fingerprint(),
        entry,
        || crate::timing::timed(crate::timing::Step::Replay, build),
        |c| c.as_ref().map_or(0, replay::TextCheck::bytes),
    )
}

/// The header line a `decompile` answer prints under its first line: what
/// of the text was checked against the binary ([`text_check`]).
///
/// Only the tools' rendering carries it; the text every other reader
/// parses ([`decompile_named`](super::decompile_named),
/// [`decompile_plain`](super::decompile_plain) and the memo) does not.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The line, without its newline; `None` when nothing could be checked.
pub fn checked_header(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    text_check(program, analysis, overlay, entry)
        .as_ref()
        .as_ref()
        .map(replay::TextCheck::header)
}

/// [`decompile_named_afresh`](super::decompile_named_afresh) that also
/// checks the answer from the same decompilation and keeps the check in
/// the memo [`text_check`] reads.
///
/// The text is not kept: only the check, which is small, so a later
/// [`checked_header`] reads it instead of decompiling again.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or `None` as for [`decompile`](super::decompile).
fn decompile_checked_afresh(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let d = decompile_witnessed(program, analysis, overlay, entry)?;
    if let Some(w) = d.take_witness() {
        text_check_with(analysis, overlay, entry, || {
            replay::check_decompiled(program, analysis, overlay, entry, (&d, &w))
        });
    }
    name_fields(program, analysis, overlay, entry, &d.text)
        .map(|out| finished(&out, program, analysis, overlay, entry))
}
