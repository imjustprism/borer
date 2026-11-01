//! The check of one function's answer: its statements replayed against
//! the machine within [`ANSWER_BLOCKS`], from the decompilation the caller
//! holds or the memoized one.

use super::{
    ANSWER_BLOCKS, ANSWER_SEED, Replay, Sampling, TextCheck, Witness, effects_of, replay_effects,
};
use crate::analysis::decompile::{Decompiled, arch, decompile_with};
use crate::analysis::{Analysis, Overlay, decompiled_witnessed};
use crate::isa::Isa;
use crate::program::Program;

/// Checks the statements of one function's answer against the binary, as
/// [`replay_function`](super::replay_function) does, under the answer's names and within
/// [`ANSWER_BLOCKS`].
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the answer is decompiled under.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// What was checked, `None` when the function does not decompile or the
/// image has no emulator.
pub(crate) fn check_answer(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<TextCheck> {
    program.arch.isa()?;
    let shared = decompiled_witnessed(program, analysis, overlay, overlay.fingerprint(), entry);
    let fresh;
    let (d, w) = match shared.as_ref().as_ref().map(|d| (d, d.take_witness())) {
        Some((d, Some(w))) => (d, w),
        _ => {
            fresh = decompile_with(program, analysis, overlay, entry, true, &[], true)?;
            let w = fresh.take_witness()?;
            (&fresh, w)
        }
    };
    check_decompiled(program, analysis, overlay, entry, (d, &w))
}

/// [`check_answer`] of a decompilation the caller already holds, with the
/// witness its lift kept.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names `d` was decompiled under.
/// * `entry` - The function's entry.
/// * `witnessed` - The decompilation and its witness.
///
/// # Returns
///
/// As [`check_answer`].
pub(in crate::analysis::decompile) fn check_decompiled(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    witnessed: (&Decompiled, &Witness),
) -> Option<TextCheck> {
    match program.arch.isa()? {
        Isa::X86 { .. } => check_in::<arch::X86>(program, analysis, overlay, entry, witnessed),
        Isa::A64 => check_in::<arch::A64>(program, analysis, overlay, entry, witnessed),
        Isa::A32 => check_in::<arch::A32>(program, analysis, overlay, entry, witnessed),
    }
}

/// [`check_decompiled`] for one instruction set.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the answer is decompiled under.
/// * `entry` - The function's entry.
/// * `witnessed` - The decompilation and its witness.
fn check_in<L: Replay>(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    (d, w): (&Decompiled, &Witness),
) -> Option<TextCheck> {
    let f = analysis.function(entry)?;
    let template = L::rig(program, analysis)?;
    let effects = effects_of(d, f);
    let r = replay_effects::<L>(
        program,
        analysis,
        overlay,
        &template,
        entry,
        ANSWER_SEED,
        (w, &d.live.succs),
        &effects,
        ANSWER_BLOCKS,
        Sampling::UntilProved,
    );
    (r.functions == 1).then(|| TextCheck::of(&r))
}
