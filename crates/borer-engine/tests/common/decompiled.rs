//! The analysis-then-decompile step every pseudo-C test takes.

use borer_engine::analysis::{Analysis, Overlay, decompile::decompile};
use borer_engine::program::Program;

/// Decompiles one function of `p` under a fresh analysis and an empty
/// overlay.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or an empty string when decompilation fails, so an
/// assertion on the text prints what came back.
pub(crate) fn decompiled(p: &Program, entry: u64) -> String {
    let a = Analysis::compute(p);
    decompile(p, &a, &Overlay::default(), entry).unwrap_or_default()
}
