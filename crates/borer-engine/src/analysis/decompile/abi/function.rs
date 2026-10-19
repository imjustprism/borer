//! How a function takes its parameters, read once per function: its
//! [`Shape`], built by the lifter of its instruction set.

use std::sync::Arc;

use super::super::{Shape, lift_a64, shape_built};
use crate::analysis::{Analysis, Function, Overlay};
use crate::isa::{Isa, x86::Register};
use crate::program::Program;

/// Returns a function's [`Shape`], read once per function and overlay
/// through [`Analysis::derived`], by the lifter of its instruction set.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names and prototypes.
/// * `f` - The function.
/// * `bitness` - Decoder bitness, `32` or `64`.
pub(in crate::analysis::decompile) fn shape(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
    bitness: u32,
) -> Arc<Shape> {
    analysis.derived.get_or_build_item(
        "shape",
        overlay.fingerprint(),
        f.entry,
        || match program.arch.isa() {
            Some(Isa::A64) => lift_a64::built_shape(program, analysis, overlay, f),
            Some(Isa::X86 { .. }) | None => shape_built(program, analysis, overlay, f, bitness),
        },
        |shape| shape.params.capacity() * size_of::<Register>(),
    )
}
