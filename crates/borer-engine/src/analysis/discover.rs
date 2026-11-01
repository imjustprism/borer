//! The discovery and return inference each instruction set runs, picked
//! by the program's [`Isa`].

use super::{Analysis, a32, a64, functions, returns, rv};
use crate::isa::Isa;
use crate::program::Program;

/// Discovers a program's functions with the walk its instruction set
/// needs.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The analysis, indexed; empty for an architecture the engine does not
/// decode.
pub(super) fn discover(program: &Program) -> Analysis {
    match program.arch.isa() {
        Some(Isa::X86 { bits }) => functions::discover(program, bits),
        Some(Isa::A64) => a64::discover(program),
        Some(Isa::A32) => a32::discover(program),
        Some(Isa::Rv(xlen)) => rv::discover(program, xlen),
        None => {
            let mut empty = Analysis::default();
            empty.finish_index(program);
            empty
        }
    }
}

/// Infers what the discovered functions return, as their instruction set
/// reads it; RISC-V functions are left as discovery found them.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The discovered functions, updated in place.
pub(super) fn infer_returns(program: &Program, analysis: &mut Analysis) {
    match program.arch.isa() {
        Some(Isa::A64) => a64::infer_returns(program, analysis),
        Some(Isa::A32) => a32::infer_returns(program, analysis),
        Some(Isa::Rv(_)) => {}
        Some(Isa::X86 { .. }) | None => returns::infer(program, analysis),
    }
}
