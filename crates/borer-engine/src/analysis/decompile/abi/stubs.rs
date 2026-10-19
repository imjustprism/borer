//! Linkage stubs: which function a PLT entry reaches once the loader binds
//! its slot.
//!
//! A shared object calls a function it exports through its PLT, since
//! another object may interpose its own copy, and the `JUMP_SLOT`
//! relocation fills the stub's GOT slot with the function's address. A
//! call to such a stub is a call to that function, and takes its
//! arguments from that function's signature.

use crate::program::Program;

/// Returns the code address a slot holds once the loader has bound it.
///
/// # Arguments
///
/// * `program` - The loaded image, its relocations applied.
/// * `slot` - The slot's address.
///
/// # Returns
///
/// The bound address, or `None` when the slot is null, cannot be read or
/// holds zero.
pub(crate) fn bound(program: &Program, slot: u64) -> Option<u64> {
    if slot == 0 {
        return None;
    }
    let word = program.read_va(slot, if program.is_64 { 8 } else { 4 })?;
    let value = match *word {
        [a, b, c, d] => u64::from(u32::from_le_bytes([a, b, c, d])),
        [a, b, c, d, e, f, g, h] => u64::from_le_bytes([a, b, c, d, e, f, g, h]),
        _ => return None,
    };
    (value != 0).then_some(value)
}

/// Returns the function a call to `entry` reaches: the bound target when
/// `entry` is a linkage stub for a function of the program's own, else
/// `entry` itself.
///
/// # Arguments
///
/// * `analysis` - The functions, their stubs bound.
/// * `entry` - A call target.
pub(crate) fn reached(analysis: &crate::analysis::Analysis, entry: u64) -> u64 {
    analysis
        .function(entry)
        .filter(|f| f.entry == entry)
        .and_then(|f| f.bound)
        .unwrap_or(entry)
}
