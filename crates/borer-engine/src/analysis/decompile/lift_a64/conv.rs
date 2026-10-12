//! The arm64 procedure call standard (AAPCS64), as far as the lifter reads
//! it: which registers a function preserves for its caller, and which a
//! call leaves holding nothing the caller set.

use crate::isa::a64::Reg;

/// The highest general register a call may change: `x0` to `x18` are the
/// argument, result and scratch registers, `x18` among them since a
/// platform that reserves it promises the caller nothing either.
// SPEC: Arm IHI 0055 (AAPCS64) 6.1.1, general-purpose registers.
const SCRATCH_X: u8 = 18;

/// The link register, which a call overwrites with its return address.
const LINK: u8 = 30;

/// The lowest and highest `v` register whose low 64 bits a function
/// preserves.
// SPEC: Arm IHI 0055 (AAPCS64) 6.1.2, SIMD and floating-point registers.
const SAVED_V: (u8, u8) = (8, 15);

/// The highest `v` register number.
const LAST_V: u8 = 31;

/// Tells whether a function must give `r` back to its caller as it found
/// it.
///
/// A store of such a register in a prologue is a save: `x19` to `x28`, the
/// frame pointer `x29`, the link register `x30` it returns through, and
/// `v8` to `v15`, whose low 64 bits the standard preserves.
///
/// # Arguments
///
/// * `r` - The register.
pub(in crate::analysis::decompile) fn callee_saved(r: Reg) -> bool {
    match r {
        Reg::X(n) => n > SCRATCH_X,
        Reg::V(n) => (SAVED_V.0..=SAVED_V.1).contains(&n),
        Reg::Sp | Reg::Zr => false,
    }
}

/// Returns the registers a call leaves holding nothing the caller set.
///
/// They are `x0` to `x18`, the link register the call writes, and every
/// `v` register but `v8` to `v15`, whose upper halves the lifter does not
/// track apart.
pub(super) fn clobbered() -> impl Iterator<Item = Reg> {
    (0..=SCRATCH_X)
        .chain(std::iter::once(LINK))
        .map(Reg::X)
        .chain(
            (0..=LAST_V)
                .filter(|n| !(SAVED_V.0..=SAVED_V.1).contains(n))
                .map(Reg::V),
        )
}
