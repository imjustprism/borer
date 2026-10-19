//! The ARM32 procedure call standard as far as the lifter reads it.
//!
//! The standard is the AAPCS with the VFP variant's floating-point
//! registers: where arguments and results travel, which registers a
//! function preserves for its caller, and which a call leaves holding
//! nothing the caller set.
//!
//! An integer or a pointer travels in `r0` to `r3`, a 64-bit integer in an
//! even-odd pair of them, and the rest on the stack. Under the hard-float
//! variant a `float` takes the next free single of `s0` to `s15` and a
//! `double` the next free double of `d0` to `d7`, a single back-filling a
//! half a double left; a result comes back in `r0` (and `r1`), `s0` or
//! `d0`. `r4` to `r11`, the stack pointer and `s16` to `s31` (`d8` to
//! `d15`) are preserved.

use crate::isa::a32::Reg;

/// The core registers an argument travels in, `r0` to `r3`.
pub(in crate::analysis::decompile) const INT_ARGS: u8 = 4;

/// The singles a float argument travels in, `s0` to `s15`.
pub(in crate::analysis::decompile) const FLOAT_SINGLES: u8 = 16;

/// The lowest and highest core register a function preserves.
const SAVED_R: (u8, u8) = (4, 11);

/// The link register, which a call overwrites with its return address and
/// a prologue saves.
const LINK: u8 = 14;

/// The intra-procedure scratch register a call may change, `r12`.
const SCRATCH: u8 = 12;

/// The lowest single a function preserves, `s16` (`d8`).
const SAVED_S: u8 = 16;

/// Tells whether a function must give `r` back to its caller as it found it.
///
/// A prologue's store of such a register is a save: `r4` to `r11`, the
/// link register it returns through, and `s16` to `s31` (`d8` to `d15`).
///
/// # Arguments
///
/// * `r` - The register.
pub(in crate::analysis::decompile) fn callee_saved(r: Reg) -> bool {
    match r {
        Reg::R(n) => (SAVED_R.0..=SAVED_R.1).contains(&n) || n == LINK,
        Reg::S(n) => n >= SAVED_S,
        Reg::D(n) => (SAVED_S / 2..SAVED_S).contains(&n),
    }
}

/// Tells whether a store of `bits` of `r` is a whole save of a register
/// the function preserves ([`callee_saved`]).
///
/// # Arguments
///
/// * `r` - The register stored.
/// * `bits` - The store's width.
pub(in crate::analysis::decompile) fn saved(r: Reg, bits: u8) -> bool {
    let whole = match r {
        Reg::R(_) | Reg::S(_) => 32,
        Reg::D(_) => 64,
    };
    bits == whole && callee_saved(r)
}

/// Returns the registers a call leaves holding nothing the caller set:
/// `r0` to `r3`, `r12`, the link register, `s0` to `s15` with `d0` to
/// `d7`, and `d16` to `d31`.
pub(in crate::analysis::decompile) fn clobbered() -> impl Iterator<Item = Reg> {
    (0..INT_ARGS)
        .chain([SCRATCH, LINK])
        .map(Reg::R)
        .chain((0..FLOAT_SINGLES).map(Reg::S))
        .chain((0..FLOAT_SINGLES / 2).map(Reg::D))
        .chain((FLOAT_SINGLES..32).map(Reg::D))
}
