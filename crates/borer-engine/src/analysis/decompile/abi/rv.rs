//! The RISC-V calling convention as far as the lifter reads it: LP64D on
//! RV64 and ILP32D on RV32.
//!
//! An integer or a pointer travels in `a0` to `a7` (`x10` to `x17`) and a
//! float or a double in `fa0` to `fa7` (`f10` to `f17`), each bank
//! counting its own arguments; a result comes back in `a0` (and `a1`) or
//! `fa0`. `s0` to `s11`, the stack pointer and `fs0` to `fs11` are
//! preserved; a prologue also saves `ra`, which it returns through.

use crate::isa::rv::{RA, Reg, SP};

/// The integer registers an argument travels in, `a0` to `a7`.
pub(in crate::analysis::decompile) const INT_ARGS: u8 = 8;

/// The float registers an argument travels in, `fa0` to `fa7`.
pub(in crate::analysis::decompile) const FLOAT_ARGS: u8 = 8;

/// The number of `a0`, the first argument register, in either bank.
pub(in crate::analysis::decompile) const FIRST_ARG: u8 = 10;

/// Tells whether a register is one the convention preserves: `s0` to
/// `s11` and `fs0` to `fs11` (`x8`, `x9`, `x18` to `x27` and their float
/// namesakes).
///
/// # Arguments
///
/// * `n` - The register's number.
fn preserved(n: u8) -> bool {
    matches!(n, 8 | 9 | 18..=27)
}

/// Tells whether a function must give `r` back to its caller as it found
/// it: a preserved register, the stack pointer, or `ra`, which a
/// prologue saves to return through.
///
/// # Arguments
///
/// * `r` - The register.
pub(in crate::analysis::decompile) fn callee_saved(r: Reg) -> bool {
    match r {
        Reg::X(n) => preserved(n) || r == RA || r == SP,
        Reg::F(n) => preserved(n),
    }
}

/// Tells whether a store of `bits` of `r` is a whole save of a register
/// the function preserves ([`callee_saved`]).
///
/// # Arguments
///
/// * `r` - The register stored.
/// * `bits` - The store's width.
/// * `word` - The integer register's width in bytes, 4 or 8; a float
///   register is saved as a double.
pub(in crate::analysis::decompile) fn saved(r: Reg, bits: u8, word: i64) -> bool {
    let whole = match r {
        Reg::X(_) => word.saturating_mul(8),
        Reg::F(_) => 64,
    };
    i64::from(bits) == whole && callee_saved(r)
}

/// Returns the registers a call leaves holding nothing the caller set:
/// `ra`, `t0` to `t6`, `a0` to `a7`, `ft0` to `ft11` and `fa0` to `fa7`.
pub(in crate::analysis::decompile) fn clobbered() -> impl Iterator<Item = Reg> {
    (1u8..32)
        .filter(|&n| n != 2 && n != 3 && n != 4 && !preserved(n))
        .map(Reg::X)
        .chain((0u8..32).filter(|&n| !preserved(n)).map(Reg::F))
}
