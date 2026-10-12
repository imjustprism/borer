//! The register-bank seam: engine-owned indexing between a decoded register
//! and a bank slot or a width view.
//!
//! iced numbers each register within its width family, and the offsets
//! between families (`st1` one past `st0`, `xmm0` where the vector slots
//! start) are x86 facts. Consumers below `isa` never do that arithmetic
//! themselves: they call this family, so the one x86 mapping lives here and
//! a second architecture replaces this module instead of
//! re-implementing the arithmetic at each consumer.

use super::Register;

/// Returns the slot a general-purpose register occupies in the bank of
/// sixteen, `rax` first.
///
/// The slot is the register's index within its width family, the identity
/// that numbers `ecx` one past `eax` as it numbers `rcx` one past `rax`, so
/// every width of a register names one slot and a bank holds one full value
/// per register. Callers bank canonical full registers; the high bytes
/// (`ah`..`bh`) number inside the byte family's own interleave and do not
/// name their register's slot.
///
/// # Arguments
///
/// * `r` - Any register.
///
/// # Returns
///
/// The bank slot, or `None` when `r` is not a general-purpose register, the
/// answer the emulator turns into its zero read and ignored write.
pub(crate) fn gpr_bank_index(r: Register) -> Option<usize> {
    r.is_gpr().then(|| r.number() - Register::RAX.number())
}

/// Returns the depth any register would have in the x87 bank of eight, its
/// family number taken modulo eight.
///
/// The emulator banks the x87 stack as a ring its `top` indexes into, so an
/// operand register that is not an `st` one still needs a ring slot and its
/// number cycles. Every x87 operand the decoder reports is `st0`..`st7`,
/// where the cycle is the identity.
///
/// # Arguments
///
/// * `r` - Any register.
pub(crate) fn st_depth_mod8(r: Register) -> usize {
    r.number().saturating_sub(Register::ST0.number()) % 8
}

/// Returns the depth of an x87 stack register below `st0`.
///
/// # Arguments
///
/// * `r` - Any register.
///
/// # Returns
///
/// `0` for `st0` through `7` for `st7`, or `None` for any other register.
pub(crate) fn st_depth(r: Register) -> Option<usize> {
    (r >= Register::ST0 && r <= Register::ST7).then(|| r.number() - Register::ST0.number())
}

/// Returns the x87 register `depth` below the stack's top.
///
/// # Arguments
///
/// * `depth` - The depth; one past `7` clamps to `st7`, the deepest
///   register, so a depth the code could not bound still names one.
///
/// # Returns
///
/// `st0` for zero through `st7`.
pub(crate) fn st_register(depth: usize) -> Register {
    Register::try_from(Register::ST0 as usize + depth.min(7)).unwrap_or(Register::ST7)
}

/// Returns the `xmm` register a vector register's index names.
///
/// The vector widths number their slots together: `ymm5` and `zmm5` carry
/// `xmm5`'s index, so the lifter unifies every width of one slot on its
/// `xmm` name.
///
/// # Arguments
///
/// * `r` - A vector register.
///
/// # Returns
///
/// `xmm0`..`xmm31`, or `r` itself when its index names no register.
pub(crate) fn as_xmm(r: Register) -> Register {
    Register::try_from(Register::XMM0 as usize + r.number()).unwrap_or(r)
}

/// Returns the `bits`-wide view of a canonical general register.
///
/// The view is the register of that width at the same bank slot: the base
/// of the `bits` family offset by `full`'s slot, the arithmetic that makes
/// `sized_register(rax, 32)` `eax`. The byte family interleaves the high
/// bytes (`ah`..`bh`) where the stack and base pointers' low bytes sit, so
/// an eight-bit view is the low-register identity alone; the multiply and
/// divide sites that ask hold `rax` and `rdx`.
///
/// # Arguments
///
/// * `full` - A canonical 64-bit general register.
/// * `bits` - 8, 16, 32 or 64; anything else reads 64.
///
/// # Returns
///
/// The view, or `full` when the slot names no register of that width.
pub(crate) fn sized_register(full: Register, bits: u8) -> Register {
    let base = match bits {
        8 => Register::AL,
        16 => Register::AX,
        32 => Register::EAX,
        _ => Register::RAX,
    };
    Register::try_from(base as usize + full.number()).unwrap_or(full)
}

/// Returns the slot of one of the first sixteen vector registers, `xmm0`
/// first.
///
/// # Arguments
///
/// * `r` - Any register.
///
/// # Returns
///
/// `0` for `xmm0` through `15` for `xmm15`, or `None` for any other
/// register: the emulator's vector bank holds the sixteen low slots, the
/// ones x86 code names without an `evex` prefix.
pub(crate) fn xmm_slot(r: Register) -> Option<usize> {
    (r >= Register::XMM0 && r <= Register::XMM15).then(|| r as usize - Register::XMM0 as usize)
}
