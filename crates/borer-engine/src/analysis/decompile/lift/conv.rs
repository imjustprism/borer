//! Register facts the x86 lifter reads: the canonical register a lane
//! belongs to, high-byte registers, float operand sizes and stack cleanup.

use super::*;

/// Returns the canonical register a text variable is named after.
///
/// General-purpose registers unify with their full-width parent (`eax` to
/// `rax`, or to `eax` in 32-bit code); vector registers unify on `xmm`.
///
/// # Arguments
///
/// * `r` - Any register.
/// * `bitness` - `32` or `64`.
pub(in crate::analysis::decompile) fn canon(r: Register, bitness: u32) -> Register {
    if r.is_vector_register() {
        as_xmm(r)
    } else if r.is_gpr() {
        if bitness == 32 {
            r.full_register32()
        } else {
            r.full_register()
        }
    } else {
        r
    }
}

/// Tells whether `r` is one of the legacy high-byte registers (`ah`..`dh`).
///
/// # Arguments
///
/// * `r` - Any register.
pub(super) fn is_high_byte(r: Register) -> bool {
    matches!(r, Register::AH | Register::BH | Register::CH | Register::DH)
}

/// Tells whether a memory operand size is a floating-point format.
///
/// # Arguments
///
/// * `ms` - The operand's memory size from iced.
pub(super) fn is_float(ms: MemorySize) -> bool {
    matches!(
        ms,
        MemorySize::Float16 | MemorySize::Float32 | MemorySize::Float64 | MemorySize::Float80
    )
}

/// Tells whether the instruction after a call is the caller's own stack
/// cleanup, `add esp, N` or a `pop` into a scratch register: the callee
/// popped nothing, which is what `__cdecl` means.
///
/// # Arguments
///
/// * `next` - The instruction that runs after the call, when known.
pub(super) fn cleans_stack(next: Option<&Instruction>) -> bool {
    next.is_some_and(|n| match n.mnemonic() {
        Mnemonic::Add => {
            n.op0_kind() == OpKind::Register
                && n.op0_register() == Register::ESP
                && matches!(n.op1_kind(), OpKind::Immediate8to32 | OpKind::Immediate32)
        }
        Mnemonic::Pop => {
            n.op0_kind() == OpKind::Register
                && matches!(n.op0_register(), Register::ECX | Register::EDX)
        }
        _ => false,
    })
}

/// Tells whether an instruction stores to `fs:[0]`, the head of the
/// structured exception handler chain: the registration in a prologue,
/// the unlink before a return.
///
/// # Arguments
///
/// * `instr` - The instruction.
pub(in crate::analysis::decompile) fn is_seh_link(instr: &Instruction) -> bool {
    instr.mnemonic() == Mnemonic::Mov
        && instr.op0_kind() == OpKind::Memory
        && instr.segment_prefix() == Register::FS
        && instr.memory_base() == Register::None
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
}
