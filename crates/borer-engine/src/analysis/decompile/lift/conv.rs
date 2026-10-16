//! Calling conventions: argument registers, stack cleanup and the canonical
//! register a lane belongs to.

use super::*;

/// Calling-convention facts the lifter needs.
///
/// Two conventions are told apart by value, never by the address of the
/// constant one came from: a `const` has no address of its own, and each
/// use may promote it to a different one.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Conv {
    /// Argument registers in order.
    pub args: &'static [Register],
    /// Registers carrying a floating-point argument: in the same slot as
    /// [`Conv::args`] on Microsoft x64, where the second argument travels
    /// in `rdx` or `xmm1` and never both, or as a sequence of their own on
    /// System V, where the first floating argument takes `xmm0` however
    /// many integer arguments came before it ([`Conv::float_seq`]).
    pub float_args: &'static [Register],
    /// Whether the convention counts its floating arguments as a sequence
    /// of their own (System V) instead of by their position among all the
    /// arguments (Microsoft x64): a call decodes which register a position
    /// holds from its float mask alone ([`Conv::arg_reg`]), so the two
    /// orders never meet.
    pub float_seq: bool,
    /// Registers a call may clobber (caller-saved), vector registers included.
    pub volatile: &'static [Register],
    /// Registers a function must preserve; their prologue saves are not shown.
    pub callee_saved: &'static [Register],
    /// Stack word size in bytes.
    pub word: i64,
    /// Bytes of callee-owned shadow space above the return address.
    pub shadow: i64,
}

/// Microsoft x64: four register arguments, 32 bytes of shadow space.
pub(super) const MS_X64: Conv = Conv {
    args: &[Register::RCX, Register::RDX, Register::R8, Register::R9],
    float_args: &[
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
    ],
    callee_saved: &[
        Register::RBX,
        Register::RBP,
        Register::RDI,
        Register::RSI,
        Register::R12,
        Register::R13,
        Register::R14,
        Register::R15,
        Register::XMM6,
        Register::XMM7,
        Register::XMM8,
        Register::XMM9,
        Register::XMM10,
        Register::XMM11,
        Register::XMM12,
        Register::XMM13,
        Register::XMM14,
        Register::XMM15,
    ],
    volatile: &[
        Register::RAX,
        Register::RCX,
        Register::RDX,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
    ],
    word: 8,
    shadow: 0x20,
    float_seq: false,
};

/// System V x86-64: six register arguments, no shadow space, all xmm volatile.
pub(super) const SYSV_X64: Conv = Conv {
    float_args: &[
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
    ],
    callee_saved: &[
        Register::RBX,
        Register::RBP,
        Register::R12,
        Register::R13,
        Register::R14,
        Register::R15,
    ],
    args: &[
        Register::RDI,
        Register::RSI,
        Register::RDX,
        Register::RCX,
        Register::R8,
        Register::R9,
    ],
    volatile: &[
        Register::RAX,
        Register::RCX,
        Register::RDX,
        Register::RSI,
        Register::RDI,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
        Register::XMM8,
        Register::XMM9,
        Register::XMM10,
        Register::XMM11,
        Register::XMM12,
        Register::XMM13,
        Register::XMM14,
        Register::XMM15,
    ],
    word: 8,
    shadow: 0,
    float_seq: true,
};

/// 32-bit cdecl: every argument on the stack, eax/ecx/edx and the vector
/// registers volatile.
pub(in crate::analysis::decompile) const CDECL_X86: Conv = Conv {
    args: &[],
    float_args: &[],
    callee_saved: &[Register::EBX, Register::EBP, Register::ESI, Register::EDI],
    volatile: &[
        Register::EAX,
        Register::ECX,
        Register::EDX,
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
    ],
    word: 4,
    shadow: 0,
    float_seq: false,
};

/// 32-bit thiscall: `this` in ecx, the rest on the stack.
pub(in crate::analysis::decompile) const THISCALL_X86: Conv = Conv {
    args: &[Register::ECX],
    ..CDECL_X86
};

/// 32-bit fastcall: the first two arguments in ecx and edx, the rest on the stack.
///
/// Also the register set a 32-bit callee is scanned for, whatever its
/// caller's convention: a callee reading `ecx` first takes `this`.
pub(in crate::analysis::decompile) const FASTCALL_X86: Conv = Conv {
    args: &[Register::ECX, Register::EDX],
    ..CDECL_X86
};

/// Go's register ABI on amd64 (`ABIInternal`, Go 1.17 on).
///
/// Nine integer argument registers and fifteen floating ones, each counted
/// on its own, no shadow space, and every register the callee's to clobber
/// but the frame pointer, `r14` (the goroutine) and `r15`.
///
/// SPEC: Go's src/cmd/compile/abi-internal.md, amd64 architecture.
pub(in crate::analysis::decompile) const GO_X64: Conv = Conv {
    args: &[
        Register::RAX,
        Register::RBX,
        Register::RCX,
        Register::RDI,
        Register::RSI,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
    ],
    float_args: &[
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
        Register::XMM8,
        Register::XMM9,
        Register::XMM10,
        Register::XMM11,
        Register::XMM12,
        Register::XMM13,
        Register::XMM14,
    ],
    callee_saved: &[Register::RBP, Register::R14, Register::R15],
    volatile: &[
        Register::RAX,
        Register::RBX,
        Register::RCX,
        Register::RDX,
        Register::RSI,
        Register::RDI,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::R12,
        Register::R13,
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
        Register::XMM6,
        Register::XMM7,
        Register::XMM8,
        Register::XMM9,
        Register::XMM10,
        Register::XMM11,
        Register::XMM12,
        Register::XMM13,
        Register::XMM14,
    ],
    word: 8,
    shadow: 0,
    float_seq: true,
};

/// The arm64 procedure call standard (AAPCS64), as far as the shared
/// executor reads a convention.
///
/// That is an eight-byte word and no shadow space. Its registers are arm64
/// ones, which the arm64 lifter names
/// ([`crate::analysis::decompile::lift_a64`]), so the x86 register lists
/// are empty.
pub(crate) const AAPCS64: Conv = Conv {
    args: &[],
    float_args: &[],
    float_seq: true,
    volatile: &[],
    callee_saved: &[],
    word: 8,
    shadow: 0,
};

impl Conv {
    /// The argument slot a register carries, if it carries one.
    ///
    /// # Arguments
    ///
    /// * `r` - A canonical register.
    ///
    /// # Returns
    ///
    /// Its rank among the argument registers: the position among the
    /// integer ones or, on Microsoft x64, among the floating ones either
    /// way, and past all the integer slots on System V, whose floating
    /// arguments a signature places by [`Conv::param_pos`] instead.
    pub(crate) fn slot(&self, r: Register) -> Option<usize> {
        self.args.iter().position(|a| *a == r).or_else(|| {
            self.float_args.iter().position(|a| *a == r).map(|j| {
                if self.float_seq {
                    self.args.len() + j
                } else {
                    j
                }
            })
        })
    }

    /// The register carrying argument position `i`, as a float mask spells
    /// the signature.
    ///
    /// On Microsoft x64 the register follows the position outright. On
    /// System V the two banks count their own arguments: a floating
    /// position holds the next floating register in order and an integer
    /// one the next integer register, however the two sequences
    /// interleave.
    ///
    /// # Arguments
    ///
    /// * `i` - The argument position, as the signature lists it.
    /// * `floats` - A bit per argument position that is floating point.
    ///
    /// # Returns
    ///
    /// The register, or `None` when the convention has no such slot.
    pub(crate) fn arg_reg(&self, i: usize, floats: u8) -> Option<Register> {
        let bit = (floats >> i.min(7)) & 1 != 0;
        if !self.float_seq {
            return if bit {
                self.float_args.get(i).copied()
            } else {
                self.args.get(i).copied()
            };
        }
        let below = u8::try_from((1u16 << i.min(8)) - 1).unwrap_or(u8::MAX);
        let prior_floats = (floats & below).count_ones() as usize;
        if bit {
            self.float_args.get(prior_floats).copied()
        } else {
            self.args.get(i - prior_floats).copied()
        }
    }

    /// The signature position a parameter register holds among the
    /// parameters a body reads.
    ///
    /// On Microsoft x64 that is its slot. System V counts its integer and
    /// floating arguments separately, and a register alone cannot say where
    /// among the integers a compiler placed a float, so the signature lists
    /// the integer parameters the body reads in their register order and
    /// the floating ones after them.
    ///
    /// # Arguments
    ///
    /// * `r` - A parameter register.
    /// * `params` - The registers the body reads as parameters.
    ///
    /// # Returns
    ///
    /// Its position, or `None` when the register carries no argument.
    pub(crate) fn param_pos(&self, r: Register, params: &[Register]) -> Option<usize> {
        let s = self.slot(r)?;
        if self.float_seq && s >= self.args.len() {
            return Some(self.float_base(params) + s - self.args.len());
        }
        Some(s)
    }

    /// One past the last integer position a body's parameters list: where
    /// the floating parameters' positions start on a convention that counts
    /// its two sequences separately.
    ///
    /// # Arguments
    ///
    /// * `params` - The registers the body reads as parameters.
    pub(crate) fn float_base(&self, params: &[Register]) -> usize {
        params
            .iter()
            .filter(|r| self.args.contains(r))
            .filter_map(|r| self.slot(*r))
            .max()
            .map_or(0, |p| p + 1)
    }

    /// The argument positions a call's registers can reach: the integer
    /// slots, and past them the floating ones on a convention that counts
    /// its two sequences separately.
    pub(crate) fn reg_args(&self) -> usize {
        self.args.len()
            + if self.float_seq {
                self.float_args.len()
            } else {
                0
            }
    }
}

/// Picks the calling convention for a program.
///
/// Raw images default to the Microsoft x64 convention (borer is PE-first);
/// arm64 code follows [`AAPCS64`] in every format.
///
/// # Arguments
///
/// * `program` - The loaded image; its format selects the convention.
/// * `bitness` - `32` selects cdecl regardless of format.
pub(crate) fn conv(program: &Program, bitness: u32) -> &'static Conv {
    if program.arch.isa() == Some(crate::isa::Isa::A64) {
        return &AAPCS64;
    }
    if bitness == 32 {
        return &CDECL_X86;
    }
    match program.format {
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => &MS_X64,
        BinaryFormat::Elf | BinaryFormat::MachO => &SYSV_X64,
    }
}

/// Picks the calling convention of one function.
///
/// A function the Go function table lists takes Go's register ABI
/// ([`GO_X64`]) on x86-64, when the table's layout says the releases that
/// wrote it pass arguments in registers; every other function takes the
/// program's ([`conv()`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `bitness` - `32` or `64`.
pub(crate) fn conv_at(program: &Program, entry: u64, bitness: u32) -> &'static Conv {
    if takes_go_registers(program, entry) {
        &GO_X64
    } else {
        conv(program, bitness)
    }
}

/// Whether a function takes Go's register ABI: x86-64 code the Go function
/// table lists, written by releases that pass arguments in registers.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
pub(crate) fn takes_go_registers(program: &Program, entry: u64) -> bool {
    program.arch == crate::program::Arch::X86_64
        && program
            .go
            .as_ref()
            .is_some_and(|g| g.version.register_abi() && g.lists(entry))
}

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

#[cfg(test)]
mod tests {
    use super::{CDECL_X86, FASTCALL_X86, MS_X64, SYSV_X64, THISCALL_X86, conv};
    use crate::program::{Arch, BinaryFormat, Program};

    /// Conventions compare by value: the one a program picks equals the
    /// constant it came from wherever that constant was promoted, and two
    /// conventions that pass arguments differently never compare equal.
    ///
    /// The thiscall promotion compared the addresses of `CDECL_X86` and
    /// `THISCALL_X86`, which a `const` does not guarantee to keep.
    ///
    /// # Panics
    ///
    /// When a convention differs from itself or equals another.
    #[test]
    fn conventions_compare_by_value() {
        let mut p = Program::raw(vec![0xc3], Arch::X86, 0, None, Vec::new());
        assert_eq!(conv(&p, 32), &CDECL_X86);
        p.format = BinaryFormat::Elf;
        assert_eq!(conv(&p, 64), &SYSV_X64);
        let all = [&MS_X64, &SYSV_X64, &CDECL_X86, &THISCALL_X86, &FASTCALL_X86];
        for (i, a) in all.iter().enumerate() {
            for (j, b) in all.iter().enumerate() {
                assert_eq!(i == j, a == b, "{i} against {j}");
            }
        }
    }
}
