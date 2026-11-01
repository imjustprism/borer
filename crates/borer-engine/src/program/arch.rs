//! The instruction-set architectures a program is written for, and what
//! the engine does with each one's code.

use crate::isa::Isa;

/// Instruction-set architectures the engine recognizes.
///
/// What the engine does with each one's code is [`Arch::supports`]; an
/// architecture it does not analyze is still identified from the headers
/// so the summary can say what a file is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arch {
    /// 32-bit x86.
    X86,
    /// 64-bit x86 (AMD64).
    X86_64,
    /// 64-bit ARM (AArch64).
    Arm64,
    /// 32-bit ARM: A32 and T32 (Thumb-2) code, which instruction set at
    /// which address told by [`Program::modes`](super::Program::modes).
    Arm,
    /// 64-bit RISC-V (RV64GC).
    RiscV64,
    /// 32-bit RISC-V (RV32GC).
    RiscV32,
    /// Anything else, or a header the loader could not read.
    Unknown,
}

impl Arch {
    /// Returns the architecture an ELF header's `e_machine` names.
    ///
    /// # Arguments
    ///
    /// * `machine` - `e_machine`.
    /// * `is_64` - Whether the file is `ELFCLASS64`, which tells RV64 from
    ///   RV32.
    pub(crate) fn from_elf(machine: u16, is_64: bool) -> Arch {
        match machine {
            62 => Arch::X86_64,
            3 => Arch::X86,
            183 => Arch::Arm64,
            40 => Arch::Arm,
            243 if is_64 => Arch::RiscV64,
            243 => Arch::RiscV32,
            _ => Arch::Unknown,
        }
    }

    /// Returns the display name used in summaries (`x86`, `x86-64`, `arm64`,
    /// `riscv64`, `unknown`).
    pub fn name(self) -> &'static str {
        match self {
            Arch::X86 => "x86",
            Arch::X86_64 => "x86-64",
            Arch::Arm64 => "arm64",
            Arch::Arm => "arm",
            Arch::RiscV64 => "riscv64",
            Arch::RiscV32 => "riscv32",
            Arch::Unknown => "unknown",
        }
    }

    /// Returns the decoder bitness for architectures the disassembler supports.
    ///
    /// # Returns
    ///
    /// `32` or `64` for x86 variants, `None` for everything else.
    pub fn bitness(self) -> Option<u32> {
        match self {
            Arch::X86 => Some(32),
            Arch::X86_64 => Some(64),
            _ => None,
        }
    }

    /// Returns the instruction set this architecture's code is written in.
    ///
    /// # Returns
    ///
    /// The instruction set, or `None` for [`Arch::Unknown`].
    pub fn isa(self) -> Option<Isa> {
        match self {
            Arch::X86 => Some(Isa::X86 { bits: 32 }),
            Arch::X86_64 => Some(Isa::X86 { bits: 64 }),
            Arch::Arm64 => Some(Isa::A64),
            Arch::Arm => Some(Isa::A32),
            Arch::RiscV64 => Some(Isa::Rv(crate::isa::rv::Xlen::X64)),
            Arch::RiscV32 => Some(Isa::Rv(crate::isa::rv::Xlen::X32)),
            Arch::Unknown => None,
        }
    }

    /// Tells whether the engine does `feature` with this architecture's code.
    ///
    /// The one table of what each instruction set supports: a stage lands
    /// for an instruction set by flipping its arm here, and every gate
    /// ([`Program::refuses`](super::Program::refuses)) follows.
    ///
    /// # Arguments
    ///
    /// * `feature` - What a tool asks of the code.
    pub fn supports(self, feature: Feature) -> bool {
        match self.isa() {
            Some(Isa::X86 { .. }) => true,
            Some(Isa::A64) => match feature {
                Feature::Disasm | Feature::Discover | Feature::Emulate | Feature::Decompile => true,
            },
            Some(Isa::A32) => match feature {
                Feature::Disasm | Feature::Discover | Feature::Decompile => true,
                Feature::Emulate => false,
            },
            Some(Isa::Rv(_)) => match feature {
                Feature::Disasm | Feature::Discover => true,
                Feature::Emulate | Feature::Decompile => false,
            },
            None => false,
        }
    }
}

/// What a code tool asks the engine to do with a program's instructions.
///
/// Support arrives one instruction set and one stage at a time, so a tool
/// names the stage it needs ([`Program::refuses`](super::Program::refuses)) instead of reading
/// support off [`Arch::bitness`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Feature {
    /// Decoding instructions to text: a linear listing at an address.
    Disasm,
    /// Function discovery, and every answer read from the analysis it
    /// builds (functions, references, the call graph).
    Discover,
    /// Running code in the emulator.
    Emulate,
    /// Lifting functions to pseudo-C.
    Decompile,
}
