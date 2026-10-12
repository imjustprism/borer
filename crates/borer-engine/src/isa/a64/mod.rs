//! AArch64 (arm64): engine-owned instruction types over the yaxpeax-arm
//! decoder.
//!
//! [`decode()`] turns one four-byte word into an [`Insn`] whose class,
//! operands, condition and control flow are engine types, and [`text`]
//! renders one as assembly. This module's three files are the only ones
//! that name the decoder crate; everything downstream reads the types
//! below.
//!
//! Every word decodes to something. A word in the SVE or SME encoding
//! space, which the decoder does not model, is an opaque instruction that
//! falls through ([`Op::Sve`], [`Op::Sme`]), so a walk over vector code
//! goes on past it; any other word that does not decode is
//! [`Op::Invalid`], where execution stops. Pointer authentication and
//! branch target identification decode as the instructions they are
//! ([`Op::Pac`], [`Op::Bti`]), and their authenticated branches carry the
//! class of the plain branch (`retaa` is a [`Op::Ret`], `braa` a
//! [`Op::Br`]).

mod decode;
mod fmt;

pub use decode::decode;
pub use fmt::text;

/// Bytes in every A64 instruction; instructions are also aligned to it.
pub const INSN_LEN: usize = 4;

/// A register an operand names: the storage, not the width it is read at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Reg {
    /// General-purpose register `x0`..`x30`, numbered 0 to 30.
    X(u8),
    /// The stack pointer: register 31 where the encoding reads it as `sp`.
    Sp,
    /// The zero register: register 31 where the encoding reads it as
    /// `xzr`/`wzr`; reads zero, and a write to it is discarded.
    Zr,
    /// SIMD and floating-point register `v0`..`v31`, numbered 0 to 31.
    V(u8),
}

/// A condition on the NZCV flags, as `b.cond`, `csel` and `ccmp` name it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cond {
    /// Equal: Z set.
    Eq,
    /// Not equal: Z clear.
    Ne,
    /// Unsigned higher or same (carry set): C set.
    Hs,
    /// Unsigned lower (carry clear): C clear.
    Lo,
    /// Negative: N set.
    Mi,
    /// Positive or zero: N clear.
    Pl,
    /// Overflow: V set.
    Vs,
    /// No overflow: V clear.
    Vc,
    /// Unsigned higher: C set and Z clear.
    Hi,
    /// Unsigned lower or same: C clear or Z set.
    Ls,
    /// Signed greater or equal: N equals V.
    Ge,
    /// Signed less than: N differs from V.
    Lt,
    /// Signed greater than: Z clear and N equals V.
    Gt,
    /// Signed less or equal: Z set or N differs from V.
    Le,
    /// Always.
    Al,
    /// Always, in the encoding `0b1111` the architecture keeps distinct
    /// from [`Cond::Al`] only for disassembly.
    Nv,
}

impl Cond {
    /// Returns the condition a four-bit encoded condition field names.
    ///
    /// # Arguments
    ///
    /// * `code` - The field; only its low four bits are read.
    #[must_use]
    pub fn from_code(code: u8) -> Cond {
        match code & 0xf {
            0x0 => Cond::Eq,
            0x1 => Cond::Ne,
            0x2 => Cond::Hs,
            0x3 => Cond::Lo,
            0x4 => Cond::Mi,
            0x5 => Cond::Pl,
            0x6 => Cond::Vs,
            0x7 => Cond::Vc,
            0x8 => Cond::Hi,
            0x9 => Cond::Ls,
            0xa => Cond::Ge,
            0xb => Cond::Lt,
            0xc => Cond::Gt,
            0xd => Cond::Le,
            0xe => Cond::Al,
            _ => Cond::Nv,
        }
    }
}

/// How a register operand or a memory index is shifted or extended before
/// use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Shift {
    /// Logical shift left.
    Lsl,
    /// Logical shift right.
    Lsr,
    /// Arithmetic shift right.
    Asr,
    /// Rotate right.
    Ror,
    /// Zero-extend the low byte.
    Uxtb,
    /// Zero-extend the low halfword.
    Uxth,
    /// Zero-extend the low word.
    Uxtw,
    /// The whole register, unsigned.
    Uxtx,
    /// Sign-extend the low byte.
    Sxtb,
    /// Sign-extend the low halfword.
    Sxth,
    /// Sign-extend the low word.
    Sxtw,
    /// The whole register, signed.
    Sxtx,
}

/// How a memory operand's address is formed and written back.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    /// `[base, offset]`: the base is left as it is.
    Offset,
    /// `[base, #disp]!`: the access is at base plus `disp`, which is then
    /// written back to the base.
    PreIndex,
    /// `[base], #disp`: the access is at the base, which is then advanced.
    PostIndex,
}

/// A memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Mem {
    /// The base register: `x0`..`x30` or `sp`.
    pub base: Reg,
    /// The index register and the width in bits it is read at, for a
    /// register offset.
    pub index: Option<(Reg, u16)>,
    /// How the index is extended; [`Shift::Lsl`] when there is none.
    pub extend: Shift,
    /// How far the extended index is shifted left, in bits.
    pub shift: u8,
    /// The constant offset, in bytes.
    pub disp: i64,
    /// Offset, pre-indexed or post-indexed.
    pub mode: Mode,
}

/// One operand of an instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Opnd {
    /// No operand in this slot; the slots after it are empty too.
    None,
    /// A register read or written at `bits`: 32 or 64 for a
    /// general-purpose register, 8 to 128 for a `v` register as a scalar.
    Reg {
        /// The register.
        reg: Reg,
        /// The width it is accessed at, in bits.
        bits: u16,
    },
    /// A register shifted or extended before use (`x1, lsl #3`, `w2,
    /// sxtw`).
    Shifted {
        /// The register.
        reg: Reg,
        /// The width it is read at, in bits.
        bits: u16,
        /// The shift or extension.
        shift: Shift,
        /// The shift amount, in bits.
        amount: u8,
    },
    /// An immediate, already extended and shifted as the encoding states
    /// (`#0x10, lsl #12` is `0x10000`).
    Imm(u64),
    /// The absolute address a PC-relative operand resolves to: a branch
    /// target, an `adr` address, an `adrp` page, a literal-load address.
    PcRel(u64),
    /// A memory operand.
    Mem(Mem),
    /// A condition (`csel`, `ccmp`).
    Cond(Cond),
    /// An operand the engine does not model yet: a vector arrangement or
    /// lane, a register list or pair, a system register, a prefetch
    /// operation, a float immediate.
    Other,
}

/// What an instruction does, in the classes the engine reads; every
/// instruction outside them is [`Op::Other`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    /// `b`: a direct jump.
    B,
    /// `b.cond` and `bc.cond`: a direct jump taken when the condition
    /// holds.
    BCond(Cond),
    /// `cbz`: a direct jump taken when the register is zero.
    Cbz,
    /// `cbnz`: a direct jump taken when the register is not zero.
    Cbnz,
    /// `tbz`: a direct jump taken when the tested bit is clear.
    Tbz,
    /// `tbnz`: a direct jump taken when the tested bit is set.
    Tbnz,
    /// `bl`: a direct call.
    Bl,
    /// `br` and its authenticated forms (`braa`, `braaz`, `brab`,
    /// `brabz`): an indirect jump.
    Br,
    /// `blr` and its authenticated forms: an indirect call.
    Blr,
    /// `ret` and its authenticated forms (`retaa`, `retab`, the
    /// `reta*sppc` family): a return.
    Ret,
    /// `eret`, `eretaa`, `eretab` and `drps`: an exception return.
    Eret,
    /// `brk`, `hlt`, `udf` and `dcps1`..`dcps3`: a trap; execution does not
    /// go on to the next instruction.
    Trap,
    /// `svc`, `hvc` and `smc`: a call into a higher exception level that
    /// comes back to the next instruction.
    Syscall,
    /// `adr`: a PC-relative address into a register.
    Adr,
    /// `adrp`: a PC-relative 4 KiB page address into a register.
    Adrp,
    /// `nop` and the hints that change no register (`yield`, `wfe`, `wfi`,
    /// `sev`, `sevl`, `esb`, `csdb`, ...).
    Nop,
    /// `bti`: a branch target landing pad; no effect on data.
    Bti,
    /// A pointer-authentication instruction (`paciasp`, `autia`, `xpaci`,
    /// `pacia1716`, ...): signs, authenticates or strips a pointer in place,
    /// which the engine treats as leaving the value as it is.
    Pac,
    /// A word in the SVE encoding space, which the decoder does not model:
    /// falls through.
    Sve,
    /// A word in the SME encoding space, likewise.
    Sme,
    /// A word that decodes to no instruction; execution does not go on.
    Invalid,
    /// Every other instruction; falls through.
    Other,
}

impl Op {
    /// Returns how this class of instruction moves control.
    #[must_use]
    pub fn flow(self) -> Flow {
        match self {
            Op::B | Op::Br | Op::BCond(Cond::Al | Cond::Nv) => Flow::Jump,
            Op::BCond(_) | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz => Flow::CondJump,
            Op::Bl | Op::Blr => Flow::Call,
            Op::Ret | Op::Eret => Flow::Return,
            Op::Trap | Op::Invalid => Flow::Invalid,
            Op::Syscall
            | Op::Adr
            | Op::Adrp
            | Op::Nop
            | Op::Bti
            | Op::Pac
            | Op::Sve
            | Op::Sme
            | Op::Other => Flow::Next,
        }
    }
}

/// How an instruction moves control.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Flow {
    /// Goes on to the next instruction.
    Next,
    /// Always jumps: to [`Insn::target`] when it is direct, through a
    /// register when it is not.
    Jump,
    /// Jumps to [`Insn::target`] or goes on to the next instruction.
    CondJump,
    /// Calls, then comes back to the next instruction.
    Call,
    /// Returns to the caller.
    Return,
    /// Does not go on: a trap, or a word that does not decode.
    Invalid,
}

/// One decoded instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Insn {
    /// Address of the instruction.
    pub va: u64,
    /// The encoded word, little-endian in the image.
    pub word: u32,
    /// What it does.
    pub op: Op,
    /// Its operands in assembly order, [`Opnd::None`] past the last.
    pub operands: [Opnd; 4],
    /// How it moves control; [`Op::flow`] of `op`.
    pub flow: Flow,
}

impl Insn {
    /// Returns where a direct branch or call goes.
    ///
    /// # Returns
    ///
    /// The absolute target of `b`, `b.cond`, `cbz`, `cbnz`, `tbz`, `tbnz`
    /// and `bl`; `None` for every other instruction, an indirect branch
    /// among them.
    #[must_use]
    pub fn target(&self) -> Option<u64> {
        match self.op {
            Op::B | Op::BCond(_) | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz | Op::Bl => {
                self.operands.iter().find_map(|o| match o {
                    Opnd::PcRel(at) => Some(*at),
                    Opnd::None
                    | Opnd::Reg { .. }
                    | Opnd::Shifted { .. }
                    | Opnd::Imm(_)
                    | Opnd::Mem(_)
                    | Opnd::Cond(_)
                    | Opnd::Other => None,
                })
            }
            Op::Br
            | Op::Blr
            | Op::Ret
            | Op::Eret
            | Op::Trap
            | Op::Syscall
            | Op::Adr
            | Op::Adrp
            | Op::Nop
            | Op::Bti
            | Op::Pac
            | Op::Sve
            | Op::Sme
            | Op::Invalid
            | Op::Other => None,
        }
    }
}
