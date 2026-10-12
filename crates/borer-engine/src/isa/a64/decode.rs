//! Decoding one A64 word with yaxpeax-arm into the engine's [`Insn`].

use yaxpeax_arch::{Decoder as _, U8Reader};
use yaxpeax_arm::armv8::a64::{
    InstDecoder, Instruction, Opcode, Operand, SIMDSizeCode, ShiftStyle, SizeCode,
};

use super::{Cond, Insn, Mem, Mode, Op, Opnd, Reg, Shift};
use crate::num::lo8;

/// The top-level encoding group (`op1`, bits 25 to 28) of the SVE space.
const GROUP_SVE: u32 = 0b0010;
/// The top-level encoding group of the SME space (with bit 31 set) and of
/// the reserved space (with it clear).
const GROUP_SME: u32 = 0b0000;
/// The register number that names `sp` or `zr`, by context.
const REG_31: u16 = 31;
/// The offset bits of the 4 KiB page an `adrp` addresses.
const PAGE_OFFSET: u64 = 0xfff;
/// The hint numbers of `bti`, `bti c`, `bti j` and `bti jc`.
const BTI_HINTS: [u16; 4] = [0x20, 0x22, 0x24, 0x26];

/// Decodes one instruction.
///
/// # Arguments
///
/// * `word` - The encoded word: the image's four bytes, read little-endian.
/// * `va` - The instruction's address, which PC-relative operands resolve
///   against.
///
/// # Returns
///
/// The instruction. A word the decoder rejects is [`Op::Sve`] or
/// [`Op::Sme`] in those encoding spaces and [`Op::Invalid`] anywhere else,
/// the branch group included, with no operands.
#[must_use]
pub fn decode(word: u32, va: u64) -> Insn {
    let bytes = word.to_le_bytes();
    let inst = match InstDecoder::default().decode(&mut U8Reader::new(&bytes)) {
        Ok(inst) if inst.opcode != Opcode::Invalid => inst,
        Ok(_) | Err(_) => return undecoded(word, va),
    };
    let op = class(&inst);
    Insn {
        va,
        word,
        op,
        operands: inst.operands.map(|o| operand(o, inst.opcode, va)),
        flow: op.flow(),
    }
}

/// Classifies a word the decoder rejected by its encoding group.
///
/// # Arguments
///
/// * `word` - The encoded word.
/// * `va` - Its address.
fn undecoded(word: u32, va: u64) -> Insn {
    let op = match (word >> 25) & 0xf {
        GROUP_SVE => Op::Sve,
        GROUP_SME if word >> 31 == 1 => Op::Sme,
        _ => Op::Invalid,
    };
    Insn {
        va,
        word,
        op,
        operands: [Opnd::None; 4],
        flow: op.flow(),
    }
}

/// Returns the class of a decoded instruction.
///
/// Every opcode not named here is [`Op::Other`]: the decoder has some six
/// hundred, and a class is added by naming its opcodes in this match.
///
/// # Arguments
///
/// * `inst` - The decoded instruction.
fn class(inst: &Instruction) -> Op {
    match inst.opcode {
        Opcode::B => Op::B,
        Opcode::Bcc(c) | Opcode::BCcc(c) => Op::BCond(Cond::from_code(c)),
        Opcode::CBZ => Op::Cbz,
        Opcode::CBNZ => Op::Cbnz,
        Opcode::TBZ => Op::Tbz,
        Opcode::TBNZ => Op::Tbnz,
        Opcode::BL => Op::Bl,
        Opcode::BR | Opcode::BRAA | Opcode::BRAAZ | Opcode::BRAB | Opcode::BRABZ => Op::Br,
        Opcode::BLR | Opcode::BLRAA | Opcode::BLRAAZ | Opcode::BLRAB | Opcode::BLRABZ => Op::Blr,
        Opcode::RET
        | Opcode::RETAA
        | Opcode::RETAB
        | Opcode::RETAASPPC
        | Opcode::RETABSPPC
        | Opcode::RETAASPPCR
        | Opcode::RETABSPPCR => Op::Ret,
        Opcode::ERET | Opcode::ERETAA | Opcode::ERETAB | Opcode::DRPS => Op::Eret,
        Opcode::BRK | Opcode::HLT | Opcode::UDF | Opcode::DCPS1 | Opcode::DCPS2 | Opcode::DCPS3 => {
            Op::Trap
        }
        Opcode::SVC | Opcode::HVC | Opcode::SMC => Op::Syscall,
        Opcode::ADR => Op::Adr,
        Opcode::ADRP => Op::Adrp,
        Opcode::HINT => match inst.operands {
            [Operand::ControlReg(crm), Operand::Immediate(op2), ..]
                if u16::try_from(op2).is_ok_and(|op2| BTI_HINTS.contains(&((crm << 3) | op2))) =>
            {
                Op::Bti
            }
            _ => Op::Nop,
        },
        Opcode::PACIA
        | Opcode::PACIB
        | Opcode::PACDA
        | Opcode::PACDB
        | Opcode::AUTIA
        | Opcode::AUTIB
        | Opcode::AUTDA
        | Opcode::AUTDB
        | Opcode::PACIZA
        | Opcode::PACIZB
        | Opcode::PACDZA
        | Opcode::PACDZB
        | Opcode::AUTIZA
        | Opcode::AUTIZB
        | Opcode::AUTDZA
        | Opcode::AUTDZB
        | Opcode::XPACI
        | Opcode::XPACD
        | Opcode::PACIASP
        | Opcode::PACIAZ
        | Opcode::PACIA1716
        | Opcode::PACIA171615
        | Opcode::PACIASPPC
        | Opcode::PACNBIASPPC
        | Opcode::PACIBSP
        | Opcode::PACIBZ
        | Opcode::PACIB1716
        | Opcode::PACIB171615
        | Opcode::PACIBSPPC
        | Opcode::PACNBIBSPPC
        | Opcode::AUTIASP
        | Opcode::AUTIAZ
        | Opcode::AUTIA1716
        | Opcode::AUTIA171615
        | Opcode::AUTIASPPC
        | Opcode::AUTIASPPCR
        | Opcode::AUTIBSP
        | Opcode::AUTIBZ
        | Opcode::AUTIB1716
        | Opcode::AUTIB171615
        | Opcode::AUTIBSPPC
        | Opcode::AUTIBSPPCR
        | Opcode::XPACLRI
        | Opcode::PACM => Op::Pac,
        Opcode::Invalid => Op::Invalid,
        _ => Op::Other,
    }
}

/// Converts one decoded operand.
///
/// # Arguments
///
/// * `o` - The decoder's operand.
/// * `opcode` - The instruction's opcode: an `adrp` offset counts from the
///   instruction's page, every other PC-relative offset from the
///   instruction.
/// * `va` - The instruction's address.
fn operand(o: Operand, opcode: Opcode, va: u64) -> Opnd {
    match o {
        Operand::Nothing => Opnd::None,
        Operand::Register(size, n) => Opnd::Reg {
            reg: gpr(n, Reg::Zr),
            bits: gpr_bits(size),
        },
        Operand::RegisterOrSP(size, n) => Opnd::Reg {
            reg: gpr(n, Reg::Sp),
            bits: gpr_bits(size),
        },
        Operand::SIMDRegister(size, n) => Opnd::Reg {
            reg: Reg::V(lo8(u64::from(n))),
            bits: simd_bits(size),
        },
        Operand::RegShift(style, amount, size, n) => Opnd::Shifted {
            reg: gpr(n, Reg::Zr),
            bits: gpr_bits(size),
            shift: shift(style),
            amount,
        },
        Operand::ConditionCode(c) => Opnd::Cond(Cond::from_code(c)),
        Operand::PCOffset(off) => Opnd::PcRel(match opcode {
            Opcode::ADRP => (va & !PAGE_OFFSET).wrapping_add_signed(off),
            _ => va.wrapping_add_signed(off),
        }),
        Operand::Immediate(v) => Opnd::Imm(u64::from(v)),
        Operand::Imm64(v) => Opnd::Imm(v),
        Operand::Imm16(v) => Opnd::Imm(u64::from(v)),
        Operand::ImmShift(v, by) => Opnd::Imm(u64::from(v).checked_shl(u32::from(by)).unwrap_or(0)),
        Operand::RegRegOffset(base, index, size, extend, amount) => Opnd::Mem(Mem {
            base: gpr(base, Reg::Sp),
            index: Some((gpr(index, Reg::Zr), gpr_bits(size))),
            extend: shift(extend),
            shift: amount,
            disp: 0,
            mode: Mode::Offset,
        }),
        Operand::RegPreIndex(base, disp, writeback) => Opnd::Mem(Mem {
            base: gpr(base, Reg::Sp),
            index: None,
            extend: Shift::Lsl,
            shift: 0,
            disp: i64::from(disp),
            mode: if writeback {
                Mode::PreIndex
            } else {
                Mode::Offset
            },
        }),
        Operand::RegPostIndex(base, disp) => Opnd::Mem(Mem {
            base: gpr(base, Reg::Sp),
            index: None,
            extend: Shift::Lsl,
            shift: 0,
            disp: i64::from(disp),
            mode: Mode::PostIndex,
        }),
        Operand::RegPostIndexReg(base, index) => Opnd::Mem(Mem {
            base: gpr(base, Reg::Sp),
            index: Some((gpr(index, Reg::Zr), 64)),
            extend: Shift::Lsl,
            shift: 0,
            disp: 0,
            mode: Mode::PostIndex,
        }),
        Operand::RegisterPair(..)
        | Operand::SIMDRegisterElements(..)
        | Operand::SIMDRegisterElementsLane(..)
        | Operand::SIMDRegisterElementsMultipleLane(..)
        | Operand::SIMDRegisterGroup(..)
        | Operand::SIMDRegisterGroupLane(..)
        | Operand::ImmediateDouble(_)
        | Operand::ImmShiftMSL(..)
        | Operand::PrefetchOp(_)
        | Operand::SystemReg(_)
        | Operand::ControlReg(_)
        | Operand::PstateField(_) => Opnd::Other,
    }
}

/// Names a general-purpose register by number.
///
/// # Arguments
///
/// * `n` - The register number, 0 to 31.
/// * `r31` - What number 31 means here: [`Reg::Sp`] or [`Reg::Zr`].
fn gpr(n: u16, r31: Reg) -> Reg {
    if n == REG_31 {
        r31
    } else {
        Reg::X(lo8(u64::from(n)))
    }
}

/// Returns the width in bits a general-purpose register is accessed at.
///
/// # Arguments
///
/// * `size` - `x` (64) or `w` (32).
fn gpr_bits(size: SizeCode) -> u16 {
    match size {
        SizeCode::X => 64,
        SizeCode::W => 32,
    }
}

/// Returns the width in bits a `v` register is accessed at as a scalar.
///
/// # Arguments
///
/// * `size` - `b`, `h`, `s`, `d` or `q`.
fn simd_bits(size: SIMDSizeCode) -> u16 {
    match size {
        SIMDSizeCode::B => 8,
        SIMDSizeCode::H => 16,
        SIMDSizeCode::S => 32,
        SIMDSizeCode::D => 64,
        SIMDSizeCode::Q => 128,
    }
}

/// Converts the decoder's shift or extension.
///
/// # Arguments
///
/// * `style` - The decoder's shift style.
fn shift(style: ShiftStyle) -> Shift {
    match style {
        ShiftStyle::LSL => Shift::Lsl,
        ShiftStyle::LSR => Shift::Lsr,
        ShiftStyle::ASR => Shift::Asr,
        ShiftStyle::ROR => Shift::Ror,
        ShiftStyle::UXTB => Shift::Uxtb,
        ShiftStyle::UXTH => Shift::Uxth,
        ShiftStyle::UXTW => Shift::Uxtw,
        ShiftStyle::UXTX => Shift::Uxtx,
        ShiftStyle::SXTB => Shift::Sxtb,
        ShiftStyle::SXTH => Shift::Sxth,
        ShiftStyle::SXTW => Shift::Sxtw,
        ShiftStyle::SXTX => Shift::Sxtx,
    }
}
