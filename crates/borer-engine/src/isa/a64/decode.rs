//! Decoding one A64 word with yaxpeax-arm into the engine's [`Insn`].

use yaxpeax_arch::{Decoder as _, U8Reader};
use yaxpeax_arm::armv8::a64::{
    InstDecoder, Instruction, Opcode, Operand, SIMDSizeCode, ShiftStyle, SizeCode,
};

use super::{Cond, Insn, Mem, Mnemonic, Mode, Op, Opnd, Reg, Rmw, Shift, Simd, Width};
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
        mnemonic: mnemonic(inst.opcode),
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
        mnemonic: Mnemonic::Other,
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

/// Returns the base instruction of a decoded opcode.
///
/// Every opcode not named here is [`Mnemonic::Other`], as in [`class`].
///
/// # Arguments
///
/// * `opcode` - The decoder's opcode.
fn mnemonic(opcode: Opcode) -> Mnemonic {
    use Width::{Byte, Half, Reg, SByte, SHalf, SWord};
    match opcode {
        Opcode::MOVZ => Mnemonic::Movz,
        Opcode::MOVN => Mnemonic::Movn,
        Opcode::MOVK => Mnemonic::Movk,
        Opcode::ADD => Mnemonic::Add,
        Opcode::ADDS => Mnemonic::Adds,
        Opcode::SUB => Mnemonic::Sub,
        Opcode::SUBS => Mnemonic::Subs,
        Opcode::ADC => Mnemonic::Adc,
        Opcode::ADCS => Mnemonic::Adcs,
        Opcode::SBC => Mnemonic::Sbc,
        Opcode::SBCS => Mnemonic::Sbcs,
        Opcode::AND => Mnemonic::And,
        Opcode::ANDS => Mnemonic::Ands,
        Opcode::ORR => Mnemonic::Orr,
        Opcode::ORN => Mnemonic::Orn,
        Opcode::EOR => Mnemonic::Eor,
        Opcode::EON => Mnemonic::Eon,
        Opcode::BIC => Mnemonic::Bic,
        Opcode::BICS => Mnemonic::Bics,
        Opcode::UBFM => Mnemonic::Ubfm,
        Opcode::SBFM => Mnemonic::Sbfm,
        Opcode::BFM => Mnemonic::Bfm,
        Opcode::EXTR => Mnemonic::Extr,
        Opcode::LSLV => Mnemonic::Lslv,
        Opcode::LSRV => Mnemonic::Lsrv,
        Opcode::ASRV => Mnemonic::Asrv,
        Opcode::RORV => Mnemonic::Rorv,
        Opcode::MADD => Mnemonic::Madd,
        Opcode::MSUB => Mnemonic::Msub,
        Opcode::SMADDL => Mnemonic::Smaddl,
        Opcode::SMSUBL => Mnemonic::Smsubl,
        Opcode::UMADDL => Mnemonic::Umaddl,
        Opcode::UMSUBL => Mnemonic::Umsubl,
        Opcode::SMULH => Mnemonic::Smulh,
        Opcode::UMULH => Mnemonic::Umulh,
        Opcode::UDIV => Mnemonic::Udiv,
        Opcode::SDIV => Mnemonic::Sdiv,
        Opcode::CLZ => Mnemonic::Clz,
        Opcode::CLS => Mnemonic::Cls,
        Opcode::RBIT => Mnemonic::Rbit,
        Opcode::REV => Mnemonic::Rev,
        Opcode::REV16 => Mnemonic::Rev16,
        Opcode::REV32 => Mnemonic::Rev32,
        Opcode::CSEL => Mnemonic::Csel,
        Opcode::CSINC => Mnemonic::Csinc,
        Opcode::CSINV => Mnemonic::Csinv,
        Opcode::CSNEG => Mnemonic::Csneg,
        Opcode::CCMP => Mnemonic::Ccmp,
        Opcode::CCMN => Mnemonic::Ccmn,
        Opcode::LDR
        | Opcode::LDUR
        | Opcode::LDTR
        | Opcode::LDAR
        | Opcode::LDLAR
        | Opcode::LDAPR
        | Opcode::LDAPUR
        | Opcode::LDXR
        | Opcode::LDAXR
        | Opcode::LDRAA
        | Opcode::LDRAB => Mnemonic::Ldr(Reg),
        Opcode::LDRB
        | Opcode::LDURB
        | Opcode::LDTRB
        | Opcode::LDARB
        | Opcode::LDLARB
        | Opcode::LDAPRB
        | Opcode::LDAPURB
        | Opcode::LDXRB
        | Opcode::LDAXRB => Mnemonic::Ldr(Byte),
        Opcode::LDRH
        | Opcode::LDURH
        | Opcode::LDTRH
        | Opcode::LDARH
        | Opcode::LDLARH
        | Opcode::LDAPRH
        | Opcode::LDAPURH
        | Opcode::LDXRH
        | Opcode::LDAXRH => Mnemonic::Ldr(Half),
        Opcode::LDRSB | Opcode::LDURSB | Opcode::LDTRSB | Opcode::LDAPURSB => Mnemonic::Ldr(SByte),
        Opcode::LDRSH | Opcode::LDURSH | Opcode::LDTRSH | Opcode::LDAPURSH => Mnemonic::Ldr(SHalf),
        Opcode::LDRSW | Opcode::LDURSW | Opcode::LDTRSW | Opcode::LDAPURSW => Mnemonic::Ldr(SWord),
        Opcode::STR
        | Opcode::STUR
        | Opcode::STTR
        | Opcode::STLR
        | Opcode::STLLR
        | Opcode::STLUR => Mnemonic::Str(Reg),
        Opcode::STRB
        | Opcode::STURB
        | Opcode::STTRB
        | Opcode::STLRB
        | Opcode::STLLRB
        | Opcode::STLURB => Mnemonic::Str(Byte),
        Opcode::STRH
        | Opcode::STURH
        | Opcode::STTRH
        | Opcode::STLRH
        | Opcode::STLLRH
        | Opcode::STLURH => Mnemonic::Str(Half),
        Opcode::LDP | Opcode::LDNP | Opcode::LDXP | Opcode::LDAXP => Mnemonic::Ldp(Reg),
        Opcode::LDPSW => Mnemonic::Ldp(SWord),
        Opcode::STP | Opcode::STNP => Mnemonic::Stp,
        Opcode::STXR | Opcode::STLXR => Mnemonic::Stxr(Reg),
        Opcode::STXRB | Opcode::STLXRB => Mnemonic::Stxr(Byte),
        Opcode::STXRH | Opcode::STLXRH => Mnemonic::Stxr(Half),
        Opcode::STXP | Opcode::STLXP => Mnemonic::Stxp,
        Opcode::LDADD(_) => Mnemonic::Atomic(Rmw::Add, Reg),
        Opcode::LDADDB(_) => Mnemonic::Atomic(Rmw::Add, Byte),
        Opcode::LDADDH(_) => Mnemonic::Atomic(Rmw::Add, Half),
        Opcode::LDCLR(_) => Mnemonic::Atomic(Rmw::Clr, Reg),
        Opcode::LDCLRB(_) => Mnemonic::Atomic(Rmw::Clr, Byte),
        Opcode::LDCLRH(_) => Mnemonic::Atomic(Rmw::Clr, Half),
        Opcode::LDEOR(_) => Mnemonic::Atomic(Rmw::Eor, Reg),
        Opcode::LDEORB(_) => Mnemonic::Atomic(Rmw::Eor, Byte),
        Opcode::LDEORH(_) => Mnemonic::Atomic(Rmw::Eor, Half),
        Opcode::LDSET(_) => Mnemonic::Atomic(Rmw::Set, Reg),
        Opcode::LDSETB(_) => Mnemonic::Atomic(Rmw::Set, Byte),
        Opcode::LDSETH(_) => Mnemonic::Atomic(Rmw::Set, Half),
        Opcode::LDSMAX(_) => Mnemonic::Atomic(Rmw::Smax, Reg),
        Opcode::LDSMAXB(_) => Mnemonic::Atomic(Rmw::Smax, Byte),
        Opcode::LDSMAXH(_) => Mnemonic::Atomic(Rmw::Smax, Half),
        Opcode::LDSMIN(_) => Mnemonic::Atomic(Rmw::Smin, Reg),
        Opcode::LDSMINB(_) => Mnemonic::Atomic(Rmw::Smin, Byte),
        Opcode::LDSMINH(_) => Mnemonic::Atomic(Rmw::Smin, Half),
        Opcode::LDUMAX(_) => Mnemonic::Atomic(Rmw::Umax, Reg),
        Opcode::LDUMAXB(_) => Mnemonic::Atomic(Rmw::Umax, Byte),
        Opcode::LDUMAXH(_) => Mnemonic::Atomic(Rmw::Umax, Half),
        Opcode::LDUMIN(_) => Mnemonic::Atomic(Rmw::Umin, Reg),
        Opcode::LDUMINB(_) => Mnemonic::Atomic(Rmw::Umin, Byte),
        Opcode::LDUMINH(_) => Mnemonic::Atomic(Rmw::Umin, Half),
        Opcode::SWP(_) => Mnemonic::Atomic(Rmw::Swp, Reg),
        Opcode::SWPB(_) => Mnemonic::Atomic(Rmw::Swp, Byte),
        Opcode::SWPH(_) => Mnemonic::Atomic(Rmw::Swp, Half),
        Opcode::CAS(_) => Mnemonic::Cas(Reg),
        Opcode::CASB(_) => Mnemonic::Cas(Byte),
        Opcode::CASH(_) => Mnemonic::Cas(Half),
        Opcode::PRFM | Opcode::PRFUM => Mnemonic::Prfm,
        Opcode::FMOV => Mnemonic::Fmov,
        Opcode::FADD => Mnemonic::Fadd,
        Opcode::FSUB => Mnemonic::Fsub,
        Opcode::FMUL => Mnemonic::Fmul,
        Opcode::FDIV => Mnemonic::Fdiv,
        Opcode::FMADD => Mnemonic::Fmadd,
        Opcode::FMSUB => Mnemonic::Fmsub,
        Opcode::FNMADD => Mnemonic::Fnmadd,
        Opcode::FNMSUB => Mnemonic::Fnmsub,
        Opcode::FSQRT => Mnemonic::Fsqrt,
        Opcode::FABS => Mnemonic::Fabs,
        Opcode::FNEG => Mnemonic::Fneg,
        Opcode::FMAX => Mnemonic::Fmax,
        Opcode::FMIN => Mnemonic::Fmin,
        Opcode::FCMP => Mnemonic::Fcmp,
        Opcode::FCMPE => Mnemonic::Fcmpe,
        Opcode::FCCMP | Opcode::FCCMPE => Mnemonic::Fccmp,
        Opcode::FCSEL => Mnemonic::Fcsel,
        Opcode::SCVTF => Mnemonic::Scvtf,
        Opcode::UCVTF => Mnemonic::Ucvtf,
        Opcode::FCVTZS => Mnemonic::Fcvtzs,
        Opcode::FCVTZU => Mnemonic::Fcvtzu,
        Opcode::FCVT => Mnemonic::Fcvt,
        Opcode::DUP => Mnemonic::Dup,
        Opcode::MOVI => Mnemonic::Movi,
        Opcode::MVNI => Mnemonic::Mvni,
        Opcode::MUL => Mnemonic::Mul,
        Opcode::ADDV => Mnemonic::Simd(Simd::Addv),
        Opcode::CMEQ => Mnemonic::Simd(Simd::Cmeq),
        Opcode::CMGT => Mnemonic::Simd(Simd::Cmgt),
        Opcode::CMGE => Mnemonic::Simd(Simd::Cmge),
        Opcode::CMHI => Mnemonic::Simd(Simd::Cmhi),
        Opcode::CMHS => Mnemonic::Simd(Simd::Cmhs),
        Opcode::CMLE => Mnemonic::Simd(Simd::Cmle),
        Opcode::CMLT => Mnemonic::Simd(Simd::Cmlt),
        Opcode::USHLL | Opcode::USHLL2 => Mnemonic::Simd(Simd::Ushll),
        Opcode::SSHLL | Opcode::SSHLL2 => Mnemonic::Simd(Simd::Sshll),
        Opcode::EXT => Mnemonic::Simd(Simd::Ext),
        Opcode::INS => Mnemonic::Simd(Simd::Ins),
        Opcode::UMOV => Mnemonic::Simd(Simd::Umov),
        Opcode::SMIN => Mnemonic::Simd(Simd::Smin),
        Opcode::SMAX => Mnemonic::Simd(Simd::Smax),
        Opcode::UMIN => Mnemonic::Simd(Simd::Umin),
        Opcode::UMAX => Mnemonic::Simd(Simd::Umax),
        Opcode::SMINV => Mnemonic::Simd(Simd::Sminv),
        Opcode::SMAXV => Mnemonic::Simd(Simd::Smaxv),
        Opcode::UMINV => Mnemonic::Simd(Simd::Uminv),
        Opcode::UMAXV => Mnemonic::Simd(Simd::Umaxv),
        Opcode::SMLAL | Opcode::SMLAL2 => Mnemonic::Simd(Simd::Smlal),
        Opcode::UMLAL | Opcode::UMLAL2 => Mnemonic::Simd(Simd::Umlal),
        Opcode::SMULL | Opcode::SMULL2 => Mnemonic::Simd(Simd::Smull),
        Opcode::UMULL | Opcode::UMULL2 => Mnemonic::Simd(Simd::Umull),
        Opcode::SADDW | Opcode::SADDW2 => Mnemonic::Simd(Simd::Saddw),
        Opcode::UADDW | Opcode::UADDW2 => Mnemonic::Simd(Simd::Uaddw),
        Opcode::ADDP => Mnemonic::Simd(Simd::Addp),
        Opcode::MLA => Mnemonic::Simd(Simd::Mla),
        Opcode::NEG => Mnemonic::Neg,
        Opcode::ABS => Mnemonic::Abs,
        Opcode::LD1 => Mnemonic::Ld1,
        Opcode::ST1 => Mnemonic::St1,
        Opcode::SVC => Mnemonic::Svc,
        Opcode::MRS => Mnemonic::Mrs,
        Opcode::MSR => Mnemonic::Msr,
        Opcode::DMB(_)
        | Opcode::DSB(_)
        | Opcode::ISB
        | Opcode::SB
        | Opcode::SSBB
        | Opcode::PSSBB
        | Opcode::CLREX => Mnemonic::Barrier,
        _ => Mnemonic::Other,
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
