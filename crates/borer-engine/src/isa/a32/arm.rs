//! The A32 decoder: one four-byte word into an [`Insn`].

use super::{
    Addr, Block, Cond, DpKind, Index, Insn, Mode, Offset, Op, Operand, PC, Reg, Shift, Width, rel,
    sext, vfp,
};

/// A four-bit register field of `w` starting at bit `at`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `at` - The field's lowest bit.
fn reg(w: u32, at: u32) -> Reg {
    Reg::R(u8::try_from((w >> at) & 0xf).unwrap_or(0))
}

/// One bit of `w`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `at` - The bit.
fn bit(w: u32, at: u32) -> bool {
    (w >> at) & 1 == 1
}

/// The shift a two-bit type field and a five-bit amount name, as an
/// immediate shift decodes them: an amount of zero means 32 for `lsr` and
/// `asr`, and `rrx` for `ror`.
///
/// # Arguments
///
/// * `ty` - The type field.
/// * `imm5` - The amount field.
pub(super) fn imm_shift(ty: u32, imm5: u32) -> (Shift, u8) {
    let amount = u8::try_from(imm5).unwrap_or(0);
    match (ty & 3, amount) {
        (0, n) => (Shift::Lsl, n),
        (1, 0) => (Shift::Lsr, 32),
        (1, n) => (Shift::Lsr, n),
        (2, 0) => (Shift::Asr, 32),
        (2, n) => (Shift::Asr, n),
        (_, 0) => (Shift::Rrx, 1),
        (_, n) => (Shift::Ror, n),
    }
}

/// The shift a two-bit type field names for a shift by a register.
///
/// # Arguments
///
/// * `ty` - The type field.
pub(super) fn reg_shift(ty: u32) -> Shift {
    match ty & 3 {
        0 => Shift::Lsl,
        1 => Shift::Lsr,
        2 => Shift::Asr,
        _ => Shift::Ror,
    }
}

/// The data-processing operation a four-bit opcode names.
///
/// # Arguments
///
/// * `opcode` - The field.
fn dp_kind(opcode: u32) -> DpKind {
    match opcode & 0xf {
        0x0 => DpKind::And,
        0x1 => DpKind::Eor,
        0x2 => DpKind::Sub,
        0x3 => DpKind::Rsb,
        0x4 => DpKind::Add,
        0x5 => DpKind::Adc,
        0x6 => DpKind::Sbc,
        0x7 => DpKind::Rsc,
        0x8 => DpKind::Tst,
        0x9 => DpKind::Teq,
        0xa => DpKind::Cmp,
        0xb => DpKind::Cmn,
        0xc => DpKind::Orr,
        0xd => DpKind::Mov,
        0xe => DpKind::Bic,
        _ => DpKind::Mvn,
    }
}

/// The value and carry of an A32 modified immediate: eight bits rotated
/// right by twice the four-bit rotation.
///
/// # Arguments
///
/// * `imm12` - The field.
pub(super) fn arm_expand(imm12: u32) -> Operand {
    let rot = ((imm12 >> 8) & 0xf) * 2;
    let value = (imm12 & 0xff).rotate_right(rot);
    Operand::Imm {
        value,
        carry: (rot != 0).then_some(bit(value, 31)),
    }
}

/// The block-transfer order the `P` and `U` bits name.
///
/// # Arguments
///
/// * `p` - Before (set) or after.
/// * `u` - Increment (set) or decrement.
pub(super) fn block(p: bool, u: bool) -> Block {
    match (p, u) {
        (false, true) => Block::Ia,
        (true, true) => Block::Ib,
        (false, false) => Block::Da,
        (true, false) => Block::Db,
    }
}

/// The addressing mode the `P` and `W` bits name.
///
/// # Arguments
///
/// * `p` - Index before the access.
/// * `w` - Write the address back.
pub(super) fn index(p: bool, w: bool) -> Index {
    match (p, w) {
        (true, false) => Index::Offset,
        (true, true) => Index::Pre,
        (false, _) => Index::Post,
    }
}

/// Decodes one A32 word.
///
/// # Arguments
///
/// * `w` - The word.
/// * `va` - Its address.
pub(super) fn decode(w: u32, va: u64) -> Insn {
    let cond_field = w >> 28;
    let mut insn = Insn {
        va,
        len: 4,
        mode: Mode::Arm,
        cond: Cond::from_code(u8::try_from(cond_field).unwrap_or(0xe)),
        sets: false,
        op: Op::Invalid,
        word: w,
    };
    if cond_field == 0xf {
        insn.cond = Cond::Al;
        insn.op = unconditional(w, va);
        return insn;
    }
    let (op, sets) = match (w >> 25) & 7 {
        0 | 1 => data(w, va),
        2 => (single(w, false), false),
        3 if bit(w, 4) => (media(w), false),
        3 => (single(w, true), false),
        4 => (
            {
                let regs = u16::try_from(w & 0xffff).unwrap_or(0);
                let (rn, wback, b) = (reg(w, 16), bit(w, 21), block(bit(w, 24), bit(w, 23)));
                if bit(w, 22) {
                    Op::Unknown
                } else if bit(w, 20) {
                    Op::Ldm {
                        rn,
                        regs,
                        wback,
                        block: b,
                    }
                } else {
                    Op::Stm {
                        rn,
                        regs,
                        wback,
                        block: b,
                    }
                }
            },
            false,
        ),
        5 => {
            let target = rel(va.wrapping_add(8), sext(w & 0xff_ffff, 24) << 2);
            (
                if bit(w, 24) {
                    Op::Bl { target }
                } else {
                    Op::B { target }
                },
                false,
            )
        }
        _ => (coprocessor(w), false),
    };
    insn.op = op;
    insn.sets = sets;
    insn
}

/// The instructions of the unconditional space (condition field `1111`):
/// `blx` to an immediate, the preloads and barriers, and Advanced SIMD.
///
/// # Arguments
///
/// * `w` - The word.
/// * `va` - Its address.
fn unconditional(w: u32, va: u64) -> Op {
    if (w >> 25) & 7 == 5 {
        let h = i64::from((w >> 24) & 1) << 1;
        return Op::Blx {
            target: rel(va.wrapping_add(8), (sext(w & 0xff_ffff, 24) << 2) | h),
        };
    }
    if (w >> 25) & 0x7f == 0x79 {
        return vfp::neon(w, false);
    }
    if (w >> 24) & 0xff == 0xf4 && !bit(w, 20) {
        return vfp::neon(w, true);
    }
    if w & 0xfff0_0000 == 0xf570_0000 {
        return Op::Nop;
    }
    if (w >> 26) & 3 == 1 && (w >> 20) & 0x5 == 0x5 {
        return Op::Nop;
    }
    Op::Invalid
}

/// Decodes the data-processing and miscellaneous space (`op1` 000 or 001).
///
/// It holds the arithmetic and logic, the multiplies, the halfword, signed
/// and dual loads and stores, the exclusives, `movw` and `movt`, `bx`,
/// `blx`, `clz` and the hints.
///
/// # Arguments
///
/// * `w` - The word.
/// * `va` - Its address.
///
/// # Returns
///
/// The operation, and whether it sets the flags.
fn data(w: u32, va: u64) -> (Op, bool) {
    let imm = bit(w, 25);
    let op1 = (w >> 20) & 0x1f;
    let s = bit(w, 20);
    if !imm && bit(w, 4) && bit(w, 7) {
        return (
            multiply_or_extra(w),
            s && (w >> 24) & 1 == 0 && (w >> 5) & 3 == 0,
        );
    }
    if op1 & 0x19 == 0x10 {
        return (if imm { special_imm(w) } else { misc(w) }, false);
    }
    let kind = dp_kind(w >> 21);
    let rn = reg(w, 16);
    let rd = reg(w, 12);
    let src = if imm {
        arm_expand(w & 0xfff)
    } else if bit(w, 4) {
        Operand::RegShift {
            rm: reg(w, 0),
            shift: reg_shift(w >> 5),
            rs: reg(w, 8),
        }
    } else {
        let (shift, amount) = imm_shift(w >> 5, (w >> 7) & 0x1f);
        Operand::Reg {
            rm: reg(w, 0),
            shift,
            amount,
        }
    };
    if !s
        && rn == PC
        && let Operand::Imm { value, .. } = src
        && matches!(kind, DpKind::Add | DpKind::Sub)
    {
        let base = va.wrapping_add(8);
        let target = if kind == DpKind::Add {
            base.wrapping_add(u64::from(value))
        } else {
            base.wrapping_sub(u64::from(value))
        };
        return (
            Op::Adr {
                rd,
                target: target & 0xffff_ffff,
            },
            false,
        );
    }
    (Op::Dp { kind, rd, rn, src }, s)
}

/// The multiplies, the exclusives and the halfword, signed and dual loads
/// and stores: the data-processing words with bits 7 and 4 set.
///
/// # Arguments
///
/// * `w` - The word.
fn multiply_or_extra(w: u32) -> Op {
    let op2 = (w >> 5) & 3;
    if op2 == 0 {
        return if bit(w, 24) {
            exclusive(w)
        } else {
            multiply(w)
        };
    }
    let (p, u, i, wb, l) = (bit(w, 24), bit(w, 23), bit(w, 22), bit(w, 21), bit(w, 20));
    let offset = if i {
        let v = i32::try_from(((w >> 4) & 0xf0) | (w & 0xf)).unwrap_or(0);
        Offset::Imm(if u { v } else { -v })
    } else {
        Offset::Reg {
            rm: reg(w, 0),
            sub: !u,
            shift: Shift::Lsl,
            amount: 0,
        }
    };
    let addr = Addr {
        base: reg(w, 16),
        offset,
        index: index(p, wb),
    };
    let rt = reg(w, 12);
    let rt2 = match rt {
        Reg::R(n) => Reg::R(n.saturating_add(1)),
        Reg::S(_) | Reg::D(_) => rt,
    };
    match (op2, l) {
        (1, false) => Op::Store {
            width: Width::Half,
            rt,
            addr,
        },
        (1, true) => Op::Load {
            width: Width::Half,
            rt,
            addr,
        },
        (2, false) => Op::LoadDual { rt, rt2, addr },
        (2, true) => Op::Load {
            width: Width::SByte,
            rt,
            addr,
        },
        (_, false) => Op::StoreDual { rt, rt2, addr },
        (_, true) => Op::Load {
            width: Width::SHalf,
            rt,
            addr,
        },
    }
}

/// The multiplies: `mul`, `mla`, `mls`, `umull`, `umlal`, `smull` and
/// `smlal`.
///
/// # Arguments
///
/// * `w` - The word.
fn multiply(w: u32) -> Op {
    let (rd_hi, rd_lo_acc, rm, rn) = (reg(w, 16), reg(w, 12), reg(w, 8), reg(w, 0));
    match (w >> 21) & 7 {
        0 => Op::Mul {
            rd: rd_hi,
            rn,
            rm,
            acc: None,
            sub: false,
        },
        1 => Op::Mul {
            rd: rd_hi,
            rn,
            rm,
            acc: Some(rd_lo_acc),
            sub: false,
        },
        3 => Op::Mul {
            rd: rd_hi,
            rn,
            rm,
            acc: Some(rd_lo_acc),
            sub: true,
        },
        op @ 4..=7 => Op::MulLong {
            signed: op & 2 != 0,
            acc: op & 1 != 0,
            lo: rd_lo_acc,
            hi: rd_hi,
            rn,
            rm,
        },
        _ => Op::Unknown,
    }
}

/// The synchronization primitives: `ldrex` and `strex` of a byte, a
/// halfword or a word as a load and a store that always succeeds; `swp`
/// and the doubleword forms are not modeled.
///
/// # Arguments
///
/// * `w` - The word.
fn exclusive(w: u32) -> Op {
    if !bit(w, 23) {
        return Op::Unknown;
    }
    let width = match (w >> 21) & 3 {
        0 => Width::Word,
        2 => Width::Byte,
        3 => Width::Half,
        _ => return Op::Unknown,
    };
    let addr = Addr {
        base: reg(w, 16),
        offset: Offset::Imm(0),
        index: Index::Offset,
    };
    if bit(w, 20) {
        Op::LoadEx {
            width,
            rt: reg(w, 12),
            addr,
        }
    } else {
        Op::StoreEx {
            width,
            rd: reg(w, 12),
            rt: reg(w, 0),
            addr,
        }
    }
}

/// `movw`, `movt` and the hints, the immediate words of the
/// miscellaneous space.
///
/// # Arguments
///
/// * `w` - The word.
fn special_imm(w: u32) -> Op {
    let imm = u16::try_from(((w >> 4) & 0xf000) | (w & 0xfff)).unwrap_or(0);
    match (w >> 20) & 0x1f {
        0x10 => Op::Movw {
            rd: reg(w, 12),
            imm,
        },
        0x14 => Op::Movt {
            rd: reg(w, 12),
            imm,
        },
        0x12 if (w >> 16) & 0xf == 0 => Op::Nop,
        _ => Op::Unknown,
    }
}

/// The miscellaneous register words: `bx`, `blx`, `clz`, `mrs`, `msr` and
/// `bkpt`.
///
/// # Arguments
///
/// * `w` - The word.
fn misc(w: u32) -> Op {
    let op = (w >> 21) & 3;
    match ((w >> 4) & 0xf, op) {
        (0, 0) if !bit(w, 22) => Op::Mrs { rd: reg(w, 12) },
        (0, 1) if (w >> 18) & 3 == 2 && !bit(w, 22) => Op::Msr { rn: reg(w, 0) },
        (1, 1) => Op::Bx { rm: reg(w, 0) },
        (1, 3) => Op::Clz {
            rd: reg(w, 12),
            rm: reg(w, 0),
        },
        (3, 1) => Op::BlxReg { rm: reg(w, 0) },
        (7, 1) => Op::Trap,
        (8 | 0xa | 0xc | 0xe, 0 | 3) => Op::Smulxy {
            rd: reg(w, 16),
            rn: reg(w, 0),
            rm: reg(w, 8),
            n_top: bit(w, 5),
            m_top: bit(w, 6),
            acc: (op == 0).then(|| reg(w, 12)),
        },
        _ => Op::Unknown,
    }
}

/// The loads and stores of a word or a byte, immediate or register offset.
///
/// # Arguments
///
/// * `w` - The word.
/// * `register` - The offset is a shifted register (`op1` 011).
fn single(w: u32, register: bool) -> Op {
    let (p, u, b, wb, l) = (bit(w, 24), bit(w, 23), bit(w, 22), bit(w, 21), bit(w, 20));
    let offset = if register {
        let (shift, amount) = imm_shift(w >> 5, (w >> 7) & 0x1f);
        Offset::Reg {
            rm: reg(w, 0),
            sub: !u,
            shift,
            amount,
        }
    } else {
        let v = i32::try_from(w & 0xfff).unwrap_or(0);
        Offset::Imm(if u { v } else { -v })
    };
    let addr = Addr {
        base: reg(w, 16),
        offset,
        index: index(p, wb),
    };
    let width = if b { Width::Byte } else { Width::Word };
    let rt = reg(w, 12);
    if l {
        Op::Load { width, rt, addr }
    } else {
        Op::Store { width, rt, addr }
    }
}

/// The media space: the extensions, the byte reversals, the bit fields,
/// the divides and the permanently undefined word.
///
/// # Arguments
///
/// * `w` - The word.
fn media(w: u32) -> Op {
    let op1 = (w >> 20) & 0x1f;
    let op2 = (w >> 5) & 7;
    let (rd, rn, rm) = (reg(w, 12), reg(w, 16), reg(w, 0));
    let lsb = u8::try_from((w >> 7) & 0x1f).unwrap_or(0);
    let field = u8::try_from((w >> 16) & 0x1f).unwrap_or(0);
    match (op1, op2) {
        (0x1f, 7) => Op::Trap,
        (0x1a | 0x1b | 0x1e | 0x1f, 2 | 6) => Op::Bfx {
            signed: op1 & 4 == 0,
            rd,
            rn: rm,
            lsb,
            width: field.saturating_add(1),
        },
        (0x0a | 0x0b | 0x0e | 0x0f, 0 | 2 | 4 | 6) => {
            let (shift, amount) = if bit(w, 6) {
                imm_shift(2, (w >> 7) & 0x1f)
            } else {
                (Shift::Lsl, lsb)
            };
            let signed = op1 & 4 == 0;
            Op::Sat {
                signed,
                rd,
                rn: rm,
                bits: if signed {
                    field.saturating_add(1)
                } else {
                    field
                },
                shift,
                amount,
            }
        }
        (0x1c | 0x1d, 0 | 4) => {
            let Some(width) = field.checked_sub(lsb).map(|d| d.saturating_add(1)) else {
                return Op::Unknown;
            };
            Op::Bfi {
                rd,
                rn: (rm != PC).then_some(rm),
                lsb,
                width,
            }
        }
        (0x15, 0) => Op::Smmul {
            rd: rn,
            rn: rm,
            rm: reg(w, 8),
            acc: (rd != PC).then_some(rd),
        },
        (0x11 | 0x13, 0) if (w >> 12) & 0xf == 0xf => Op::Div {
            signed: op1 == 0x11,
            rd: rn,
            rn: rm,
            rm: reg(w, 8),
        },
        (0x0a | 0x0b | 0x0e | 0x0f, 3) => Op::Extend {
            signed: op1 & 4 == 0,
            bits: if op1 & 1 == 0 { 8 } else { 16 },
            rd,
            rm,
            rotate: u8::try_from(((w >> 10) & 3) * 8).unwrap_or(0),
            add: (rn != PC).then_some(rn),
        },
        (0x0b, 1) => Op::Rev { rd, rm },
        (0x0b, 5) => Op::Rev16 { rd, rm },
        (0x0f, 1) => Op::Rbit { rd, rm },
        (0x0f, 5) => Op::Revsh { rd, rm },
        _ => Op::Unknown,
    }
}

/// The coprocessor space: `svc`, and the VFP instructions ([`vfp`]).
///
/// # Arguments
///
/// * `w` - The word.
fn coprocessor(w: u32) -> Op {
    if (w >> 24) & 0xf == 0xf {
        return Op::Svc { imm: w & 0xff_ffff };
    }
    vfp::decode(w)
}
