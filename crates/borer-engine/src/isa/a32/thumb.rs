//! The T32 decoder: a 16-bit instruction, or a 32-bit one's two
//! halfwords, into an [`Insn`].

use super::arm::{imm_shift, index, reg_shift};
use super::{
    Addr, Cond, DpKind, Index, Insn, Mode, Offset, Op, Operand, PC, Reg, SP, Shift, Width, rel,
    sext, vfp,
};

/// One bit of `v`.
///
/// # Arguments
///
/// * `v` - The halfword or word.
/// * `at` - The bit.
fn bit(v: u32, at: u32) -> bool {
    (v >> at) & 1 == 1
}

/// A register field of `v` starting at bit `at`, `width` bits wide.
///
/// # Arguments
///
/// * `v` - The halfword.
/// * `at` - The field's lowest bit.
/// * `width` - Its width: 3 or 4.
fn reg(v: u32, at: u32, width: u32) -> Reg {
    Reg::R(u8::try_from((v >> at) & ((1 << width) - 1)).unwrap_or(0))
}

/// Tells whether a first halfword opens a 32-bit instruction.
///
/// # Arguments
///
/// * `hw1` - The halfword.
pub(super) fn wide(hw1: u16) -> bool {
    matches!(hw1 >> 11, 0b11101..=0b11111)
}

/// Decodes one T32 instruction.
///
/// # Arguments
///
/// * `hw1` - The first halfword.
/// * `hw2` - The second, for a 32-bit instruction; ignored otherwise.
/// * `va` - Its address.
/// * `in_it` - Whether it is inside an `IT` block, where the 16-bit data
///   instructions do not set the flags.
pub(super) fn decode(hw1: u16, hw2: u16, va: u64, in_it: bool) -> Insn {
    let mut insn = Insn {
        va,
        len: 2,
        mode: Mode::Thumb,
        cond: Cond::Al,
        sets: false,
        op: Op::Invalid,
        word: u32::from(hw1),
    };
    if wide(hw1) {
        insn.len = 4;
        insn.word = (u32::from(hw1) << 16) | u32::from(hw2);
        let (op, sets, cond) = wide_op(u32::from(hw1), u32::from(hw2), va);
        insn.op = op;
        insn.sets = sets;
        insn.cond = cond;
    } else {
        let (op, sets, cond) = narrow(u32::from(hw1), va, in_it);
        insn.op = op;
        insn.sets = sets;
        insn.cond = cond;
    }
    insn
}

/// A data-processing instruction of a register shifted by an immediate.
///
/// # Arguments
///
/// * `kind` - The operation.
/// * `rd` - The destination.
/// * `rn` - The first source.
/// * `rm` - The register operand.
/// * `shift` - Its shift.
/// * `amount` - The shift amount.
fn dp_reg(kind: DpKind, rd: Reg, rn: Reg, rm: Reg, shift: Shift, amount: u8) -> Op {
    Op::Dp {
        kind,
        rd,
        rn,
        src: Operand::Reg { rm, shift, amount },
    }
}

/// A data-processing instruction of an immediate.
///
/// # Arguments
///
/// * `kind` - The operation.
/// * `rd` - The destination.
/// * `rn` - The first source.
/// * `value` - The immediate.
fn dp_imm(kind: DpKind, rd: Reg, rn: Reg, value: u32) -> Op {
    Op::Dp {
        kind,
        rd,
        rn,
        src: Operand::Imm { value, carry: None },
    }
}

/// An address of a base and an immediate offset.
///
/// # Arguments
///
/// * `base` - The base.
/// * `off` - The offset in bytes.
fn at(base: Reg, off: u32) -> Addr {
    Addr {
        base,
        offset: Offset::Imm(i32::try_from(off).unwrap_or(0)),
        index: Index::Offset,
    }
}

/// Decodes a 16-bit instruction.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `va` - Its address.
/// * `in_it` - Inside an `IT` block.
///
/// # Returns
///
/// The operation, whether it sets the flags, and its own condition (a
/// conditional branch's).
fn narrow(h: u32, va: u64, in_it: bool) -> (Op, bool, Cond) {
    let s = !in_it;
    let al = Cond::Al;
    let (r0, r3, r8) = (reg(h, 0, 3), reg(h, 3, 3), reg(h, 8, 3));
    let imm5 = (h >> 6) & 0x1f;
    let imm8 = h & 0xff;
    match h >> 10 {
        0x00..=0x05 => {
            let (shift, amount) = imm_shift(h >> 11, imm5);
            (dp_reg(DpKind::Mov, r0, r0, r3, shift, amount), s, al)
        }
        0x06 | 0x07 => {
            let rm = reg(h, 6, 3);
            let imm3 = (h >> 6) & 7;
            let op = match (h >> 9) & 3 {
                0 => dp_reg(DpKind::Add, r0, r3, rm, Shift::Lsl, 0),
                1 => dp_reg(DpKind::Sub, r0, r3, rm, Shift::Lsl, 0),
                2 => dp_imm(DpKind::Add, r0, r3, imm3),
                _ => dp_imm(DpKind::Sub, r0, r3, imm3),
            };
            (op, s, al)
        }
        0x08..=0x0f => {
            let (op, sets) = match (h >> 11) & 3 {
                0 => (dp_imm(DpKind::Mov, r8, r8, imm8), s),
                1 => (dp_imm(DpKind::Cmp, r8, r8, imm8), true),
                2 => (dp_imm(DpKind::Add, r8, r8, imm8), s),
                _ => (dp_imm(DpKind::Sub, r8, r8, imm8), s),
            };
            (op, sets, al)
        }
        0x10 => {
            let (rdn, rm) = (r0, r3);
            let reg_op = |kind| dp_reg(kind, rdn, rdn, rm, Shift::Lsl, 0);
            let by = |shift| Op::Dp {
                kind: DpKind::Mov,
                rd: rdn,
                rn: rdn,
                src: Operand::RegShift {
                    rm: rdn,
                    shift,
                    rs: rm,
                },
            };
            let (op, sets) = match (h >> 6) & 0xf {
                0x0 => (reg_op(DpKind::And), s),
                0x1 => (reg_op(DpKind::Eor), s),
                0x2 => (by(Shift::Lsl), s),
                0x3 => (by(Shift::Lsr), s),
                0x4 => (by(Shift::Asr), s),
                0x5 => (reg_op(DpKind::Adc), s),
                0x6 => (reg_op(DpKind::Sbc), s),
                0x7 => (by(Shift::Ror), s),
                0x8 => (reg_op(DpKind::Tst), true),
                0x9 => (dp_imm(DpKind::Rsb, rdn, rm, 0), s),
                0xa => (reg_op(DpKind::Cmp), true),
                0xb => (reg_op(DpKind::Cmn), true),
                0xc => (reg_op(DpKind::Orr), s),
                0xd => (
                    Op::Mul {
                        rd: rdn,
                        rn: rm,
                        rm: rdn,
                        acc: None,
                        sub: false,
                    },
                    s,
                ),
                0xe => (reg_op(DpKind::Bic), s),
                _ => (
                    Op::Dp {
                        kind: DpKind::Mvn,
                        rd: rdn,
                        rn: rdn,
                        src: Operand::Reg {
                            rm,
                            shift: Shift::Lsl,
                            amount: 0,
                        },
                    },
                    s,
                ),
            };
            (op, sets, al)
        }
        0x11 => {
            let rdn = Reg::R(u8::try_from(((h >> 4) & 8) | (h & 7)).unwrap_or(0));
            let rm = reg(h, 3, 4);
            let (op, sets) = match (h >> 8) & 3 {
                0 => (dp_reg(DpKind::Add, rdn, rdn, rm, Shift::Lsl, 0), false),
                1 => (dp_reg(DpKind::Cmp, rdn, rdn, rm, Shift::Lsl, 0), true),
                2 => (dp_reg(DpKind::Mov, rdn, rdn, rm, Shift::Lsl, 0), false),
                _ if bit(h, 7) => (Op::BlxReg { rm }, false),
                _ => (Op::Bx { rm }, false),
            };
            (op, sets, al)
        }
        0x12 | 0x13 => (
            Op::Load {
                width: Width::Word,
                rt: r8,
                addr: at(PC, imm8 * 4),
            },
            false,
            al,
        ),
        0x14..=0x17 => {
            let addr = Addr {
                base: r3,
                offset: Offset::Reg {
                    rm: reg(h, 6, 3),
                    sub: false,
                    shift: Shift::Lsl,
                    amount: 0,
                },
                index: Index::Offset,
            };
            let op = match (h >> 9) & 7 {
                0 => Op::Store {
                    width: Width::Word,
                    rt: r0,
                    addr,
                },
                1 => Op::Store {
                    width: Width::Half,
                    rt: r0,
                    addr,
                },
                2 => Op::Store {
                    width: Width::Byte,
                    rt: r0,
                    addr,
                },
                3 => Op::Load {
                    width: Width::SByte,
                    rt: r0,
                    addr,
                },
                4 => Op::Load {
                    width: Width::Word,
                    rt: r0,
                    addr,
                },
                5 => Op::Load {
                    width: Width::Half,
                    rt: r0,
                    addr,
                },
                6 => Op::Load {
                    width: Width::Byte,
                    rt: r0,
                    addr,
                },
                _ => Op::Load {
                    width: Width::SHalf,
                    rt: r0,
                    addr,
                },
            };
            (op, false, al)
        }
        0x18..=0x23 => {
            let (width, scale) = match h >> 12 {
                6 => (Width::Word, 4),
                7 => (Width::Byte, 1),
                _ => (Width::Half, 2),
            };
            let addr = at(r3, imm5 * scale);
            let op = if bit(h, 11) {
                Op::Load {
                    width,
                    rt: r0,
                    addr,
                }
            } else {
                Op::Store {
                    width,
                    rt: r0,
                    addr,
                }
            };
            (op, false, al)
        }
        0x24..=0x27 => {
            let addr = at(SP, imm8 * 4);
            let op = if bit(h, 11) {
                Op::Load {
                    width: Width::Word,
                    rt: r8,
                    addr,
                }
            } else {
                Op::Store {
                    width: Width::Word,
                    rt: r8,
                    addr,
                }
            };
            (op, false, al)
        }
        0x28 | 0x29 => (
            Op::Adr {
                rd: r8,
                target: ((va.wrapping_add(4) & !3).wrapping_add(u64::from(imm8 * 4))) & 0xffff_ffff,
            },
            false,
            al,
        ),
        0x2a | 0x2b => (dp_imm(DpKind::Add, r8, SP, imm8 * 4), false, al),
        0x2c..=0x2f => (misc16(h, va), false, al),
        0x30..=0x33 => {
            let rn = r8;
            let regs = u16::try_from(imm8).unwrap_or(0);
            let op = if bit(h, 11) {
                let Reg::R(n) = rn else {
                    return (Op::Invalid, false, al);
                };
                Op::Ldm {
                    rn,
                    regs,
                    wback: regs & (1 << n) == 0,
                    block: super::Block::Ia,
                }
            } else {
                Op::Stm {
                    rn,
                    regs,
                    wback: true,
                    block: super::Block::Ia,
                }
            };
            (op, false, al)
        }
        0x34..=0x37 => match (h >> 8) & 0xf {
            0xe => (Op::Trap, false, al),
            0xf => (Op::Svc { imm: imm8 }, false, al),
            c => (
                Op::B {
                    target: rel(va.wrapping_add(4), sext(imm8, 8) << 1),
                },
                false,
                Cond::from_code(u8::try_from(c).unwrap_or(0xe)),
            ),
        },
        0x38 | 0x39 => (
            Op::B {
                target: rel(va.wrapping_add(4), sext(h & 0x7ff, 11) << 1),
            },
            false,
            al,
        ),
        _ => (Op::Invalid, false, al),
    }
}

/// The miscellaneous 16-bit instructions: the stack adjustments, `cbz`
/// and `cbnz`, the extensions, `push` and `pop`, the byte reversals,
/// `bkpt`, `it` and the hints.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `va` - Its address.
fn misc16(h: u32, va: u64) -> Op {
    let (r0, r3) = (reg(h, 0, 3), reg(h, 3, 3));
    let low8 = u16::try_from(h & 0xff).unwrap_or(0);
    match (h >> 5) & 0x7f {
        0x00..=0x03 => dp_imm(DpKind::Add, SP, SP, (h & 0x7f) * 4),
        0x04..=0x07 => dp_imm(DpKind::Sub, SP, SP, (h & 0x7f) * 4),
        0x08..=0x0f | 0x18..=0x1f | 0x48..=0x4f | 0x58..=0x5f => Op::Cbz {
            rn: r0,
            target: rel(
                va.wrapping_add(4),
                i64::from((((h >> 9) & 1) << 6) | (((h >> 3) & 0x1f) << 1)),
            ),
            nonzero: bit(h, 11),
        },
        0x10..=0x17 => {
            let (signed, bits) = match (h >> 6) & 3 {
                0 => (true, 16),
                1 => (true, 8),
                2 => (false, 16),
                _ => (false, 8),
            };
            Op::Extend {
                signed,
                bits,
                rd: r0,
                rm: r3,
                rotate: 0,
                add: None,
            }
        }
        0x20..=0x2f => Op::Stm {
            rn: SP,
            regs: low8 | if bit(h, 8) { 1 << 14 } else { 0 },
            wback: true,
            block: super::Block::Db,
        },
        0x60..=0x6f => Op::Ldm {
            rn: SP,
            regs: low8 | if bit(h, 8) { 1 << 15 } else { 0 },
            wback: true,
            block: super::Block::Ia,
        },
        0x50..=0x57 => match (h >> 6) & 3 {
            0 => Op::Rev { rd: r0, rm: r3 },
            1 => Op::Rev16 { rd: r0, rm: r3 },
            3 => Op::Revsh { rd: r0, rm: r3 },
            _ => Op::Invalid,
        },
        0x70..=0x77 => Op::Trap,
        0x78..=0x7f if h & 0xf != 0 => Op::It {
            first: Cond::from_code(u8::try_from((h >> 4) & 0xf).unwrap_or(0xe)),
            mask: u8::try_from(h & 0xf).unwrap_or(0),
        },
        0x78..=0x7f => Op::Nop,
        _ => Op::Unknown,
    }
}

/// The value and carry of a T32 modified immediate.
///
/// # Arguments
///
/// * `imm12` - The `i:imm3:imm8` field.
fn expand(imm12: u32) -> Operand {
    let imm8 = imm12 & 0xff;
    if (imm12 >> 10) & 3 == 0 {
        let value = match (imm12 >> 8) & 3 {
            0 => imm8,
            1 => (imm8 << 16) | imm8,
            2 => (imm8 << 24) | (imm8 << 8),
            _ => imm8 * 0x0101_0101,
        };
        return Operand::Imm { value, carry: None };
    }
    let value = (0x80 | (imm12 & 0x7f)).rotate_right((imm12 >> 7) & 0x1f);
    Operand::Imm {
        value,
        carry: Some(bit(value, 31)),
    }
}

/// The T32 data-processing operation a four-bit opcode names, and the
/// operation it is with the destination or the first source `pc`: a
/// compare, a move.
///
/// # Arguments
///
/// * `op` - The opcode.
/// * `rd_pc` - The destination field is `pc` and the flags are set.
/// * `rn_pc` - The first source field is `pc`.
fn t32_kind(op: u32, rd_pc: bool, rn_pc: bool) -> Option<DpKind> {
    Some(match op {
        0x0 if rd_pc => DpKind::Tst,
        0x0 => DpKind::And,
        0x1 => DpKind::Bic,
        0x2 if rn_pc => DpKind::Mov,
        0x2 => DpKind::Orr,
        0x3 if rn_pc => DpKind::Mvn,
        0x3 => DpKind::Orn,
        0x4 if rd_pc => DpKind::Teq,
        0x4 => DpKind::Eor,
        0x8 if rd_pc => DpKind::Cmn,
        0x8 => DpKind::Add,
        0xa => DpKind::Adc,
        0xb => DpKind::Sbc,
        0xd if rd_pc => DpKind::Cmp,
        0xd => DpKind::Sub,
        0xe => DpKind::Rsb,
        _ => return None,
    })
}

/// Decodes a 32-bit instruction.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
/// * `va` - Its address.
///
/// # Returns
///
/// The operation, whether it sets the flags, and its own condition (a
/// conditional branch's).
fn wide_op(h1: u32, h2: u32, va: u64) -> (Op, bool, Cond) {
    let al = Cond::Al;
    let op1 = (h1 >> 11) & 3;
    let op2 = (h1 >> 4) & 0x7f;
    match op1 {
        1 if op2 & 0x64 == 0 => (multiple(h1, h2), false, al),
        1 if op2 & 0x64 == 4 => (dual(h1, h2), false, al),
        1 if op2 & 0x60 == 0x20 => shifted(h1, h2),
        1 => (coprocessor(h1, h2), false, al),
        2 if bit(h2, 15) => branch(h1, h2, va),
        2 if bit(h1, 9) => (plain_imm(h1, h2, va), false, al),
        2 => modified_imm(h1, h2),
        _ if op2 & 0x71 == 0 => (store(h1, h2), false, al),
        _ if op2 & 0x67 == 1 || op2 & 0x67 == 3 || op2 & 0x67 == 5 => (load(h1, h2), false, al),
        _ if op2 & 0x71 == 0x10 => (vfp::neon((h1 << 16) | h2, true), false, al),
        _ if op2 & 0x70 == 0x20 => register(h1, h2),
        _ if op2 & 0x78 == 0x30 => (mul32(h1, h2), false, al),
        _ if op2 & 0x78 == 0x38 => (long_mul(h1, h2), false, al),
        _ if op2 & 0x40 != 0 => (coprocessor(h1, h2), false, al),
        _ => (Op::Invalid, false, al),
    }
}

/// `ldm`, `stm`, `push.w` and `pop.w`.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn multiple(h1: u32, h2: u32) -> Op {
    let rn = reg(h1, 0, 4);
    let regs = u16::try_from(h2).unwrap_or(0);
    let wback = bit(h1, 5);
    let b = match (h1 >> 7) & 3 {
        1 => super::Block::Ia,
        2 => super::Block::Db,
        _ => return Op::Unknown,
    };
    if bit(h1, 4) {
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
}

/// `ldrd` and `strd`, the word, byte and halfword exclusives, and `tbb`
/// and `tbh`.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn dual(h1: u32, h2: u32) -> Op {
    let (p, u, w, l) = (bit(h1, 8), bit(h1, 7), bit(h1, 5), bit(h1, 4));
    let rn = reg(h1, 0, 4);
    let (rt, rt2) = (reg(h2, 12, 4), reg(h2, 8, 4));
    if p || w {
        let off = i32::try_from((h2 & 0xff) * 4).unwrap_or(0);
        let addr = Addr {
            base: rn,
            offset: Offset::Imm(if u { off } else { -off }),
            index: index(p, w),
        };
        return if l {
            Op::LoadDual { rt, rt2, addr }
        } else {
            Op::StoreDual { rt, rt2, addr }
        };
    }
    let base = |off: u32| at(rn, off);
    match (u, (h1 >> 4) & 3, (h2 >> 4) & 0xf) {
        (false, 0, _) => Op::StoreEx {
            width: Width::Word,
            rd: rt2,
            rt,
            addr: base((h2 & 0xff) * 4),
        },
        (false, 1, _) => Op::LoadEx {
            width: Width::Word,
            rt,
            addr: base((h2 & 0xff) * 4),
        },
        (true, 1, 0) => Op::Tb {
            half: false,
            rn,
            rm: reg(h2, 0, 4),
        },
        (true, 1, 1) => Op::Tb {
            half: true,
            rn,
            rm: reg(h2, 0, 4),
        },
        (true, 1, 4) => Op::LoadEx {
            width: Width::Byte,
            rt,
            addr: base(0),
        },
        (true, 1, 5) => Op::LoadEx {
            width: Width::Half,
            rt,
            addr: base(0),
        },
        (true, 0, 4) => Op::StoreEx {
            width: Width::Byte,
            rd: reg(h2, 0, 4),
            rt,
            addr: base(0),
        },
        (true, 0, 5) => Op::StoreEx {
            width: Width::Half,
            rd: reg(h2, 0, 4),
            rt,
            addr: base(0),
        },
        _ => Op::Unknown,
    }
}

/// The data processing over a register shifted by an immediate.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
///
/// # Returns
///
/// The operation, whether it sets the flags, and the condition (always).
fn shifted(h1: u32, h2: u32) -> (Op, bool, Cond) {
    let s = bit(h1, 4);
    let (rn, rd, rm) = (reg(h1, 0, 4), reg(h2, 8, 4), reg(h2, 0, 4));
    let imm5 = ((h2 >> 10) & 0x1c) | ((h2 >> 6) & 3);
    let (shift, amount) = imm_shift(h2 >> 4, imm5);
    let Some(kind) = t32_kind((h1 >> 5) & 0xf, rd == PC && s, rn == PC) else {
        return (Op::Unknown, false, Cond::Al);
    };
    (dp_reg(kind, rd, rn, rm, shift, amount), s, Cond::Al)
}

/// The data processing over a modified immediate.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
///
/// # Returns
///
/// The operation, whether it sets the flags, and the condition (always).
fn modified_imm(h1: u32, h2: u32) -> (Op, bool, Cond) {
    let s = bit(h1, 4);
    let (rn, rd) = (reg(h1, 0, 4), reg(h2, 8, 4));
    let imm12 = ((h1 & 0x400) << 1) | ((h2 >> 4) & 0x700) | (h2 & 0xff);
    let Some(kind) = t32_kind((h1 >> 5) & 0xf, rd == PC && s, rn == PC) else {
        return (Op::Unknown, false, Cond::Al);
    };
    let src = match (kind.arithmetic(), expand(imm12)) {
        (true, Operand::Imm { value, .. }) => Operand::Imm { value, carry: None },
        (_, other) => other,
    };
    (Op::Dp { kind, rd, rn, src }, s, Cond::Al)
}

/// The data processing over a plain immediate: `addw`, `subw`, `adr`,
/// `movw`, `movt` and the bit fields.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
/// * `va` - Its address, for `adr`.
fn plain_imm(h1: u32, h2: u32, va: u64) -> Op {
    let (rn, rd) = (reg(h1, 0, 4), reg(h2, 8, 4));
    let imm12 = ((h1 & 0x400) << 1) | ((h2 >> 4) & 0x700) | (h2 & 0xff);
    let lsb = u8::try_from(((h2 >> 10) & 0x1c) | ((h2 >> 6) & 3)).unwrap_or(0);
    let field = u8::try_from(h2 & 0x1f).unwrap_or(0);
    let pc = va.wrapping_add(4) & !3;
    match (h1 >> 4) & 0x1f {
        0x00 if rn == PC => Op::Adr {
            rd,
            target: pc.wrapping_add(u64::from(imm12)) & 0xffff_ffff,
        },
        0x00 => dp_imm(DpKind::Add, rd, rn, imm12),
        0x0a if rn == PC => Op::Adr {
            rd,
            target: pc.wrapping_sub(u64::from(imm12)) & 0xffff_ffff,
        },
        0x0a => dp_imm(DpKind::Sub, rd, rn, imm12),
        k @ (0x04 | 0x0c) => {
            let imm = u16::try_from(((h1 & 0xf) << 12) | imm12).unwrap_or(0);
            if k == 0x04 {
                Op::Movw { rd, imm }
            } else {
                Op::Movt { rd, imm }
            }
        }
        k @ (0x10 | 0x12 | 0x18 | 0x1a) if k & 2 == 0 || lsb != 0 => {
            let signed = k & 8 == 0;
            Op::Sat {
                signed,
                rd,
                rn,
                bits: if signed {
                    field.saturating_add(1)
                } else {
                    field
                },
                shift: if k & 2 == 0 { Shift::Lsl } else { Shift::Asr },
                amount: lsb,
            }
        }
        k @ (0x14 | 0x1c) => Op::Bfx {
            signed: k == 0x14,
            rd,
            rn,
            lsb,
            width: field.saturating_add(1),
        },
        0x16 => match field.checked_sub(lsb) {
            Some(d) => Op::Bfi {
                rd,
                rn: (rn != PC).then_some(rn),
                lsb,
                width: d.saturating_add(1),
            },
            None => Op::Unknown,
        },
        _ => Op::Unknown,
    }
}

/// The branches and miscellaneous control: `b.w`, the conditional
/// `b<c>.w`, `bl`, `blx` to an immediate, the hints and barriers, `udf`.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
/// * `va` - Its address.
///
/// # Returns
///
/// The operation, whether it sets the flags, and a conditional branch's
/// condition.
fn branch(h1: u32, h2: u32, va: u64) -> (Op, bool, Cond) {
    let al = Cond::Al;
    let op1 = (h2 >> 12) & 7;
    let s = (h1 >> 10) & 1;
    let (j1, j2) = ((h2 >> 13) & 1, (h2 >> 11) & 1);
    let pc = va.wrapping_add(4);
    let long = || {
        let (i1, i2) = (!(j1 ^ s) & 1, !(j2 ^ s) & 1);
        let imm = (s << 24) | (i1 << 23) | (i2 << 22) | ((h1 & 0x3ff) << 12) | ((h2 & 0x7ff) << 1);
        sext(imm, 25)
    };
    match op1 {
        0 | 2 => {
            let op = (h1 >> 4) & 0x7f;
            if op & 0x38 != 0x38 {
                let imm =
                    (s << 20) | (j2 << 19) | (j1 << 18) | ((h1 & 0x3f) << 12) | ((h2 & 0x7ff) << 1);
                return (
                    Op::B {
                        target: rel(pc, sext(imm, 21)),
                    },
                    false,
                    Cond::from_code(u8::try_from((h1 >> 6) & 0xf).unwrap_or(0xe)),
                );
            }
            let op = match op {
                0x3a | 0x3b => Op::Nop,
                0x7f if op1 == 2 => Op::Trap,
                0x38 | 0x39 if (h2 >> 8) & 0xc == 0x8 => Op::Msr { rn: reg(h1, 0, 4) },
                0x3e | 0x3f if !bit(h1, 4) => Op::Mrs { rd: reg(h2, 8, 4) },
                _ => Op::Unknown,
            };
            (op, false, al)
        }
        1 | 3 => (
            Op::B {
                target: rel(pc, long()),
            },
            false,
            al,
        ),
        4 | 6 => (
            Op::Blx {
                target: rel(pc & !3, long()),
            },
            false,
            al,
        ),
        _ => (
            Op::Bl {
                target: rel(pc, long()),
            },
            false,
            al,
        ),
    }
}

/// The stores of one register: `str`, `strb` and `strh` in every
/// addressing mode.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn store(h1: u32, h2: u32) -> Op {
    let width = match (h1 >> 5) & 3 {
        0 => Width::Byte,
        1 => Width::Half,
        2 => Width::Word,
        _ => return Op::Invalid,
    };
    let Some(addr) = single_addr(h1, h2) else {
        return Op::Unknown;
    };
    Op::Store {
        width,
        rt: reg(h2, 12, 4),
        addr,
    }
}

/// The address of a single load or store: a 12-bit positive offset, an
/// 8-bit offset in any addressing mode, or a shifted register.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
///
/// # Returns
///
/// The address, or `None` for a form outside them.
fn single_addr(h1: u32, h2: u32) -> Option<Addr> {
    let rn = reg(h1, 0, 4);
    if bit(h1, 7) {
        return Some(at(rn, h2 & 0xfff));
    }
    if bit(h2, 11) {
        let (p, u, w) = (bit(h2, 10), bit(h2, 9), bit(h2, 8));
        let off = i32::try_from(h2 & 0xff).unwrap_or(0);
        if p && u && !w {
            return Some(at(rn, h2 & 0xff));
        }
        return Some(Addr {
            base: rn,
            offset: Offset::Imm(if u { off } else { -off }),
            index: index(p, w),
        });
    }
    if (h2 >> 6) & 0x3f == 0 {
        return Some(Addr {
            base: rn,
            offset: Offset::Reg {
                rm: reg(h2, 0, 4),
                sub: false,
                shift: Shift::Lsl,
                amount: u8::try_from((h2 >> 4) & 3).unwrap_or(0),
            },
            index: Index::Offset,
        });
    }
    None
}

/// The loads of one register, the literal forms among them, and the
/// preloads.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn load(h1: u32, h2: u32) -> Op {
    let signed = bit(h1, 8);
    let width = match ((h1 >> 5) & 3, signed) {
        (0, false) => Width::Byte,
        (0, true) => Width::SByte,
        (1, false) => Width::Half,
        (1, true) => Width::SHalf,
        (2, false) => Width::Word,
        _ => return Op::Invalid,
    };
    let rt = reg(h2, 12, 4);
    let rn = reg(h1, 0, 4);
    if rt == PC && width != Width::Word {
        return Op::Nop;
    }
    let addr = if rn == PC {
        let off = i32::try_from(h2 & 0xfff).unwrap_or(0);
        Some(Addr {
            base: PC,
            offset: Offset::Imm(if bit(h1, 7) { off } else { -off }),
            index: Index::Offset,
        })
    } else {
        single_addr(h1, h2)
    };
    match addr {
        Some(addr) => Op::Load { width, rt, addr },
        None => Op::Unknown,
    }
}

/// The data processing over registers: shifts by a register, the
/// extensions, the byte reversals, `rbit` and `clz`.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
///
/// # Returns
///
/// The operation, whether it sets the flags, and the condition (always).
fn register(h1: u32, h2: u32) -> (Op, bool, Cond) {
    let al = Cond::Al;
    let op1 = (h1 >> 4) & 0xf;
    let op2 = (h2 >> 4) & 0xf;
    let (rn, rd, rm) = (reg(h1, 0, 4), reg(h2, 8, 4), reg(h2, 0, 4));
    if (h2 >> 12) & 0xf != 0xf {
        return (Op::Unknown, false, al);
    }
    if op2 == 0 && op1 & 8 == 0 {
        return (
            Op::Dp {
                kind: DpKind::Mov,
                rd,
                rn: rd,
                src: Operand::RegShift {
                    rm: rn,
                    shift: reg_shift(op1 >> 1),
                    rs: rm,
                },
            },
            bit(h1, 4),
            al,
        );
    }
    let op = match (op1, op2) {
        (0 | 1 | 4 | 5, 8..=0xf) => Op::Extend {
            signed: op1 & 1 == 0,
            bits: if op1 & 4 == 0 { 16 } else { 8 },
            rd,
            rm,
            rotate: u8::try_from(((h2 >> 4) & 3) * 8).unwrap_or(0),
            add: (rn != PC).then_some(rn),
        },
        (9, 8) => Op::Rev { rd, rm },
        (9, 9) => Op::Rev16 { rd, rm },
        (9, 0xa) => Op::Rbit { rd, rm },
        (9, 0xb) => Op::Revsh { rd, rm },
        (0xb, 8) => Op::Clz { rd, rm },
        _ => Op::Unknown,
    };
    (op, false, al)
}

/// `mul`, `mla` and `mls`.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn mul32(h1: u32, h2: u32) -> Op {
    let (rn, ra, rd, rm) = (reg(h1, 0, 4), reg(h2, 12, 4), reg(h2, 8, 4), reg(h2, 0, 4));
    match ((h1 >> 4) & 7, (h2 >> 4) & 3) {
        (0, 0) => Op::Mul {
            rd,
            rn,
            rm,
            acc: (ra != PC).then_some(ra),
            sub: false,
        },
        (0, 1) => Op::Mul {
            rd,
            rn,
            rm,
            acc: Some(ra),
            sub: true,
        },
        (5, 0) => Op::Smmul {
            rd,
            rn,
            rm,
            acc: (ra != PC).then_some(ra),
        },
        (1, nm) => Op::Smulxy {
            rd,
            rn,
            rm,
            n_top: nm & 2 != 0,
            m_top: nm & 1 != 0,
            acc: (ra != PC).then_some(ra),
        },
        _ => Op::Unknown,
    }
}

/// The long multiplies and the divides.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn long_mul(h1: u32, h2: u32) -> Op {
    let (rn, lo, hi, rm) = (reg(h1, 0, 4), reg(h2, 12, 4), reg(h2, 8, 4), reg(h2, 0, 4));
    let long = |signed, acc| Op::MulLong {
        signed,
        acc,
        lo,
        hi,
        rn,
        rm,
    };
    match ((h1 >> 4) & 7, (h2 >> 4) & 0xf) {
        (0, 0) => long(true, false),
        (2, 0) => long(false, false),
        (4, 0) => long(true, true),
        (6, 0) => long(false, true),
        (1, 0xf) => Op::Div {
            signed: true,
            rd: hi,
            rn,
            rm,
        },
        (3, 0xf) => Op::Div {
            signed: false,
            rd: hi,
            rn,
            rm,
        },
        _ => Op::Unknown,
    }
}

/// The coprocessor space: the VFP instructions ([`vfp`]) and Advanced
/// SIMD.
///
/// # Arguments
///
/// * `h1` - The first halfword.
/// * `h2` - The second.
fn coprocessor(h1: u32, h2: u32) -> Op {
    let w = (h1 << 16) | h2;
    if (h1 >> 12) & 0xf == 0xf || (h1 >> 8) & 0xf == 0xf {
        return vfp::neon(w, false);
    }
    vfp::decode(w)
}
