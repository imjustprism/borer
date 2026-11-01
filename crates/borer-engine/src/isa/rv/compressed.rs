//! The C extension: each 16-bit instruction decoded to the 32-bit
//! operation it expands to.

use super::{Alu, BrCond, FOp, Fmt, Op, Reg, SP, Width, Xlen, ZERO, rel, sext};

/// Returns bits `lo` to `lo + n - 1` of `h`.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `lo` - The lowest bit.
/// * `n` - How many bits.
fn b(h: u16, lo: u32, n: u32) -> u32 {
    (u32::from(h) >> lo) & ((1 << n) - 1)
}

/// Returns the register a five-bit field at `lo` names.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `lo` - The field's lowest bit.
fn full(h: u16, lo: u32) -> u8 {
    crate::num::lo8(u64::from(b(h, lo, 5)))
}

/// Returns the register `x8` to `x15` a three-bit field at `lo` names.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `lo` - The field's lowest bit.
fn prime(h: u16, lo: u32) -> u8 {
    crate::num::lo8(u64::from(8 + b(h, lo, 3)))
}

/// Returns the six-bit signed immediate of the CI format: bit 12 then
/// bits 6 to 2.
///
/// # Arguments
///
/// * `h` - The halfword.
fn ci_imm(h: u16) -> i64 {
    sext((b(h, 12, 1) << 5) | b(h, 2, 5), 6)
}

/// Returns the six-bit shift amount of `c.slli`, `c.srli` and `c.srai`.
///
/// # Arguments
///
/// * `h` - The halfword.
fn shamt(h: u16) -> i64 {
    i64::from((b(h, 12, 1) << 5) | b(h, 2, 5))
}

/// Decodes a compressed instruction.
///
/// # Arguments
///
/// * `h` - The halfword; its low two bits are not `11`.
/// * `va` - Its address.
/// * `xlen` - The register width, which picks the RV32 or RV64 meaning of
///   the encodings the two give different instructions.
pub(super) fn decode(h: u16, va: u64, xlen: Xlen) -> Op {
    if h == 0 {
        return Op::Invalid;
    }
    match h & 3 {
        0 => quadrant0(h, xlen),
        1 => quadrant1(h, va, xlen),
        _ => quadrant2(h, xlen),
    }
}

/// Decodes quadrant 0: the stack-pointer `addi` and the loads and stores
/// through `x8` to `x15`.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `xlen` - The register width.
fn quadrant0(h: u16, xlen: Xlen) -> Op {
    let rd = prime(h, 2);
    let rs1 = Reg::X(prime(h, 7));
    let off_w = i64::from((b(h, 10, 3) << 3) | (b(h, 6, 1) << 2) | (b(h, 5, 1) << 6));
    let off_d = i64::from((b(h, 10, 3) << 3) | (b(h, 5, 2) << 6));
    let rv64 = xlen == Xlen::X64;
    match b(h, 13, 3) {
        0 => {
            let imm =
                (b(h, 11, 2) << 4) | (b(h, 7, 4) << 6) | (b(h, 6, 1) << 2) | (b(h, 5, 1) << 3);
            if imm == 0 {
                return Op::Invalid;
            }
            Op::Imm {
                op: Alu::Add,
                rd: Reg::X(rd),
                rs1: SP,
                imm: i64::from(imm),
                word: false,
            }
        }
        1 => Op::Float(FOp::Load {
            fmt: Fmt::D,
            rd: Reg::F(rd),
            rs1,
            off: off_d,
        }),
        2 => Op::Load {
            width: Width::W,
            rd: Reg::X(rd),
            rs1,
            off: off_w,
        },
        3 if rv64 => Op::Load {
            width: Width::D,
            rd: Reg::X(rd),
            rs1,
            off: off_d,
        },
        3 => Op::Float(FOp::Load {
            fmt: Fmt::S,
            rd: Reg::F(rd),
            rs1,
            off: off_w,
        }),
        5 => Op::Float(FOp::Store {
            fmt: Fmt::D,
            rs2: Reg::F(rd),
            rs1,
            off: off_d,
        }),
        6 => Op::Store {
            width: Width::W,
            rs2: Reg::X(rd),
            rs1,
            off: off_w,
        },
        7 if rv64 => Op::Store {
            width: Width::D,
            rs2: Reg::X(rd),
            rs1,
            off: off_d,
        },
        7 => Op::Float(FOp::Store {
            fmt: Fmt::S,
            rs2: Reg::F(rd),
            rs1,
            off: off_w,
        }),
        _ => Op::Unknown,
    }
}

/// Decodes quadrant 1: the immediate forms, the register arithmetic on
/// `x8` to `x15`, `c.j`, `c.jal` and the compare-with-zero branches.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `va` - Its address.
/// * `xlen` - The register width.
fn quadrant1(h: u16, va: u64, xlen: Xlen) -> Op {
    let rd = Reg::X(full(h, 7));
    let imm = ci_imm(h);
    let imm_op = |op, rd, rs1, imm, word| Op::Imm {
        op,
        rd,
        rs1,
        imm,
        word,
    };
    match b(h, 13, 3) {
        0 => imm_op(Alu::Add, rd, rd, imm, false),
        1 if xlen == Xlen::X64 => {
            if rd == ZERO {
                return Op::Invalid;
            }
            imm_op(Alu::Add, rd, rd, imm, true)
        }
        1 | 5 => Op::Jal {
            rd: if b(h, 13, 3) == 1 { super::RA } else { ZERO },
            target: rel(xlen, va, cj_offset(h)),
        },
        2 => imm_op(Alu::Add, rd, ZERO, imm, false),
        3 if rd == SP => {
            let v = (b(h, 12, 1) << 9)
                | (b(h, 6, 1) << 4)
                | (b(h, 5, 1) << 6)
                | (b(h, 3, 2) << 7)
                | (b(h, 2, 1) << 5);
            if v == 0 {
                return Op::Invalid;
            }
            imm_op(Alu::Add, SP, SP, sext(v, 10), false)
        }
        3 => {
            if imm == 0 {
                return Op::Invalid;
            }
            Op::Lui { rd, imm: imm << 12 }
        }
        4 => arith(h, xlen),
        _ => {
            let off = (b(h, 12, 1) << 8)
                | (b(h, 10, 2) << 3)
                | (b(h, 5, 2) << 6)
                | (b(h, 3, 2) << 1)
                | (b(h, 2, 1) << 5);
            Op::Branch {
                cond: if b(h, 13, 3) == 6 {
                    BrCond::Eq
                } else {
                    BrCond::Ne
                },
                rs1: Reg::X(prime(h, 7)),
                rs2: ZERO,
                target: rel(xlen, va, sext(off, 9)),
            }
        }
    }
}

/// Returns the offset of `c.j` and `c.jal`.
///
/// # Arguments
///
/// * `h` - The halfword.
fn cj_offset(h: u16) -> i64 {
    let off = (b(h, 12, 1) << 11)
        | (b(h, 11, 1) << 4)
        | (b(h, 9, 2) << 8)
        | (b(h, 8, 1) << 10)
        | (b(h, 7, 1) << 6)
        | (b(h, 6, 1) << 7)
        | (b(h, 3, 3) << 1)
        | (b(h, 2, 1) << 5);
    sext(off, 12)
}

/// Decodes the quadrant 1 arithmetic group (`funct3` 100) on `x8` to
/// `x15`.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `xlen` - The register width.
fn arith(h: u16, xlen: Xlen) -> Op {
    let rd = Reg::X(prime(h, 7));
    let rs2 = Reg::X(prime(h, 2));
    let imm = |op, imm| Op::Imm {
        op,
        rd,
        rs1: rd,
        imm,
        word: false,
    };
    let reg = |op, word| Op::Reg3 {
        op,
        rd,
        rs1: rd,
        rs2,
        word,
    };
    let rv32_wide = xlen == Xlen::X32 && b(h, 12, 1) == 1;
    match (b(h, 10, 2), b(h, 12, 1), b(h, 5, 2)) {
        (0, ..) if !rv32_wide => imm(Alu::Srl, shamt(h)),
        (1, ..) if !rv32_wide => imm(Alu::Sra, shamt(h)),
        (2, ..) => imm(Alu::And, ci_imm(h)),
        (3, 0, 0) => reg(Alu::Sub, false),
        (3, 0, 1) => reg(Alu::Xor, false),
        (3, 0, 2) => reg(Alu::Or, false),
        (3, 0, 3) => reg(Alu::And, false),
        (3, 1, 0) if xlen == Xlen::X64 => reg(Alu::Sub, true),
        (3, 1, 1) if xlen == Xlen::X64 => reg(Alu::Add, true),
        (3, 1, _) => Op::Unknown,
        _ => Op::Invalid,
    }
}

/// Decodes quadrant 2: `c.slli`, the stack-pointer loads and stores,
/// `c.mv`, `c.add`, `c.jr`, `c.jalr` and `c.ebreak`.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `xlen` - The register width.
fn quadrant2(h: u16, xlen: Xlen) -> Op {
    let rd = full(h, 7);
    let rs2 = full(h, 2);
    let rv64 = xlen == Xlen::X64;
    let lsp_w = i64::from((b(h, 12, 1) << 5) | (b(h, 4, 3) << 2) | (b(h, 2, 2) << 6));
    let lsp_d = i64::from((b(h, 12, 1) << 5) | (b(h, 5, 2) << 3) | (b(h, 2, 3) << 6));
    let ssp_w = i64::from((b(h, 9, 4) << 2) | (b(h, 7, 2) << 6));
    let ssp_d = i64::from((b(h, 10, 3) << 3) | (b(h, 7, 3) << 6));
    match b(h, 13, 3) {
        0 if rv64 || b(h, 12, 1) == 0 => Op::Imm {
            op: Alu::Sll,
            rd: Reg::X(rd),
            rs1: Reg::X(rd),
            imm: shamt(h),
            word: false,
        },
        1 => Op::Float(FOp::Load {
            fmt: Fmt::D,
            rd: Reg::F(rd),
            rs1: SP,
            off: lsp_d,
        }),
        2 if rd != 0 => Op::Load {
            width: Width::W,
            rd: Reg::X(rd),
            rs1: SP,
            off: lsp_w,
        },
        3 if rv64 && rd != 0 => Op::Load {
            width: Width::D,
            rd: Reg::X(rd),
            rs1: SP,
            off: lsp_d,
        },
        3 if !rv64 => Op::Float(FOp::Load {
            fmt: Fmt::S,
            rd: Reg::F(rd),
            rs1: SP,
            off: lsp_w,
        }),
        4 => moves(h, rd, rs2),
        5 => Op::Float(FOp::Store {
            fmt: Fmt::D,
            rs2: Reg::F(rs2),
            rs1: SP,
            off: ssp_d,
        }),
        6 => Op::Store {
            width: Width::W,
            rs2: Reg::X(rs2),
            rs1: SP,
            off: ssp_w,
        },
        7 if rv64 => Op::Store {
            width: Width::D,
            rs2: Reg::X(rs2),
            rs1: SP,
            off: ssp_d,
        },
        7 => Op::Float(FOp::Store {
            fmt: Fmt::S,
            rs2: Reg::F(rs2),
            rs1: SP,
            off: ssp_w,
        }),
        _ => Op::Invalid,
    }
}

/// Decodes the quadrant 2 group `funct3` 100: `c.jr`, `c.mv`,
/// `c.ebreak`, `c.jalr` and `c.add`.
///
/// # Arguments
///
/// * `h` - The halfword.
/// * `rd` - The `rd`/`rs1` field.
/// * `rs2` - The `rs2` field.
fn moves(h: u16, rd: u8, rs2: u8) -> Op {
    let (r, s) = (Reg::X(rd), Reg::X(rs2));
    match (b(h, 12, 1), rd, rs2) {
        (0, 0, 0) => Op::Invalid,
        (0, _, 0) => Op::Jalr {
            rd: ZERO,
            rs1: r,
            off: 0,
        },
        (0, ..) => Op::Reg3 {
            op: Alu::Add,
            rd: r,
            rs1: ZERO,
            rs2: s,
            word: false,
        },
        (_, 0, 0) => Op::Ebreak,
        (_, _, 0) => Op::Jalr {
            rd: super::RA,
            rs1: r,
            off: 0,
        },
        _ => Op::Reg3 {
            op: Alu::Add,
            rd: r,
            rs1: r,
            rs2: s,
            word: false,
        },
    }
}
