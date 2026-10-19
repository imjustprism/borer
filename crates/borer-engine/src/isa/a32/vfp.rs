//! The VFP instructions, whose encodings A32 and T32 share below the top
//! four bits: the extension-register loads and stores, the transfers
//! between core and VFP registers, and the scalar data processing.

use super::{Addr, Cvt, FpOp, FpUn, Index, Offset, Op, PC, Reg};

/// One bit of `w`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `at` - The bit.
fn bit(w: u32, at: u32) -> bool {
    (w >> at) & 1 == 1
}

/// A core register field of `w` starting at bit `at`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `at` - The field's lowest bit.
fn core(w: u32, at: u32) -> Reg {
    Reg::R(u8::try_from((w >> at) & 0xf).unwrap_or(0))
}

/// A VFP register from a four-bit field and its extra bit: a single is
/// `field:extra`, a double `extra:field`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `at` - Where the four-bit field starts.
/// * `extra` - Where the extra bit is.
/// * `double` - Whether the register is a double.
fn vreg(w: u32, at: u32, extra: u32, double: bool) -> Reg {
    let field = u8::try_from((w >> at) & 0xf).unwrap_or(0);
    let x = u8::from(bit(w, extra));
    if double {
        Reg::D((x << 4) | field)
    } else {
        Reg::S((field << 1) | x)
    }
}

/// Decodes a word of the coprocessor space.
///
/// It is [`super::arm`]'s `op1` 110 or 111 but `svc`, which the VFP
/// instructions live in for coprocessors 10 and 11; T32 hands its
/// coprocessor words over with the same layout.
///
/// # Arguments
///
/// * `w` - The word; bits 31 to 28 are not read.
///
/// # Returns
///
/// The VFP instruction, [`Op::Neon`] for an Advanced SIMD transfer, and
/// [`Op::Unknown`] for another coprocessor or a form not modeled.
pub(super) fn decode(w: u32) -> Op {
    if (w >> 9) & 7 != 5 {
        return Op::Unknown;
    }
    let double = bit(w, 8);
    if (w >> 25) & 7 == 6 {
        return transfer(w, double);
    }
    if !bit(w, 24) && bit(w, 4) {
        return core_move(w, double);
    }
    if bit(w, 24) || bit(w, 4) {
        return Op::Unknown;
    }
    arith(w, double)
}

/// The extension-register loads and stores (`vldr`, `vstr`, `vldm`,
/// `vstm`, `vpush`, `vpop`) and the 64-bit transfers between two core
/// registers and a double (`vmov r0, r1, d0`).
///
/// # Arguments
///
/// * `w` - The word.
/// * `double` - The registers are doubles.
fn transfer(w: u32, double: bool) -> Op {
    let (p, u, wb, l) = (bit(w, 24), bit(w, 23), bit(w, 21), bit(w, 20));
    let rn = core(w, 16);
    let vd = vreg(w, 12, 22, double);
    if (w >> 21) & 0xf == 2 {
        if !double || (w >> 4) & 0xd != 1 {
            return Op::Unknown;
        }
        return Op::VmovPair {
            to_core: l,
            rt: core(w, 12),
            rt2: core(w, 16),
            dm: vreg(w, 0, 5, true),
        };
    }
    let imm8 = u8::try_from(w & 0xff).unwrap_or(0);
    if p && !wb {
        let off = i32::from(imm8) * 4;
        let addr = Addr {
            base: rn,
            offset: Offset::Imm(if u { off } else { -off }),
            index: Index::Offset,
        };
        return if l {
            Op::VLoad { vd, addr }
        } else {
            Op::VStore { vd, addr }
        };
    }
    if p == u || (p && !wb) || rn == PC {
        return Op::Unknown;
    }
    let count = if double { imm8 / 2 } else { imm8 };
    if count == 0 {
        return Op::Unknown;
    }
    if l {
        Op::VLdm {
            rn,
            first: vd,
            count,
            wback: wb,
            db: p,
        }
    } else {
        Op::VStm {
            rn,
            first: vd,
            count,
            wback: wb,
            db: p,
        }
    }
}

/// The 8-, 16- and 32-bit transfers between a core register and a VFP
/// register or `FPSCR`: `vmov r0, s0`, `vmov s0, r0`, `vmrs` and `vmsr`;
/// the lane moves and `vdup` are Advanced SIMD.
///
/// # Arguments
///
/// * `w` - The word.
/// * `double` - Bit 8: a lane move.
fn core_move(w: u32, double: bool) -> Op {
    let rt = core(w, 12);
    match ((w >> 21) & 7, bit(w, 20)) {
        (0, to_core) if !double => Op::VmovCore {
            to_core,
            rt,
            sn: vreg(w, 16, 7, false),
        },
        (7, true) if !double && (w >> 16) & 0xf == 1 => Op::Vmrs { rt },
        (7, false) if !double && (w >> 16) & 0xf == 1 => Op::Vmsr { rt },
        _ => Op::Neon {
            core: bit(w, 20).then_some(rt),
            base: None,
            stores: false,
        },
    }
}

/// An Advanced SIMD instruction outside the core moves: what its effect
/// on the core registers and memory is, which the engine needs even
/// where it does not model the instruction.
///
/// # Arguments
///
/// * `w` - The word, in the A32 layout: a T32 word's first halfword
///   above its second.
/// * `element` - It is an element or structure load or store, whose base
///   (bits 19 to 16) is written back unless bits 3 to 0 are all set, and
///   which stores unless bit 21 is set.
pub(super) fn neon(w: u32, element: bool) -> Op {
    let rn = core(w, 16);
    Op::Neon {
        core: None,
        base: (element && w & 0xf != 0xf).then_some(rn),
        stores: element && !bit(w, 21),
    }
}

/// The VFP data processing: the arithmetic, the immediate moves, the
/// register moves and sign operations, the compares and the conversions.
///
/// # Arguments
///
/// * `w` - The word.
/// * `double` - The operation is on doubles.
fn arith(w: u32, double: bool) -> Op {
    let opc1 = ((w >> 21) & 4) | ((w >> 20) & 3);
    let neg = bit(w, 6);
    let vd = vreg(w, 12, 22, double);
    let vn = vreg(w, 16, 7, double);
    let vm = vreg(w, 0, 5, double);
    let bin = |op: FpOp| Op::FpBin { op, vd, vn, vm };
    match opc1 {
        0 => bin(if neg { FpOp::Mls } else { FpOp::Mla }),
        1 => bin(if neg { FpOp::Nmla } else { FpOp::Nmls }),
        2 => bin(if neg { FpOp::Nmul } else { FpOp::Mul }),
        3 => bin(if neg { FpOp::Sub } else { FpOp::Add }),
        4 if !neg => bin(FpOp::Div),
        5 => bin(if neg { FpOp::Fnma } else { FpOp::Fnms }),
        6 => bin(if neg { FpOp::Fms } else { FpOp::Fma }),
        7 => other(w, double, vd, vm),
        _ => Op::Unknown,
    }
}

/// The VFP data-processing words of `opc1` 1x11: the immediate moves, the
/// one-source operations, the compares and the conversions.
///
/// # Arguments
///
/// * `w` - The word.
/// * `double` - Bit 8.
/// * `vd` - The destination at that precision.
/// * `vm` - The source at that precision.
fn other(w: u32, double: bool, vd: Reg, vm: Reg) -> Op {
    if !bit(w, 6) {
        return Op::FpImm {
            vd,
            imm8: u8::try_from(((w >> 12) & 0xf0) | (w & 0xf)).unwrap_or(0),
        };
    }
    let op7 = bit(w, 7);
    let un = |op: FpUn| Op::FpUn { op, vd, vm };
    match (w >> 16) & 0xf {
        0 => un(if op7 { FpUn::Abs } else { FpUn::Mov }),
        1 => un(if op7 { FpUn::Sqrt } else { FpUn::Neg }),
        4 => Op::FpCmp { vd, vm: Some(vm) },
        5 if w & 0x2f == 0 => Op::FpCmp { vd, vm: None },
        7 if op7 => Op::Vcvt {
            cvt: if double {
                Cvt::DoubleToSingle
            } else {
                Cvt::SingleToDouble
            },
            vd: vreg(w, 12, 22, !double),
            vm,
        },
        8 => Op::Vcvt {
            cvt: if op7 {
                Cvt::SignedToFloat
            } else {
                Cvt::UnsignedToFloat
            },
            vd,
            vm: vreg(w, 0, 5, false),
        },
        opc2 @ (0xc | 0xd) => Op::Vcvt {
            cvt: match (opc2 == 0xd, op7) {
                (true, true) => Cvt::FloatToSigned,
                (false, true) => Cvt::FloatToUnsigned,
                (true, false) => Cvt::FloatToSignedR,
                (false, false) => Cvt::FloatToUnsignedR,
            },
            vd: vreg(w, 12, 22, false),
            vm,
        },
        _ => Op::Unknown,
    }
}
