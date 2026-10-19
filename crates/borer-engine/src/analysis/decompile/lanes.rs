//! Which vector registers a function only ever reads as a single.
//!
//! A legacy scalar single (`addss`, `cvtsi2ss`, `movss xmm, xmm`) replaces
//! the low 32 bits of its destination and keeps the bits above, so the
//! lifter spells it as a merge of the new lane into the old register,
//! `(v & 0xffffffff00000000) | (e & 0xffffffff)`: an integer operation on
//! a float's bits, which C cannot write and which leaves the register an
//! integer. When nothing in the function reads those kept bits, they are
//! dead and the register holds just the single.
//!
//! This is solved once over the whole function, flow-insensitively, like a
//! type: every instruction says how many low bits of each vector register
//! it reads (a single's 32, a double's 64, the whole register), and a copy
//! or a lane-wise operation between two registers joins them, since the
//! bits of one flow into the other. A register whose joined reads all stop
//! at 32 bits needs nothing above its single ([`Lanes::read`]). An
//! instruction this does not know reads the whole of every vector register
//! it uses, so a guess never drops a bit something reads.

use crate::isa::x86::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpKind, Register,
};

/// Number of vector registers tracked, `xmm0` to `xmm31`.
const REGS: usize = 32;

/// Width in bits of the whole register: what an unknown access reads.
const WHOLE: u8 = 128;

/// The vector registers a call may pass arguments in, which it reads whole.
const CALL_ARGS: usize = 8;

/// The vector registers solved over one function, a bit per register.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct Lanes {
    /// Bit `n` set when nothing reads `xmm{n}` above its low 32 bits.
    pub(super) read: u32,
}

/// Solves the vector registers of a function.
///
/// # Arguments
///
/// * `code` - Each block's instructions.
/// * `ret_float` - The width in bits of the float the function returns in
///   `xmm0`, or `None` when it returns none there.
pub(super) fn solve(code: &[Vec<Instruction>], ret_float: Option<u8>) -> Lanes {
    let mut parent: [usize; REGS] = std::array::from_fn(|i| i);
    let mut read = [0u8; REGS];
    let mut info = InstructionInfoFactory::new();
    for i in code.iter().flatten() {
        match uses(i) {
            Some(us) => {
                for u in us {
                    match u {
                        Use::Read(r, w) => read[r] = read[r].max(w),
                        Use::Join(a, b) => {
                            let (ra, rb) = (root(&parent, a), root(&parent, b));
                            parent[ra] = rb;
                        }
                    }
                }
            }
            None => {
                for u in info.info(i).used_registers() {
                    if let Some(r) = index(u.register()) {
                        read[r] = WHOLE;
                    }
                }
            }
        }
        match i.flow_control() {
            FlowControl::Call | FlowControl::IndirectCall => {
                for r in read.iter_mut().take(CALL_ARGS) {
                    *r = WHOLE;
                }
            }
            FlowControl::Return => {
                if let Some(w) = ret_float {
                    read[0] = read[0].max(w);
                }
            }
            FlowControl::Next
            | FlowControl::UnconditionalBranch
            | FlowControl::IndirectBranch
            | FlowControl::ConditionalBranch
            | FlowControl::Interrupt
            | FlowControl::XbeginXabortXend
            | FlowControl::Exception => {}
        }
    }
    let mut widest = [0u8; REGS];
    for r in 0..REGS {
        let top = root(&parent, r);
        widest[top] = widest[top].max(read[r]);
    }
    Lanes {
        read: (0..REGS)
            .filter(|&r| widest[root(&parent, r)] <= 32)
            .fold(0u32, |m, r| m | (1 << r)),
    }
}

/// What one instruction does with a vector register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Use {
    /// It reads the register's low bits, this many.
    Read(usize, u8),
    /// The bits of one register flow into the other.
    Join(usize, usize),
}

/// Finds a register's representative.
///
/// # Arguments
///
/// * `parent` - Each register's parent in the union-find forest.
/// * `r` - The register.
///
/// # Returns
///
/// The root of its tree.
fn root(parent: &[usize; REGS], mut r: usize) -> usize {
    while let Some(&p) = parent.get(r).filter(|&&p| p != r) {
        r = p;
    }
    r
}

/// Returns a vector register's number, `xmm`, `ymm` or `zmm` alike.
///
/// # Arguments
///
/// * `r` - Any register.
///
/// # Returns
///
/// The number, or `None` for a register that is no vector register.
fn index(r: Register) -> Option<usize> {
    (r.is_xmm() || r.is_ymm() || r.is_zmm())
        .then(|| r.number())
        .filter(|&n| n < REGS)
}

/// Returns the vector register an operand names.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `op` - The operand's position.
fn reg(i: &Instruction, op: u32) -> Option<usize> {
    (i.op_kind(op) == OpKind::Register)
        .then(|| index(i.op_register(op)))
        .flatten()
}

/// Says what an instruction does with the vector registers it names.
///
/// A legacy scalar operation reads its source at the scalar's width and
/// keeps its destination's bits above the lane in the destination itself,
/// which reads nothing. The VEX form takes those bits from its first source
/// instead, which joins the two. A move to a vector register from memory or
/// a general register writes it whole; one out of a vector register reads
/// the bits it moves. A copy or a lane-wise logical operation between two
/// registers joins them, and with itself it zeroes or keeps the register.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// The uses, or `None` for an instruction this does not model, which reads
/// every vector register it uses whole.
fn uses(i: &Instruction) -> Option<Vec<Use>> {
    let mn = i.mnemonic();
    let n = i.op_count();
    let regs: Vec<Option<usize>> = (0..n).map(|op| reg(i, op)).collect();
    let at = |op: usize| regs.get(op).copied().flatten();
    if regs.iter().all(Option::is_none) {
        return Some(Vec::new());
    }
    let reads = |from: usize, w: u8| -> Vec<Use> {
        (from..regs.len())
            .filter_map(|op| Some(Use::Read(at(op)?, w)))
            .collect()
    };
    let out = match mn {
        Mnemonic::Comiss
        | Mnemonic::Ucomiss
        | Mnemonic::Comisd
        | Mnemonic::Ucomisd
        | Mnemonic::Vcomiss
        | Mnemonic::Vucomiss
        | Mnemonic::Vcomisd
        | Mnemonic::Vucomisd
        | Mnemonic::Cvttss2si
        | Mnemonic::Cvtss2si
        | Mnemonic::Cvttsd2si
        | Mnemonic::Cvtsd2si
        | Mnemonic::Vcvttss2si
        | Mnemonic::Vcvtss2si
        | Mnemonic::Vcvttsd2si
        | Mnemonic::Vcvtsd2si => reads(0, source_width(mn)?),
        Mnemonic::Addss
        | Mnemonic::Subss
        | Mnemonic::Mulss
        | Mnemonic::Divss
        | Mnemonic::Minss
        | Mnemonic::Maxss
        | Mnemonic::Sqrtss
        | Mnemonic::Cvtss2sd
        | Mnemonic::Cvtsi2ss
        | Mnemonic::Cvtsi2sd
        | Mnemonic::Addsd
        | Mnemonic::Subsd
        | Mnemonic::Mulsd
        | Mnemonic::Divsd
        | Mnemonic::Minsd
        | Mnemonic::Maxsd
        | Mnemonic::Sqrtsd
        | Mnemonic::Cvtsd2ss
            if n == 2 =>
        {
            at(0)?;
            reads(1, source_width(mn)?)
        }
        Mnemonic::Vaddss
        | Mnemonic::Vsubss
        | Mnemonic::Vmulss
        | Mnemonic::Vdivss
        | Mnemonic::Vminss
        | Mnemonic::Vmaxss
        | Mnemonic::Vsqrtss
        | Mnemonic::Vcvtss2sd
        | Mnemonic::Vcvtsi2ss
        | Mnemonic::Vcvtsi2sd
        | Mnemonic::Vaddsd
        | Mnemonic::Vsubsd
        | Mnemonic::Vmulsd
        | Mnemonic::Vdivsd
        | Mnemonic::Vminsd
        | Mnemonic::Vmaxsd
        | Mnemonic::Vsqrtsd
        | Mnemonic::Vcvtsd2ss
        | Mnemonic::Vmovss
        | Mnemonic::Vmovsd
            if n == 3 =>
        {
            let (d, upper) = (at(0)?, at(1)?);
            let mut us = vec![Use::Join(d, upper)];
            us.extend(reads(1, source_width(mn)?));
            us
        }
        Mnemonic::Movss | Mnemonic::Movsd | Mnemonic::Vmovss | Mnemonic::Vmovsd if n == 2 => {
            let w = result_width(mn)?;
            match (at(0), at(1)) {
                (Some(_) | None, Some(s)) => vec![Use::Read(s, w)],
                (Some(_), None) => Vec::new(),
                (None, None) => return None,
            }
        }
        Mnemonic::Movd | Mnemonic::Vmovd | Mnemonic::Movq | Mnemonic::Vmovq if n == 2 => {
            let w = if matches!(mn, Mnemonic::Movd | Mnemonic::Vmovd) {
                32
            } else {
                64
            };
            at(1).map(|s| Use::Read(s, w)).into_iter().collect()
        }
        Mnemonic::Movaps
        | Mnemonic::Movapd
        | Mnemonic::Movups
        | Mnemonic::Movupd
        | Mnemonic::Movdqa
        | Mnemonic::Movdqu
        | Mnemonic::Vmovaps
        | Mnemonic::Vmovapd
        | Mnemonic::Vmovups
        | Mnemonic::Vmovupd
        | Mnemonic::Vmovdqa
        | Mnemonic::Vmovdqu
            if n == 2 =>
        {
            match (at(0), at(1)) {
                (Some(d), Some(s)) => vec![Use::Join(d, s)],
                (None, Some(s)) => vec![Use::Read(s, WHOLE)],
                (Some(_), None) => Vec::new(),
                (None, None) => return None,
            }
        }
        Mnemonic::Xorps
        | Mnemonic::Xorpd
        | Mnemonic::Andps
        | Mnemonic::Andpd
        | Mnemonic::Andnps
        | Mnemonic::Andnpd
        | Mnemonic::Orps
        | Mnemonic::Orpd
        | Mnemonic::Pxor
        | Mnemonic::Pand
        | Mnemonic::Por
        | Mnemonic::Vxorps
        | Mnemonic::Vxorpd
        | Mnemonic::Vandps
        | Mnemonic::Vandpd
        | Mnemonic::Vandnps
        | Mnemonic::Vandnpd
        | Mnemonic::Vorps
        | Mnemonic::Vorpd
        | Mnemonic::Vpxor
        | Mnemonic::Vpand
        | Mnemonic::Vpor => {
            let d = at(0)?;
            let zero = matches!(
                mn,
                Mnemonic::Xorps
                    | Mnemonic::Xorpd
                    | Mnemonic::Pxor
                    | Mnemonic::Vxorps
                    | Mnemonic::Vxorpd
                    | Mnemonic::Vpxor
            ) && regs.iter().skip(1).all(|r| *r == Some(d));
            if zero {
                Vec::new()
            } else {
                regs.iter()
                    .skip(1)
                    .flatten()
                    .map(|&s| Use::Join(d, s))
                    .collect()
            }
        }
        _ => return None,
    };
    Some(out)
}

/// Returns the width in bits a scalar instruction reads its vector source
/// at: a single's 32, a double's 64.
///
/// # Arguments
///
/// * `mn` - The mnemonic.
///
/// # Returns
///
/// The width, or `None` for a mnemonic that is no scalar operation.
fn source_width(mn: Mnemonic) -> Option<u8> {
    match mn {
        Mnemonic::Cvtss2sd | Mnemonic::Vcvtss2sd => Some(32),
        Mnemonic::Cvtsd2ss | Mnemonic::Vcvtsd2ss => Some(64),
        Mnemonic::Cvtsi2ss | Mnemonic::Cvtsi2sd | Mnemonic::Vcvtsi2ss | Mnemonic::Vcvtsi2sd => {
            Some(WHOLE)
        }
        Mnemonic::Comiss
        | Mnemonic::Ucomiss
        | Mnemonic::Vcomiss
        | Mnemonic::Vucomiss
        | Mnemonic::Cvttss2si
        | Mnemonic::Cvtss2si
        | Mnemonic::Vcvttss2si
        | Mnemonic::Vcvtss2si => Some(32),
        Mnemonic::Comisd
        | Mnemonic::Ucomisd
        | Mnemonic::Vcomisd
        | Mnemonic::Vucomisd
        | Mnemonic::Cvttsd2si
        | Mnemonic::Cvtsd2si
        | Mnemonic::Vcvttsd2si
        | Mnemonic::Vcvtsd2si => Some(64),
        _ => result_width(mn),
    }
}

/// Returns the width in bits of the float a scalar instruction writes to
/// its destination's low lane: a single's 32, a double's 64.
///
/// # Arguments
///
/// * `mn` - The mnemonic.
///
/// # Returns
///
/// The width, or `None` for a mnemonic that writes no scalar float.
fn result_width(mn: Mnemonic) -> Option<u8> {
    Some(match mn {
        Mnemonic::Addss
        | Mnemonic::Subss
        | Mnemonic::Mulss
        | Mnemonic::Divss
        | Mnemonic::Minss
        | Mnemonic::Maxss
        | Mnemonic::Sqrtss
        | Mnemonic::Cvtsd2ss
        | Mnemonic::Cvtsi2ss
        | Mnemonic::Movss
        | Mnemonic::Vaddss
        | Mnemonic::Vsubss
        | Mnemonic::Vmulss
        | Mnemonic::Vdivss
        | Mnemonic::Vminss
        | Mnemonic::Vmaxss
        | Mnemonic::Vsqrtss
        | Mnemonic::Vcvtsd2ss
        | Mnemonic::Vcvtsi2ss
        | Mnemonic::Vmovss => 32,
        Mnemonic::Addsd
        | Mnemonic::Subsd
        | Mnemonic::Mulsd
        | Mnemonic::Divsd
        | Mnemonic::Minsd
        | Mnemonic::Maxsd
        | Mnemonic::Sqrtsd
        | Mnemonic::Cvtss2sd
        | Mnemonic::Cvtsi2sd
        | Mnemonic::Movsd
        | Mnemonic::Vaddsd
        | Mnemonic::Vsubsd
        | Mnemonic::Vmulsd
        | Mnemonic::Vdivsd
        | Mnemonic::Vminsd
        | Mnemonic::Vmaxsd
        | Mnemonic::Vsqrtsd
        | Mnemonic::Vcvtss2sd
        | Mnemonic::Vcvtsi2sd
        | Mnemonic::Vmovsd => 64,
        _ => return None,
    })
}
