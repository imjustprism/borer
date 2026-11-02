//! Which registers a RISC-V instruction reads and writes, and a register's
//! one-byte code.

use super::{CsrSrc, FOp, Insn, Op, Reg, ZERO};

/// The registers an instruction reads and writes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Registers {
    /// The registers read; `x0` never among them.
    pub reads: Vec<Reg>,
    /// The registers written; `x0` never among them.
    pub writes: Vec<Reg>,
}

/// Returns a register's one-byte code: `x0` to `x31` are 0 to 31, `f0` to
/// `f31` are 32 to 63.
///
/// # Arguments
///
/// * `r` - The register.
#[must_use]
pub fn code(r: Reg) -> u8 {
    match r {
        Reg::X(n) => n & 31,
        Reg::F(n) => 32 + (n & 31),
    }
}

/// Returns the register a [`code`] names.
///
/// # Arguments
///
/// * `c` - The code.
///
/// # Returns
///
/// The register, or `None` for a code past `f31`.
#[must_use]
pub fn from_code(c: u8) -> Option<Reg> {
    match c {
        0..=31 => Some(Reg::X(c)),
        32..=63 => Some(Reg::F(c - 32)),
        _ => None,
    }
}

impl Insn {
    /// Returns the registers the instruction reads and writes, as its
    /// operands name them; `x0` is left out of both.
    ///
    /// An instruction the engine does not model reads and writes nothing
    /// it can name.
    #[must_use]
    pub fn registers(&self) -> Registers {
        let (reads, writes): (Vec<Reg>, Vec<Reg>) = match self.op {
            Op::Lui { rd, .. } | Op::Auipc { rd, .. } | Op::Jal { rd, .. } => (vec![], vec![rd]),
            Op::Jalr { rd, rs1, .. }
            | Op::Load { rd, rs1, .. }
            | Op::Imm { rd, rs1, .. }
            | Op::Lr { rd, rs1, .. } => (vec![rs1], vec![rd]),
            Op::Branch { rs1, rs2, .. } | Op::Store { rs1, rs2, .. } => (vec![rs1, rs2], vec![]),
            Op::Reg3 { rd, rs1, rs2, .. }
            | Op::Sc { rd, rs1, rs2, .. }
            | Op::Amo { rd, rs1, rs2, .. } => (vec![rs1, rs2], vec![rd]),
            Op::Csr { rd, src, .. } => match src {
                CsrSrc::Reg(r) => (vec![r], vec![rd]),
                CsrSrc::Imm(_) => (vec![], vec![rd]),
            },
            Op::Float(f) => float(f),
            Op::Fence { .. }
            | Op::FenceI
            | Op::Ecall
            | Op::Ebreak
            | Op::TrapRet
            | Op::System
            | Op::Unknown
            | Op::Invalid => (vec![], vec![]),
        };
        let named = |v: Vec<Reg>| v.into_iter().filter(|r| *r != ZERO).collect();
        Registers {
            reads: named(reads),
            writes: named(writes),
        }
    }
}

/// Returns the registers a float instruction reads and writes.
///
/// # Arguments
///
/// * `f` - The operation.
fn float(f: FOp) -> (Vec<Reg>, Vec<Reg>) {
    match f {
        FOp::Load { rd, rs1, .. }
        | FOp::Sqrt { rd, rs1, .. }
        | FOp::Class { rd, rs1, .. }
        | FOp::ToInt { rd, rs1, .. }
        | FOp::FromInt { rd, rs1, .. }
        | FOp::Convert { rd, rs1, .. }
        | FOp::MvToInt { rd, rs1, .. }
        | FOp::MvFromInt { rd, rs1, .. } => (vec![rs1], vec![rd]),
        FOp::Store { rs1, rs2, .. } => (vec![rs1, rs2], vec![]),
        FOp::Arith { rd, rs1, rs2, .. } | FOp::Cmp { rd, rs1, rs2, .. } => {
            (vec![rs1, rs2], vec![rd])
        }
        FOp::Fused {
            rd, rs1, rs2, rs3, ..
        } => (vec![rs1, rs2, rs3], vec![rd]),
    }
}
