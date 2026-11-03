//! The A extension for the RISC-V lifter: load-reserved, store-conditional
//! and the atomic memory operations.
//!
//! One thread observes no reservation and no ordering, so a load-reserved
//! is a load, a store-conditional is a store that succeeds, writing 0, as
//! the emulator runs it, and an atomic memory operation reads the old
//! value into a temporary, stores its operation of that value and `rs2`,
//! then hands the old value to `rd`. A word sign-extends into an RV64
//! register, as a `lw` does.

use super::super::expr::{Cc, Cond, Expr, Flags, Op, fold, sign_extend, ternary};
use super::Lift;
use super::step::access;
use crate::isa::rv::{AmoOp, Op as ROp, Reg, Width, Xlen};
use crate::isa::x86::ConditionCode;

impl Lift<'_, '_> {
    /// Lifts `lr`, `sc` or an `amo`; any other operation is left alone.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    pub(super) fn atomic(&mut self, op: ROp) {
        match op {
            ROp::Lr { width, rd, rs1, .. } => self.load_reserved(width, rd, rs1),
            ROp::Sc {
                width,
                rd,
                rs1,
                rs2,
                ..
            } => self.store_conditional(width, (rd, rs1, rs2)),
            ROp::Amo {
                op,
                width,
                rd,
                rs1,
                rs2,
                ..
            } => self.amo(op, width, (rd, rs1, rs2)),
            ROp::Lui { .. }
            | ROp::Auipc { .. }
            | ROp::Jal { .. }
            | ROp::Jalr { .. }
            | ROp::Branch { .. }
            | ROp::Load { .. }
            | ROp::Store { .. }
            | ROp::Imm { .. }
            | ROp::Reg3 { .. }
            | ROp::Fence { .. }
            | ROp::FenceI
            | ROp::Ecall
            | ROp::Ebreak
            | ROp::Csr { .. }
            | ROp::Float(_)
            | ROp::TrapRet
            | ROp::System
            | ROp::Unknown
            | ROp::Invalid => {}
        }
    }

    /// Returns a value read from memory as an `lr` or `amo` of `width`
    /// gives it to a register: a word sign-extended on RV64.
    ///
    /// # Arguments
    ///
    /// * `v` - The value read.
    /// * `width` - What was read.
    fn widened(&self, v: Expr, width: Width) -> Expr {
        if width == Width::W && self.xlen == Xlen::X64 {
            sign_extend(v, 32)
        } else {
            v
        }
    }

    /// Lifts `lr.w` and `lr.d`: a load.
    ///
    /// # Arguments
    ///
    /// * `width` - What it reads.
    /// * `rd` - The destination.
    /// * `rs1` - The address.
    fn load_reserved(&mut self, width: Width, rd: Reg, rs1: Reg) {
        let v = self.ex.read_at(self.get(rs1), access(width));
        let v = self.widened(v, width);
        self.write(rd, v);
    }

    /// Lifts `sc.w` and `sc.d`: the store, then status 0 in `rd`.
    ///
    /// # Arguments
    ///
    /// * `width` - What it writes.
    /// * `(rd, rs1, rs2)` - The status, the address and the value.
    fn store_conditional(&mut self, width: Width, (rd, rs1, rs2): (Reg, Reg, Reg)) {
        let ty = access(width);
        let v = self.narrowed(rs2, ty);
        self.ex.store_at(self.get(rs1), ty, v);
        self.write(rd, Expr::Const(0));
    }

    /// Lifts an atomic memory operation: memory takes `op` of its old
    /// value and `rs2`, and `rd` the old value.
    ///
    /// The old value is a temporary read before anything is written, so
    /// `rd` naming `rs1` or `rs2` still sees what the instruction read.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `width` - What it moves.
    /// * `(rd, rs1, rs2)` - The old value's destination, the address and
    ///   the operand.
    fn amo(&mut self, op: AmoOp, width: Width, (rd, rs1, rs2): (Reg, Reg, Reg)) {
        let ty = access(width);
        let n = ty.bits();
        let at = self.get(rs1);
        let loaded = self.ex.read_at(at.clone(), ty);
        let old = self.ex.tmp_of(&loaded, ty);
        let s = self.narrowed(rs2, ty);
        let pick = |cc, kept: Expr, other: Expr| {
            ternary(
                Cond {
                    cc: Cc(cc),
                    flags: Flags::Cmp(kept.clone(), other.clone(), n),
                },
                kept,
                other,
            )
        };
        let new = match op {
            AmoOp::Swap => s,
            AmoOp::Add => fold(Op::Add, old.clone(), s, n),
            AmoOp::Xor => fold(Op::Xor, old.clone(), s, n),
            AmoOp::And => fold(Op::And, old.clone(), s, n),
            AmoOp::Or => fold(Op::Or, old.clone(), s, n),
            AmoOp::Min => pick(ConditionCode::le, old.clone(), s),
            AmoOp::Max => pick(ConditionCode::ge, old.clone(), s),
            AmoOp::Minu => pick(ConditionCode::be, old.clone(), s),
            AmoOp::Maxu => pick(ConditionCode::ae, old.clone(), s),
        };
        self.ex.store_at(at, ty, new);
        let old = self.widened(old, width);
        self.write(rd, old);
    }
}
