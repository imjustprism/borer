//! The integer operations for the RISC-V lifter, and the loads and stores.
//!
//! Each handler computes every value before it writes anything and answers
//! `None` for a form it does not model, which leaves the instruction
//! unmodeled. Values are folded at the register width; a `w` form folds
//! at 32 bits and sign-extends its result, a comparison is the 0 or 1 its
//! condition holds, and a load sign-extends or zero-extends as its width
//! says.

use super::super::expr::{
    Cc, Cond, Expr, Flags, Op, Ty, fold, mask, mask_bits, sign_extend, ternary,
};
use super::{Lift, offset};
use crate::isa::rv::{Alu, Insn, Op as ROp, Width, Xlen};
use crate::isa::x86::ConditionCode;

/// The type a load or store of `width` moves.
///
/// # Arguments
///
/// * `width` - What it moves.
fn access(width: Width) -> Ty {
    match width {
        Width::B | Width::Bu => Ty::U8,
        Width::H | Width::Hu => Ty::U16,
        Width::W | Width::Wu => Ty::U32,
        Width::D => Ty::U64,
    }
}

/// The 0 or 1 a comparison of two values holds.
///
/// # Arguments
///
/// * `cc` - The comparison.
/// * `a` - The left value.
/// * `b` - The right value.
/// * `bits` - Their width.
fn truth(cc: ConditionCode, a: Expr, b: Expr, bits: u8) -> Expr {
    Expr::Cond(Box::new(Cond {
        cc: Cc(cc),
        flags: Flags::Cmp(a, b, bits),
    }))
}

/// Returns a division or remainder as RISC-V defines it.
///
/// A zero divisor gives all ones for a quotient and the dividend for a
/// remainder, and a signed divisor of -1 the negated dividend (which wraps
/// for the most negative one) and a zero remainder, where C leaves both
/// undefined, so a divisor not known to be neither is tested.
///
/// # Arguments
///
/// * `op` - [`Op::Div`], [`Op::SDiv`], [`Op::Rem`] or [`Op::SRem`].
/// * `x` - The dividend, as the operation reads it.
/// * `y` - The divisor, as the operation reads it.
/// * `bits` - The width.
fn divide(op: Op, x: Expr, y: Expr, bits: u8) -> Expr {
    let quotient = matches!(op, Op::Div | Op::SDiv);
    let by_zero = if quotient {
        Expr::Const(mask_bits(bits))
    } else {
        x.clone()
    };
    let by_minus_one = if quotient {
        fold(Op::Sub, Expr::Const(0), x.clone(), bits)
    } else {
        Expr::Const(0)
    };
    let signed = matches!(op, Op::SDiv | Op::SRem);
    let all_ones = mask_bits(bits);
    if let Expr::Const(c) = y {
        return if c & all_ones == 0 {
            by_zero
        } else if signed && c & all_ones == all_ones {
            by_minus_one
        } else {
            fold(op, x, y, bits)
        };
    }
    let is = |k: u64| Cond {
        cc: Cc(ConditionCode::e),
        flags: Flags::Cmp(y.clone(), Expr::Const(k), bits),
    };
    let v = fold(op, x, y.clone(), bits);
    if signed {
        ternary(is(0), by_zero, ternary(is(all_ones), by_minus_one, v))
    } else {
        ternary(is(0), by_zero, v)
    }
}

impl Lift<'_, '_> {
    /// Lifts an instruction that does not move control.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn step(&mut self, i: &Insn) {
        let w = self.w();
        let done = match i.op {
            ROp::Lui { rd, imm } => {
                let v = self.xlen.addr(imm.cast_unsigned());
                self.write(rd, Expr::Const(v));
                Some(())
            }
            ROp::Auipc { rd, target } => {
                self.write(rd, Expr::Const(target));
                Some(())
            }
            ROp::Imm {
                op,
                rd,
                rs1,
                imm,
                word,
            } => {
                let a = self.get(rs1);
                let b = Expr::Const(self.xlen.addr(imm.cast_unsigned()));
                let v = if op == Alu::Add && !word {
                    Some(offset(a, imm, w))
                } else {
                    self.alu(op, a, b, word)
                };
                v.map(|v| self.write(rd, v))
            }
            ROp::Reg3 {
                op,
                rd,
                rs1,
                rs2,
                word,
            } => {
                let (a, b) = (self.get(rs1), self.get(rs2));
                self.alu(op, a, b, word).map(|v| self.write(rd, v))
            }
            ROp::Load {
                width,
                rd,
                rs1,
                off,
            } => {
                let at = offset(self.get(rs1), off, w);
                let ty = access(width);
                let v = self.ex.read_at(at, ty);
                let v = match width {
                    Width::B | Width::H => sign_extend(v, ty.bits()),
                    Width::W if self.xlen == Xlen::X64 => sign_extend(v, 32),
                    Width::W | Width::Bu | Width::Hu | Width::Wu | Width::D => v,
                };
                self.write(rd, v);
                Some(())
            }
            ROp::Store {
                width,
                rs2,
                rs1,
                off,
            } => {
                let ty = access(width);
                let v = self.get(rs2);
                let v = if ty.bits() < w {
                    mask(v, (1u64 << ty.bits()) - 1)
                } else {
                    v
                };
                let at = offset(self.get(rs1), off, w);
                self.ex.store_at(at, ty, v);
                Some(())
            }
            ROp::Fence { .. } | ROp::FenceI => Some(()),
            ROp::Float(f) => self.float(f),
            ROp::Jal { .. }
            | ROp::Jalr { .. }
            | ROp::Branch { .. }
            | ROp::Ecall
            | ROp::Ebreak
            | ROp::Csr { .. }
            | ROp::Lr { .. }
            | ROp::Sc { .. }
            | ROp::Amo { .. }
            | ROp::TrapRet
            | ROp::System
            | ROp::Unknown
            | ROp::Invalid => None,
        };
        if done.is_none() {
            self.unmodeled(i);
        }
    }

    /// Computes an integer operation at the register width, or at 32 bits
    /// with the result sign-extended for a `w` form.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    /// * `word` - Whether it is a `w` form.
    ///
    /// # Returns
    ///
    /// The value, or `None` for `mulhsu`, which no operator spells.
    fn alu(&self, op: Alu, a: Expr, b: Expr, word: bool) -> Option<Expr> {
        let w = if word { 32 } else { self.w() };
        let shift = |e: Expr| match e {
            Expr::Const(c) => Expr::Const(c & u64::from(w - 1)),
            e => fold(Op::And, e, Expr::Const(u64::from(w - 1)), w),
        };
        let signed = |e: Expr| if w >= 64 { e } else { sign_extend(e, w) };
        let v = match op {
            Alu::Add => fold(Op::Add, a, b, w),
            Alu::Sub => fold(Op::Sub, a, b, w),
            Alu::Sll => fold(Op::Shl, a, shift(b), w),
            Alu::Srl if word => fold(Op::Shr, mask(a, 0xffff_ffff), shift(b), w),
            Alu::Srl => fold(Op::Shr, a, shift(b), w),
            Alu::Sra => fold(Op::Sar, signed(a), shift(b), w),
            Alu::Slt => truth(ConditionCode::l, a, b, w),
            Alu::Sltu => truth(ConditionCode::b, a, b, w),
            Alu::Xor => fold(Op::Xor, a, b, w),
            Alu::Or => fold(Op::Or, a, b, w),
            Alu::And => fold(Op::And, a, b, w),
            Alu::Mul => fold(Op::Mul, a, b, w),
            Alu::Mulh => fold(Op::SMulHi(w), a, b, w),
            Alu::Mulhu => fold(Op::MulHi(w), a, b, w),
            Alu::Div => divide(Op::SDiv, signed(a), signed(b), w),
            Alu::Rem => divide(Op::SRem, signed(a), signed(b), w),
            Alu::Divu if word => divide(Op::Div, mask(a, 0xffff_ffff), mask(b, 0xffff_ffff), w),
            Alu::Remu if word => divide(Op::Rem, mask(a, 0xffff_ffff), mask(b, 0xffff_ffff), w),
            Alu::Divu => divide(Op::Div, a, b, w),
            Alu::Remu => divide(Op::Rem, a, b, w),
            Alu::Mulhsu => return None,
        };
        Some(if word { sign_extend(v, 32) } else { v })
    }
}
