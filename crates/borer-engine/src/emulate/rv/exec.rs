//! One RISC-V instruction on the machine.

use super::{Machine, return_to};
use crate::emulate::{Stop, lo64, sign_extend};
use crate::isa::rv::{self, Alu, AmoOp, BrCond, Insn, Op, Reg, Width, Xlen};
use crate::num::{lo32, sext32};

/// The stop for an instruction the machine does not model, naming it.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(super) fn unmodeled(i: &Insn) -> Stop {
    Stop::Unmodeled(format!("{} at {:#x}", rv::text(i), i.va))
}

/// Returns a register's number as an index.
///
/// # Arguments
///
/// * `r` - The register.
pub(super) fn n(r: Reg) -> usize {
    match r {
        Reg::X(n) | Reg::F(n) => usize::from(n),
    }
}

impl Machine<'_> {
    /// Reads an integer register.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    pub(super) fn get(&self, r: Reg) -> u64 {
        self.x.get(n(r)).copied().unwrap_or(0)
    }

    /// Reads an integer register as the signed value it holds at the
    /// register width.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn signed(&self, r: Reg) -> i64 {
        self.signed_value(self.get(r))
    }

    /// Reads a value as signed at the register width.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn signed_value(&self, v: u64) -> i64 {
        match self.xlen {
            Xlen::X32 => sext32(v).cast_signed(),
            Xlen::X64 => v.cast_signed(),
        }
    }

    /// Returns the shift amounts' mask at the register width.
    fn shift_mask(&self) -> u64 {
        u64::from(self.xlen.bits() - 1)
    }

    /// Hands control to `to`, which ends the run when it is the return
    /// sentinel.
    ///
    /// # Arguments
    ///
    /// * `to` - The target.
    ///
    /// # Errors
    ///
    /// [`Stop::Returned`] at the sentinel.
    fn transfer(&self, to: u64) -> Result<Option<u64>, Stop> {
        if to == return_to(self.xlen) {
            Err(Stop::Returned)
        } else {
            Ok(Some(to))
        }
    }

    /// Executes one instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// Where control goes, or `None` to fall through.
    ///
    /// # Errors
    ///
    /// Why the run stops.
    pub(super) fn step(&mut self, i: &Insn) -> Result<Option<u64>, Stop> {
        match i.op {
            Op::Lui { rd, imm } => self.set_x(n(rd), imm.cast_unsigned()),
            Op::Auipc { rd, target } => self.set_x(n(rd), target),
            Op::Jal { rd, target } => {
                self.set_x(n(rd), i.next());
                return self.transfer(target);
            }
            Op::Jalr { rd, rs1, off } => {
                let to = self.xlen.addr(self.get(rs1).wrapping_add_signed(off)) & !1;
                self.set_x(n(rd), i.next());
                return self.transfer(to);
            }
            Op::Branch {
                cond,
                rs1,
                rs2,
                target,
            } => return Ok(self.taken(cond, rs1, rs2).then_some(target)),
            Op::Load {
                width,
                rd,
                rs1,
                off,
            } => {
                let at = self.xlen.addr(self.get(rs1).wrapping_add_signed(off));
                let raw = self.load(at, width.bytes())?;
                let v = match width {
                    Width::B => sign_extend(raw, 8).cast_unsigned(),
                    Width::H => sign_extend(raw, 16).cast_unsigned(),
                    Width::W => sext32(raw),
                    Width::Bu | Width::Hu | Width::Wu | Width::D => raw,
                };
                self.set_x(n(rd), v);
            }
            Op::Store {
                width,
                rs2,
                rs1,
                off,
            } => {
                let at = self.xlen.addr(self.get(rs1).wrapping_add_signed(off));
                self.store(at, width.bytes(), self.get(rs2))?;
            }
            Op::Imm {
                op,
                rd,
                rs1,
                imm,
                word,
            } => {
                let v = self.alu(op, self.get(rs1), imm.cast_unsigned(), word);
                self.set_x(n(rd), v);
            }
            Op::Reg3 {
                op,
                rd,
                rs1,
                rs2,
                word,
            } => {
                let v = self.alu(op, self.get(rs1), self.get(rs2), word);
                self.set_x(n(rd), v);
            }
            Op::Fence { .. } | Op::FenceI => {}
            Op::Ecall => return self.syscall(),
            Op::Lr { width, rd, rs1, .. } => {
                let raw = self.load(self.get(rs1), width.bytes())?;
                let v = if width == Width::W { sext32(raw) } else { raw };
                self.set_x(n(rd), v);
            }
            Op::Sc {
                width,
                rd,
                rs1,
                rs2,
                ..
            } => {
                self.store(self.get(rs1), width.bytes(), self.get(rs2))?;
                self.set_x(n(rd), 0);
            }
            Op::Amo {
                op,
                width,
                rd,
                rs1,
                rs2,
                ..
            } => self.amo(op, width, rd, rs1, rs2)?,
            Op::Float(f) => self.float(i, f)?,
            Op::Ebreak | Op::Csr { .. } | Op::TrapRet | Op::System | Op::Unknown | Op::Invalid => {
                return Err(unmodeled(i));
            }
        }
        Ok(None)
    }

    /// Tells whether a conditional branch is taken.
    ///
    /// # Arguments
    ///
    /// * `cond` - The comparison.
    /// * `rs1` - The left operand.
    /// * `rs2` - The right operand.
    fn taken(&self, cond: BrCond, rs1: Reg, rs2: Reg) -> bool {
        let (a, b) = (self.get(rs1), self.get(rs2));
        let (sa, sb) = (self.signed(rs1), self.signed(rs2));
        match cond {
            BrCond::Eq => a == b,
            BrCond::Ne => a != b,
            BrCond::Lt => sa < sb,
            BrCond::Ge => sa >= sb,
            BrCond::Ltu => a < b,
            BrCond::Geu => a >= b,
        }
    }

    /// Computes an integer operation at the register width, or on the low
    /// word with the result sign-extended for a `w` form.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    /// * `word` - Whether it is a `w` form.
    fn alu(&self, op: Alu, a: u64, b: u64, word: bool) -> u64 {
        if word {
            return sext32(word_alu(op, lo32(a), lo32(b)));
        }
        let (sa, sb) = (self.signed_value(a), self.signed_value(b));
        let b = self.xlen.addr(b);
        let sh = b & self.shift_mask();
        let wide = self.xlen == Xlen::X64;
        match op {
            Alu::Add => a.wrapping_add(b),
            Alu::Sub => a.wrapping_sub(b),
            Alu::Sll => a << sh,
            Alu::Slt => u64::from(sa < sb),
            Alu::Sltu => u64::from(a < b),
            Alu::Xor => a ^ b,
            Alu::Srl => a >> sh,
            Alu::Sra => (sa >> sh).cast_unsigned(),
            Alu::Or => a | b,
            Alu::And => a & b,
            Alu::Mul => a.wrapping_mul(b),
            Alu::Mulh if wide => lo64((i128::from(sa) * i128::from(sb)).cast_unsigned() >> 64),
            Alu::Mulhsu if wide => lo64((i128::from(sa) * i128::from(b)).cast_unsigned() >> 64),
            Alu::Mulhu if wide => lo64((u128::from(a) * u128::from(b)) >> 64),
            Alu::Mulh => (sa * sb).cast_unsigned() >> 32,
            Alu::Mulhsu => (sa * b.cast_signed()).cast_unsigned() >> 32,
            Alu::Mulhu => (a * b) >> 32,
            Alu::Div if b == 0 => u64::MAX,
            Alu::Div => sa.wrapping_div(sb).cast_unsigned(),
            Alu::Divu if b == 0 => u64::MAX,
            Alu::Divu => a / b,
            Alu::Rem if b == 0 => a,
            Alu::Rem => sa.wrapping_rem(sb).cast_unsigned(),
            Alu::Remu if b == 0 => a,
            Alu::Remu => a % b,
        }
    }

    /// Runs an atomic read-modify-write.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `width` - `W` or `D`.
    /// * `rd` - Where the old value goes.
    /// * `rs1` - The address.
    /// * `rs2` - The operand.
    ///
    /// # Errors
    ///
    /// A fault or a full memory.
    fn amo(&mut self, op: AmoOp, width: Width, rd: Reg, rs1: Reg, rs2: Reg) -> Result<(), Stop> {
        let at = self.get(rs1);
        let raw = self.load(at, width.bytes())?;
        let narrow = width == Width::W;
        let old = if narrow { sext32(raw) } else { raw };
        let src = if narrow {
            sext32(self.get(rs2))
        } else {
            self.get(rs2)
        };
        let (so, ss) = (old.cast_signed(), src.cast_signed());
        let new = match op {
            AmoOp::Swap => src,
            AmoOp::Add => old.wrapping_add(src),
            AmoOp::Xor => old ^ src,
            AmoOp::And => old & src,
            AmoOp::Or => old | src,
            AmoOp::Min => so.min(ss).cast_unsigned(),
            AmoOp::Max => so.max(ss).cast_unsigned(),
            AmoOp::Minu => old.min(src),
            AmoOp::Maxu => old.max(src),
        };
        self.store(at, width.bytes(), new)?;
        self.set_x(n(rd), old);
        Ok(())
    }
}

/// Computes an RV64 `w` operation on two words.
///
/// # Arguments
///
/// * `op` - The operation.
/// * `a` - The left word.
/// * `b` - The right word.
fn word_alu(op: Alu, a: u32, b: u32) -> u64 {
    let (sa, sb) = (a.cast_signed(), b.cast_signed());
    let sh = b & 31;
    u64::from(match op {
        Alu::Add => a.wrapping_add(b),
        Alu::Sub => a.wrapping_sub(b),
        Alu::Sll => a << sh,
        Alu::Srl => a >> sh,
        Alu::Sra => (sa >> sh).cast_unsigned(),
        Alu::Mul => a.wrapping_mul(b),
        Alu::Div if b == 0 => u32::MAX,
        Alu::Div => sa.wrapping_div(sb).cast_unsigned(),
        Alu::Divu if b == 0 => u32::MAX,
        Alu::Divu => a / b,
        Alu::Rem if b == 0 => a,
        Alu::Rem => sa.wrapping_rem(sb).cast_unsigned(),
        Alu::Remu if b == 0 => a,
        Alu::Remu => a % b,
        Alu::Slt
        | Alu::Sltu
        | Alu::Xor
        | Alu::Or
        | Alu::And
        | Alu::Mulh
        | Alu::Mulhsu
        | Alu::Mulhu => 0,
    })
}
