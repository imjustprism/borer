//! Which registers an A64 instruction's operands read and write.

use super::{Insn, Mem, Mnemonic, Mode, Op, Opnd, Reg};

/// Mask of a register field in an encoding.
const FIELD: u32 = 0x1f;
/// Where an encoding's first source register field starts (`Rn`).
const RN_AT: u32 = 5;
/// Where an encoding's second source register field starts (`Rm`).
const RM_AT: u32 = 16;
/// The width a vector register is read or written at when its operand is
/// one the engine does not model.
const WHOLE_V: u16 = 128;
/// The width of an address register.
const ADDRESS: u16 = 64;

/// The `v` register `k` places after `first` in an `ld1`/`st1` group,
/// wrapping from `v31` to `v0` as the architecture numbers them.
///
/// # Arguments
///
/// * `first` - The first register's number.
/// * `k` - The offset from it.
fn group_reg(first: u8, k: u8) -> Reg {
    Reg::V(first.wrapping_add(k) % 32)
}

/// The registers an instruction's operands read and write.
///
/// A register written is written whole: a `w` write clears the upper half
/// of its `x` register, and a scalar `v` write every bit above it. The
/// zero register is never listed. Control flow adds nothing here: a call's
/// arguments and the registers it changes, and a return's result, are the
/// procedure call standard's, which a caller adds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Registers {
    /// The registers read, each with the width read in bits.
    pub reads: Vec<(Reg, u16)>,
    /// The registers written.
    pub writes: Vec<Reg>,
}

impl Registers {
    /// Records the reads an operand makes: a register at its width, a
    /// memory operand's base and index, and the base a pre- or
    /// post-index writes back.
    ///
    /// # Arguments
    ///
    /// * `o` - The operand.
    fn read(&mut self, o: Opnd) {
        match o {
            Opnd::Reg { reg, bits } | Opnd::Shifted { reg, bits, .. } => {
                if reg != Reg::Zr {
                    self.reads.push((reg, bits));
                }
            }
            Opnd::Mem(m) => self.address(m),
            Opnd::None | Opnd::Imm(_) | Opnd::PcRel(_) | Opnd::Cond(_) | Opnd::Other => {}
        }
    }

    /// Records the registers a memory operand's address reads, and the base
    /// a pre- or post-index writes back.
    ///
    /// # Arguments
    ///
    /// * `m` - The memory operand.
    fn address(&mut self, m: Mem) {
        self.reads.push((m.base, ADDRESS));
        if m.mode != Mode::Offset {
            self.writes.push(m.base);
        }
        if let Some((r, bits)) = m.index
            && r != Reg::Zr
        {
            self.reads.push((r, bits));
        }
    }

    /// Records the write an operand makes, or a memory operand's reads.
    ///
    /// # Arguments
    ///
    /// * `o` - The operand.
    fn write(&mut self, o: Opnd) {
        match o {
            Opnd::Reg { reg, .. } | Opnd::Shifted { reg, .. } => {
                if reg != Reg::Zr {
                    self.writes.push(reg);
                }
            }
            Opnd::Mem(m) => self.address(m),
            Opnd::None | Opnd::Imm(_) | Opnd::PcRel(_) | Opnd::Cond(_) | Opnd::Other => {}
        }
    }

    /// Records every operand from `from` on as read.
    ///
    /// # Arguments
    ///
    /// * `ops` - The operands.
    /// * `from` - The first one read.
    fn rest(&mut self, ops: &[Opnd; 4], from: usize) {
        for o in ops.iter().skip(from) {
            self.read(*o);
        }
    }

    /// Records the `v` registers an encoding's register fields name, read,
    /// and the destination written, for a vector form whose operands the
    /// decoder leaves unmodeled.
    ///
    /// # Arguments
    ///
    /// * `word` - The encoding.
    fn vector_fields(&mut self, word: u32) {
        let at = |shift: u32| Reg::V(crate::num::lo8(u64::from((word >> shift) & FIELD)));
        for r in [at(0), at(RN_AT), at(RM_AT)] {
            self.reads.push((r, WHOLE_V));
        }
        self.writes.push(at(0));
    }
}

impl Insn {
    /// Returns the registers the instruction's operands read and write.
    ///
    /// A store, a compare and a prefetch read every operand; a load writes
    /// its destination or pair; an exclusive store writes its status, an
    /// atomic the old value, a compare-and-swap its compare register; a
    /// move-keep and a bitfield insert read the destination they write;
    /// every other data-processing instruction writes its first operand and
    /// reads the rest. A branch on a register reads it; an indirect branch,
    /// call or return reads its target.
    #[must_use]
    pub fn registers(&self) -> Registers {
        let mut r = Registers::default();
        let ops = &self.operands;
        match self.op {
            Op::Br | Op::Blr | Op::Ret | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz => {
                r.read(ops[0]);
            }
            Op::Adr | Op::Adrp => r.write(ops[0]),
            Op::B
            | Op::BCond(_)
            | Op::Bl
            | Op::Eret
            | Op::Trap
            | Op::Syscall
            | Op::Nop
            | Op::Bti
            | Op::Pac
            | Op::Sve
            | Op::Sme
            | Op::Invalid => {}
            Op::Other => self.data(&mut r),
        }
        r
    }

    /// Records the roles of a data-processing, load, store or system
    /// instruction's operands.
    ///
    /// # Arguments
    ///
    /// * `r` - Where the roles go.
    fn data(&self, r: &mut Registers) {
        let ops = &self.operands;
        match self.mnemonic {
            Mnemonic::Str(_)
            | Mnemonic::Stp
            | Mnemonic::Prfm
            | Mnemonic::Ccmp
            | Mnemonic::Ccmn
            // INVARIANT: the floating-point compares write the flags only;
            // their register operands are all sources.
            | Mnemonic::Fcmp
            | Mnemonic::Fcmpe
            | Mnemonic::Fccmp
            | Mnemonic::Svc => r.rest(ops, 0),
            Mnemonic::Ldr(_) | Mnemonic::Mrs | Mnemonic::Stxr(_) | Mnemonic::Stxp => {
                r.write(ops[0]);
                r.rest(ops, 1);
            }
            Mnemonic::Ldp(_) => {
                r.write(ops[0]);
                r.write(ops[1]);
                r.rest(ops, 2);
            }
            // INVARIANT: the register list is an operand the decoder
            // leaves unmodeled, so the word names the registers.
            Mnemonic::Ld1 => {
                r.rest(ops, 1);
                let Some((first, count)) = super::ld1_group(self.word) else {
                    return;
                };
                for k in 0..count {
                    r.writes.push(group_reg(first, k));
                }
            }
            Mnemonic::St1 => {
                r.rest(ops, 1);
                let Some((first, count)) = super::ld1_group(self.word) else {
                    return;
                };
                for k in 0..count {
                    r.reads.push((group_reg(first, k), WHOLE_V));
                }
            }
            Mnemonic::Atomic(..) => {
                r.read(ops[0]);
                r.write(ops[1]);
                r.rest(ops, 2);
            }
            Mnemonic::Cas(_) | Mnemonic::Movk | Mnemonic::Bfm => {
                r.rest(ops, 0);
                r.write(ops[0]);
            }
            Mnemonic::Msr => r.rest(ops, 1),
            Mnemonic::Barrier => {}
            Mnemonic::Movz
            | Mnemonic::Movn
            | Mnemonic::Add
            | Mnemonic::Adds
            | Mnemonic::Sub
            | Mnemonic::Subs
            | Mnemonic::Adc
            | Mnemonic::Adcs
            | Mnemonic::Sbc
            | Mnemonic::Sbcs
            | Mnemonic::And
            | Mnemonic::Ands
            | Mnemonic::Orr
            | Mnemonic::Orn
            | Mnemonic::Eor
            | Mnemonic::Eon
            | Mnemonic::Bic
            | Mnemonic::Bics
            | Mnemonic::Ubfm
            | Mnemonic::Sbfm
            | Mnemonic::Extr
            | Mnemonic::Lslv
            | Mnemonic::Lsrv
            | Mnemonic::Asrv
            | Mnemonic::Rorv
            | Mnemonic::Madd
            | Mnemonic::Msub
            | Mnemonic::Smaddl
            | Mnemonic::Smsubl
            | Mnemonic::Umaddl
            | Mnemonic::Umsubl
            | Mnemonic::Smulh
            | Mnemonic::Umulh
            | Mnemonic::Udiv
            | Mnemonic::Sdiv
            | Mnemonic::Clz
            | Mnemonic::Cls
            | Mnemonic::Rbit
            | Mnemonic::Rev
            | Mnemonic::Rev16
            | Mnemonic::Rev32
            | Mnemonic::Csel
            | Mnemonic::Csinc
            | Mnemonic::Csinv
            | Mnemonic::Csneg
            | Mnemonic::Fmov
            | Mnemonic::Fadd
            | Mnemonic::Fsub
            | Mnemonic::Fmul
            | Mnemonic::Fdiv
            | Mnemonic::Fsqrt
            | Mnemonic::Fabs
            | Mnemonic::Fneg
            | Mnemonic::Fcsel
            | Mnemonic::Fmax
            | Mnemonic::Fmin
            | Mnemonic::Scvtf
            | Mnemonic::Ucvtf
            | Mnemonic::Fcvtzs
            | Mnemonic::Fcvtzu
            | Mnemonic::Fcvt
            | Mnemonic::Dup
            | Mnemonic::Mul
            | Mnemonic::Neg
            | Mnemonic::Abs
            | Mnemonic::Movi
            | Mnemonic::Mvni
            | Mnemonic::Other => {
                r.rest(ops, 1);
                r.write(ops[0]);
                if ops.contains(&Opnd::Other) {
                    r.vector_fields(self.word);
                }
            }
        }
    }
}
