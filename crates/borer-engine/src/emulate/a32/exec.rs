//! The integer instructions of the ARM32 machine: data processing with its
//! shifter, multiplies and divides, bit operations, loads and stores,
//! block transfers, branches and the supervisor call.

use super::{
    EXIT_CALLS, HISTORY_MAX, MEMORY_MAX, Machine, RETURN_TO, SYSCALL_NR, WORD, WRITE_CALL, on_stack,
};
use crate::emulate::{Stop, Written, fill_byte};
use crate::isa::a32::{
    self, Addr, Block, Cond, DpKind, Flow, Index, Insn, Offset, Op, Operand, PC, Reg, Shift, Width,
};
use crate::num::{lo8, lo16, lo32};

/// A register shifted as an operand reads it, with the shifter's carry.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `shift` - The shift.
/// * `n` - The amount; a shift by a register reads the low byte.
/// * `cin` - The carry flag, which a shift of zero leaves.
pub(crate) fn shift_c(v: u32, shift: Shift, n: u32, cin: bool) -> (u32, bool) {
    let bit = |x: u32, at: u32| (x >> at) & 1 == 1;
    match shift {
        _ if n == 0 && shift != Shift::Rrx => (v, cin),
        Shift::Lsl if n < 32 => (v << n, bit(v, 32 - n)),
        Shift::Lsl if n == 32 => (0, bit(v, 0)),
        Shift::Lsl => (0, false),
        Shift::Lsr if n < 32 => (v >> n, bit(v, n - 1)),
        Shift::Lsr if n == 32 => (0, bit(v, 31)),
        Shift::Lsr => (0, false),
        Shift::Asr if n < 32 => ((v.cast_signed() >> n).cast_unsigned(), bit(v, n - 1)),
        Shift::Asr => (if bit(v, 31) { u32::MAX } else { 0 }, bit(v, 31)),
        Shift::Ror if n.is_multiple_of(32) => (v, bit(v, 31)),
        Shift::Ror => {
            let r = v.rotate_right(n % 32);
            (r, bit(r, 31))
        }
        Shift::Rrx => ((u32::from(cin) << 31) | (v >> 1), bit(v, 0)),
    }
}

/// `AddWithCarry`: the sum of two words and a carry in, with the carry
/// and the signed overflow out.
///
/// # Arguments
///
/// * `x` - The first word.
/// * `y` - The second.
/// * `carry` - The carry in.
pub(crate) fn add_with_carry(x: u32, y: u32, carry: bool) -> (u32, bool, bool) {
    let unsigned = u64::from(x) + u64::from(y) + u64::from(carry);
    let signed = i64::from(x.cast_signed()) + i64::from(y.cast_signed()) + i64::from(carry);
    let result = lo32(unsigned);
    (
        result,
        u64::from(result) != unsigned,
        i64::from(result.cast_signed()) != signed,
    )
}

/// Ends a transfer: at the return sentinel, the routine has returned to
/// its caller.
///
/// # Arguments
///
/// * `to` - Where control goes, its low bit already cleared.
///
/// # Errors
///
/// [`Stop::Returned`] when `to` is the sentinel.
fn transfer(to: u64) -> Result<Option<u64>, Stop> {
    if to == RETURN_TO {
        Err(Stop::Returned)
    } else {
        Ok(Some(to))
    }
}

/// The stop for an instruction the machine does not model, naming it.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(super) fn unmodeled(i: &Insn) -> Stop {
    Stop::Unmodeled(format!("{} at {:#x}", a32::text(i), i.va))
}

impl Machine<'_> {
    /// Tells whether an instruction runs: one under no condition, one
    /// whose condition holds, and under [`Machine::set_forced`] one that
    /// moves control.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn runs(&self, i: &Insn) -> bool {
        !i.predicated() || (self.forced && i.flow() != Flow::Next) || self.holds(i.cond)
    }

    /// Tells whether a condition holds on the flags.
    ///
    /// # Arguments
    ///
    /// * `cond` - The condition.
    pub(super) fn holds(&self, cond: Cond) -> bool {
        match cond {
            Cond::Eq => self.z,
            Cond::Ne => !self.z,
            Cond::Hs => self.c,
            Cond::Lo => !self.c,
            Cond::Mi => self.n,
            Cond::Pl => !self.n,
            Cond::Vs => self.v,
            Cond::Vc => !self.v,
            Cond::Hi => self.c && !self.z,
            Cond::Ls => !self.c || self.z,
            Cond::Ge => self.n == self.v,
            Cond::Lt => self.n != self.v,
            Cond::Gt => !self.z && self.n == self.v,
            Cond::Le => self.z || self.n != self.v,
            Cond::Al | Cond::Nv => true,
        }
    }

    /// The flags as the APSR holds them, in bits 28 to 31.
    pub(super) fn nzcv(&self) -> u32 {
        (u32::from(self.n) << 31)
            | (u32::from(self.z) << 30)
            | (u32::from(self.c) << 29)
            | (u32::from(self.v) << 28)
    }

    /// Sets the flags from bits 28 to 31 of a word.
    ///
    /// # Arguments
    ///
    /// * `v` - The word.
    pub(super) fn set_nzcv(&mut self, v: u32) {
        self.n = (v >> 31) & 1 == 1;
        self.z = (v >> 30) & 1 == 1;
        self.c = (v >> 29) & 1 == 1;
        self.v = (v >> 28) & 1 == 1;
    }

    /// Reads a core register as an instruction reads it: `pc` as the
    /// instruction's address plus 8 (A32) or 4 (T32).
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `i` - The instruction reading it.
    pub(super) fn get(&self, r: Reg, i: &Insn) -> u32 {
        match r {
            PC => lo32(i.pc()),
            Reg::R(n) => self.r.get(usize::from(n)).copied().unwrap_or(0),
            Reg::S(n) => self.single(n),
            Reg::D(n) => lo32(self.double(n)),
        }
    }

    /// Writes a core register other than `pc`.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `v` - The value.
    pub(super) fn set(&mut self, r: Reg, v: u32) {
        match r {
            Reg::R(n) => {
                if let Some(slot) = self.r.get_mut(usize::from(n)) {
                    *slot = v;
                }
            }
            Reg::S(n) => self.set_single(n, v),
            Reg::D(n) => self.set_double(n, u64::from(v)),
        }
    }

    /// Writes `pc`: a branch, into the instruction set the address's low
    /// bit names when the write interworks.
    ///
    /// # Arguments
    ///
    /// * `v` - The address written.
    /// * `interwork` - Whether the low bit selects the instruction set
    ///   (`bx`, a load, an A32 data-processing write); otherwise it is
    ///   dropped and the set stays.
    ///
    /// # Errors
    ///
    /// [`Stop::Returned`] at the return sentinel.
    pub(super) fn write_pc(&mut self, v: u32, interwork: bool) -> Result<Option<u64>, Stop> {
        if interwork {
            self.thumb = v & 1 == 1;
        }
        let to = if self.thumb {
            u64::from(v & !1)
        } else {
            u64::from(v & !3)
        };
        self.it = a32::ItState::default();
        transfer(to)
    }

    /// Writes a register, a write of `pc` being a branch.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `v` - The value.
    /// * `interwork` - Whether a write of `pc` interworks.
    ///
    /// # Errors
    ///
    /// [`Stop::Returned`] when it branches to the return sentinel.
    fn write(&mut self, r: Reg, v: u32, interwork: bool) -> Result<Option<u64>, Stop> {
        if r == PC {
            self.write_pc(v, interwork)
        } else {
            self.set(r, v);
            Ok(None)
        }
    }

    /// The link a call writes: the address after it, with the low bit set
    /// in T32.
    ///
    /// # Arguments
    ///
    /// * `i` - The call.
    fn link(&mut self, i: &Insn) {
        self.r[14] = lo32(i.next()) | u32::from(self.thumb);
    }

    /// A data-processing operand and the shifter's carry.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `src` - The operand.
    fn operand(&self, i: &Insn, src: Operand) -> (u32, bool) {
        match src {
            Operand::Imm { value, carry } => (value, carry.unwrap_or(self.c)),
            Operand::Reg { rm, shift, amount } => {
                shift_c(self.get(rm, i), shift, u32::from(amount), self.c)
            }
            Operand::RegShift { rm, shift, rs } => {
                shift_c(self.get(rm, i), shift, self.get(rs, i) & 0xff, self.c)
            }
        }
    }

    /// Executes one instruction whose condition holds.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// `Ok(Some(target))` for a taken branch, `Ok(None)` to fall through.
    ///
    /// # Errors
    ///
    /// The [`Stop`] that ends the run.
    pub(super) fn step(&mut self, i: &Insn) -> Result<Option<u64>, Stop> {
        let arm = !self.thumb;
        match i.op {
            Op::Dp { kind, rd, rn, src } => self.data(i, kind, rd, rn, src),
            Op::Movw { rd, imm } => self.write(rd, u32::from(imm), arm),
            Op::Movt { rd, imm } => {
                let v = (self.get(rd, i) & 0xffff) | (u32::from(imm) << 16);
                self.write(rd, v, arm)
            }
            Op::Adr { rd, target } => self.write(rd, lo32(target), arm),
            Op::Mul {
                rd,
                rn,
                rm,
                acc,
                sub,
            } => {
                let p = self.get(rn, i).wrapping_mul(self.get(rm, i));
                let v = match acc {
                    Some(a) if sub => self.get(a, i).wrapping_sub(p),
                    Some(a) => self.get(a, i).wrapping_add(p),
                    None => p,
                };
                if i.sets {
                    self.n = v >> 31 == 1;
                    self.z = v == 0;
                }
                self.write(rd, v, arm)
            }
            Op::MulLong {
                signed,
                acc,
                lo,
                hi,
                rn,
                rm,
            } => {
                let (x, y) = (self.get(rn, i), self.get(rm, i));
                let p = if signed {
                    (i64::from(x.cast_signed()) * i64::from(y.cast_signed())).cast_unsigned()
                } else {
                    u64::from(x) * u64::from(y)
                };
                let held = (u64::from(self.get(hi, i)) << 32) | u64::from(self.get(lo, i));
                let v = if acc { p.wrapping_add(held) } else { p };
                if i.sets {
                    self.n = v >> 63 == 1;
                    self.z = v == 0;
                }
                self.set(lo, lo32(v));
                self.set(hi, lo32(v >> 32));
                Ok(None)
            }
            Op::Smmul { rd, rn, rm, acc } => {
                let p = i64::from(self.get(rn, i).cast_signed())
                    * i64::from(self.get(rm, i).cast_signed());
                let p = p
                    .cast_unsigned()
                    .wrapping_add(acc.map_or(0, |a| u64::from(self.get(a, i)) << 32));
                self.write(rd, lo32(p >> 32), arm)
            }
            Op::Smulxy {
                rd,
                rn,
                rm,
                n_top,
                m_top,
                acc,
            } => {
                let half = |v: u32, top: bool| {
                    i32::from(lo16(u64::from(if top { v >> 16 } else { v })).cast_signed())
                };
                let p = half(self.get(rn, i), n_top).wrapping_mul(half(self.get(rm, i), m_top));
                let v = p
                    .cast_unsigned()
                    .wrapping_add(acc.map_or(0, |a| self.get(a, i)));
                self.write(rd, v, arm)
            }
            Op::Div { signed, rd, rn, rm } => {
                let (x, y) = (self.get(rn, i), self.get(rm, i));
                let v = match (y, signed) {
                    (0, _) => 0,
                    (_, true) => x
                        .cast_signed()
                        .wrapping_div(y.cast_signed())
                        .cast_unsigned(),
                    (_, false) => x / y,
                };
                self.write(rd, v, arm)
            }
            Op::Clz { rd, rm } => {
                let v = self.get(rm, i).leading_zeros();
                self.write(rd, v, arm)
            }
            Op::Rbit { rd, rm } => {
                let v = self.get(rm, i).reverse_bits();
                self.write(rd, v, arm)
            }
            Op::Rev { rd, rm } => {
                let v = self.get(rm, i).swap_bytes();
                self.write(rd, v, arm)
            }
            Op::Rev16 { rd, rm } => {
                let x = self.get(rm, i);
                self.write(rd, ((x & 0x00ff_00ff) << 8) | ((x >> 8) & 0x00ff_00ff), arm)
            }
            Op::Revsh { rd, rm } => {
                let x = self.get(rm, i);
                let half = u16::try_from(((x & 0xff) << 8) | ((x >> 8) & 0xff)).unwrap_or(0);
                self.write(rd, i32::from(half.cast_signed()).cast_unsigned(), arm)
            }
            Op::Bfx {
                signed,
                rd,
                rn,
                lsb,
                width,
            } => {
                let x = self.get(rn, i);
                let (lsb, width) = (u32::from(lsb), u32::from(width));
                let up = 32u32.saturating_sub(lsb + width);
                let v = if signed {
                    ((x << up).cast_signed() >> (up + lsb)).cast_unsigned()
                } else {
                    (x << up) >> (up + lsb)
                };
                self.write(rd, v, arm)
            }
            Op::Sat {
                signed,
                rd,
                rn,
                bits,
                shift,
                amount,
            } => {
                let x = self.get(rn, i).cast_signed();
                let x = i64::from(match shift {
                    Shift::Lsl => x.wrapping_shl(u32::from(amount)),
                    Shift::Lsr | Shift::Asr | Shift::Ror | Shift::Rrx => {
                        x >> u32::from(amount).min(31)
                    }
                });
                let bits = u32::from(bits);
                let (lo, hi) = if signed {
                    let half = 1i64 << bits.clamp(1, 32).saturating_sub(1);
                    (-half, half - 1)
                } else {
                    (0, (1i64 << bits.min(31)) - 1)
                };
                let v = lo32(x.clamp(lo, hi).cast_unsigned());
                self.write(rd, v, arm)
            }
            Op::Bfi { rd, rn, lsb, width } => {
                let field = ones(u32::from(width)) << lsb;
                let src = rn.map_or(0, |r| self.get(r, i)) << lsb;
                let v = (self.get(rd, i) & !field) | (src & field);
                self.write(rd, v, arm)
            }
            Op::Extend {
                signed,
                bits,
                rd,
                rm,
                rotate,
                add,
            } => {
                let x = self.get(rm, i).rotate_right(u32::from(rotate));
                let v = match (signed, bits) {
                    (true, 8) => i32::from(lo8(u64::from(x)).cast_signed()).cast_unsigned(),
                    (true, _) => i32::from(u16::try_from(x & 0xffff).unwrap_or(0).cast_signed())
                        .cast_unsigned(),
                    (false, 8) => x & 0xff,
                    (false, _) => x & 0xffff,
                };
                let v = v.wrapping_add(add.map_or(0, |a| self.get(a, i)));
                self.write(rd, v, arm)
            }
            Op::Load { width, rt, addr } | Op::LoadEx { width, rt, addr } => {
                let (at, back) = self.address(i, addr);
                let raw = self.load(u64::from(at), usize::from(width.bytes()))?;
                let v = match width {
                    Width::Word | Width::Byte | Width::Half => lo32(raw),
                    Width::SByte => i32::from(lo8(raw).cast_signed()).cast_unsigned(),
                    Width::SHalf => {
                        i32::from(u16::try_from(raw & 0xffff).unwrap_or(0).cast_signed())
                            .cast_unsigned()
                    }
                };
                if let Some(b) = back {
                    self.set(addr.base, b);
                }
                self.write(rt, v, true)
            }
            Op::Store { width, rt, addr } => {
                let v = self.get(rt, i);
                let (at, back) = self.address(i, addr);
                self.store(u64::from(at), usize::from(width.bytes()), u64::from(v))?;
                if let Some(b) = back {
                    self.set(addr.base, b);
                }
                Ok(None)
            }
            Op::StoreEx {
                width,
                rd,
                rt,
                addr,
            } => {
                let v = self.get(rt, i);
                let (at, _) = self.address(i, addr);
                self.store(u64::from(at), usize::from(width.bytes()), u64::from(v))?;
                self.set(rd, 0);
                Ok(None)
            }
            Op::LoadDual { rt, rt2, addr } => {
                let (at, back) = self.address(i, addr);
                let a = lo32(self.load(u64::from(at), 4)?);
                let b = lo32(self.load(u64::from(at.wrapping_add(4)), 4)?);
                if let Some(w) = back {
                    self.set(addr.base, w);
                }
                self.set(rt, a);
                self.set(rt2, b);
                Ok(None)
            }
            Op::StoreDual { rt, rt2, addr } => {
                let (a, b) = (self.get(rt, i), self.get(rt2, i));
                let (at, back) = self.address(i, addr);
                self.store(u64::from(at), 4, u64::from(a))?;
                self.store(u64::from(at.wrapping_add(4)), 4, u64::from(b))?;
                if let Some(w) = back {
                    self.set(addr.base, w);
                }
                Ok(None)
            }
            Op::Ldm {
                rn,
                regs,
                wback,
                block,
            } => {
                let (start, end) = self.span(i, rn, regs, block);
                let mut values = Vec::with_capacity(16);
                for (k, n) in (0u32..).zip((0u8..16).filter(|n| regs & (1 << n) != 0)) {
                    let at = start.wrapping_add(4 * k);
                    values.push((n, lo32(self.load(u64::from(at), 4)?)));
                }
                if wback {
                    self.set(rn, end);
                }
                let mut out = Ok(None);
                for (n, v) in values {
                    out = self.write(Reg::R(n), v, true);
                }
                out
            }
            Op::Stm {
                rn,
                regs,
                wback,
                block,
            } => {
                let (start, end) = self.span(i, rn, regs, block);
                for (k, n) in (0u32..).zip((0u8..16).filter(|n| regs & (1 << n) != 0)) {
                    let v = self.get(Reg::R(n), i);
                    self.store(u64::from(start.wrapping_add(4 * k)), 4, u64::from(v))?;
                }
                if wback {
                    self.set(rn, end);
                }
                Ok(None)
            }
            Op::B { target } => {
                if self.holds(i.cond) {
                    transfer(target)
                } else {
                    Ok(None)
                }
            }
            Op::Bl { target } => {
                self.link(i);
                transfer(target)
            }
            Op::Blx { target } => {
                self.link(i);
                self.thumb = !self.thumb;
                transfer(target)
            }
            Op::BlxReg { rm } => {
                let to = self.get(rm, i);
                self.link(i);
                self.write_pc(to, true)
            }
            Op::Bx { rm } => {
                let to = self.get(rm, i);
                self.write_pc(to, true)
            }
            Op::Cbz {
                rn,
                target,
                nonzero,
            } => {
                if (self.get(rn, i) != 0) == nonzero {
                    transfer(target)
                } else {
                    Ok(None)
                }
            }
            Op::Tb { half, rn, rm } => {
                let (base, index) = (self.get(rn, i), self.get(rm, i));
                let entry = if half {
                    self.load(u64::from(base.wrapping_add(index.wrapping_mul(2))), 2)?
                } else {
                    self.load(u64::from(base.wrapping_add(index)), 1)?
                };
                transfer(i.pc().wrapping_add(entry * 2) & WORD)
            }
            Op::Svc { imm } => self.syscall(i, imm),
            Op::Mrs { rd } => {
                let v = self.nzcv();
                self.write(rd, v, arm)
            }
            Op::Msr { rn } => {
                let v = self.get(rn, i);
                self.set_nzcv(v);
                Ok(None)
            }
            Op::It { .. } | Op::Nop => Ok(None),
            Op::VLoad { .. }
            | Op::VStore { .. }
            | Op::VLdm { .. }
            | Op::VStm { .. }
            | Op::FpBin { .. }
            | Op::FpUn { .. }
            | Op::FpImm { .. }
            | Op::FpCmp { .. }
            | Op::Vcvt { .. }
            | Op::VmovCore { .. }
            | Op::VmovPair { .. }
            | Op::Vmrs { .. }
            | Op::Vmsr { .. } => self.vfp(i).map(|()| None),
            Op::Invalid => {
                let executable = self.program.section_at(i.va).is_some_and(|s| s.executable);
                Err(if executable {
                    Stop::Unmodeled(format!("bad opcode at {:#x}", i.va))
                } else {
                    Stop::Fault(i.va)
                })
            }
            Op::Trap | Op::Neon { .. } | Op::Unknown => Err(unmodeled(i)),
        }
    }

    /// A data-processing instruction: the operation, the flags when it sets
    /// them, and the result into the destination unless it only compares.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `kind` - The operation.
    /// * `rd` - The destination.
    /// * `rn` - The first source.
    /// * `src` - The second.
    ///
    /// # Errors
    ///
    /// [`Stop::Returned`] when a write of `pc` returns.
    fn data(
        &mut self,
        i: &Insn,
        kind: DpKind,
        rd: Reg,
        rn: Reg,
        src: Operand,
    ) -> Result<Option<u64>, Stop> {
        let a = if kind.moves() { 0 } else { self.get(rn, i) };
        let (b, carry) = self.operand(i, src);
        let logic = |r: u32| (r, carry, self.v);
        let (r, c, v) = match kind {
            DpKind::And | DpKind::Tst => logic(a & b),
            DpKind::Eor | DpKind::Teq => logic(a ^ b),
            DpKind::Orr => logic(a | b),
            DpKind::Orn => logic(a | !b),
            DpKind::Bic => logic(a & !b),
            DpKind::Mov => logic(b),
            DpKind::Mvn => logic(!b),
            DpKind::Add | DpKind::Cmn => add_with_carry(a, b, false),
            DpKind::Adc => add_with_carry(a, b, self.c),
            DpKind::Sub | DpKind::Cmp => add_with_carry(a, !b, true),
            DpKind::Sbc => add_with_carry(a, !b, self.c),
            DpKind::Rsb => add_with_carry(b, !a, true),
            DpKind::Rsc => add_with_carry(b, !a, self.c),
        };
        if i.sets && (rd != PC || kind.compares()) {
            self.n = r >> 31 == 1;
            self.z = r == 0;
            self.c = c;
            self.v = v;
        }
        if kind.compares() {
            return Ok(None);
        }
        let interwork = !self.thumb;
        self.write(rd, r, interwork)
    }

    /// The address a memory operand names and the value it writes back to
    /// its base.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `a` - The operand.
    pub(super) fn address(&self, i: &Insn, a: Addr) -> (u32, Option<u32>) {
        let base = if a.base == PC {
            lo32(i.pc() & !3)
        } else {
            self.get(a.base, i)
        };
        let at = match a.offset {
            Offset::Imm(d) => base.wrapping_add_signed(d),
            Offset::Reg {
                rm,
                sub,
                shift,
                amount,
            } => {
                let off = shift_c(self.get(rm, i), shift, u32::from(amount), self.c).0;
                if sub {
                    base.wrapping_sub(off)
                } else {
                    base.wrapping_add(off)
                }
            }
        };
        match a.index {
            Index::Offset => (at, None),
            Index::Pre => (at, Some(at)),
            Index::Post => (base, Some(at)),
        }
    }

    /// The first address a block transfer touches and the base it writes
    /// back.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `rn` - The base.
    /// * `regs` - The registers.
    /// * `block` - The order.
    fn span(&self, i: &Insn, rn: Reg, regs: u16, block: Block) -> (u32, u32) {
        let base = self.get(rn, i);
        let bytes = 4 * regs.count_ones();
        match block {
            Block::Ia => (base, base.wrapping_add(bytes)),
            Block::Ib => (base.wrapping_add(4), base.wrapping_add(bytes)),
            Block::Da => (
                base.wrapping_sub(bytes).wrapping_add(4),
                base.wrapping_sub(bytes),
            ),
            Block::Db => (base.wrapping_sub(bytes), base.wrapping_sub(bytes)),
        }
    }

    /// `svc #0`: a Linux EABI system call, its number in `r7`. The exit
    /// numbers end the run, `write` returns its count, and every other
    /// number returns zero.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `imm` - Its immediate.
    ///
    /// # Errors
    ///
    /// [`Stop::Exited`] for `exit` and `exit_group`; an unmodeled stop for
    /// another immediate.
    fn syscall(&mut self, i: &Insn, imm: u32) -> Result<Option<u64>, Stop> {
        if imm != 0 {
            return Err(unmodeled(i));
        }
        let nr = self.r[SYSCALL_NR];
        if EXIT_CALLS.contains(&nr) {
            return Err(Stop::Exited);
        }
        self.r[0] = if nr == WRITE_CALL { self.r[2] } else { 0 };
        Ok(None)
    }

    /// Reads a byte as a load reads it: written, else the image's, else the
    /// fill.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    fn load_byte(&self, addr: u64) -> Option<u8> {
        self.byte_at(addr)
            .or_else(|| self.fill.map(|seed| fill_byte(seed, addr)))
    }

    /// Loads `bytes` bytes at `addr`, little-endian.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most eight.
    ///
    /// # Errors
    ///
    /// [`Stop::Fault`] at the first byte nothing backs.
    pub(super) fn load(&self, addr: u64, bytes: usize) -> Result<u64, Stop> {
        let mut v = 0u64;
        for (k, shift) in (0..crate::num::from_usize(bytes)).zip((0u32..).step_by(8)) {
            let a = addr.wrapping_add(k) & WORD;
            v |= u64::from(self.load_byte(a).ok_or(Stop::Fault(a))?) << shift;
        }
        Ok(v)
    }

    /// Stores the low `bytes` bytes of `v`, little-endian, recording each
    /// byte in the write history.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most eight.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when memory would grow past its cap.
    pub(super) fn store(&mut self, addr: u64, bytes: usize, v: u64) -> Result<(), Stop> {
        for (k, shift) in (0..crate::num::from_usize(bytes)).zip((0u32..).step_by(8)) {
            let a = addr.wrapping_add(k) & WORD;
            if self.mem.len() >= MEMORY_MAX && !self.mem.contains(a) {
                return Err(Stop::MemoryFull(a));
            }
            let value = lo8(v >> shift);
            if self.history.len() < HISTORY_MAX {
                self.history.push(Written { addr: a, value });
            }
            self.mem.set(a, value, !on_stack(a));
        }
        Ok(())
    }
}

/// The mask of the low `n` bits, all of them from 32 up.
///
/// # Arguments
///
/// * `n` - How many.
fn ones(n: u32) -> u32 {
    if n >= 32 { u32::MAX } else { (1 << n) - 1 }
}
