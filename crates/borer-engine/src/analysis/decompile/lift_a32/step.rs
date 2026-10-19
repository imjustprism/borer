//! Data processing for the ARM32 lifter: the moves, arithmetic and logic
//! with their shifter and flags, the multiplies and divides, the bit
//! operations, and an instruction under a condition.
//!
//! Each handler computes every value before it writes anything and
//! answers `None` for a form it does not model, which leaves the
//! instruction unmodeled. Values are folded at 32 bits.

use super::super::expr::{Expr, Flags, Key, Op, Ty, UnOp, fold, mask, sign_extend, ternary};
use super::super::helper::Helper;
use super::super::lift_a64::flags::{answer, condition, value};
use super::flags::{self, next_reader};
use super::{Lift, WORD};
use crate::isa::a32::{Cond, DpKind, Insn, Op as AOp, Operand, PC, Reg, SP, Shift};

/// A register shifted by a constant amount, and the shifter's carry as 1
/// or 0 (`None` when the shift leaves the carry).
///
/// # Arguments
///
/// * `x` - The register's value.
/// * `shift` - The shift.
/// * `n` - The amount, 0 to 32.
/// * `carry` - The carry flag in, 1 or 0, for `rrx`.
fn shift_by(x: Expr, shift: Shift, n: u8, carry: &dyn Fn() -> Expr) -> (Expr, Option<Expr>) {
    let k = |v: u64| Expr::Const(v);
    let bit_at = |e: Expr, at: u64| fold(Op::And, fold(Op::Shr, e, k(at), 32), k(1), 32);
    let n64 = u64::from(n);
    match (shift, n) {
        (Shift::Rrx, _) => (
            fold(
                Op::Or,
                fold(Op::Shl, carry(), k(31), 32),
                fold(Op::Shr, x.clone(), k(1), 32),
                32,
            ),
            Some(bit_at(x, 0)),
        ),
        (_, 0) => (x, None),
        (Shift::Lsl, 32) => (k(0), Some(bit_at(x, 0))),
        (Shift::Lsl, _) => (
            fold(Op::Shl, x.clone(), k(n64), 32),
            Some(bit_at(x, 32 - n64)),
        ),
        (Shift::Lsr, 32) => (k(0), Some(bit_at(x, 31))),
        (Shift::Lsr, _) => (
            fold(Op::Shr, x.clone(), k(n64), 32),
            Some(bit_at(x, n64 - 1)),
        ),
        (Shift::Asr, 32) => (sar(x.clone(), k(31)), Some(bit_at(x, 31))),
        (Shift::Asr, _) => (sar(x.clone(), k(n64)), Some(bit_at(x, n64 - 1))),
        (Shift::Ror, _) => {
            let r = fold(Op::Ror(32), x, k(n64 % 32), 32);
            let c = bit_at(r.clone(), 31);
            (r, Some(c))
        }
    }
}

/// An arithmetic shift right of a word: its value read as the signed
/// 32-bit integer it is, so the text shifts the sign in.
///
/// # Arguments
///
/// * `x` - The word.
/// * `by` - The amount.
pub(super) fn sar(x: Expr, by: Expr) -> Expr {
    fold(Op::Sar, sign_extend(x, 32), by, 32)
}

/// The mask of the low `n` bits of a word.
///
/// # Arguments
///
/// * `n` - How many, 1 to 32.
fn ones(n: u8) -> u64 {
    if n >= 32 { WORD } else { (1u64 << n) - 1 }
}

/// A value cut to 32 bits for an operation that depends on its width.
///
/// # Arguments
///
/// * `e` - The value.
fn word(e: Expr) -> Expr {
    Expr::Cast(Box::new(e), Ty::U32)
}

impl Lift<'_, '_> {
    /// Lifts an instruction that does not move control.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `later` - The block's instructions after it, for the flags'
    ///   reader.
    pub(super) fn step(&mut self, i: &Insn, later: &[Insn]) {
        let done = match i.op {
            AOp::Dp { kind, rd, rn, src } => self.data(i, kind, rd, rn, src, later),
            AOp::Movw { rd, imm } => self.put(rd, Expr::Const(u64::from(imm))),
            AOp::Movt { rd, imm } => {
                let low = mask(self.get(i, rd), 0xffff);
                self.put(rd, fold(Op::Or, low, Expr::Const(u64::from(imm) << 16), 32))
            }
            AOp::Adr { rd, target } => self.put(rd, Expr::Const(target)),
            AOp::Mul {
                rd,
                rn,
                rm,
                acc,
                sub,
            } => {
                let p = fold(Op::Mul, self.get(i, rn), self.get(i, rm), 32);
                let v = match acc {
                    Some(a) if sub => fold(Op::Sub, self.get(i, a), p, 32),
                    Some(a) => fold(Op::Add, self.get(i, a), p, 32),
                    None => p,
                };
                if i.sets {
                    self.ex.flags = Flags::Result(v.clone(), 32);
                }
                self.put(rd, v)
            }
            AOp::MulLong {
                signed,
                acc,
                lo,
                hi,
                rn,
                rm,
            } => self.mul_long(i, signed, acc, lo, hi, rn, rm),
            AOp::Smmul { rd, rn, rm, acc } => {
                let p = fold(Op::SMulHi(32), self.get(i, rn), self.get(i, rm), 32);
                let v = match acc {
                    Some(a) => fold(Op::Add, self.get(i, a), p, 32),
                    None => p,
                };
                self.put(rd, v)
            }
            AOp::Smulxy {
                rd,
                rn,
                rm,
                n_top,
                m_top,
                acc,
            } => {
                let half = |e: Expr, top: bool| {
                    if top {
                        sar(e, Expr::Const(16))
                    } else {
                        sign_extend(e, 16)
                    }
                };
                let p = fold(
                    Op::Mul,
                    half(self.get(i, rn), n_top),
                    half(self.get(i, rm), m_top),
                    32,
                );
                let v = match acc {
                    Some(a) => fold(Op::Add, self.get(i, a), p, 32),
                    None => p,
                };
                self.put(rd, v)
            }
            AOp::Div { signed, rd, rn, rm } => {
                let (x, y) = (self.get(i, rn), self.get(i, rm));
                let v = if signed {
                    fold(Op::SDiv, sign_extend(x, 32), sign_extend(y, 32), 32)
                } else {
                    fold(Op::Div, x, y, 32)
                };
                self.put(rd, v)
            }
            AOp::Clz { rd, rm } => {
                let v = Expr::Un(UnOp::Lzcnt, Box::new(word(self.get(i, rm))));
                self.put(rd, v)
            }
            AOp::Rbit { rd, rm } => {
                let v = Expr::Helper(Helper::Rbit, vec![word(self.get(i, rm))]);
                self.put(rd, v)
            }
            AOp::Rev { rd, rm } => {
                let v = Expr::Un(UnOp::Bswap, Box::new(word(self.get(i, rm))));
                self.put(rd, v)
            }
            AOp::Rev16 { rd, rm } => {
                let v = Expr::Helper(Helper::Rev16, vec![word(self.get(i, rm))]);
                self.put(rd, v)
            }
            AOp::Revsh { rd, rm } => {
                let x = self.get(i, rm);
                let swapped = fold(
                    Op::Or,
                    fold(Op::Shl, mask(x.clone(), 0xff), Expr::Const(8), 32),
                    mask(fold(Op::Shr, x, Expr::Const(8), 32), 0xff),
                    32,
                );
                self.put(rd, sign_extend(swapped, 16))
            }
            AOp::Bfx {
                signed,
                rd,
                rn,
                lsb,
                width,
            } => {
                let x = self.get(i, rn);
                let shifted = if lsb == 0 {
                    x
                } else {
                    fold(Op::Shr, x, Expr::Const(u64::from(lsb)), 32)
                };
                let v = if signed {
                    sign_extend(shifted, width)
                } else {
                    mask(shifted, ones(width))
                };
                self.put(rd, v)
            }
            AOp::Sat {
                signed,
                rd,
                rn,
                bits,
                shift,
                amount,
            } => {
                let x = self.get(i, rn);
                let x = match (shift, amount) {
                    (_, 0) => x,
                    (Shift::Lsl, n) => fold(Op::Shl, x, Expr::Const(u64::from(n)), 32),
                    (Shift::Lsr | Shift::Asr | Shift::Ror | Shift::Rrx, n) => {
                        sar(x, Expr::Const(u64::from(n.min(31))))
                    }
                };
                let (lo, hi) = if signed {
                    let half = 1u64 << bits.clamp(1, 32).saturating_sub(1);
                    ((half.wrapping_neg()) & WORD, half - 1)
                } else {
                    (0, (1u64 << bits.min(31)) - 1)
                };
                let test = |cc, bound| super::super::expr::Cond {
                    cc: super::super::expr::Cc(cc),
                    flags: Flags::Cmp(x.clone(), Expr::Const(bound), 32),
                };
                let v = if signed && bits >= 32 {
                    x
                } else {
                    ternary(
                        test(crate::isa::x86::ConditionCode::l, lo),
                        Expr::Const(lo),
                        ternary(
                            test(crate::isa::x86::ConditionCode::g, hi),
                            Expr::Const(hi),
                            x.clone(),
                        ),
                    )
                };
                self.put(rd, v)
            }
            AOp::Bfi { rd, rn, lsb, width } => {
                let field = ones(width) << lsb;
                let kept = fold(Op::And, self.get(i, rd), Expr::Const(!field & WORD), 32);
                let v = match rn {
                    Some(r) => fold(
                        Op::Or,
                        kept,
                        fold(
                            Op::And,
                            fold(Op::Shl, self.get(i, r), Expr::Const(u64::from(lsb)), 32),
                            Expr::Const(field),
                            32,
                        ),
                        32,
                    ),
                    None => kept,
                };
                self.put(rd, v)
            }
            AOp::Extend {
                signed,
                bits,
                rd,
                rm,
                rotate,
                add,
            } => {
                let x = self.get(i, rm);
                let x = if rotate == 0 {
                    x
                } else {
                    fold(Op::Ror(32), x, Expr::Const(u64::from(rotate)), 32)
                };
                let v = if signed {
                    sign_extend(x, bits)
                } else {
                    mask(x, ones(bits))
                };
                let v = match add {
                    Some(a) => fold(Op::Add, self.get(i, a), v, 32),
                    None => v,
                };
                self.put(rd, v)
            }
            AOp::Load { .. }
            | AOp::LoadEx { .. }
            | AOp::Store { .. }
            | AOp::StoreEx { .. }
            | AOp::LoadDual { .. }
            | AOp::StoreDual { .. }
            | AOp::Ldm { .. }
            | AOp::Stm { .. } => self.memory(i),
            AOp::VLoad { .. }
            | AOp::VStore { .. }
            | AOp::VLdm { .. }
            | AOp::VStm { .. }
            | AOp::FpBin { .. }
            | AOp::FpUn { .. }
            | AOp::FpImm { .. }
            | AOp::FpCmp { .. }
            | AOp::Vcvt { .. }
            | AOp::VmovCore { .. }
            | AOp::VmovPair { .. }
            | AOp::Vmrs { .. } => self.vfp(i),
            AOp::It { .. } | AOp::Nop => Some(()),
            AOp::Mrs { rd } => {
                let word = super::super::lift_a64::flags::nzcv_word(&self.ex.flags);
                self.put(rd, word)
            }
            AOp::Msr { rn } => {
                let v = self.get(i, rn);
                self.ex.flags = Flags::Carry(fold(Op::And, v, Expr::Const(0xf000_0000), 32));
                Some(())
            }
            AOp::Vmsr { .. }
            | AOp::Svc { .. }
            | AOp::Trap
            | AOp::Neon { .. }
            | AOp::Unknown
            | AOp::Invalid
            | AOp::B { .. }
            | AOp::Bl { .. }
            | AOp::Blx { .. }
            | AOp::BlxReg { .. }
            | AOp::Bx { .. }
            | AOp::Cbz { .. }
            | AOp::Tb { .. } => None,
        };
        if done.is_none() {
            self.unmodeled(i);
        }
    }

    /// Writes a register an instruction computed, refusing `pc`, which
    /// moves control and is lifted as a jump.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `v` - The value.
    pub(super) fn put(&mut self, r: Reg, v: Expr) -> Option<()> {
        if r == PC {
            return None;
        }
        self.write(r, v);
        Some(())
    }

    /// A data-processing operand, and the shifter's carry as 1 or 0 when
    /// it makes one.
    ///
    /// A shift by a register is by its low byte: 32 and up shifts every
    /// bit out (`lsl`, `lsr`) or copies the sign through (`asr`), and a
    /// rotation is by the amount modulo 32. Its carry is the last bit
    /// shifted out, or the carry flag as it was for a shift by zero; with
    /// the flags unknown it is not modeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `src` - The operand.
    fn operand(&self, i: &Insn, src: Operand) -> (Expr, Option<Expr>) {
        let carry = || value(&self.ex.flags, Cond::Hs);
        match src {
            Operand::Imm { value: v, carry: c } => (
                Expr::Const(u64::from(v)),
                c.map(|b| Expr::Const(u64::from(b))),
            ),
            Operand::Reg { rm, shift, amount } => shift_by(self.get(i, rm), shift, amount, &carry),
            Operand::RegShift { rm, shift, rs } => {
                let x = self.get(i, rm);
                let by = mask(self.get(i, rs), 0xff);
                let against = |n: u64, cc| super::super::expr::Cond {
                    cc: super::super::expr::Cc(cc),
                    flags: Flags::Cmp(by.clone(), Expr::Const(n), 32),
                };
                let small = against(32, crate::isa::x86::ConditionCode::b);
                let v = match shift {
                    Shift::Lsl => ternary(
                        small,
                        fold(Op::Shl, x.clone(), by.clone(), 32),
                        Expr::Const(0),
                    ),
                    Shift::Lsr => ternary(
                        small,
                        fold(Op::Shr, x.clone(), by.clone(), 32),
                        Expr::Const(0),
                    ),
                    Shift::Asr => ternary(
                        small,
                        sar(x.clone(), by.clone()),
                        sar(x.clone(), Expr::Const(31)),
                    ),
                    Shift::Ror | Shift::Rrx => fold(
                        Op::Ror(32),
                        x.clone(),
                        fold(Op::And, by.clone(), Expr::Const(31), 32),
                        32,
                    ),
                };
                if matches!(self.ex.flags, Flags::Unknown) {
                    return (v, None);
                }
                let bit_at = |at: Expr| {
                    fold(
                        Op::And,
                        fold(Op::Shr, x.clone(), at, 32),
                        Expr::Const(1),
                        32,
                    )
                };
                let less_one = || fold(Op::Sub, by.clone(), Expr::Const(1), 32);
                let within = against(33, crate::isa::x86::ConditionCode::b);
                let out = match shift {
                    Shift::Lsl => ternary(
                        within,
                        bit_at(fold(Op::Sub, Expr::Const(32), by.clone(), 32)),
                        Expr::Const(0),
                    ),
                    Shift::Lsr => ternary(within, bit_at(less_one()), Expr::Const(0)),
                    Shift::Asr => ternary(within, bit_at(less_one()), bit_at(Expr::Const(31))),
                    Shift::Ror | Shift::Rrx => {
                        bit_at(fold(Op::And, less_one(), Expr::Const(31), 32))
                    }
                };
                let none = against(0, crate::isa::x86::ConditionCode::e);
                (v, Some(ternary(none, carry(), out)))
            }
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
    /// * `later` - The block's instructions after it.
    fn data(
        &mut self,
        i: &Insn,
        kind: DpKind,
        rd: Reg,
        rn: Reg,
        src: Operand,
        later: &[Insn],
    ) -> Option<()> {
        if !kind.compares() && rd == PC {
            return None;
        }
        let a = if kind.moves() {
            Expr::Const(0)
        } else {
            self.get(i, rn)
        };
        let (b, shifter) = self.operand(i, src);
        let not = |e: Expr| fold(Op::Xor, e, Expr::Const(WORD), 32);
        let carry = || value(&self.ex.flags, Cond::Hs);
        let flag_carry = !matches!(self.ex.flags, Flags::Unknown);
        let r = match kind {
            DpKind::And | DpKind::Tst => fold(Op::And, a.clone(), b.clone(), 32),
            DpKind::Eor | DpKind::Teq => fold(Op::Xor, a.clone(), b.clone(), 32),
            DpKind::Orr => fold(Op::Or, a.clone(), b.clone(), 32),
            DpKind::Orn => fold(Op::Or, a.clone(), not(b.clone()), 32),
            DpKind::Bic => fold(Op::And, a.clone(), not(b.clone()), 32),
            DpKind::Mov => b.clone(),
            DpKind::Mvn => not(b.clone()),
            DpKind::Add | DpKind::Cmn => fold(Op::Add, a.clone(), b.clone(), 32),
            DpKind::Sub | DpKind::Cmp => fold(Op::Sub, a.clone(), b.clone(), 32),
            DpKind::Rsb => fold(Op::Sub, b.clone(), a.clone(), 32),
            DpKind::Adc if flag_carry => fold(
                Op::Add,
                fold(Op::Add, a.clone(), b.clone(), 32),
                carry(),
                32,
            ),
            DpKind::Sbc if flag_carry => fold(
                Op::Sub,
                fold(Op::Sub, a.clone(), b.clone(), 32),
                fold(Op::Xor, carry(), Expr::Const(1), 32),
                32,
            ),
            DpKind::Rsc if flag_carry => fold(
                Op::Sub,
                fold(Op::Sub, b.clone(), a.clone(), 32),
                fold(Op::Xor, carry(), Expr::Const(1), 32),
                32,
            ),
            DpKind::Adc | DpKind::Sbc | DpKind::Rsc => return None,
        };
        if i.sets {
            let asked = next_reader(later);
            let old = self.ex.flags.clone();
            self.ex.flags = match kind {
                DpKind::Add | DpKind::Cmn => Flags::Add(a, b, 32),
                DpKind::Sub | DpKind::Cmp => Flags::Cmp(a, b, 32),
                DpKind::Rsb => Flags::Cmp(b, a, 32),
                DpKind::Adc => flags::with_carry(&a, &b, &carry(), &r),
                DpKind::Sbc => {
                    let (readers, reset) = flags::readers(later);
                    (reset || !self.flags_out)
                        .then(|| flags::wide_compare(&old, &a, &b, &readers))
                        .flatten()
                        .unwrap_or_else(|| flags::with_carry(&a, &not(b.clone()), &carry(), &r))
                }
                DpKind::Rsc => flags::with_carry(&b, &not(a), &carry(), &r),
                DpKind::And
                | DpKind::Tst
                | DpKind::Eor
                | DpKind::Teq
                | DpKind::Orr
                | DpKind::Orn
                | DpKind::Bic
                | DpKind::Mov
                | DpKind::Mvn => flags::logical(r.clone(), shifter, &old, asked),
            };
        }
        if kind.compares() {
            return Some(());
        }
        self.write(rd, r);
        Some(())
    }

    /// `umull`, `smull`, `umlal` and `smlal`: the 64-bit product, plus the
    /// pair for the accumulating forms, the low word into `lo` and the
    /// high into `hi`.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - The factors are signed.
    /// * `acc` - The pair accumulates.
    /// * `lo` - The low word's register.
    /// * `hi` - The high word's register.
    /// * `rn` - The first factor.
    /// * `rm` - The second.
    #[expect(
        clippy::too_many_arguments,
        reason = "the instruction's operands, each named as the encoding names it"
    )]
    fn mul_long(
        &mut self,
        i: &Insn,
        signed: bool,
        acc: bool,
        lo: Reg,
        hi: Reg,
        rn: Reg,
        rm: Reg,
    ) -> Option<()> {
        if i.sets || lo == PC || hi == PC {
            return None;
        }
        let (x, y) = (self.get(i, rn), self.get(i, rm));
        let p_lo = fold(Op::Mul, x.clone(), y.clone(), 32);
        let high = if signed {
            Op::SMulHi(32)
        } else {
            Op::MulHi(32)
        };
        let p_hi = fold(high, x, y, 32);
        let (v_lo, v_hi) = if acc {
            let (a_lo, a_hi) = (self.get(i, lo), self.get(i, hi));
            let sum = fold(Op::Add, p_lo.clone(), a_lo.clone(), 32);
            let carry = fold(Op::UAddO(32), p_lo, a_lo, 32);
            (sum, fold(Op::Add, fold(Op::Add, p_hi, a_hi, 32), carry, 32))
        } else {
            (p_lo, p_hi)
        };
        self.write_all(vec![(lo, v_lo), (hi, v_hi)]);
        Some(())
    }

    /// Lifts an instruction under a condition that does not move control:
    /// each register it writes takes the new value when the condition
    /// holds and keeps the old one otherwise, and flags it sets are the
    /// truth of the condition the next reader asks, chosen the same way.
    /// A store under a condition is an `if` around the store; the other
    /// forms are not modeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `later` - The block's instructions after it.
    pub(super) fn predicated(&mut self, i: &Insn, later: &[Insn]) {
        let cond = condition(&self.ex.flags, i.cond);
        if matches!(cond.flags, Flags::Unknown) {
            return self.unmodeled(i);
        }
        if let AOp::Store { .. } = i.op {
            if self.conditional_store(i, &cond).is_none() {
                self.unmodeled(i);
            }
            return;
        }
        let writes = i.registers().writes;
        if writes.contains(&SP)
            || matches!(
                i.op,
                AOp::FpCmp { .. }
                    | AOp::Vmrs { .. }
                    | AOp::Vmsr { .. }
                    | AOp::StoreEx { .. }
                    | AOp::StoreDual { .. }
                    | AOp::Stm { .. }
                    | AOp::VStore { .. }
                    | AOp::VStm { .. }
                    | AOp::Ldm { .. }
                    | AOp::VLdm { .. }
            )
        {
            return self.unmodeled(i);
        }
        let old: Vec<(Reg, Expr)> = writes.iter().map(|&r| (r, self.get(i, r))).collect();
        let old_flags = self.ex.flags.clone();
        let outer = self.ex.deferred.replace(Vec::new());
        let unmodeled = self.ex.unmodeled;
        self.step(i, later);
        let waiting = std::mem::replace(&mut self.ex.deferred, outer).unwrap_or_default();
        if self.ex.unmodeled != unmodeled {
            return;
        }
        for (r, was) in old {
            let new = self.ex.env.get(Key::A32(r));
            if new != was {
                self.write(r, ternary(cond.clone(), new, was));
            }
        }
        if i.sets {
            let new_flags = std::mem::replace(&mut self.ex.flags, old_flags.clone());
            self.ex.flags = match next_reader(later) {
                Some(asked) => {
                    let then = value(&new_flags, asked);
                    let otherwise = value(&old_flags, asked);
                    answer(asked, ternary(cond, then, otherwise))
                }
                None => Flags::Unknown,
            };
        }
        for k in waiting {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
    }
}
