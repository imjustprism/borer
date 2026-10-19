//! Loads and stores for the ARM32 lifter: one register, a pair, and the
//! block transfers, in every addressing mode.
//!
//! An address is the base plus an immediate or a shifted register, or a
//! literal's absolute address; off the stack pointer it is a frame offset,
//! so the access is a stack slot. A pre-indexed access writes the address
//! back to its base and a post-indexed one the base plus the offset, after
//! the access. `push` and `stm` store the lowest register at the lowest
//! address, `pop` and `ldm` load them so, and a `strex` is its store and a
//! status of zero.

use super::super::expr::{Cond, Expr, Op, Ty, fold, mask, sign_extend, ternary};
use super::super::lift::EffectKind;
use super::{Lift, offset};
use crate::isa::a32::{Addr, Block, Index, Insn, Offset, Op as AOp, PC, Reg, Shift, Width};

/// The type a load or store of `width` moves.
///
/// # Arguments
///
/// * `width` - What it moves.
pub(super) fn access(width: Width) -> Ty {
    match width {
        Width::Word => Ty::U32,
        Width::Byte | Width::SByte => Ty::U8,
        Width::Half | Width::SHalf => Ty::U16,
    }
}

/// A register shifted by a constant for an address, without the carry.
///
/// # Arguments
///
/// * `x` - The register's value.
/// * `shift` - The shift.
/// * `n` - The amount.
fn scaled(x: Expr, shift: Shift, n: u8) -> Expr {
    let by = Expr::Const(u64::from(n));
    match (shift, n) {
        (_, 0) => x,
        (Shift::Lsl, _) => fold(Op::Shl, x, by, 32),
        (Shift::Lsr, _) => fold(Op::Shr, x, by, 32),
        (Shift::Asr, _) => super::step::sar(x, by),
        (Shift::Ror | Shift::Rrx, _) => fold(Op::Ror(32), x, by, 32),
    }
}

impl Lift<'_, '_> {
    /// The address a memory operand names, and the value it writes back
    /// to its base.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `a` - The operand.
    pub(super) fn address(&self, i: &Insn, a: Addr) -> (Expr, Option<(Reg, Expr)>) {
        let base = if a.base == PC {
            Expr::Const(i.pc() & !3 & super::WORD)
        } else {
            self.get(i, a.base)
        };
        let at = match a.offset {
            Offset::Imm(d) => offset(base.clone(), i64::from(d)),
            Offset::Reg {
                rm,
                sub,
                shift,
                amount,
            } => {
                let off = scaled(self.get(i, rm), shift, amount);
                fold(if sub { Op::Sub } else { Op::Add }, base.clone(), off, 32)
            }
        };
        match a.index {
            Index::Offset => (at, None),
            Index::Pre => (at.clone(), Some((a.base, at))),
            Index::Post => (base, Some((a.base, at))),
        }
    }

    /// The value a load from a literal pool reads: the bytes the image
    /// holds at a `pc`-relative address in a section nothing writes, which
    /// are as constant as the code around them.
    ///
    /// # Arguments
    ///
    /// * `a` - The load's memory operand.
    /// * `at` - The address it names.
    /// * `n` - The bytes it reads, 1 to 8.
    ///
    /// # Returns
    ///
    /// The little-endian value, or `None` for a load that is no literal's.
    pub(super) fn literal(&self, a: Addr, at: &Expr, n: u16) -> Option<u64> {
        let Expr::Const(va) = *at else {
            return None;
        };
        if a.base != PC || a.index != Index::Offset {
            return None;
        }
        let program = self.ex.ctx.program;
        if program.section_at(va)?.writable {
            return None;
        }
        let bytes = program.read_va(va, usize::from(n))?;
        Some(
            bytes
                .iter()
                .rev()
                .fold(0, |acc, b| (acc << 8) | u64::from(*b)),
        )
    }

    /// Lifts a load or store of core registers.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// `None` for a form not modeled: one that writes `pc` (lifted as the
    /// jump or return it is), or a base written back that is also loaded.
    pub(super) fn memory(&mut self, i: &Insn) -> Option<()> {
        match i.op {
            AOp::Load { width, rt, addr } | AOp::LoadEx { width, rt, addr } => {
                if rt == PC {
                    return None;
                }
                let (at, back) = self.address(i, addr);
                if let Some(t) = self.dispatch_index(i, addr) {
                    self.table_idx = Some(t);
                }
                let ty = access(width);
                let v = match self.literal(addr, &at, u16::from(ty.bits() / 8)) {
                    Some(c) => Expr::Const(c),
                    None => self.ex.read_at(at, ty),
                };
                let v = if width.signed() {
                    sign_extend(v, ty.bits())
                } else {
                    v
                };
                let mut writes = vec![(rt, v)];
                writes.extend(back);
                self.write_all(writes);
                Some(())
            }
            AOp::Store { width, rt, addr } => {
                let ty = access(width);
                let v = self.get(i, rt);
                let v = if ty.bits() < 32 {
                    mask(v, (1u64 << ty.bits()) - 1)
                } else {
                    v
                };
                let (at, back) = self.address(i, addr);
                self.ex.store_at(at, ty, v);
                if let Some((r, a)) = back {
                    self.write(r, a);
                }
                Some(())
            }
            AOp::StoreEx {
                width,
                rd,
                rt,
                addr,
            } => {
                let ty = access(width);
                let v = self.get(i, rt);
                let v = if ty.bits() < 32 {
                    mask(v, (1u64 << ty.bits()) - 1)
                } else {
                    v
                };
                let (at, _) = self.address(i, addr);
                self.ex.store_at(at, ty, v);
                self.put(rd, Expr::Const(0))
            }
            AOp::LoadDual { rt, rt2, addr } => {
                let (at, back) = self.address(i, addr);
                let a = self.ex.read_at(at.clone(), Ty::U32);
                let b = self.ex.read_at(offset(at, 4), Ty::U32);
                let mut writes = vec![(rt, a), (rt2, b)];
                writes.extend(back);
                self.write_all(writes);
                Some(())
            }
            AOp::StoreDual { rt, rt2, addr } => {
                let (a, b) = (self.get(i, rt), self.get(i, rt2));
                let (at, back) = self.address(i, addr);
                self.ex.store_at(at.clone(), Ty::U32, a);
                self.ex.store_at(offset(at, 4), Ty::U32, b);
                if let Some((r, w)) = back {
                    self.write(r, w);
                }
                Some(())
            }
            AOp::Ldm {
                rn,
                regs,
                wback,
                block,
            } => self.load_multiple(i, rn, regs & 0x7fff, wback, block),
            AOp::Stm {
                rn,
                regs,
                wback,
                block,
            } => {
                if regs & 0x8000 != 0 {
                    return None;
                }
                let (start, end) = self.span(i, rn, regs, block);
                let values: Vec<Expr> = list(regs).map(|r| self.get(i, r)).collect();
                for (k, v) in (0i64..).zip(values) {
                    self.ex.store_at(offset(start.clone(), 4 * k), Ty::U32, v);
                }
                if wback {
                    self.write(rn, end);
                }
                Some(())
            }
            AOp::Dp { .. }
            | AOp::Movw { .. }
            | AOp::Movt { .. }
            | AOp::Adr { .. }
            | AOp::Mul { .. }
            | AOp::MulLong { .. }
            | AOp::Smmul { .. }
            | AOp::Smulxy { .. }
            | AOp::Div { .. }
            | AOp::Clz { .. }
            | AOp::Rbit { .. }
            | AOp::Rev { .. }
            | AOp::Rev16 { .. }
            | AOp::Revsh { .. }
            | AOp::Bfx { .. }
            | AOp::Sat { .. }
            | AOp::Bfi { .. }
            | AOp::Extend { .. }
            | AOp::B { .. }
            | AOp::Bl { .. }
            | AOp::Blx { .. }
            | AOp::BlxReg { .. }
            | AOp::Bx { .. }
            | AOp::Cbz { .. }
            | AOp::Tb { .. }
            | AOp::It { .. }
            | AOp::Svc { .. }
            | AOp::Trap
            | AOp::Nop
            | AOp::Mrs { .. }
            | AOp::Msr { .. }
            | AOp::VLoad { .. }
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
            | AOp::Vmrs { .. }
            | AOp::Vmsr { .. }
            | AOp::Neon { .. }
            | AOp::Unknown
            | AOp::Invalid => None,
        }
    }

    /// The loads of `ldm` and `pop`, `pc` left out: each listed register
    /// from its word, the base written back.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `rn` - The base.
    /// * `regs` - The registers, `pc` not among them.
    /// * `wback` - Whether the base is written back.
    /// * `block` - The order.
    pub(super) fn load_multiple(
        &mut self,
        i: &Insn,
        rn: Reg,
        regs: u16,
        wback: bool,
        block: Block,
    ) -> Option<()> {
        let all = if let AOp::Ldm { regs: r, .. } = i.op {
            r
        } else {
            regs
        };
        let (start, end) = self.span(i, rn, all, block);
        let mut writes: Vec<(Reg, Expr)> = list(regs)
            .zip(0i64..)
            .map(|(r, k)| (r, self.ex.read_at(offset(start.clone(), 4 * k), Ty::U32)))
            .collect();
        if wback && regs & (1 << register_number(rn)) == 0 {
            writes.push((rn, end));
        }
        self.write_all(writes);
        Some(())
    }

    /// The first address a block transfer touches and the base it writes
    /// back.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `rn` - The base.
    /// * `regs` - Every register it moves, `pc` among them.
    /// * `block` - The order.
    fn span(&self, i: &Insn, rn: Reg, regs: u16, block: Block) -> (Expr, Expr) {
        let base = self.get(i, rn);
        let bytes = 4 * i64::from(regs.count_ones());
        match block {
            Block::Ia => (base.clone(), offset(base, bytes)),
            Block::Ib => (offset(base.clone(), 4), offset(base, bytes)),
            Block::Da => (offset(base.clone(), 4 - bytes), offset(base, -bytes)),
            Block::Db => (offset(base.clone(), -bytes), offset(base, -bytes)),
        }
    }

    /// The index of the jump table a load reads an entry of, when the
    /// block dispatches through it: the load's index register.
    ///
    /// # Arguments
    ///
    /// * `i` - The load.
    /// * `addr` - Its address.
    fn dispatch_index(&self, i: &Insn, addr: Addr) -> Option<Expr> {
        if self.table_load != Some(i.va) {
            return None;
        }
        let Offset::Reg { rm, .. } = addr.offset else {
            return None;
        };
        Some(self.get(i, rm))
    }

    /// A store under a condition: memory takes the value when the
    /// condition holds and keeps what it held otherwise, the text an `if`
    /// around the store. Write-back forms are not modeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The store.
    /// * `cond` - Its condition on the flags.
    pub(super) fn conditional_store(&mut self, i: &Insn, cond: &Cond) -> Option<()> {
        let AOp::Store { width, rt, addr } = i.op else {
            return None;
        };
        if addr.index != Index::Offset {
            return None;
        }
        let ty = access(width);
        let v = self.get(i, rt);
        let mut new = if ty.bits() < 32 {
            mask(v, (1u64 << ty.bits()) - 1)
        } else {
            v
        };
        let (mut at, _) = self.address(i, addr);
        if matches!(at, Expr::Sp(_)) {
            return None;
        }
        let loaded = self.ex.read_at(at.clone(), ty);
        let mut seen = self.ex.tmp_of(&loaded, ty);
        self.ex.settle_frame_region(&at, None, false, true);
        let c = cond.clone();
        self.ex.protect_memory_around(&mut [
            (&mut at, self.ex.word_ty()),
            (&mut new, ty),
            (&mut seen, ty),
        ]);
        let kept = ternary(c.clone(), new.clone(), seen);
        self.ex.note_escape(&kept);
        self.ex.note_escape(&at);
        if let Some(p) = &mut self.ex.ctx.probe {
            p.store(&at, ty, &kept);
        }
        if self.ex.emit {
            let names = self.ex.names();
            let shown = c.render(&names, false);
            let lhs = Expr::deref(at.clone(), ty).render(&names);
            let rhs = new.render(&names);
            self.ex.lines.push(format!("if ({shown}) {{"));
            self.ex.lines.push(format!("{lhs} = {rhs};"));
            self.ex.lines.push("}".to_owned());
        }
        self.ex.record(EffectKind::Store(Box::new((at, ty, kept))));
        Some(())
    }
}

/// The registers of a block transfer, lowest first.
///
/// # Arguments
///
/// * `regs` - Bit `n` for `rn`.
pub(super) fn list(regs: u16) -> impl Iterator<Item = Reg> {
    (0u8..16).filter(move |n| regs & (1 << n) != 0).map(Reg::R)
}

/// The number of a core register.
///
/// # Arguments
///
/// * `r` - The register.
fn register_number(r: Reg) -> u8 {
    match r {
        Reg::R(n) => n,
        Reg::S(_) | Reg::D(_) => 0,
    }
}
