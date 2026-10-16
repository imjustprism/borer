//! Loads and stores for the arm64 lifter: one register or a pair, the
//! ordered forms, in every addressing mode.
//!
//! An address is the base plus an immediate or an extended, shifted index
//! register, or a literal's absolute address; off the stack pointer it is
//! a frame offset, so the access is a stack slot. A pre-indexed access
//! writes the address back to the base, a post-indexed one the base plus
//! the offset, after the access, the way the machine orders them. An
//! acquire or release form is its plain form, as for one thread it is.
//! A store-exclusive is that store and a status of zero, which is how the
//! machine runs it; it does not fail. An atomic is that load, the
//! modification, and the store, with the old value left in the destination;
//! `cas` stores only when memory matches, and either way leaves the old
//! value in the compare register.

use super::super::expr::{Cc, Cond, Expr, Flags, Op, Ty, UnOp, fold, sign_extend, ternary, unary};
use super::super::lift::EffectKind;
use super::{Lift, low, shifted};
use crate::isa::a64::{self, Insn, Mode, Opnd, Reg, Rmw, Width};
use crate::isa::x86::ConditionCode;
use crate::num::{from_usize, lo8};

/// A base register and the value an access writes back to it.
type WriteBack = Option<(Reg, Expr)>;

/// Bytes one `ld1`/`st1` register moves.
const GROUP_BYTES: u64 = 16;

/// The `v` register `k` places after `first` in an `ld1`/`st1` group,
/// wrapping from `v31` to `v0` as the architecture numbers them.
///
/// # Arguments
///
/// * `first` - The first register's number.
/// * `k` - The offset from it.
fn group_reg(first: u8, k: u32) -> Reg {
    Reg::V(first.wrapping_add(lo8(u64::from(k))) % 32)
}

/// The type one element of `width` moves for a register of `bits`, and
/// whether the load sign-extends it.
///
/// A `v` register at a single's or a double's width moves a float, as the
/// x86 lifter's `movss` and `movsd` do, so the access itself types it.
///
/// # Arguments
///
/// * `width` - What the access moves.
/// * `r` - The register moved, whose class tells a float.
/// * `bits` - The register's width: 32 or 64, or 8 to 128 for a `v`
///   register.
fn access(width: Width, r: Reg, bits: u16) -> (Ty, bool) {
    let float = match r {
        Reg::V(_) => matches!(bits, 32 | 64),
        Reg::X(_) | Reg::Sp | Reg::Zr => false,
    };
    match width {
        Width::Reg => (
            match (bits, float) {
                (32, true) => Ty::F32,
                (64, true) => Ty::F64,
                _ => Ty::from_bits(u8::try_from(bits).unwrap_or(u8::MAX)),
            },
            false,
        ),
        Width::Byte => (Ty::U8, false),
        Width::Half => (Ty::U16, false),
        Width::SByte => (Ty::U8, true),
        Width::SHalf => (Ty::U16, true),
        Width::SWord => (Ty::U32, true),
    }
}

/// Returns the value a store of `ty` writes.
///
/// A register's value is cut to a narrower store's width, so a slot
/// holding it reads back as the bytes the store wrote. A whole register
/// stored is its own variable, which a prologue's save is recognized by.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `ty` - The store's type.
fn stored(v: Expr, ty: Ty) -> Expr {
    match ty.bits() {
        bits @ 1..=63 => low(v, u16::from(bits)),
        _ => v,
    }
}

/// A register operand of a load or store, general or `v`, with its width.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `k` - The operand's position.
fn register(i: &Insn, k: usize) -> Option<(Reg, u16)> {
    match i.operands.get(k).copied()? {
        Opnd::Reg { reg, bits } => Some((reg, bits)),
        Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    }
}

impl Lift<'_, '_> {
    /// The address a memory operand names, and the write-back it makes.
    ///
    /// # Arguments
    ///
    /// * `o` - The operand.
    ///
    /// # Returns
    ///
    /// The address the access is at, and the base register with the value
    /// a pre- or post-indexed form leaves in it; `None` when the operand is
    /// no memory operand or literal address.
    fn address(&self, o: Opnd) -> Option<(Expr, WriteBack)> {
        let m = match o {
            Opnd::PcRel(at) => return Some((Expr::Const(at), None)),
            Opnd::Mem(m) => m,
            Opnd::None
            | Opnd::Reg { .. }
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::Cond(_)
            | Opnd::Other => return None,
        };
        let base = self.read(m.base);
        let indexed = match m.index {
            Some((reg, bits)) => fold(
                Op::Add,
                base.clone(),
                shifted(self.reg_at(reg, bits), bits, m.extend, m.shift, 64),
                64,
            ),
            None => base.clone(),
        };
        let at = fold(Op::Add, indexed, Expr::Const(m.disp.cast_unsigned()), 64);
        Some(match m.mode {
            Mode::Offset => (at, None),
            Mode::PreIndex => (at.clone(), Some((m.base, at))),
            Mode::PostIndex => (base, Some((m.base, at))),
        })
    }

    /// The index a jump table's entry is loaded at: the index register,
    /// extended but not scaled, so case `k` is entry `k`; the base when it
    /// is the index register that holds the table's address.
    ///
    /// # Arguments
    ///
    /// * `o` - The load's memory operand.
    fn table_index(&self, o: Opnd) -> Option<Expr> {
        let Opnd::Mem(m) = o else {
            return None;
        };
        let (reg, bits) = m.index?;
        let index = self.reg_at(reg, bits);
        let base = self.read(m.base);
        Some(match (&index, &base) {
            (Expr::Const(_), b) if !matches!(b, Expr::Const(_)) => base,
            _ => shifted(index, bits, m.extend, 0, 64),
        })
    }

    /// A load of one register (`ldr`, `ldur`, `ldar`, `ldxr`, `ldraa`, the
    /// literal form, and the narrow and signed forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    pub(super) fn load(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i.operands[1])?;
        if self.table_load == Some(i.va) {
            self.ex.switch_idx = self.table_index(i.operands[1]);
        }
        let (ty, signed) = access(width, rt, bits);
        let v = self.ex.read_at(addr, ty);
        let v = if signed { sign_extend(v, ty.bits()) } else { v };
        let mut writes = vec![(rt, bits, v)];
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// A store of one register (`str`, `stur`, `stlr`, and the narrow
    /// forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    pub(super) fn store(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i.operands[1])?;
        let ty = access(width, rt, bits).0;
        let v = stored(self.reg_at(rt, bits), ty);
        self.ex.store_at(addr, ty, v);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }

    /// A store-exclusive of one register (`stxr`, `stlxr`), which always
    /// succeeds: the store, then status 0 at 32 bits, as the machine
    /// writes it. Ordering and a failed monitor add nothing it does.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, register, address.
    /// * `width` - What it moves.
    pub(super) fn store_exclusive(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (status, _) = register(i, 0)?;
        let (rt, bits) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        let v = stored(self.reg_at(rt, bits), ty);
        self.ex.store_at(addr, ty, v);
        self.write(status, 32, Expr::Const(0));
        Some(())
    }

    /// A store-exclusive of two registers (`stxp`, `stlxp`), which always
    /// succeeds: the two stores, then status 0 at 32 bits, as the machine
    /// writes it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, two registers, address.
    pub(super) fn store_exclusive_pair(&mut self, i: &Insn) -> Option<()> {
        let (status, _) = register(i, 0)?;
        let (first, bits) = register(i, 1)?;
        let (second, _) = register(i, 2)?;
        let (ty, _) = access(Width::Reg, first, bits);
        let step = Expr::Const(from_usize(usize::from(bits / 8)));
        let (addr, _) = self.address(i.operands[3])?;
        let a = stored(self.reg_at(first, bits), ty);
        let b = stored(self.reg_at(second, bits), ty);
        self.ex.store_at(addr.clone(), ty, a);
        self.ex.store_at(fold(Op::Add, addr, step, 64), ty, b);
        self.write(status, 32, Expr::Const(0));
        Some(())
    }

    /// An atomic read-modify-write (`ldadd`, `ldclr`, `ldeor`, `ldset`,
    /// `ldsmax`, `ldsmin`, `ldumax`, `ldumin`, `swp`, in every ordering).
    ///
    /// Memory takes `op` of its old value and `Rs`, and `Rt` takes the old
    /// value. The old value is read into a temporary before anything is
    /// written, so `Rt` and `Rs` being one register still uses the value
    /// the instruction read, and a later read of `Rt` does not see the
    /// bytes the store just wrote. Ordering adds nothing one thread observes.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `op` - The modification.
    /// * `width` - What it moves.
    pub(super) fn atomic(&mut self, i: &Insn, op: Rmw, width: Width) -> Option<()> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        let n = ty.bits();
        let loaded = self.ex.read_at(addr.clone(), ty);
        let old = self.ex.tmp_of(&loaded, ty);
        let s = stored(self.reg_at(rs, bits), ty);
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
            Rmw::Add => fold(Op::Add, old.clone(), s, n),
            Rmw::Clr => fold(Op::And, old.clone(), unary(UnOp::Not, s, n), n),
            Rmw::Eor => fold(Op::Xor, old.clone(), s, n),
            Rmw::Set => fold(Op::Or, old.clone(), s, n),
            Rmw::Smax => pick(ConditionCode::ge, old.clone(), s),
            Rmw::Smin => pick(ConditionCode::le, old.clone(), s),
            Rmw::Umax => pick(ConditionCode::ae, old.clone(), s),
            Rmw::Umin => pick(ConditionCode::be, old.clone(), s),
            Rmw::Swp => s,
        };
        self.write(rt, bits, old);
        self.ex.store_at(addr, ty, new);
        Some(())
    }

    /// `cas` in every ordering.
    ///
    /// Memory takes `Rt` when it equals `Rs`, and `Rs` takes the old value
    /// either way. The text is an `if` around that store; the recorded
    /// store is the old bytes when the compare fails, which is the memory
    /// the machine leaves. The old value is read before `Rs` is written, so
    /// the compare still sees the register the instruction read. Ordering
    /// adds nothing one thread observes.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `width` - What it moves.
    pub(super) fn compare_swap(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        let loaded = self.ex.read_at(addr.clone(), ty);
        let old = self.ex.tmp_of(&loaded, ty);
        let mut expect = stored(self.reg_at(rs, bits), ty);
        let mut new = stored(self.reg_at(rt, bits), ty);
        let mut at = addr;
        self.ex.settle_frame_region(&at, None, false, true);
        let mut seen = old.clone();
        self.ex.protect_memory_around(&mut [
            (&mut at, self.ex.word_ty()),
            (&mut new, ty),
            (&mut seen, ty),
            (&mut expect, ty),
        ]);
        let n = ty.bits();
        let new = match ty {
            Ty::U8 | Ty::U16 | Ty::U32 => crate::analysis::decompile::expr::low_bits_read(new, n),
            Ty::U64 | Ty::U128 | Ty::F32 | Ty::F64 => new,
        };
        let eq = Cond {
            cc: Cc(ConditionCode::e),
            flags: Flags::Cmp(seen.clone(), expect, n),
        };
        let kept = ternary(eq.clone(), new.clone(), seen);
        self.ex.note_escape(&kept);
        self.ex.note_escape(&at);
        if let Expr::Const(a) = at
            && self.ex.emit
            && self.ex.is_data(a)
        {
            self.ex.ctx.globals.insert((a, ty));
        }
        if let Some(p) = &mut self.ex.ctx.probe {
            p.store(&at, ty, &kept);
        }
        if self.ex.emit {
            let names = self.ex.names();
            let cond = eq.render(&names, false);
            let lhs = Expr::deref(at.clone(), ty).render(&names);
            let rhs = new.render(&names);
            self.ex.lines.push(format!("if ({cond}) {{"));
            self.ex.lines.push(format!("{lhs} = {rhs};"));
            self.ex.lines.push("}".to_owned());
        }
        self.ex.record(EffectKind::Store(Box::new((at, ty, kept))));
        self.write(rs, bits, old);
        Some(())
    }

    /// A load of two registers from consecutive elements (`ldp`, `ldnp`,
    /// `ldxp`, `ldaxp`, `ldpsw`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    /// * `width` - What each element moves.
    pub(super) fn load_pair(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (addr, back) = self.address(i.operands[2])?;
        let (ty, signed) = access(width, first, bits);
        let step = Expr::Const(u64::from(ty.bits() / 8));
        let a = self.ex.read_at(addr.clone(), ty);
        let b = self.ex.read_at(fold(Op::Add, addr, step, 64), ty);
        let extend = |v: Expr| if signed { sign_extend(v, ty.bits()) } else { v };
        let mut writes = vec![(first, bits, extend(a)), (second, bits, extend(b))];
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// A store of two registers to consecutive elements (`stp`, `stnp`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    pub(super) fn store_pair(&mut self, i: &Insn) -> Option<()> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (ty, _) = access(Width::Reg, first, bits);
        let step = Expr::Const(from_usize(usize::from(bits / 8)));
        let (addr, _) = self.address(i.operands[2])?;
        let a = stored(self.reg_at(first, bits), ty);
        self.ex.store_at(addr, ty, a);
        let (addr, back) = self.address(i.operands[2])?;
        let b = stored(self.reg_at(second, bits), ty);
        self.ex.store_at(fold(Op::Add, addr, step, 64), ty, b);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }

    /// `ld1`: one to four consecutive `v` registers loaded from
    /// consecutive sixteen-byte blocks, the base written back as its
    /// operand says — a pair load generalized to its register count.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    pub(super) fn load_group(&mut self, i: &Insn) -> Option<()> {
        let (first, count) = a64::ld1_group(i.word)?;
        let (addr, back) = self.address(i.operands[1])?;
        let mut writes = Vec::with_capacity(usize::from(count) + 1);
        for k in 0..u32::from(count) {
            let at = if k == 0 {
                addr.clone()
            } else {
                fold(
                    Op::Add,
                    addr.clone(),
                    Expr::Const(u64::from(k) * GROUP_BYTES),
                    64,
                )
            };
            writes.push((group_reg(first, k), 128, self.ex.read_at(at, Ty::U128)));
        }
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// `st1`: the store counterpart of [`Lift::load_group`].
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    pub(super) fn store_group(&mut self, i: &Insn) -> Option<()> {
        let (first, count) = a64::ld1_group(i.word)?;
        for k in 0..u32::from(count) {
            let (addr, _) = self.address(i.operands[1])?;
            let v = stored(self.reg_at(group_reg(first, k), 128), Ty::U128);
            self.ex.store_at(
                fold(Op::Add, addr, Expr::Const(u64::from(k) * GROUP_BYTES), 64),
                Ty::U128,
                v,
            );
        }
        let (_, back) = self.address(i.operands[1])?;
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }
}
