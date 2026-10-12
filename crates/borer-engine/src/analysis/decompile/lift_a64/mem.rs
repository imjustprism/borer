//! Loads and stores for the arm64 lifter: one register or a pair, the
//! ordered forms, in every addressing mode.
//!
//! An address is the base plus an immediate or an extended, shifted index
//! register, or a literal's absolute address; off the stack pointer it is
//! a frame offset, so the access is a stack slot. A pre-indexed access
//! writes the address back to the base, a post-indexed one the base plus
//! the offset, after the access, the way the machine orders them. An
//! acquire or release form is its plain form, as for one thread it is.
//! The exclusive stores and the atomics are statements the lifter does not
//! model ([`super::step`]).

use super::super::expr::{Expr, Op, Ty, fold, sign_extend};
use super::{Lift, low, shifted};
use crate::isa::a64::{Insn, Mode, Opnd, Reg, Width};
use crate::num::from_usize;

/// A base register and the value an access writes back to it.
type WriteBack = Option<(Reg, Expr)>;

/// The type one element of `width` moves for a register of `bits`, and
/// whether the load sign-extends it.
///
/// # Arguments
///
/// * `width` - What the access moves.
/// * `bits` - The register's width: 32 or 64, or 8 to 128 for a `v`
///   register.
fn access(width: Width, bits: u16) -> (Ty, bool) {
    match width {
        Width::Reg => (Ty::from_bits(u8::try_from(bits).unwrap_or(u8::MAX)), false),
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
                shifted(self.read(reg), bits, m.extend, m.shift, 64),
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
        let index = self.read(reg);
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
        let (ty, signed) = access(width, bits);
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
        let ty = access(width, bits).0;
        let v = stored(self.read(rt), ty);
        self.ex.store_at(addr, ty, v);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
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
        let (ty, signed) = access(width, bits);
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
        let (ty, _) = access(Width::Reg, bits);
        let step = Expr::Const(from_usize(usize::from(bits / 8)));
        let (addr, _) = self.address(i.operands[2])?;
        let a = stored(self.read(first), ty);
        self.ex.store_at(addr, ty, a);
        // INVARIANT: the first store may write a register out under its
        // own name (one whose value reads the memory stored to), which
        // leaves an expression read before it naming the register's new
        // value; the second half's address and value are read again after
        // it, so they name what the registers hold now.
        let (addr, back) = self.address(i.operands[2])?;
        let b = stored(self.read(second), ty);
        self.ex.store_at(fold(Op::Add, addr, step, 64), ty, b);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }
}
