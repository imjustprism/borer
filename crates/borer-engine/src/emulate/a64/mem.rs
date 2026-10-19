//! Loads and stores for the arm64 machine: one register or a pair, the
//! ordered and exclusive forms, and the atomics, in every addressing mode.
//!
//! An address is the base plus an immediate or an extended, shifted index
//! register, or a literal's absolute address; a pre-indexed access writes
//! the address back to the base and a post-indexed one the base plus the
//! offset, after the access. Ordering does not matter to one thread, so an
//! acquire or release form is its plain form, a store-exclusive always
//! succeeds, and an atomic is a load and a store.

use super::{Machine, mask_wide, on_stack, unmodeled};
use crate::emulate::{HISTORY_MAX, MEMORY_MAX, Stop, Written, lo64, mask, sign_extend};
use crate::isa::a64::{self, Insn, Layout, Mode, Opnd, Reg, Rmw, Width};
use crate::num::{from_usize, lo8};

/// A base register and the value an access writes back to it.
type WriteBack = Option<(Reg, u64)>;

/// Bytes a whole `v` register moves.
const GROUP_LEN: usize = 16;

impl Machine<'_> {
    /// The address a memory operand names, and the write-back it makes.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The memory operand's position.
    ///
    /// # Returns
    ///
    /// The address the access is at, and the base register with the value
    /// a pre- or post-indexed form leaves in it.
    ///
    /// # Errors
    ///
    /// When the operand is no memory operand or literal address.
    fn address(&self, i: &Insn, k: usize) -> Result<(u64, WriteBack), Stop> {
        let m = match i.operands.get(k).copied().unwrap_or(Opnd::None) {
            Opnd::PcRel(at) => return Ok((at, None)),
            Opnd::Mem(m) => m,
            Opnd::None
            | Opnd::Reg { .. }
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::Cond(_)
            | Opnd::Other => return Err(unmodeled(i)),
        };
        let base = lo64(self.reg(m.base));
        let index = m.index.map_or(0, |(reg, bits)| {
            super::alu::shifted(lo64(self.reg(reg)), u32::from(bits), m.extend, m.shift, 64)
        });
        let offset = m.disp.cast_unsigned().wrapping_add(index);
        Ok(match m.mode {
            Mode::Offset => (base.wrapping_add(offset), None),
            Mode::PreIndex => {
                let at = base.wrapping_add(offset);
                (at, Some((m.base, at)))
            }
            Mode::PostIndex => (base, Some((m.base, base.wrapping_add(offset)))),
        })
    }

    /// Applies an access's write-back to its base register.
    ///
    /// # Arguments
    ///
    /// * `back` - The base and its new value, if the access writes back.
    fn write_back(&mut self, back: WriteBack) {
        if let Some((reg, v)) = back {
            self.set_reg(reg, 64, u128::from(v));
        }
    }

    /// Loads `bytes` bytes, little-endian.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most sixteen.
    ///
    /// # Errors
    ///
    /// A fault at the first byte neither written nor backed by the image.
    fn load(&mut self, addr: u64, bytes: usize) -> Result<u128, Stop> {
        let mut v = 0u128;
        for (k, shift) in (0..from_usize(bytes)).zip((0u32..).step_by(8)) {
            let a = addr.wrapping_add(k);
            v |= u128::from(self.load_byte(a).ok_or(Stop::Fault(a))?) << shift;
        }
        if self.trace_cap > 0 {
            self.step_memory.push((false, addr, bytes, v));
        }
        Ok(v)
    }

    /// Stores the low `bytes` bytes of `v`, little-endian, recording each
    /// byte in the write history and marking those off the stack as
    /// written.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most sixteen.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when a byte not yet held would take memory
    /// past [`MEMORY_MAX`]; the bytes before it are written.
    fn store(&mut self, addr: u64, bytes: usize, v: u128) -> Result<(), Stop> {
        if self.trace_cap > 0 {
            let shown = mask_wide(v, u16::try_from(bytes * 8).unwrap_or(128));
            self.step_memory.push((true, addr, bytes, shown));
        }
        for (k, shift) in (0..from_usize(bytes)).zip((0u32..).step_by(8)) {
            let a = addr.wrapping_add(k);
            if self.mem.len() >= MEMORY_MAX && !self.mem.contains(a) {
                return Err(Stop::MemoryFull(a));
            }
            let value = lo8(lo64(v >> shift));
            if self.history.len() < HISTORY_MAX {
                self.history.push(Written { addr: a, value });
            }
            self.mem.set(a, value, !on_stack(a));
        }
        Ok(())
    }

    /// Loads one element of `width` for a register of `bits`, extended as
    /// the width says.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `width` - What the load moves.
    /// * `bits` - The register's width.
    ///
    /// # Errors
    ///
    /// When the load faults.
    fn load_as(&mut self, addr: u64, width: Width, bits: u16) -> Result<u128, Stop> {
        let bytes = width_bytes(width, bits);
        let v = self.load(addr, bytes)?;
        Ok(match width {
            Width::Reg | Width::Byte | Width::Half => v,
            Width::SByte | Width::SHalf | Width::SWord => {
                let from = u32::try_from(bytes * 8).unwrap_or(64);
                u128::from(sign_extend(lo64(v), from).cast_unsigned())
            }
        })
    }

    /// A load of one register (`ldr`, `ldur`, `ldar`, `ldxr`, `ldraa`, the
    /// literal form, and the narrow and signed forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or the load faults.
    pub(super) fn load_one(&mut self, i: &Insn, width: Width) -> Result<(), Stop> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i, 1)?;
        let v = self.load_as(addr, width, bits)?;
        self.set_reg(rt, bits, v);
        self.write_back(back);
        Ok(())
    }

    /// A store of one register (`str`, `stur`, `stlr`, and the narrow
    /// forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or memory is full.
    pub(super) fn store_one(&mut self, i: &Insn, width: Width) -> Result<(), Stop> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i, 1)?;
        self.store(addr, width_bytes(width, bits), self.reg(rt))?;
        self.write_back(back);
        Ok(())
    }

    /// A load of two registers from consecutive elements (`ldp`, `ldnp`,
    /// `ldxp`, `ldaxp`, `ldpsw`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    /// * `width` - What each element moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or a load faults.
    pub(super) fn load_pair(&mut self, i: &Insn, width: Width) -> Result<(), Stop> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (addr, back) = self.address(i, 2)?;
        let step = from_usize(width_bytes(width, bits));
        let a = self.load_as(addr, width, bits)?;
        let b = self.load_as(addr.wrapping_add(step), width, bits)?;
        self.set_reg(first, bits, a);
        self.set_reg(second, bits, b);
        self.write_back(back);
        Ok(())
    }

    /// A store of two registers to consecutive elements (`stp`, `stnp`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or memory is full.
    pub(super) fn store_pair(&mut self, i: &Insn) -> Result<(), Stop> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (addr, back) = self.address(i, 2)?;
        let bytes = width_bytes(Width::Reg, bits);
        self.store(addr, bytes, self.reg(first))?;
        self.store(
            addr.wrapping_add(from_usize(bytes)),
            bytes,
            self.reg(second),
        )?;
        self.write_back(back);
        Ok(())
    }

    /// `ld1` to `ld4` and `ld1r` to `ld4r` in every form
    /// ([`a64::structure`]): whole registers, interleaved elements, one
    /// lane of each register with the rest kept, or one element
    /// replicated, the base written back as its operand says.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    ///
    /// # Errors
    ///
    /// When the word is no structure load the machine reads, or a load
    /// faults.
    pub(super) fn load_structure(&mut self, i: &Insn) -> Result<(), Stop> {
        let s = a64::structure(i.word).ok_or_else(|| unmodeled(i))?;
        let (addr, back) = self.address(i, 1)?;
        let span = if s.whole { GROUP_LEN } else { GROUP_LEN / 2 };
        let mut regs = Vec::with_capacity(usize::from(s.count));
        for k in 0..s.count {
            regs.push(match s.layout {
                Layout::Blocks => {
                    self.load(addr.wrapping_add(u64::from(k) * from_usize(span)), span)?
                }
                Layout::Lane(_) => self.reg(s.reg(k)),
                Layout::Interleaved | Layout::Replicate => 0,
            });
        }
        if s.layout != Layout::Blocks {
            let bytes = usize::from(s.elem / 8);
            for slot in s.slots() {
                let v = self.load(addr.wrapping_add(slot.at), bytes)?;
                let at = slot.lane * u32::from(s.elem);
                if let Some(r) = regs.get_mut(usize::from(slot.reg)) {
                    *r = (*r & !(mask_wide(u128::MAX, s.elem) << at)) | (v << at);
                }
            }
        }
        for (k, v) in (0u8..).zip(regs) {
            self.set_reg(s.reg(k), 128, v);
        }
        self.write_back(back);
        Ok(())
    }

    /// `st1` to `st4` in every form: the store counterpart of
    /// [`Machine::load_structure`].
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    ///
    /// # Errors
    ///
    /// When the word is no structure store, or memory is full.
    pub(super) fn store_structure(&mut self, i: &Insn) -> Result<(), Stop> {
        let s = a64::structure(i.word).ok_or_else(|| unmodeled(i))?;
        if s.layout == Layout::Replicate {
            return Err(unmodeled(i));
        }
        let (addr, back) = self.address(i, 1)?;
        if s.layout == Layout::Blocks {
            let span = if s.whole { GROUP_LEN } else { GROUP_LEN / 2 };
            for k in 0..s.count {
                let at = addr.wrapping_add(u64::from(k) * from_usize(span));
                self.store(at, span, self.reg(s.reg(k)))?;
            }
        } else {
            let bytes = usize::from(s.elem / 8);
            for slot in s.slots() {
                let v = self.reg(s.reg(slot.reg)) >> (slot.lane * u32::from(s.elem));
                self.store(addr.wrapping_add(slot.at), bytes, v)?;
            }
        }
        self.write_back(back);
        Ok(())
    }

    /// A store-exclusive of one register (`stxr`, `stlxr`), which always
    /// succeeds: its status register reads zero.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, register, address.
    /// * `width` - What it moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or memory is full.
    pub(super) fn store_exclusive(&mut self, i: &Insn, width: Width) -> Result<(), Stop> {
        let (status, _) = register(i, 0)?;
        let (rt, bits) = register(i, 1)?;
        let (addr, _) = self.address(i, 2)?;
        self.store(addr, width_bytes(width, bits), self.reg(rt))?;
        self.set_reg(status, 32, 0);
        Ok(())
    }

    /// A store-exclusive of two registers (`stxp`, `stlxp`), which always
    /// succeeds.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, two registers, address.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or memory is full.
    pub(super) fn store_exclusive_pair(&mut self, i: &Insn) -> Result<(), Stop> {
        let (status, _) = register(i, 0)?;
        let (first, bits) = register(i, 1)?;
        let (second, _) = register(i, 2)?;
        let (addr, _) = self.address(i, 3)?;
        let bytes = width_bytes(Width::Reg, bits);
        self.store(addr, bytes, self.reg(first))?;
        self.store(
            addr.wrapping_add(from_usize(bytes)),
            bytes,
            self.reg(second),
        )?;
        self.set_reg(status, 32, 0);
        Ok(())
    }

    /// An atomic read-modify-write (`ldadd`, `ldclr`, `ldeor`, `ldset`,
    /// `ldsmax`, `ldsmin`, `ldumax`, `ldumin`, `swp`, in every ordering):
    /// memory takes `op` of its old value and the first register, and the
    /// second register takes the old value.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `op` - The modification.
    /// * `width` - What it moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled, the load faults, or memory is full.
    pub(super) fn atomic(&mut self, i: &Insn, op: Rmw, width: Width) -> Result<(), Stop> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i, 2)?;
        let bytes = width_bytes(width, bits);
        let n = u32::try_from(bytes * 8).unwrap_or(64);
        let old = lo64(self.load(addr, bytes)?);
        let s = mask(lo64(self.reg(rs)), n);
        let new = match op {
            Rmw::Add => old.wrapping_add(s),
            Rmw::Clr => old & !s,
            Rmw::Eor => old ^ s,
            Rmw::Set => old | s,
            Rmw::Smax => {
                if sign_extend(old, n) >= sign_extend(s, n) {
                    old
                } else {
                    s
                }
            }
            Rmw::Smin => {
                if sign_extend(old, n) <= sign_extend(s, n) {
                    old
                } else {
                    s
                }
            }
            Rmw::Umax => old.max(s),
            Rmw::Umin => old.min(s),
            Rmw::Swp => s,
        };
        self.store(addr, bytes, u128::from(new))?;
        self.set_reg(rt, bits, u128::from(old));
        Ok(())
    }

    /// `cas` in every ordering: memory takes `Rt` when it equals `Rs`, and
    /// `Rs` takes the old value either way.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `width` - What it moves.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled, the load faults, or memory is full.
    pub(super) fn compare_swap(&mut self, i: &Insn, width: Width) -> Result<(), Stop> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i, 2)?;
        let bytes = width_bytes(width, bits);
        let n = u32::try_from(bytes * 8).unwrap_or(64);
        let old = lo64(self.load(addr, bytes)?);
        if old == mask(lo64(self.reg(rs)), n) {
            self.store(addr, bytes, self.reg(rt))?;
        }
        self.set_reg(rs, bits, u128::from(old));
        Ok(())
    }
}

/// A register operand of a load or store, general or `v`, with its width.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `k` - The operand's position.
///
/// # Errors
///
/// When the operand is no register: a register list or lane, which the
/// machine does not model.
fn register(i: &Insn, k: usize) -> Result<(Reg, u16), Stop> {
    match i.operands.get(k).copied().unwrap_or(Opnd::None) {
        Opnd::Reg { reg, bits } => Ok((reg, bits)),
        Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => Err(unmodeled(i)),
    }
}

/// The bytes one element of `width` moves for a register of `bits`.
///
/// # Arguments
///
/// * `width` - What the access moves.
/// * `bits` - The register's width: 32 or 64, or 8 to 128 for a `v`
///   register.
fn width_bytes(width: Width, bits: u16) -> usize {
    match width {
        Width::Reg => usize::from(bits / 8),
        Width::Byte | Width::SByte => 1,
        Width::Half | Width::SHalf => 2,
        Width::SWord => 4,
    }
}
