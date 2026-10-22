//! The executor's state: register and memory reads and writes, stack slots, and
//! writing values out.

use super::*;
use crate::analysis::decompile::frame::Access;

/// Tells whether an address adds a sign-extended term to its base, an
/// index that may be negative.
///
/// # Arguments
///
/// * `addr` - The address.
fn signed_index(addr: &Expr) -> bool {
    match addr {
        Expr::Sext(..) => true,
        Expr::Bin(Op::Add, l, r) => signed_index(l) || signed_index(r),
        _ => false,
    }
}

/// Tells whether a variable is a machine register whose pending value
/// liveness may drop: an x86 register, or an arm64 general or `v`
/// register (the stack pointer is tracked as an offset, not a value).
///
/// # Arguments
///
/// * `k` - The variable.
fn is_register(k: Key) -> bool {
    matches!(
        k,
        Key::Reg(_) | Key::A64(crate::isa::a64::Reg::X(_) | crate::isa::a64::Reg::V(_))
    ) || matches!(k, Key::A32(r) if r != crate::isa::a32::SP)
}

impl<'a> Exec<'_, 'a> {
    /// Returns the name resolver for rendering.
    pub(in crate::analysis::decompile) fn names(&self) -> Names<'a> {
        self.ctx.names()
    }

    /// Returns the decoder bitness (32 or 64).
    pub(super) fn bitness(&self) -> u32 {
        self.ctx.bitness
    }

    /// Returns the text variable of a register (its canonical parent).
    ///
    /// # Arguments
    ///
    /// * `r` - Any register.
    pub(super) fn canon(&self, r: Register) -> Key {
        Key::Reg(canon(r, self.bitness()))
    }

    /// Returns the stack pointer register for this bitness.
    pub(super) fn rsp(&self) -> Register {
        if self.bitness() == 32 {
            Register::ESP
        } else {
            Register::RSP
        }
    }

    /// Tells whether a register write lands on the stack pointer, a narrow
    /// one included.
    ///
    /// A 64-bit program that writes `esp` (`lea esp, [rbx+c]`, `xchg esp,
    /// eax`) moves the stack pointer as surely as one that writes `rsp`;
    /// comparing the full register would miss it and leave the tracked
    /// offset at a value the machine no longer holds.
    ///
    /// # Arguments
    ///
    /// * `r` - The register written.
    pub(super) fn is_stack_pointer(&self, r: Register) -> bool {
        self.canon(r) == self.canon(self.rsp())
    }

    /// Returns the accumulator register for this bitness.
    pub(super) fn rax(&self) -> Register {
        if self.bitness() == 32 {
            Register::EAX
        } else {
            Register::RAX
        }
    }

    /// Returns the data register for this bitness (high half of products).
    pub(super) fn rdx(&self) -> Register {
        if self.bitness() == 32 {
            Register::EDX
        } else {
            Register::RDX
        }
    }

    /// Returns the machine word type for this bitness.
    pub(in crate::analysis::decompile) fn word_ty(&self) -> Ty {
        if self.bitness() == 32 {
            Ty::U32
        } else {
            Ty::U64
        }
    }

    /// Reads a register as an expression.
    ///
    /// The stack pointer reads as its tracked offset; byte and word registers
    /// mask (and shift, for `ah`-style registers) their parent's value, unless
    /// the parent holds a value a call left no wider than the lane read
    /// ([`Env::narrow`]); 32-bit reads are not masked (documented roughness,
    /// the lifter's invariant).
    ///
    /// # Arguments
    ///
    /// * `r` - The register as written in the instruction.
    pub(super) fn reg_read(&self, r: Register) -> Expr {
        if r == self.rsp() {
            return match self.env.sp {
                Some(k) => Expr::Sp(k),
                None => self
                    .env
                    .vals
                    .get(&self.canon(r))
                    .cloned()
                    .unwrap_or(Expr::Var(self.canon(r))),
            };
        }
        let key = self.canon(r);
        let full = self.assumed(self.env.get(key));
        let narrow = self.env.narrow.get(&key).copied().unwrap_or(64);
        match r.size() {
            1 if is_high_byte(r) => mask(fold(Op::Shr, full, Expr::Const(8), 64), 0xff),
            1 if narrow <= 8 => full,
            1 => mask(full, 0xff),
            2 if narrow <= 16 => full,
            2 => mask(full, 0xffff),
            8 if narrow == 32 && self.ctx.bitness == 64 => mask(full, 0xffff_ffff),
            _ => full,
        }
    }

    /// A register's whole value as the environment holds it, its upper half
    /// cleared when a 32-bit write left it so: the value a byte or word
    /// write merges into (`mov r12d, eax; xor r12b, 1` keeps `rax`'s upper
    /// half out of `r12`).
    ///
    /// # Arguments
    ///
    /// * `key` - The register.
    pub(super) fn full_value(&self, key: Key) -> Expr {
        let v = self.env.get(key);
        if self.ctx.bitness == 64 && self.env.narrow.get(&key) == Some(&32) {
            mask(v, 0xffff_ffff)
        } else {
            v
        }
    }

    /// Applies the block's equality assumption to a value being read.
    ///
    /// # Arguments
    ///
    /// * `e` - The value as the environment holds it.
    ///
    /// # Returns
    ///
    /// `e` with the assumed variable replaced by its constant, or `e` itself.
    pub(in crate::analysis::decompile) fn assumed(&self, e: Expr) -> Expr {
        match self.assume {
            Some((k, c)) if e.mentions(k) => e.subst(&Expr::Var(k), &Expr::Const(c)),
            _ => e,
        }
    }

    /// Reads operand `op` of `instr` as an expression.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `op` - Operand index.
    ///
    /// # Returns
    ///
    /// The register or memory value, the branch target or immediate as a
    /// constant, and `0` for operand kinds the lifter does not model.
    pub(super) fn val(&mut self, instr: &Instruction, op: u32) -> Expr {
        match instr.op_kind(op) {
            OpKind::Register => self.reg_read(instr.op_register(op)),
            OpKind::Memory => self.mem_read(instr, op),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                Expr::Const(instr.near_branch_target())
            }
            k if is_imm(k) => Expr::Const(instr.immediate(op)),
            _ => Expr::Const(0),
        }
    }

    /// Reads the operand of a bit count, scan or byte swap at the width the
    /// instruction works on.
    ///
    /// A count, scan or swap of a value depends on its width, not only on
    /// its value (`lzcnt eax, ecx` counts from bit 31), and the register's
    /// value is read whole (a 32-bit read is not masked), so an
    /// operand narrower than the machine word is cast to its width: the
    /// operation is the one on its operand's type, as C reads
    /// `lzcnt((uint32_t)x)`. A load of that width already has it.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `op` - Operand index.
    /// * `bits` - The operation's width.
    pub(super) fn lane_operand(&mut self, instr: &Instruction, op: u32, bits: u8) -> Expr {
        let v = self.val(instr, op);
        match &v {
            _ if bits >= self.word_ty().bits() => v,
            Expr::Const(_) => v,
            Expr::Deref(_, ty) | Expr::Cast(_, ty) | Expr::Bitcast(_, ty) if ty.bits() == bits => v,
            _ => Expr::Cast(Box::new(v), Ty::from_bits(bits)),
        }
    }

    /// Builds the address expression of the instruction's memory operand.
    ///
    /// iced pre-computes rip-relative displacements into absolute targets, so
    /// a missing or `rip` base yields a constant. `fs`/`gs` segment prefixes
    /// add the segment register as a variable. A 16-bit address
    /// ([`crate::disasm::addresses_16_bit`]) reads the 16-bit registers, takes
    /// its displacement as the signed word it is, and wraps at 64 KiB.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `op` - Operand index (iced exposes one memory operand per instruction).
    pub(super) fn addr(&self, instr: &Instruction, op: u32) -> Expr {
        let _ = op;
        let sixteen = crate::disasm::addresses_16_bit(instr);
        let disp = if sixteen {
            i64::from(crate::num::lo16(instr.memory_displacement64()).cast_signed()).cast_unsigned()
        } else {
            crate::disasm::displacement(instr, self.bitness()).cast_unsigned()
        };
        let base = instr.memory_base();
        let mut e = if base == Register::None || base == Register::RIP {
            Expr::Const(disp)
        } else {
            fold(Op::Add, self.reg_read(base), Expr::Const(disp), 64)
        };
        let index = instr.memory_index();
        if index != Register::None {
            let scaled = fold(
                Op::Mul,
                self.reg_read(index),
                Expr::Const(u64::from(instr.memory_index_scale())),
                64,
            );
            e = fold(Op::Add, e, scaled, 64);
        }
        if sixteen {
            e = fold(Op::And, e, Expr::Const(0xffff), 64);
        }
        let seg = instr.segment_prefix();
        if matches!(seg, Register::FS | Register::GS) {
            e = fold(Op::Add, Expr::Var(Key::Reg(seg)), e, 64);
        }
        self.in_alloca(e)
    }

    /// Spells an address inside a block an `alloca` made room for through
    /// the variable that holds the block's address.
    ///
    /// `[rcx+rax]` with `rcx` the stack pointer before the `alloca` and
    /// `rax` its size negated is the block's first byte, whichever way the
    /// sum is written ([`dynamic_room`]), and a constant past it is an
    /// offset into the block.
    ///
    /// # Arguments
    ///
    /// * `e` - The address.
    ///
    /// # Returns
    ///
    /// The address through the block's variable, or `e` itself.
    fn in_alloca(&self, e: Expr) -> Expr {
        if self.env.allocas.is_empty() {
            return e;
        }
        let (room, past) = match &e {
            Expr::Bin(Op::Add, l, r) => match (&**l, &**r) {
                (inner, Expr::Const(c)) if !matches!(inner, Expr::Sp(_)) => (inner.clone(), *c),
                _ => (e.clone(), 0),
            },
            _ => (e.clone(), 0),
        };
        let Some((k, size)) = room_below(&room) else {
            return e;
        };
        let held = self
            .env
            .allocas
            .iter()
            .find(|(at, n, _)| *at == k && *n == size)
            .map(|(_, _, t)| Expr::Var(*t));
        match held {
            Some(t) if past == 0 => t,
            Some(t) => fold(Op::Add, t, Expr::Const(past), 64),
            None => e,
        }
    }

    /// Returns the access type of the instruction's memory operand.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    pub(super) fn mem_ty(instr: &Instruction) -> Ty {
        let ms = instr.memory_size();
        Ty::from_size(ms.size(), is_float(ms))
    }

    /// Reads the instruction's memory operand.
    ///
    /// Stack slots read through [`Exec::slot_read`]; constant data addresses
    /// become named globals (recorded for declaration); anything else is a
    /// typed dereference.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `op` - Operand index.
    pub(super) fn mem_read(&mut self, instr: &Instruction, op: u32) -> Expr {
        let ty = Self::mem_ty(instr);
        let addr = self.addr(instr, op);
        let addr = self.tls_to_global(addr);
        self.read_at(addr, ty)
    }

    /// Reads memory of `ty` at `addr`, as [`Exec::mem_read`] reads an
    /// operand.
    ///
    /// A read through a computed frame address (`[esp+eax*4+0x10]`) may
    /// land on any slot from its base up, so their pending stores are
    /// written out first ([`Exec::settle_frame_region`]).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `ty` - The access type.
    pub(in crate::analysis::decompile) fn read_at(&mut self, addr: Expr, ty: Ty) -> Expr {
        match addr {
            Expr::Sp(k) => self.slot_read(k, ty),
            Expr::Const(a) if self.is_data(a) && self.const_float(a, ty).is_some() => self
                .const_float(a, ty)
                .map_or(Expr::Const(0), |bits| Expr::FConst(bits, ty)),
            Expr::Const(a) if self.is_data(a) => {
                let key = Key::Global(a, ty.bits());
                self.note_global(a, ty);
                self.assumed(Expr::Var(key))
            }
            other => {
                self.settle_frame_region(&other, None, false, false);
                Expr::deref(other, ty)
            }
        }
    }

    /// Records an access of `ty` to the global at `a` (emission pass only),
    /// the first one fixing the type it is declared with.
    ///
    /// # Arguments
    ///
    /// * `a` - The global's address.
    /// * `ty` - The access type.
    pub(in crate::analysis::decompile) fn note_global(&mut self, a: u64, ty: Ty) {
        if !self.emit {
            return;
        }
        self.ctx.globals.insert((a, ty));
        if !self.ctx.global_types.contains_key(&a) {
            std::sync::Arc::make_mut(&mut self.ctx.global_types).insert(a, ty);
        }
    }

    /// Tells whether `a` lies in a non-executable (data) section.
    ///
    /// # Arguments
    ///
    /// * `a` - A virtual address.
    pub(in crate::analysis::decompile) fn is_data(&self, a: u64) -> bool {
        let program = self.ctx.program;
        crate::analysis::decompile::expr::tls_slot(a).is_some()
            || program
                .section_at(a)
                .or_else(|| program.zero_fill_at(a))
                .is_some_and(|s| !s.executable)
    }

    /// Tells whether a value is the thread's TLS array: `*(gs + 0x58)` or a
    /// variable holding it.
    ///
    /// # Arguments
    ///
    /// * `e` - The value.
    pub(super) fn is_tls_array(&self, e: &Expr) -> bool {
        is_tls_array_expr(e, &self.env.tls_arrays)
    }

    /// Tells whether a value is this module's TLS block: the TLS array
    /// indexed by anything, or a variable holding that.
    ///
    /// # Arguments
    ///
    /// * `e` - The value.
    pub(super) fn is_tls_block(&self, e: &Expr) -> bool {
        is_tls_block_expr(e, &self.env.tls_arrays, &self.env.tls_blocks)
    }

    /// Replaces the address of a known TLS singleton slot with the synthetic
    /// global that names it.
    ///
    /// Either operand order is folded: the compiler writes the block plus the
    /// constant slot offset as often as the constant plus the block
    /// (`0x90 + r15`), and leaving the second form raw left the manager access
    /// spelled as a bare dereference where the first read as the singleton.
    ///
    /// # Arguments
    ///
    /// * `addr` - A memory operand's address.
    pub(super) fn tls_to_global(&self, addr: Expr) -> Expr {
        if let Expr::Bin(Op::Add, a, b) = &addr {
            let block_off = match (&**a, &**b) {
                (block, Expr::Const(off)) => Some((block, *off)),
                (Expr::Const(off), block) => Some((block, *off)),
                _ => None,
            };
            if let Some((block, off)) = block_off
                && self.is_tls_block(block)
                && self.ctx.analysis.classes.tls_slots.contains_key(&off)
            {
                return Expr::Const(crate::analysis::decompile::expr::TLS_BASE + off);
            }
        }
        addr
    }

    /// Reads a stack slot.
    ///
    /// An overlapping slot with a known value has an unemitted store the
    /// reader may depend on through aliasing, so it is written out first;
    /// so is the slot itself when its pending store has another width
    /// (`movups [rsp+40h], xmm0; movzx r9d, word [rsp+40h]` reads two bytes
    /// of the sixteen the store has not written yet). A slot whose value is
    /// known at exactly this width yields that value, its bits when a float
    /// is read as an integer ([`bitcast`]); otherwise the slot's text
    /// variable is read at this width.
    ///
    /// # Arguments
    ///
    /// * `k` - Slot offset from the entry rsp.
    /// * `ty` - Access type.
    pub(super) fn slot_read(&mut self, k: i64, ty: Ty) -> Expr {
        self.ctx.frame.note(k, Access::Load(ty));
        self.note_slot(k, ty);
        if let Some(v) = self.slot_view(k, ty) {
            return self.assumed(v);
        }
        let overlapping: Vec<i64> = self
            .env
            .slot_bits
            .iter()
            .filter(|(o, bits)| {
                (**o != k || **bits != ty.bits()) && ranges_overlap(**o, **bits, k, ty.bits())
            })
            .map(|(o, _)| *o)
            .collect();
        for o in overlapping {
            self.materialize(Key::Slot(o), &mut Vec::new(), None);
        }
        let end = k.saturating_add(i64::from(ty.bits() / 8).max(1));
        let covered = self
            .slot_def
            .range(k.saturating_sub(SLOT_BYTES_MAX - 1)..=k)
            .any(|(d, b)| d.saturating_add(i64::from(*b / 8).max(1)) >= end);
        if !covered {
            let widest = self.slot_use.entry(k).or_default();
            *widest = (*widest).max(ty.bits());
        }
        if self.env.slot_bits.get(&k) == Some(&ty.bits())
            && let Some(v) = self.env.vals.get(&Key::Slot(k))
        {
            let v = match ty {
                Ty::U32 | Ty::U64 if v.is_float() || self.float_param(v) => bitcast(v.clone(), ty),
                Ty::F32 | Ty::F64 if matches!(v, Expr::Bitcast(..)) => bitcast(v.clone(), ty),
                Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::F32 | Ty::F64 => v.clone(),
            };
            return self.assumed(v);
        }
        if let Some(&stored) = self.env.slot_bits.get(&k)
            && stored > ty.bits()
            && stored <= 64
            && !matches!(ty, Ty::F32 | Ty::F64)
        {
            let whole = Expr::deref(Expr::Sp(k), Ty::from_bits(stored));
            return self.assumed(mask(whole, (1u64 << ty.bits()) - 1));
        }
        self.assumed(Expr::deref(Expr::Sp(k), ty))
    }

    /// Reads a slot as a view of the stores this block made around it: the
    /// high part of one wider store, or a word two narrower stores fill.
    ///
    /// An aggregate passed or returned by value in registers is spilled at
    /// `-O0` one way and read back the other: a structure of two `int`s
    /// arrives in one register, is stored whole and read a field at a time
    /// (`h_point_cross`), or is built a field at a time and read back whole
    /// into the result register (`h_mkpoint`). Each slot's text variable
    /// holds only its own store, so the view is spelled over the stores'
    /// values ([`Exec::slot_bits_of`]): the high half is a shift of the
    /// whole, the whole an `|` of the halves.
    ///
    /// # Arguments
    ///
    /// * `k` - Slot offset from the entry rsp.
    /// * `ty` - Access type, an integer of at most 64 bits.
    ///
    /// # Returns
    ///
    /// The value, or `None` when the read is no such view: it starts a
    /// store, another store of this block overlaps it, or a store's bits
    /// spell no integer ([`Exec::slot_bits_of`]).
    fn slot_view(&mut self, k: i64, ty: Ty) -> Option<Expr> {
        if matches!(ty, Ty::F32 | Ty::F64 | Ty::U128) {
            return None;
        }
        let bits = ty.bits();
        let end = k.saturating_add(i64::from(bits / 8));
        let stores: Vec<(i64, u8)> = self
            .slot_def
            .range(k.saturating_sub(SLOT_BYTES_MAX - 1)..end)
            .map(|(d, b)| (*d, *b))
            .filter(|&(d, b)| ranges_overlap(d, b, k, bits))
            .collect();
        match *stores.as_slice() {
            [(d, dbits)]
                if d < k && d.saturating_add(i64::from(dbits / 8)) >= end && dbits <= 64 =>
            {
                let shift = u64::try_from(k - d).ok()?.checked_mul(8)?;
                let whole = self.slot_bits_of(d, dbits)?;
                let high = fold(Op::Shr, whole, Expr::Const(shift), dbits);
                Some(mask(high, mask_bits(bits)))
            }
            [(lo, lbits), (hi, hbits)]
                if lo == k
                    && lbits < bits
                    && hi == k.saturating_add(i64::from(lbits / 8))
                    && hi.saturating_add(i64::from(hbits / 8)) == end =>
            {
                let high = self.slot_bits_of(hi, hbits)?;
                let low = self.slot_bits_of(lo, lbits)?;
                let upper = fold(
                    Op::Shl,
                    mask(high, mask_bits(hbits)),
                    Expr::Const(u64::from(lbits)),
                    bits,
                );
                Some(fold(Op::Or, upper, mask(low, mask_bits(lbits)), bits))
            }
            _ => None,
        }
    }

    /// Returns the bits a store of this block left in a slot, as an
    /// integer of the store's width.
    ///
    /// A value the environment holds at that width that is an integer
    /// ([`Exec::integral`]) is itself; any other pending value is written
    /// out first, and the slot's variable is read at the store's width.
    ///
    /// # Arguments
    ///
    /// * `d` - The store's slot offset.
    /// * `dbits` - Its width in bits.
    ///
    /// # Returns
    ///
    /// The bits, or `None` when the block stored a floating-point value
    /// there ([`Exec::float_def`]), or a value whose type the text decides
    /// later: their bits are no integer the slot's variable spells.
    fn slot_bits_of(&mut self, d: i64, dbits: u8) -> Option<Expr> {
        if self.float_def.contains(&d) {
            return None;
        }
        if let Some(v) = self.env.vals.get(&Key::Slot(d)) {
            if self.env.slot_bits.get(&d) != Some(&dbits) {
                self.materialize(Key::Slot(d), &mut Vec::new(), None);
            } else if self.integral(v) {
                return Some(v.clone());
            } else {
                return None;
            }
        }
        Some(Expr::deref(Expr::Sp(d), Ty::from_bits(dbits)))
    }

    /// Tells whether a value is an integer by its own shape
    /// ([`integer_bits`]), or a parameter the convention passes in a
    /// general register.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn integral(&self, v: &Expr) -> bool {
        match v {
            Expr::Var(Key::Param(i)) => self.ctx.arg_floats & (1u8 << (*i).min(7)) == 0,
            _ => integer_bits(v),
        }
    }

    /// Lifts a drop of the stack pointer by a run-time amount as the
    /// `alloca` it compiles from.
    ///
    /// `sub rsp, rax` after a `__chkstk` of a computed size, or `mov rsp,
    /// rcx` with `rcx` the old stack pointer less one, makes room on the
    /// stack the frame does not have: the text gets `t = alloca(n);` and
    /// every value that is the new stack pointer, the stack pointer itself
    /// among them, is `t` from here on. The size the compiler rounded up to
    /// the stack's alignment (`align_up(n, 0x10)`) is written as the size
    /// asked for. The statement is checked as the assignment of the new
    /// stack pointer it is on the machine.
    ///
    /// # Arguments
    ///
    /// * `sp` - The stack pointer's variable.
    /// * `v` - The new stack pointer: the old one less `size`.
    /// * `size` - The bytes made room for.
    pub(super) fn alloca(&mut self, sp: Key, v: &Expr, size: Expr) {
        let t = self.fresh_tmp(Ty::U64);
        let n = self.names();
        let asked = match &size {
            Expr::Helper(Helper::AlignUp, args) if args.len() == 2 => args.first(),
            _ => None,
        }
        .unwrap_or(&size);
        emit_line!(
            self,
            format!("{} = alloca({});", n.key(t), asked.render(&n))
        );
        self.record(EffectKind::Assign(t, v.clone(), 64));
        for held in self.env.vals.values_mut() {
            if held == v {
                *held = Expr::Var(t);
            }
        }
        if let Some((k, _)) = room_below(v) {
            self.env.allocas.push((k, size, t));
        }
        self.env.vals.insert(sp, Expr::Var(t));
        self.env.sp = None;
    }

    /// Records a slot's declaration type on first sight (emission pass only).
    ///
    /// # Arguments
    ///
    /// * `k` - Slot offset.
    /// * `ty` - Access type.
    pub(super) fn note_slot(&mut self, k: i64, ty: Ty) {
        self.declare(Key::Slot(k), ty);
    }

    /// Assigns a register lazily: the value stays symbolic until needed.
    ///
    /// Writing the stack pointer updates the tracked offset instead; a write
    /// that lowers it by an amount no constant gives is an `alloca`
    /// ([`Exec::alloca`]). A byte
    /// or word write merges into the parent register only when some later
    /// instruction reads bits it keeps; otherwise the lane is the whole value
    /// (`mov al, [p]; mov [q], al` never mentions `rax`).
    ///
    /// # Arguments
    ///
    /// * `r` - The register as written in the instruction.
    /// * `v` - The new value.
    pub(super) fn reg_write(&mut self, r: Register, v: Expr) {
        if self.is_stack_pointer(r) {
            /// Most bytes a `sub esp` outside the prologue makes room for
            /// arguments with: a structure passed by value is copied there.
            const ARGS_ROOM_MAX: i64 = 0x100;
            let sp_key = self.canon(r);
            let region = self.env.vals.remove(&sp_key);
            if self.bitness() == 64 && r.size() == 8 {
                if let Some(size) = dynamic_room(&v) {
                    self.alloca(sp_key, &v, size);
                    return;
                }
                if let Some(Expr::Var(t)) = region
                    && v.mentions(t)
                {
                    self.env.vals.insert(sp_key, v);
                    self.env.sp = None;
                    return;
                }
            }
            let before = self.env.sp;
            self.env.sp = match v {
                _ if self.bitness() == 64 && r.size() < 8 => None,
                Expr::Sp(k) => Some(k),
                Expr::Bin(Op::And, ref l, ref m)
                    if matches!(**l, Expr::Sp(_))
                        && matches!(**m, Expr::Const(c) if c.wrapping_neg().is_power_of_two() && c.wrapping_neg() <= 4096) =>
                {
                    match **l {
                        Expr::Sp(k) => Some(k),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let (Some(b), Some(a)) = (before, self.env.sp)
                && self.bitness() == 32
                && !self.entry
                && (b - a).abs() <= ARGS_ROOM_MAX
            {
                let words = u32::try_from((b - a).abs() / self.ctx.conv.word).unwrap_or(0);
                self.args_pushed = if a < b {
                    self.args_pushed + words
                } else {
                    self.args_pushed.saturating_sub(words)
                };
            }
            return;
        }
        let key = self.canon(r);
        let lane = lane_bits(r);
        let needed = self
            .regs_needed
            .as_ref()
            .map_or(64, |m| m.get(&key).copied().unwrap_or(0));
        let merged = match r.size() {
            1 if is_high_byte(r) => {
                crate::analysis::decompile::expr::merge_bits(self.full_value(key), v, 8, 8)
            }
            1 | 2
                if needed <= lane
                    && matches!(&v, Expr::Var(k) if self.env.narrow.get(k).is_some_and(|b| *b <= lane)) =>
            {
                v
            }
            1 | 2 if needed <= lane => mask(v, if lane == 8 { 0xff } else { 0xffff }),
            1 => crate::analysis::decompile::expr::merge_bits(self.full_value(key), v, 8, 0),
            2 => crate::analysis::decompile::expr::merge_bits(self.full_value(key), v, 16, 0),
            _ => v,
        };
        let wide = known_bits(&merged) > 0xffff_ffff;
        self.assign(key, merged);
        if wide
            && r.size() == 4
            && self.ctx.bitness == 64
            && self.env.narrow.get(&key).is_none_or(|b| *b > 32)
        {
            self.env.narrow.insert(key, 32);
        }
    }

    /// Records `key := v`; expressions above [`MAX_EXPR`] nodes, and those
    /// above [`INLINE_MAX`] that the block reads twice or more before
    /// rewriting `key`, are written out immediately. A vector register keeps
    /// inlining, since its one declared type may not fit every value, and so
    /// does half of a division idiom ([`Expr::partial_idiom`]), which only
    /// reads as the division it is once its sign fix folds into it.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    /// * `v` - Its new value.
    pub(in crate::analysis::decompile) fn assign(&mut self, key: Key, v: Expr) {
        let v = self.bounded(v);
        self.written_here.insert(key);
        self.big_written.remove(&key);
        self.env.set(key, v.clone());
        if let Some(c) = self.class_of_expr(&v) {
            self.env.classes.insert(key, c);
        }
        let reads = self.reads_ahead.get(&key).copied().unwrap_or(0);
        let scalar = !matches!(key, Key::Reg(r) if r.is_vector_register())
            && !matches!(key, Key::A64(crate::isa::a64::Reg::V(_)));
        let reuse = scalar && v.size() > INLINE_MAX && reads >= 2 && !v.partial_idiom();
        if v.size() > MAX_EXPR || reuse {
            self.big_written.insert(key, v);
            match self.deferred.as_mut() {
                Some(d) => d.push(key),
                None => self.materialize(key, &mut Vec::new(), None),
            }
        }
    }

    /// The expression `key` was written out as, when a later read is only
    /// its name.
    ///
    /// A float's width lives on that expression. The next assignment drops
    /// it until that assignment is written out too, so a store does not
    /// keep a width the register no longer holds.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    pub(in crate::analysis::decompile) fn early_value(&self, key: Key) -> Option<&Expr> {
        self.big_written.get(&key)
    }

    /// Writes the registers an instruction sets at once, each value read
    /// before any of them changes (`imul` sets `edx:eax`, `xchg` both its
    /// operands).
    ///
    /// Every value is recorded before any is written out early, so the
    /// write-out of one protects the others as readers of its old value: a
    /// value held aside while another was written out would name the new
    /// one (`edx = smulhi32(x, y); eax = x * y;` with `x` reading `edx`).
    ///
    /// # Arguments
    ///
    /// * `writes` - The registers, in the order the instruction sets them,
    ///   with their values.
    pub(super) fn reg_write_all(&mut self, writes: Vec<(Register, Expr)>) {
        let outer = self.deferred.replace(Vec::new());
        for (r, v) in writes {
            self.reg_write(r, v);
        }
        let waiting = std::mem::replace(&mut self.deferred, outer).unwrap_or_default();
        for k in waiting {
            self.materialize(k, &mut Vec::new(), None);
        }
    }

    /// A value as the environment may hold it: itself, or, when nothing is
    /// written out and it is past [`SYMBOLIC_MAX`] nodes, a fresh unknown.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    pub(super) fn bounded(&mut self, v: Expr) -> Expr {
        if self.ctx.symbolic_only && v.size() > SYMBOLIC_MAX {
            self.ctx.tmp_count += 1;
            Expr::Var(Key::Tmp(self.ctx.tmp_count))
        } else {
            v
        }
    }

    /// Lowers the escape floor when a stack address flows somewhere a callee can see it.
    ///
    /// Everything from that offset up to the caller frame may then be read or
    /// written by calls.
    ///
    /// # Arguments
    ///
    /// * `e` - The value that escaped (an argument, a stored value, a store address).
    pub(in crate::analysis::decompile) fn note_escape(&mut self, e: &Expr) {
        if let Some(k) = e.min_sp() {
            self.ctx.escape_floor = Some(self.ctx.escape_floor.map_or(k, |f| f.min(k)));
        }
    }

    /// Tells whether slot `o` is at or above the escape floor.
    ///
    /// # Arguments
    ///
    /// * `o` - Slot offset.
    pub(super) fn exposed(&self, o: i64) -> bool {
        self.ctx.escape_floor.is_some_and(|f| o >= f)
    }

    /// Copies an operand in flight into a temporary when it reads one of
    /// `slots`, whose pending stores are about to be written out.
    ///
    /// The operand was read before those stores, through the slot's text
    /// variable or a computed frame address, so once they are in the text
    /// it would read what they left (`mov ecx,[rsp+58h]; mov
    /// [rsp+58h],rbx; ...; mov [rsp+58h],ecx`).
    ///
    /// # Arguments
    ///
    /// * `e` - The operand.
    /// * `ty` - Its type, the temporary's declaration.
    /// * `slots` - The slots about to be written out.
    fn hold_slot_reads(&mut self, e: Expr, ty: Ty, slots: &[i64]) -> Expr {
        if slots.iter().any(|o| e.may_read(Key::Slot(*o))) {
            self.tmp_of(&e, ty)
        } else {
            e
        }
    }

    /// Stores to a stack slot lazily.
    ///
    /// A partial overwrite of another known slot, or of this one's pending
    /// store at a wider width, writes that store out first (its text
    /// variable must hold the bytes the new store keeps). Readers of the old
    /// slot value in the environment stay valid because the lazy store
    /// changes nothing in the text yet; a stored value that reads a slot
    /// written out so is copied into a temporary first, since it was read
    /// before that store (`mov ecx,[rsp+58h]; mov [rsp+58h],rbx; ...; mov
    /// [rsp+58h],ecx`).
    ///
    /// # Arguments
    ///
    /// * `k` - Slot offset.
    /// * `ty` - Store type.
    /// * `v` - The stored value.
    pub(super) fn slot_write(&mut self, k: i64, ty: Ty, v: Expr) {
        if !self.seh_registered {
            return;
        }
        if self.is_register_save(ty, &v) {
            self.env.vals.remove(&Key::Slot(k));
            self.env.slot_bits.remove(&k);
            return;
        }
        let access = match v {
            _ if matches!(ty, Ty::F32 | Ty::F64) || v.is_float() => Access::StoreFloat(ty),
            Expr::Const(_) => Access::StoreConst(ty),
            _ => Access::StoreInt(ty),
        };
        self.ctx.frame.note(k, access);
        let (ty, v) = self.ctx.frame.store(k, ty, v);
        self.note_slot(k, ty);
        let widest = self.slot_def.entry(k).or_default();
        *widest = (*widest).max(ty.bits());
        if matches!(ty, Ty::F32 | Ty::F64) || v.is_float() {
            self.float_def.insert(k);
        }
        let bits = ty.bits();
        let overlapping: Vec<i64> = self
            .env
            .slot_bits
            .iter()
            .filter(|(o, obits)| {
                (**o != k || bits < **obits) && ranges_overlap(**o, **obits, k, bits)
            })
            .map(|(o, _)| *o)
            .collect();
        let v = self.hold_slot_reads(v, ty, &overlapping);
        for o in overlapping {
            self.materialize(Key::Slot(o), &mut Vec::new(), None);
            self.env.slot_bits.remove(&o);
        }
        self.note_escape(&v);
        self.env.slot_bits.insert(k, bits);
        let v = self.bounded(v);
        let big = v.size() > MAX_EXPR;
        self.env.set(Key::Slot(k), v);
        if big {
            self.materialize(Key::Slot(k), &mut Vec::new(), None);
        }
    }

    /// Writes out the pending stores of the frame slots an access through
    /// a computed address may touch, and, for a write, every value that
    /// reads one, forgetting what the slots held.
    ///
    /// The slots are text variables while such an access reads or writes
    /// the frame's bytes: a store still pending in the environment would
    /// print after a copy over it and undo the copy (`memcpy(&local_74, p,
    /// 112); local_34 = 0.0;`), a read through the address would miss it,
    /// and a value that reads a slot would read what the write left. A
    /// region at a known slot with a known length covers what it spans; any
    /// other may cover every slot from its base up, or, copying backward,
    /// any slot at all. An arm64 address adding a sign-extended index to
    /// its base may cover any slot as well: `va_arg` reads the register
    /// save area below the `__gr_top` it adds a negative offset to. The
    /// verifier's symbolic pass writes nothing out; it forgets what the
    /// written slots held.
    ///
    /// # Arguments
    ///
    /// * `addr` - The access's address: the region's start, or its end when
    ///   copying backward.
    /// * `len` - Its length in bytes, when known.
    /// * `backward` - The direction flag is set: the region ends at `addr`.
    /// * `writes` - The access writes the region.
    pub(in crate::analysis::decompile) fn settle_frame_region(
        &mut self,
        addr: &Expr,
        len: Option<&Expr>,
        backward: bool,
        writes: bool,
    ) {
        let Some(lo) = Self::frame_base(addr) else {
            return;
        };
        let span = match (addr, len, backward) {
            (Expr::Sp(k), Some(Expr::Const(n)), false) => {
                i64::try_from(*n).ok().map(|n| (*k, k.saturating_add(n)))
            }
            _ => None,
        };
        let below = backward
            || (self.ctx.program.arch.isa() == Some(crate::isa::Isa::A64) && signed_index(addr));
        if !writes {
            let seen = match span {
                Some((a, b)) => SlotUse::Window(a, b),
                None if below => SlotUse::All,
                None => SlotUse::Window(lo, i64::MAX),
            };
            let before = self.written_slots();
            self.call_uses.push((seen, before));
        }
        let covers = |o: i64, end: i64| match span {
            Some((a, b)) => o < b && a < end,
            None => below || end > lo,
        };
        let stores: Vec<i64> = self
            .env
            .slot_bits
            .iter()
            .filter(|(o, bits)| covers(**o, **o + i64::from(**bits / 8).max(1)))
            .map(|(o, _)| *o)
            .collect();
        if self.ctx.symbolic_only {
            if writes {
                for o in stores {
                    self.env.vals.remove(&Key::Slot(o));
                    self.env.slot_bits.remove(&o);
                }
            }
            return;
        }
        for &o in &stores {
            self.materialize(Key::Slot(o), &mut Vec::new(), None);
        }
        if !writes {
            return;
        }
        let reads =
            |e: &Expr| e.any_var(&|k| matches!(k, Key::Slot(o) if covers(o, o + SLOT_BYTES_MAX)));
        let readers: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(k, v)| !matches!(k, Key::Slot(o) if stores.contains(o)) && reads(v))
            .map(|(k, _)| *k)
            .collect();
        for r in readers {
            if self.dead_reg(r) {
                self.forget_dead(r);
            } else {
                self.materialize(r, &mut Vec::new(), None);
            }
        }
        self.protect_flags(&reads);
        for o in stores {
            self.env.vals.remove(&Key::Slot(o));
            self.env.slot_bits.remove(&o);
        }
    }

    /// Stores to the instruction's memory operand: slot stores stay lazy, real stores emit.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction (operand 0 is the destination).
    /// * `v` - The stored value.
    pub(super) fn store(&mut self, instr: &Instruction, v: Expr) {
        if self.ctx.seh_frame && (is_seh_link(instr) || try_level_store(instr, self.ctx.bitness)) {
            self.seh_registered |= is_seh_link(instr);
            return;
        }
        let ty = Self::mem_ty(instr);
        let addr = self.addr(instr, 0);
        let addr = self.tls_to_global(addr);
        self.store_at(addr, ty, v);
    }

    /// Stores `v` of `ty` at `addr`, as [`Exec::store`] stores to an
    /// operand: a slot lazily, anything else as a store line.
    ///
    /// A store through a computed frame address may land on any slot from
    /// its base up, so their pending stores are written out first and
    /// their values forgotten ([`Exec::settle_frame_region`]). A float
    /// constant stored as an integer of its width (a dword copy of a
    /// `float` slot) is its bits, not the number converted.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `ty` - The store type.
    /// * `v` - The stored value.
    pub(in crate::analysis::decompile) fn store_at(&mut self, addr: Expr, ty: Ty, v: Expr) {
        let v = match v {
            Expr::FConst(bits, fty)
                if matches!(ty, Ty::U32 | Ty::U64) && fty.bits() == ty.bits() =>
            {
                Expr::Const(bits)
            }
            other => other,
        };
        match addr {
            Expr::Sp(k) => self.slot_write(k, ty, v),
            other => {
                self.settle_frame_region(&other, None, false, true);
                match float_store(ty, &v) {
                    Some((fty, fv)) => self.emit_store(other, fty, &fv),
                    None => self.emit_store(other, ty, &v),
                }
            }
        }
    }

    /// The frame offset a computed address is based on: `Sp(k)` alone or
    /// plus other terms (`&local_28 + (eax >> 5) * 4`), or the lower of a
    /// choice's two arms (`a2 ?: &local_58`, which is the slot when `a2` is
    /// null), never a stack address read out of memory.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    pub(super) fn frame_base(addr: &Expr) -> Option<i64> {
        match addr {
            Expr::Sp(k) => Some(*k),
            Expr::Bin(Op::Add, l, r) => Self::frame_base(l).or_else(|| Self::frame_base(r)),
            Expr::Ternary(_, a, b) => match (Self::frame_base(a), Self::frame_base(b)) {
                (Some(x), Some(y)) => Some(x.min(y)),
                (x, y) => x.or(y),
            },
            _ => None,
        }
    }

    /// Recognizes a push that only makes room on the stack.
    ///
    /// MSVC reserves a word of frame with `push ecx` rather than
    /// `sub esp,4`, in the prologue and after calls alike. The register then
    /// holds nothing on any path here ([`Env::unset`]): the last call
    /// clobbered it, or the function neither set nor received it. The slot
    /// gets no value, so the push never renders as the store of an unset
    /// register nor counts among the words pushed for a callee of unknown
    /// arity. It is still pushed for the next call ([`Env::fresh`]): MSVC
    /// fills a parameter the callee ignores the same way (`push ecx; push
    /// [ebp+8]; push ecx; call f` for an `f` reading only its second word),
    /// and a callee stated to take the word reads it as the slot it is, so
    /// the arguments above it keep their places. A register written out
    /// under its own name is set, and its push is the argument it is, as is
    /// a push of the `eax` a call just returned.
    ///
    /// # Arguments
    ///
    /// * `v` - The pushed value.
    pub(super) fn makes_room(&self, v: &Expr) -> bool {
        matches!(v, Expr::Var(k @ Key::Reg(_)) if self.env.unset.contains(k))
    }

    /// Recognizes the save of a callee-saved register, in the prologue or
    /// wherever a shrink-wrapped prologue put it.
    ///
    /// A store of a register the function preserves for its caller
    /// ([`abi::saved`]) in full (a word for a general register, sixteen
    /// bytes for `xmm6` and up under the Microsoft x64 convention) that
    /// still holds its entry value (written on no path here, no lazy
    /// value; [`Env::touched`]) is the compiler preserving it, an ABI event
    /// and no statement: the slot is left without a value so the save never
    /// renders, and the matching restore before `ret` is dead code. Under
    /// the block check ([`super::super::verify`]) a save stays the store it
    /// is, which the check compares with the machine's.
    ///
    /// # Arguments
    ///
    /// * `ty` - Store type.
    /// * `v` - The stored value.
    pub(super) fn is_register_save(&self, ty: Ty, v: &Expr) -> bool {
        let Expr::Var(key) = v else {
            return false;
        };
        self.ctx.probe.is_none()
            && abi::saved(self.ctx.conv, *key, ty.bits())
            && !self.env.touched.contains(key)
            && !self.written_here.contains(key)
            && !self.env.vals.contains_key(key)
    }

    /// Emits a store to non-slot memory after protecting memory readers.
    ///
    /// # Arguments
    ///
    /// * `addr` - The destination address.
    /// * `ty` - Store type.
    /// * `v` - The stored value; a value computed from the destination
    ///   itself (`*p = *p + 1`) renders as a compound assignment (`*p += 1`),
    ///   as a register's does. A store narrower than a word keeps only the
    ///   value's low bits, so the masks those bits pass through are dropped
    ///   ([`crate::analysis::decompile::expr::low_bits_read`]).
    pub(super) fn emit_store(&mut self, addr: Expr, ty: Ty, v: &Expr) {
        self.note_escape(v);
        self.note_escape(&addr);
        let v = match ty {
            Ty::U8 | Ty::U16 | Ty::U32 => {
                crate::analysis::decompile::expr::low_bits_read(v.clone(), ty.bits())
            }
            Ty::U64 | Ty::U128 | Ty::F32 | Ty::F64 => v.clone(),
        };
        let (mut addr, mut v) = (addr, v);
        let word = self.word_ty();
        self.protect_memory_around(&mut [(&mut addr, word), (&mut v, ty)]);
        let v = &v;
        if let Some(p) = &mut self.ctx.probe {
            p.store(&addr, ty, v);
        }
        if let Expr::Const(a) = addr
            && self.is_data(a)
        {
            self.note_global(a, ty);
        }
        if !self.emit {
            return;
        }
        self.record(EffectKind::Store(Box::new((addr.clone(), ty, v.clone()))));
        let n = self.names();
        let line = match addr {
            Expr::Const(a) if self.is_data(a) => {
                format!("{} = {};", n.global_place(a, ty.bits()).0, v.render(&n))
            }
            other => {
                let lhs = Expr::deref(other, ty);
                let compound = match v {
                    Expr::Bin(op, l, r) => match op.compound() {
                        Some(sym) if **l == lhs => Some((sym, r.as_ref())),
                        Some(sym) if op.is_commutative() && **r == lhs => Some((sym, l.as_ref())),
                        _ => None,
                    },
                    _ => None,
                };
                match compound {
                    Some(("+=", Expr::Const(c)))
                        if *c >= 1 << 63 && c.wrapping_neg() <= 0xffff_ffff =>
                    {
                        format!("{} -= {};", lhs.render(&n), c.wrapping_neg())
                    }
                    Some((sym, rhs)) => format!("{} {sym} {};", lhs.render(&n), rhs.render(&n)),
                    None => format!("{} = {};", lhs.render(&n), v.render(&n)),
                }
            }
        };
        emit_line!(self, line);
    }

    /// Writes `key`'s symbolic value out as `name = value;`.
    ///
    /// Every reader of the old text value is protected first; pending flags
    /// that read `key` are parked. The value written is the one left after
    /// that: a reader written out first may have parked it in a temporary,
    /// since it reads the reader's old value (`tmp_1 = (rax + rbx) * 100;
    /// rax += rbx; rbx = tmp_1;`).
    ///
    /// # Arguments
    ///
    /// * `key` - The variable to write out.
    /// * `stack` - Keys whose materialization is in progress: a reader found
    ///   there and this key read each other, so the reader's value is parked
    ///   in a temporary instead.
    /// * `live` - At a block end, the liveness oracle that lets dead
    ///   registers be forgotten instead of written.
    pub(in crate::analysis::decompile) fn materialize(
        &mut self,
        key: Key,
        stack: &mut Vec<Key>,
        live: Option<&LiveFn<'_>>,
    ) {
        if self.ctx.symbolic_only {
            return;
        }
        let Some(val) = self.env.vals.get(&key).cloned() else {
            return;
        };
        if val == Expr::Var(key) {
            self.env.vals.remove(&key);
            return;
        }
        stack.push(key);
        self.protect_readers(key, stack, live);
        stack.pop();
        self.protect_flags(&|e: &Expr| e.mentions(key));
        let Some(val) = self.env.vals.get(&key).cloned() else {
            return;
        };
        if val == Expr::Var(key) {
            self.env.vals.remove(&key);
            return;
        }
        self.write_out(key, &val);
    }

    /// Emits `name = value;`, as a compound assignment when `value` is `name op y`.
    ///
    /// Writing the variable the block's equality assumption is about ends
    /// that assumption: from here on `name` denotes the new value, not the
    /// one the branch compared. The expression is kept when the register
    /// was not already written out for its size, so a later read of the
    /// name can still see a float's width. A 32-bit write zero-extends:
    /// the value kept for a later read in the block stays whole, and the
    /// text wraps it, or a `uint64_t` sum of it keeps bits the machine
    /// cleared.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    /// * `val` - Its value, removed from the environment here.
    pub(super) fn write_out(&mut self, key: Key, val: &Expr) {
        if self.ctx.symbolic_only {
            return;
        }
        if self.assume.is_some_and(|(k, _)| k == key) {
            self.assume = None;
        }
        self.declare(key, self.ty_of(key));
        self.big_written.entry(key).or_insert_with(|| val.clone());
        self.env.vals.remove(&key);
        if key == self.canon(self.rax()) {
            self.env.result_in_rax = true;
        }
        let class = self.class_of_expr(val);
        match class {
            Some(c) => {
                self.env.classes.insert(key, c);
            }
            None => {
                self.env.classes.remove(&key);
            }
        }
        if self.is_tls_array(val) {
            self.env.tls_arrays.insert(key);
        } else {
            self.env.tls_arrays.remove(&key);
        }
        if self.is_tls_block(val) {
            self.env.tls_blocks.insert(key);
        } else {
            self.env.tls_blocks.remove(&key);
        }
        if !self.emit {
            return;
        }
        let bits = match key {
            Key::Global(_, bits) => bits,
            Key::Slot(o) => self
                .env
                .slot_bits
                .get(&o)
                .copied()
                .unwrap_or_else(|| self.ty_of(key).bits()),
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) | Key::A32(_) => {
                self.ty_of(key).bits()
            }
        };
        let val = &match key {
            Key::Slot(_) | Key::Global(..) if bits < 64 && !val.is_float() => {
                crate::analysis::decompile::expr::low_bits_read(val.clone(), bits)
            }
            Key::Slot(_)
            | Key::Global(..)
            | Key::Reg(_)
            | Key::Tmp(_)
            | Key::Param(_)
            | Key::A64(_)
            | Key::A32(_) => val.clone(),
        };
        self.record(EffectKind::Assign(key, val.clone(), bits));
        let n = self.names();
        let name = match key {
            Key::Slot(o) => n.slot_at(o, Ty::from_bits(bits)).0,
            Key::Reg(_)
            | Key::Tmp(_)
            | Key::Param(_)
            | Key::Global(..)
            | Key::A64(_)
            | Key::A32(_) => n.key(key),
        };
        let shown = if self.ctx.bitness == 64 && self.env.narrow.get(&key) == Some(&32) {
            mask(val.clone(), 0xffff_ffff)
        } else {
            val.clone()
        };
        let compound = match &shown {
            Expr::Bin(op, l, r) => match op.compound() {
                Some(sym) if l.is_var(key) => Some((sym, (**r).clone())),
                Some(sym) if op.is_commutative() && r.is_var(key) => Some((sym, (**l).clone())),
                _ => None,
            },
            _ => None,
        };
        let line = match compound {
            Some(("+=", Expr::Const(c))) if c >= 1 << 63 && c.wrapping_neg() <= 0xffff_ffff => {
                format!("{name} -= {};", c.wrapping_neg())
            }
            Some((sym, rhs)) => format!("{name} {sym} {};", rhs.render(&n)),
            None => format!("{name} = {};", shown.render(&n)),
        };
        self.lines.push(line);
    }

    /// Builds the location expression of a memory operand for intrinsics that
    /// update memory in place.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction (operand 0 is the memory operand).
    ///
    /// # Returns
    ///
    /// A slot name, a named global, or a typed dereference.
    pub(super) fn location(&mut self, instr: &Instruction) -> Expr {
        let ty = Self::mem_ty(instr);
        match self.addr(instr, 0) {
            Expr::Sp(k) => {
                self.note_slot(k, ty);
                Expr::deref(Expr::Sp(k), ty)
            }
            Expr::Const(a) if self.is_data(a) => {
                self.note_global(a, ty);
                Expr::Var(Key::Global(a, ty.bits()))
            }
            other => Expr::deref(other, ty),
        }
    }

    /// Lifts `[lock] cmpxchg [m], src` as a `cmpxchgN` intrinsic.
    ///
    /// rax receives the old value; ZF says whether it matched the expected
    /// value (so the store happened).
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `bits` - Operand width.
    pub(super) fn cmpxchg(&mut self, instr: &Instruction, bits: u8) {
        let rax_key = self.canon(self.rax());
        let expected = self.reg_read(sized_register(self.rax(), bits));
        let expected = self.tmp_if(expected, &|e: &Expr| e.mentions(rax_key));
        let mut new = self.val(instr, 1);
        let mut expected = expected;
        let loc = self.atomic_location(instr, &mut [&mut expected, &mut new]);
        self.clobber(rax_key);
        self.declare(rax_key, self.word_ty());
        let n = self.names();
        emit_line!(
            self,
            format!(
                "{} = cmpxchg{bits}({}, {}, {});",
                n.key(rax_key),
                loc.render(&n),
                expected.render(&n),
                new.render(&n)
            )
        );
        self.record(EffectKind::Unmodeled);
        self.flags = if self.flags_needed & !RflagsBits::ZF == 0 {
            Flags::Cmp(Expr::Var(rax_key), expected, bits)
        } else {
            Flags::Cmp(expected, Expr::Var(rax_key), bits)
        };
    }

    /// The memory an atomic read-modify-write touches, once its effect is
    /// accounted for: every known value in memory is forgotten, and a stack
    /// slot it names is clobbered.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    fn atomic_location(&mut self, instr: &Instruction, flight: &mut [&mut Expr]) -> Expr {
        let mut loc = self.location(instr);
        let (ty, word) = (Self::mem_ty(instr), self.word_ty());
        if let Expr::Deref(addr, _) = &mut loc {
            let mut all: Vec<(&mut Expr, Ty)> = flight.iter_mut().map(|e| (&mut **e, ty)).collect();
            all.push((&mut **addr, word));
            self.protect_memory_around(&mut all);
        } else {
            let mut all: Vec<(&mut Expr, Ty)> = flight.iter_mut().map(|e| (&mut **e, ty)).collect();
            self.protect_memory_around(&mut all);
        }
        if let Expr::Deref(a, _) = &loc
            && let Expr::Sp(k) = **a
        {
            self.clobber(Key::Slot(k));
        }
        loc
    }

    /// Lifts `[lock] xadd [m], r` as an `xaddN` intrinsic.
    ///
    /// The register receives the old value, memory the sum.
    ///
    /// The flags are those of the addition the exchange performs, so a
    /// branch after it reads the sum the way it would after a plain
    /// `add` of the same operands.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `bits` - Operand width.
    pub(super) fn xadd(&mut self, instr: &Instruction, bits: u8) {
        let reg = instr.op1_register();
        let key = self.canon(reg);
        let mut old = self.val(instr, 0);
        let mut add = self.val(instr, 1);
        let loc = self.atomic_location(instr, &mut [&mut old, &mut add]);
        self.clobber(key);
        self.declare(key, self.word_ty());
        let n = self.names();
        emit_line!(
            self,
            format!(
                "{} = xadd{bits}({}, {});",
                n.key(key),
                loc.render(&n),
                add.render(&n)
            )
        );
        self.record(EffectKind::Unmodeled);
        self.flags = Flags::Add(old, add, bits);
    }

    /// Emits a `lock`-prefixed read-modify-write as an atomic intrinsic.
    ///
    /// `lock add [m], v` becomes `tmp = atomic_add32(m, v);`, the temporary
    /// holding the new value so a flag reader after it (`lock dec` then
    /// `jz` on a reference count) reads `tmp == 0`; with no flag reader
    /// after it, it is a statement, `atomic_add32(m, v);`, as a reference
    /// count taken is. `inc` and
    /// `dec` arrive as add and sub of one. Memory is forgotten as after any
    /// store through an unknown pointer.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `bits` - Operand width.
    /// * `op` - The arithmetic mnemonic.
    /// * `v` - The operand value.
    pub(super) fn locked(&mut self, instr: &Instruction, bits: u8, op: Mnemonic, v: &Expr) {
        let name = match op {
            Mnemonic::Add => "add",
            Mnemonic::Sub => "sub",
            Mnemonic::And => "and",
            Mnemonic::Or => "or",
            _ => "xor",
        };
        let mut v = v.clone();
        let loc = self.atomic_location(instr, &mut [&mut v]);
        let v = &v;
        if self.flags_needed == 0 {
            let n = self.names();
            emit_line!(
                self,
                format!("atomic_{name}{bits}({}, {});", loc.render(&n), v.render(&n))
            );
            self.record(EffectKind::Unmodeled);
            self.flags = Flags::Unknown;
            return;
        }
        let id = if self.emit {
            self.ctx.tmp_count += 1;
            self.ctx.tmp_count
        } else {
            self.tmp_local += 1;
            self.tmp_local
        };
        let key = Key::Tmp(id);
        self.declare(key, Self::mem_ty(instr));
        let n = self.names();
        emit_line!(
            self,
            format!(
                "{} = atomic_{name}{bits}({}, {});",
                n.key(key),
                loc.render(&n),
                v.render(&n)
            )
        );
        self.record(EffectKind::Unmodeled);
        let new = Expr::Var(key);
        self.flags = match op {
            _ if self.zero_or_sign_only() => Flags::Result(new, bits),
            Mnemonic::Add => Flags::Add(fold(Op::Sub, new, v.clone(), bits), v.clone(), bits),
            Mnemonic::Sub => Flags::Cmp(fold(Op::Add, new, v.clone(), bits), v.clone(), bits),
            _ => Flags::Test(new.clone(), new, bits),
        };
    }

    /// Tells whether every flag bit a later reader needs is the zero or the
    /// sign flag.
    ///
    /// Those two an arithmetic result answers on its own, so `sub rbx, 1;
    /// jne` reads the register the result lands in, `rbx != 0`, and not a
    /// copy of what the register held. A reader of the carry or the
    /// overflow needs the operands.
    pub(super) fn zero_or_sign_only(&self) -> bool {
        self.flags_needed & !(RflagsBits::ZF | RflagsBits::SF) == 0
    }

    /// Parks `key`'s value in a temporary so it can be assigned later without
    /// re-reading variables that change first.
    ///
    /// An x87 register's value is parked in a `double`, which holds it
    /// whole; anything else in a word.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable whose value is parked.
    pub(super) fn park(&mut self, key: Key) {
        let Some(val) = self.env.vals.remove(&key) else {
            return;
        };
        let parked = match val {
            Expr::Const(_) => val,
            _ if key.is_x87() => self.tmp_of(&val, Ty::F64),
            _ => self.tmp_of(&val, self.word_ty()),
        };
        self.env.vals.insert(key, parked);
    }

    /// Reads a float constant from read-only data.
    ///
    /// # Arguments
    ///
    /// * `a` - Address of the value.
    /// * `ty` - The access type; only [`Ty::F32`] and [`Ty::F64`] qualify.
    ///
    /// # Returns
    ///
    /// The bit pattern when `a` lies in a non-writable section, else `None`.
    pub(super) fn const_float(&self, a: u64, ty: Ty) -> Option<u64> {
        let width = match ty {
            Ty::F32 => 4,
            Ty::F64 => 8,
            Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => return None,
        };
        let program = self.ctx.program;
        if program.section_at(a).is_none_or(|s| s.writable) {
            return None;
        }
        let bytes = program.read_va(a, width)?;
        let mut buf = [0u8; 8];
        buf[..width].copy_from_slice(bytes);
        Some(u64::from_le_bytes(buf))
    }

    /// Returns the declaration type of a variable.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    ///
    /// # Returns
    ///
    /// The scalar float type a vector register held (else `uint128_t`), the
    /// word type for registers, temporaries and globals, and the first-seen
    /// (else last-stored, else word) type for slots.
    pub(super) fn ty_of(&self, key: Key) -> Ty {
        match key {
            Key::Reg(r) if r.is_vector_register() => {
                self.ctx.reg_ty.get(&key).copied().unwrap_or(Ty::U128)
            }
            Key::Reg(r) if r >= Register::ST0 && r <= Register::ST7 => Ty::F64,
            Key::A64(crate::isa::a64::Reg::V(_)) => Ty::U128,
            Key::A32(crate::isa::a32::Reg::D(_)) => {
                self.ctx.reg_ty.get(&key).copied().unwrap_or(Ty::U64)
            }
            Key::A32(crate::isa::a32::Reg::S(_)) => {
                self.ctx.reg_ty.get(&key).copied().unwrap_or(self.word_ty())
            }
            Key::Reg(_)
            | Key::Tmp(_)
            | Key::Global(..)
            | Key::Param(_)
            | Key::A64(_)
            | Key::A32(_) => self.word_ty(),
            Key::Slot(k) => self
                .ctx
                .declared
                .get(&Key::Slot(k))
                .copied()
                .or_else(|| self.env.slot_bits.get(&k).map(|b| Ty::from_bits(*b)))
                .unwrap_or(self.word_ty()),
        }
    }

    /// Records a variable's declaration type on first sight (emission pass only).
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    /// * `ty` - Its type.
    pub(in crate::analysis::decompile) fn declare(&mut self, key: Key, ty: Ty) {
        if self.emit && !self.ctx.declared.contains_key(&key) {
            let ty = match key {
                Key::Slot(k) => self.ctx.frame.ty(k).unwrap_or(ty),
                Key::Reg(_)
                | Key::Param(_)
                | Key::Tmp(_)
                | Key::Global(..)
                | Key::A64(_)
                | Key::A32(_) => ty,
            };
            self.ctx.declared.insert(key, ty);
            if let Key::Slot(k) = key {
                std::sync::Arc::make_mut(&mut self.ctx.slot_types).insert(k, ty);
            }
        }
    }

    /// Materializes every environment entry (other than `key` itself) that
    /// may read text variable `key` ([`Expr::may_read`]).
    ///
    /// At a block end (`live` given) a register nobody reads again is simply
    /// forgotten; a reader already being materialized is parked instead.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable about to change.
    /// * `stack` - Keys whose materialization is in progress.
    /// * `live` - Liveness oracle at a block end.
    pub(super) fn protect_readers(
        &mut self,
        key: Key,
        stack: &mut Vec<Key>,
        live: Option<&LiveFn<'_>>,
    ) {
        let readers: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(k, v)| **k != key && v.may_read(key))
            .map(|(k, _)| *k)
            .collect();
        for x in readers {
            let dead = match live {
                Some(l) => is_register(x) && !l(x),
                None => self.dead_reg(x),
            };
            if dead {
                self.forget_dead(x);
            } else if stack.contains(&x) {
                self.park(x);
            } else {
                self.materialize(x, stack, live);
            }
        }
    }

    /// Writes out every value that was read from memory, as
    /// [`Exec::protect_memory`] does, keeping right the operands an
    /// instruction holds while it does.
    ///
    /// A store's value and address, or an atomic's operands, were read from
    /// the environment before the writes, so a variable they name may change
    /// under them: after `mov ecx, [rax+rcx*4]; mov [rbx+0x24], ecx` the
    /// write-out of `rcx = g[rcx]` makes the stored `g[rcx]` read the new
    /// `rcx`. Where an operand holds the pending value of a variable being
    /// written, it reads that variable instead (`*(rbx + 0x24) = rcx`); where
    /// it still needs the old value of one, it is copied into a temporary
    /// before any write. Only the emission pass renders these operands, so
    /// the dataflow pass protects as before.
    ///
    /// # Arguments
    ///
    /// * `flight` - The operands, rewritten in place, each with the type a
    ///   temporary holding it is declared with.
    pub(in crate::analysis::decompile) fn protect_memory_around(
        &mut self,
        flight: &mut [(&mut Expr, Ty)],
    ) {
        /// The first marker id, counted down: far above any temporary.
        const MARK: u32 = u32::MAX - 1;
        if !self.emit || self.ctx.symbolic_only {
            self.protect_memory();
            return;
        }
        let mut writes: BTreeSet<Key> = BTreeSet::new();
        {
            let pending = &self.env.vals;
            loop {
                let more: Vec<Key> = pending
                    .iter()
                    .filter(|(k, v)| {
                        !writes.contains(*k)
                            && !self.dead_reg(**k)
                            && **v != Expr::Var(**k)
                            && (v.mem_dependent()
                                || v.any_var(&|j| j != **k && writes.contains(&j)))
                    })
                    .map(|(k, _)| *k)
                    .collect();
                if more.is_empty() {
                    break;
                }
                writes.extend(more);
            }
        }
        let hazard = |e: &Expr| e.any_var(&|j| writes.contains(&j));
        if !flight.iter().any(|(e, _)| hazard(e)) {
            self.protect_memory();
            return;
        }
        let mut order: Vec<(Key, Expr)> = writes
            .iter()
            .filter_map(|k| Some((*k, self.env.vals.get(k)?.clone())))
            .collect();
        order.sort_by_key(|(_, v)| std::cmp::Reverse(v.size()));
        let marker = |i: usize| Expr::Var(Key::Tmp(MARK - u32::try_from(i).unwrap_or(0)));
        for (e, ty) in flight.iter_mut() {
            if !hazard(e) {
                continue;
            }
            let marked = order
                .iter()
                .enumerate()
                .fold((*e).clone(), |m, (i, (_, v))| m.subst(v, &marker(i)));
            **e = if hazard(&marked) {
                self.tmp_of(e, *ty)
            } else {
                marked
            };
        }
        self.protect_memory();
        for (i, (k, _)) in order.iter().enumerate() {
            let now = self.env.vals.get(k).cloned().unwrap_or(Expr::Var(*k));
            for (e, _) in flight.iter_mut() {
                **e = e.subst(&marker(i), &now);
            }
        }
    }

    /// Writes out every value that was read from memory, because a store or
    /// call is about to change memory; a register nothing reads later is
    /// forgotten instead.
    pub(in crate::analysis::decompile) fn protect_memory(&mut self) {
        let readers: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(_, v)| v.mem_dependent())
            .map(|(k, _)| *k)
            .collect();
        for r in readers {
            if self.dead_reg(r) {
                self.forget_dead(r);
            } else {
                self.materialize(r, &mut Vec::new(), None);
            }
        }
        self.protect_flags(&|e: &Expr| e.mem_dependent());
    }

    /// Tells whether register `k` is read by no later instruction, so its
    /// pending value may be dropped rather than written out.
    ///
    /// An x87 register never is: the next push or pop moves its value to a
    /// neighbouring position, a read the per-instruction needs do not see.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable; only registers can be dead here.
    pub(super) fn dead_reg(&self, k: Key) -> bool {
        is_register(k)
            && !k.is_x87()
            && self
                .regs_needed
                .as_ref()
                .is_some_and(|m| !m.contains_key(&k))
    }

    /// Drops the pending value of a dead register ([`Exec::dead_reg`])
    /// without writing it out.
    ///
    /// Its text variable then holds no value the machine does, so the
    /// register is no longer named as one, nor counted as set for the next
    /// call ([`Env::clobbered`], [`Env::fresh`]): a computed
    /// jump the text reads as a tail call (`jmp rax` through a table the
    /// analysis could not bound) reads arguments the liveness never saw,
    /// and passed `rdx` by its stale name after a store dropped the load
    /// it held.
    ///
    /// # Arguments
    ///
    /// * `k` - The register.
    pub(super) fn forget_dead(&mut self, k: Key) {
        self.env.vals.remove(&k);
        self.big_written.remove(&k);
        self.env.fresh.remove(&k);
        self.env.clobbered.insert(k);
    }

    /// Copies pending flag operands matching `pred` into temporaries so the
    /// eventual condition still reads the values the compare saw.
    ///
    /// Dead flags are dropped instead of protected.
    ///
    /// # Arguments
    ///
    /// * `pred` - Selects the operands about to become stale.
    pub(super) fn protect_flags(&mut self, pred: &dyn Fn(&Expr) -> bool) {
        if let Some((held, saved)) = self.status_ah.take() {
            let ah = self.canon(Register::AH);
            let read_later = self
                .regs_needed
                .as_ref()
                .is_none_or(|m| m.get(&ah).is_some_and(|lane| *lane >= 16));
            if let (true, Flags::Float(l, r, bits)) = (read_later, saved) {
                let (l, r) = self.tmp_pair(l, r, pred);
                self.status_ah = Some((held, Flags::Float(l, r, bits)));
            }
        }
        let flags = std::mem::replace(&mut self.flags, Flags::Unknown);
        self.flags = match flags {
            _ if self.flags_needed == 0 => Flags::Unknown,
            Flags::Cmp(l, r, b) => {
                let (l, r) = self.tmp_pair(l, r, pred);
                Flags::Cmp(l, r, b)
            }
            Flags::Float(l, r, b) => {
                let (l, r) = self.tmp_pair(l, r, pred);
                Flags::Float(l, r, b)
            }
            Flags::FCmp(p, l, r, b) => {
                let (l, r) = self.tmp_pair(l, r, pred);
                Flags::FCmp(p, l, r, b)
            }
            Flags::Test(l, r, b) => {
                let (l, r) = self.tmp_pair(l, r, pred);
                Flags::Test(l, r, b)
            }
            Flags::Result(e, b) => Flags::Result(self.tmp_if(e, pred), b),
            Flags::Shift(e, b, c) => Flags::Shift(self.tmp_if(e, pred), b, self.tmp_if(c, pred)),
            Flags::Add(l, r, b) => Flags::Add(self.tmp_if(l, pred), self.tmp_if(r, pred), b),
            Flags::Carry(e) => Flags::Carry(self.tmp_if(e, pred)),
            Flags::Truth(e, cc) => Flags::Truth(self.tmp_if(e, pred), cc),
            Flags::Unknown => Flags::Unknown,
        };
        if let Some(idx) = self.switch_idx.take() {
            self.switch_idx = Some(self.tmp_if(idx, pred));
        }
    }

    /// Returns what reads a variable's pending value back once it is
    /// written out: the variable itself, or a stack slot read at the width
    /// the value was stored at when its name is declared at another.
    ///
    /// A slot's name reads as many bits as it is declared with, so a
    /// `uint32_t local_58` holds only the low half of the qword stored to
    /// it (`*(uint64_t*)&local_58 = x;`), and a dword stored to a `uint64_t`
    /// leaves the name's high half what it was. A read at the store's width
    /// is the value when the value is an integer the store keeps whole, or
    /// when its reader looks at no bit above the store's; the name itself
    /// is when its reader looks at exactly the bits it is declared with, all
    /// of them stored. A slot declared wider than a word is named bare at
    /// every width ([`Names::slot_at`]), so no read of it is spelled at the
    /// store's.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    /// * `value` - Its pending value.
    /// * `need` - The low bits of the value its reader looks at, when that
    ///   is all it looks at: a compare of that width of the value itself.
    ///
    /// # Returns
    ///
    /// The read, or `None` when no read of the variable is the value: a
    /// float, a slot declared wider than a word, or bits the store did not
    /// keep.
    fn read_back(&self, key: Key, value: &Expr, need: Option<u8>) -> Option<Expr> {
        let Key::Slot(o) = key else {
            return Some(Expr::Var(key));
        };
        let declared = self.ty_of(key).bits();
        let stored = self.env.slot_bits.get(&o).copied().unwrap_or(declared);
        if stored == declared || (need == Some(declared) && declared < stored) {
            return Some(Expr::Var(key));
        }
        let kept = known_bits(value) & !mask_bits(stored) == 0 || need.is_some_and(|b| b <= stored);
        (declared <= 64 && stored <= 64 && !value.is_float() && kept)
            .then(|| Expr::deref(Expr::Sp(o), Ty::from_bits(stored)))
    }

    /// Places a phi: writes `key = value;` at the block's end.
    ///
    /// The values that read the old `key` are written out first. Then
    /// condition and switch-index operands that computed exactly `value`
    /// read it back from `key` ([`Exec::read_back`]; a copy or constant is
    /// not worth naming, so only real computations are rewritten);
    /// operands reading the old `key` any other way are copied to
    /// temporaries. The readers go first because
    /// writing one out copies the operands that read it into temporaries,
    /// which would otherwise copy a rewritten operand before `key` holds
    /// what it reads (`tmp_1 = r11 | r8;` ahead of `r8 <<= 12` for `r11 |
    /// (r8 << 12)`).
    ///
    /// # Arguments
    ///
    /// * `key` - The variable a successor needs in the text.
    /// * `live` - Liveness oracle for the readers protected on the way.
    pub(in crate::analysis::decompile) fn materialize_phi(&mut self, key: Key, live: &LiveFn<'_>) {
        if !self.env.vals.contains_key(&key) {
            return;
        }
        self.protect_readers(key, &mut vec![key], Some(live));
        let Some(value) = self.env.vals.get(&key).cloned() else {
            return;
        };
        let value = &value;
        let marker = Expr::Var(Key::Tmp(0));
        let rewrite = |ex: &mut Self, e: Expr, bits: Option<u8>| -> Expr {
            if matches!(e, Expr::Const(_)) {
                return e;
            }
            let back = (value.size() > 1)
                .then(|| ex.read_back(key, value, bits.filter(|_| e == *value)))
                .flatten();
            let marked = match &back {
                Some(_) => e.subst(value, &marker),
                None => e.clone(),
            };
            match &back {
                _ if marked.mentions(key) => ex.tmp_if(e, &|_| true),
                Some(b) => marked.subst(&marker, b),
                None => marked,
            }
        };
        let pair = |ex: &mut Self, l: Expr, r: Expr, bits: Option<u8>| -> (Expr, Expr) {
            let same = l == r;
            let l = rewrite(ex, l, bits);
            let r = if same {
                l.clone()
            } else {
                rewrite(ex, r, bits)
            };
            (l, r)
        };
        let flags = std::mem::replace(&mut self.flags, Flags::Unknown);
        self.flags = match flags {
            Flags::Cmp(l, r, b) => {
                let (l, r) = pair(self, l, r, Some(b));
                Flags::Cmp(l, r, b)
            }
            Flags::Float(l, r, b) => {
                let (l, r) = pair(self, l, r, None);
                Flags::Float(l, r, b)
            }
            Flags::FCmp(p, l, r, b) => {
                let (l, r) = pair(self, l, r, None);
                Flags::FCmp(p, l, r, b)
            }
            Flags::Test(l, r, b) => {
                let (l, r) = pair(self, l, r, Some(b));
                Flags::Test(l, r, b)
            }
            Flags::Result(e, b) => Flags::Result(rewrite(self, e, Some(b)), b),
            Flags::Shift(e, b, c) => {
                Flags::Shift(rewrite(self, e, None), b, rewrite(self, c, None))
            }
            Flags::Add(l, r, b) => {
                Flags::Add(rewrite(self, l, Some(b)), rewrite(self, r, Some(b)), b)
            }
            Flags::Carry(e) => Flags::Carry(rewrite(self, e, None)),
            Flags::Truth(e, cc) => Flags::Truth(rewrite(self, e, None), cc),
            Flags::Unknown => Flags::Unknown,
        };
        if let Some(idx) = self.switch_idx.take() {
            self.switch_idx = Some(rewrite(self, idx, None));
        }
        let Some(val) = self.env.vals.remove(&key) else {
            return;
        };
        self.write_out(key, &val);
    }

    /// Copies both operands of a compare into temporaries where `pred`
    /// selects them, one copy serving both sides when they are the same.
    ///
    /// `test r, r` compares a value with itself; copied once, the condition
    /// reads `t == 0` rather than `(t1 & t2) == 0`.
    ///
    /// # Arguments
    ///
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    /// * `pred` - Decides whether a copy is needed.
    ///
    /// # Returns
    ///
    /// The operands, copied where needed.
    pub(super) fn tmp_pair(
        &mut self,
        l: Expr,
        r: Expr,
        pred: &dyn Fn(&Expr) -> bool,
    ) -> (Expr, Expr) {
        let same = l == r;
        let l = self.tmp_if(l, pred);
        let r = if same {
            l.clone()
        } else {
            self.tmp_if(r, pred)
        };
        (l, r)
    }

    /// Copies `e` into a fresh temporary when `pred` selects it.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression; constants are never copied.
    /// * `pred` - Decides whether the copy is needed.
    ///
    /// # Returns
    ///
    /// The temporary's variable, or `e` unchanged.
    pub(super) fn tmp_if(&mut self, e: Expr, pred: &dyn Fn(&Expr) -> bool) -> Expr {
        if matches!(e, Expr::Const(_)) || !pred(&e) {
            return e;
        }
        self.tmp_of(&e, self.word_ty())
    }

    /// Declares a fresh temporary of type `ty`, numbered for the pass.
    ///
    /// # Arguments
    ///
    /// * `ty` - The temporary's declared type.
    ///
    /// # Returns
    ///
    /// The temporary's key.
    pub(in crate::analysis::decompile) fn fresh_tmp(&mut self, ty: Ty) -> Key {
        let id = if self.emit {
            self.ctx.tmp_count += 1;
            self.ctx.tmp_count
        } else {
            self.tmp_local += 1;
            self.tmp_local
        };
        let key = Key::Tmp(id);
        self.declare(key, ty);
        key
    }

    /// Copies `e` into a fresh temporary of type `ty`.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `ty` - The temporary's declared type.
    ///
    /// # Returns
    ///
    /// The temporary's variable.
    pub(in crate::analysis::decompile) fn tmp_of(&mut self, e: &Expr, ty: Ty) -> Expr {
        let key = self.fresh_tmp(ty);
        if let (Some(p), Key::Tmp(id)) = (&mut self.ctx.probe, key) {
            p.temp(id, e);
        }
        let n = self.names();
        emit_line!(self, format!("{} = {};", n.key(key), e.render(&n)));
        if self.emit {
            self.record(EffectKind::Assign(key, e.clone(), ty.bits()));
        }
        Expr::Var(key)
    }

    /// Forgets `key` because it is about to change without a modeled value,
    /// ending the block's equality assumption when it is about `key`.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable being clobbered.
    pub(in crate::analysis::decompile) fn clobber(&mut self, key: Key) {
        if self.assume.is_some_and(|(k, _)| k == key) {
            self.assume = None;
        }
        self.protect_readers(key, &mut Vec::new(), None);
        self.protect_flags(&|e: &Expr| e.mentions(key));
        self.env.vals.remove(&key);
        self.env.narrow.remove(&key);
        self.env.unset.remove(&key);
        if let Key::Slot(o) = key {
            self.env.slot_bits.remove(&o);
        }
    }
}

/// Recognizes a write to the try level, `[ebp-4]`, in a 32-bit function
/// with a registered handler: `mov` of a constant or a register, or the
/// `or [ebp-4], -1` and `and [ebp-4], 0` the compiler prefers.
///
/// # Arguments
///
/// * `instr` - The instruction (operand 0 is the destination).
/// * `bitness` - 32 or 64; only 32-bit code keeps a try level there.
pub(in crate::analysis::decompile) fn try_level_store(instr: &Instruction, bitness: u32) -> bool {
    bitness == 32
        && matches!(
            instr.mnemonic(),
            Mnemonic::Mov | Mnemonic::Or | Mnemonic::And
        )
        && instr.op0_kind() == OpKind::Memory
        && instr.memory_base() == Register::EBP
        && instr.memory_index() == Register::None
        && crate::disasm::displacement(instr, 32) == -4
        && matches!(
            instr.op1_kind(),
            OpKind::Register
                | OpKind::Immediate32
                | OpKind::Immediate8to32
                | OpKind::Immediate32to64
        )
}

/// The bytes a new stack pointer makes room for below a tracked one, when
/// no constant gives them: `sp - n` or `sp + -n` with `n` computed.
///
/// # Arguments
///
/// * `v` - The new stack pointer.
///
/// # Returns
///
/// The amount, or `None` for a constant one or a value not relative to a
/// tracked stack offset.
fn dynamic_room(v: &Expr) -> Option<Expr> {
    room_below(v).map(|(_, size)| size)
}

/// Reads a value as a stack offset less an amount no constant gives: `sp -
/// n`, `sp + -n` or `-n + sp`.
///
/// # Arguments
///
/// * `v` - The value.
///
/// # Returns
///
/// The offset and the amount, or `None` for any other value.
fn room_below(v: &Expr) -> Option<(i64, Expr)> {
    let (k, size) = match v {
        Expr::Bin(Op::Sub, base, size) => match **base {
            Expr::Sp(k) => (k, &**size),
            _ => return None,
        },
        Expr::Bin(Op::Add, l, r) => match (&**l, &**r) {
            (Expr::Sp(k), Expr::Un(UnOp::Neg, size)) | (Expr::Un(UnOp::Neg, size), Expr::Sp(k)) => {
                (*k, &**size)
            }
            _ => return None,
        },
        _ => return None,
    };
    (!matches!(size, Expr::Const(_))).then(|| (k, size.clone()))
}
