//! Reading and writing operands: registers by width, memory through the
//! overlay, and the stack.

use super::sse::Width;
use super::{
    Emulator, HISTORY_MAX, PAGE, Stop, Written, branch_target, canon, lane_shift, lo64, mask,
    mem_bytes, reg_bits, seg_slot,
};
use crate::isa::x86::{Instruction, Mnemonic, OpKind, Register, gpr_bank_index, xmm_slot};
use crate::num::{from_usize, lo8};

impl Emulator<'_> {
    /// Reads operand 0 as a value (for read-modify-write instructions).
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    pub(super) fn dest(&mut self, i: &Instruction) -> Result<u64, Stop> {
        self.operand(i, 0)
    }

    /// Reads the source operand: operand 1 for two-operand forms, else 0.
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    pub(super) fn source(&mut self, i: &Instruction) -> Result<u64, Stop> {
        let idx = u32::from(i.op_count() > 1);
        self.operand(i, idx)
    }

    /// Reads operand `n`.
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    pub(super) fn operand(&mut self, i: &Instruction, n: u32) -> Result<u64, Stop> {
        match i.op_kind(n) {
            OpKind::Register => Ok(self.reg_sized(i.op_register(n))),
            OpKind::Immediate8 => Ok(u64::from(i.immediate8())),
            OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate32to64
            | OpKind::Immediate64 => Ok(i.immediate(n)),
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.load(addr, mem_bytes(i))
            }
            other => Err(Stop::Unmodeled(format!("operand {other:?}"))),
        }
    }

    /// Reads operand `n` as a 128-bit vector.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `n` - The operand index.
    ///
    /// # Errors
    ///
    /// When the operand is neither a vector register nor memory.
    pub(super) fn vector_operand(&mut self, i: &Instruction, n: u32) -> Result<u128, Stop> {
        match i.op_kind(n) {
            OpKind::Register => match xmm_slot(i.op_register(n)) {
                Some(k) => Ok(self.xmm[k]),
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op_register(n)))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                let lo = self.load(addr, 8)?;
                let hi = self.load(addr.wrapping_add(8), 8)?;
                Ok(u128::from(lo) | (u128::from(hi) << 64))
            }
            other => Err(Stop::Unmodeled(format!("vector operand {other:?}"))),
        }
    }

    /// Writes a 128-bit vector to operand 0.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// When operand 0 is neither a vector register nor memory, or memory
    /// would grow past its cap.
    pub(super) fn vector_store(&mut self, i: &Instruction, v: u128) -> Result<(), Stop> {
        match i.op0_kind() {
            OpKind::Register => match xmm_slot(i.op0_register()) {
                Some(k) => {
                    self.xmm[k] = v;
                    Ok(())
                }
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op0_register()))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.write(addr, lo64(v), 8)?;
                self.write(addr.wrapping_add(8), lo64(v >> 64), 8)
            }
            other => Err(Stop::Unmodeled(format!("vector store {other:?}"))),
        }
    }

    /// Moves the low `width` bytes between a vector register and elsewhere.
    ///
    /// `movss`, `movsd`, `movd` and `movq` carry a scalar in the bottom of a
    /// vector register. A read from memory clears the rest of the register,
    /// as the hardware does; a move between two vector registers leaves the
    /// upper bytes of the destination alone.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `width` - The lane carried.
    ///
    /// # Errors
    ///
    /// When neither operand is a vector register, which is not a form these
    /// mnemonics take.
    pub(super) fn scalar_move(&mut self, i: &Instruction, width: Width) -> Result<(), Stop> {
        let dst_vec = i.op0_kind() == OpKind::Register && xmm_slot(i.op0_register()).is_some();
        let src_vec = i.op_kind(1) == OpKind::Register && xmm_slot(i.op_register(1)).is_some();
        let merge = matches!(i.mnemonic(), Mnemonic::Movss | Mnemonic::Movsd);
        let mask = width.lane();
        if dst_vec {
            let src = if src_vec {
                self.vector_operand(i, 1)? & mask
            } else {
                u128::from(self.operand(i, 1)?) & mask
            };
            let keep = if src_vec && merge {
                self.vector_operand(i, 0)? & !mask
            } else {
                0
            };
            self.vector_store(i, keep | src)?;
            return Ok(());
        }
        if src_vec {
            let v = lo64(self.vector_operand(i, 1)? & mask);
            return self.store(i, v);
        }
        Err(Stop::Unmodeled(format!("scalar move {:?}", i.mnemonic())))
    }

    /// Writes `v` to operand 0, register or memory.
    ///
    /// # Errors
    ///
    /// When operand 0 is a kind the emulator cannot write, or memory would
    /// grow past its cap.
    pub(super) fn store(&mut self, i: &Instruction, v: u64) -> Result<(), Stop> {
        match i.op0_kind() {
            OpKind::Register => {
                self.write_reg_op(i, v);
                Ok(())
            }
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.write(addr, v, mem_bytes(i))
            }
            other => Err(Stop::Unmodeled(format!("store {other:?}"))),
        }
    }

    /// Writes `v` to the register named by operand 0, honoring its width.
    pub(super) fn write_reg_op(&mut self, i: &Instruction, v: u64) {
        self.set_reg_sized(i.op0_register(), v);
    }

    /// The destination of an indirect jump or call: the register's value, or
    /// the pointer loaded from the memory operand (a dispatch's jump table).
    ///
    /// # Arguments
    ///
    /// * `i` - The indirect jump or call.
    ///
    /// # Errors
    ///
    /// A fault when the table entry is unmapped, or unmodeled for a form that
    /// is neither register nor memory.
    fn indirect_target(&self, i: &Instruction) -> Result<u64, Stop> {
        match i.op0_kind() {
            OpKind::Register => Ok(self.reg(canon(i.op0_register()))),
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.load(addr, self.word)
            }
            other => Err(Stop::Unmodeled(format!("indirect {other:?}"))),
        }
    }

    /// The destination of a jump or call: its direct target, else
    /// [`Emulator::indirect_target`].
    ///
    /// # Arguments
    ///
    /// * `i` - The jump or call.
    ///
    /// # Errors
    ///
    /// As [`Emulator::indirect_target`].
    pub(super) fn transfer_target(&self, i: &Instruction) -> Result<u64, Stop> {
        branch_target(i).map_or_else(|| self.indirect_target(i), Ok)
    }

    /// Whether a condition holds under the current flags.
    ///
    /// # Arguments
    ///
    /// * `m` - The instruction's mnemonic, named in the stop.
    /// * `cond` - The conditional jump that reads the same flags.
    ///
    /// # Errors
    ///
    /// Unmodeled when the condition rests on a flag nothing computed.
    pub(super) fn condition(&self, m: Mnemonic, cond: Mnemonic) -> Result<bool, Stop> {
        self.jcc_taken(cond)
            .ok_or_else(|| Stop::Unmodeled(format!("{m:?} on flags it did not set")))
    }

    /// The effective address of a memory operand.
    ///
    /// A 16-bit address ([`crate::disasm::addresses_16_bit`]) reads the
    /// 16-bit registers and wraps at 64 KiB before the segment base is added.
    ///
    /// # Errors
    ///
    /// Never; kept fallible for symmetry with the operand readers.
    pub(super) fn mem_addr(&self, i: &Instruction) -> Result<u64, Stop> {
        if i.memory_base() == Register::RIP || i.memory_base() == Register::EIP {
            return Ok(i.ip_rel_memory_address());
        }
        let sixteen = crate::disasm::addresses_16_bit(i);
        let read = |r: Register| {
            if sixteen {
                self.reg_sized(r)
            } else {
                self.reg(canon(r))
            }
        };
        let base = if i.memory_base() == Register::None {
            0
        } else {
            read(i.memory_base())
        };
        let index = if i.memory_index() == Register::None {
            0
        } else {
            read(i.memory_index()).wrapping_mul(u64::from(i.memory_index_scale()))
        };
        let offset = base
            .wrapping_add(index)
            .wrapping_add(i.memory_displacement64());
        let offset = if sixteen { offset & 0xffff } else { offset };
        let segment = match (self.bitness, i.segment_prefix()) {
            (32, Register::FS) | (64, Register::GS) => self.teb,
            _ => 0,
        };
        Ok(self.narrow(offset.wrapping_add(segment)))
    }

    /// Whether anything backs `addr`: a written byte or the mapped image.
    ///
    /// Used in best-effort mode to tell a real transfer target from an import
    /// slot the OS loader would have filled, which stays zero or unmapped here.
    pub(super) fn mapped(&self, addr: u64) -> bool {
        self.byte(addr).is_some()
    }

    /// Whether best-effort mode skips a transfer to `to`: nothing maps it
    /// and it is not an API stub, so it is an import the OS loader would
    /// have resolved.
    ///
    /// # Arguments
    ///
    /// * `to` - The transfer target.
    pub(super) fn unresolved(&self, to: u64) -> bool {
        self.permissive && !self.apis.contains_key(&to) && !self.mapped(to)
    }

    /// Reads up to sixteen instruction bytes at `ip`, written bytes over image.
    ///
    /// The fetch consults memory the run has written before the static image,
    /// so code a packer decrypts into memory executes as the decrypted bytes,
    /// not the encrypted ones on disk. Code written into space the image never
    /// mapped (a packer's virtual-only section) is fetched from memory alone.
    ///
    /// # Returns
    ///
    /// The bytes to decode, or `None` when neither memory nor image backs `ip`.
    pub(super) fn fetch(&self, ip: u64) -> Option<Vec<u8>> {
        let window = ip..ip.saturating_add(16);
        if !self.mem.any_dirty(window.clone())
            && self.patched.range(window).next().is_none()
            && let Some(s) = self.program.read_va_upto(ip, 16)
        {
            return Some(s.to_vec());
        }
        let out = self.code_at(ip, 16);
        (!out.is_empty()).then_some(out)
    }

    /// Loads `bytes` bytes from `addr`, little-endian.
    ///
    /// On a 32-bit target the bytes past `0xffff_ffff` wrap to address
    /// zero, as the machine's linear addresses do.
    ///
    /// # Errors
    ///
    /// A fault when a byte is neither written nor backed by the image.
    pub(super) fn load(&self, addr: u64, bytes: usize) -> Result<u64, Stop> {
        if self.profiling && !self.on_stack(addr) {
            let mut pages = self.page_reads.borrow_mut();
            let entry = pages.entry(addr & !(PAGE - 1)).or_insert((0, self.last_ip));
            entry.0 += 1;
        }
        let mut v = 0u64;
        for k in 0..from_usize(bytes) {
            let a = self.narrow(addr.wrapping_add(k));
            let byte = self.byte_at(a).ok_or(Stop::Fault(a))?;
            v |= u64::from(byte) << (k * 8);
        }
        if self.trace_cap > 0 {
            self.step_memory.borrow_mut().push((false, addr, bytes, v));
        }
        Ok(v)
    }

    /// Writes the low `bytes` bytes of `v` to `addr`, little-endian.
    ///
    /// A write outside the stack is recorded as materialized: the bytes a
    /// packer decrypts into memory, which [`Emulator::run`] can then execute.
    /// On a 32-bit target the bytes past `0xffff_ffff` wrap to address zero.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when a byte not yet held would take memory past
    /// its cap; the bytes before it are written.
    pub(super) fn write(&mut self, addr: u64, v: u64, bytes: usize) -> Result<(), Stop> {
        if self.trace_cap > 0 {
            self.step_memory.borrow_mut().push((true, addr, bytes, v));
        }
        for k in 0..from_usize(bytes) {
            let a = self.narrow(addr.wrapping_add(k));
            if self.mem.len() >= self.memory_max && !self.mem.contains(a) {
                return Err(Stop::MemoryFull(a));
            }
            let byte = lo8(v >> (k * 8));
            if self.history.len() < HISTORY_MAX {
                self.history.push(Written {
                    addr: a,
                    value: byte,
                });
            }
            if self.origin.is_some() {
                self.step_writes.push(a);
            }
            self.mem.set(a, byte, !self.on_stack(a));
        }
        Ok(())
    }

    /// Whether the step that just ran birthed the watched value.
    ///
    /// A value is born the moment it exists whole: in any general register,
    /// or in memory at any alignment a write of this step touched, so a
    /// value built by two narrow stores is born by the one that completes
    /// it, whatever earlier steps wrote the other half. The instruction's
    /// own fetch does not count.
    ///
    /// # Returns
    ///
    /// Whether the watched value appeared.
    pub(super) fn born(&self) -> bool {
        let Some(watch) = self.origin else {
            return false;
        };
        if self.regs.contains(&watch) {
            return true;
        }
        self.step_writes.iter().any(|a| {
            (0..8).any(|back| {
                let at = a.wrapping_sub(back);
                (0..8).all(|k| self.byte(at.wrapping_add(k)) == Some(lo8(watch >> (k * 8))))
            })
        })
    }

    /// Whether `addr` is in the scratch stack the emulator hands the routine.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    pub(super) fn on_stack(&self, addr: u64) -> bool {
        addr >= self.stack_base.wrapping_sub(self.stack_span)
            && addr < self.stack_base.wrapping_add(self.stack_span)
    }

    /// Pushes a word onto the scratch stack.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when the word would take memory past its cap.
    pub(super) fn push(&mut self, v: u64) -> Result<(), Stop> {
        let sp = self.narrow(self.reg(Register::RSP).wrapping_sub(from_usize(self.word)));
        self.set_reg(Register::RSP, sp);
        self.write(sp, v, self.word)
    }

    /// Pops a word from the scratch stack.
    ///
    /// # Errors
    ///
    /// A fault when the stack word was never written.
    pub(super) fn pop(&mut self) -> Result<u64, Stop> {
        let sp = self.reg(Register::RSP);
        let v = self.load(sp, self.word)?;
        self.set_reg(
            Register::RSP,
            self.narrow(sp.wrapping_add(from_usize(self.word))),
        );
        Ok(v)
    }

    /// Writes `v` into register `r` honoring its named width.
    pub(super) fn set_reg_sized(&mut self, r: Register, v: u64) {
        let bits = reg_bits(r);
        let full = canon(r);
        let cur = self.reg(full);
        let placed = if bits >= 32 {
            mask(v, bits)
        } else {
            let at = lane_shift(r);
            (cur & !(mask(u64::MAX, bits) << at)) | (mask(v, bits) << at)
        };
        self.set_reg(full, placed);
    }

    /// Sets the zero, sign and parity flags from a result of `bits` width.
    ///
    /// Overflow goes unknown here and an instruction that computes it assigns
    /// it after, so an instruction the emulator models without overflow
    /// cannot leave a stale one behind for a signed jump to read.
    pub(super) fn set_flags(&mut self, r: u64, bits: u32) {
        let v = mask(r, bits);
        self.flags_zero = v == 0;
        self.flags_sign = v >> (bits - 1) & 1 == 1;
        self.flags_parity = lo8(v).count_ones().is_multiple_of(2);
        self.flags_over = None;
    }

    /// Reads a register at its named width.
    pub(super) fn reg_sized(&self, r: Register) -> u64 {
        let bits = reg_bits(r);
        mask(self.reg(canon(r)) >> lane_shift(r), bits)
    }

    /// The full-width value of a canonical register.
    ///
    /// The general registers and the six segment registers are held (a
    /// segment as its zero-extended selector, [`Emulator::segments`]). Any
    /// other register (a debug or control one, which `mov eax, dr7` names)
    /// reads as zero: the decoder numbers each register within its own kind,
    /// so `dr0` shares `rax`'s number, and indexing by it read and wrote
    /// `rax`.
    pub(super) fn reg(&self, r: Register) -> u64 {
        if let Some(slot) = seg_slot(r) {
            return self.segs[slot];
        }
        let Some(at) = gpr_bank_index(r) else {
            return 0;
        };
        self.regs.get(at).copied().unwrap_or(0)
    }

    /// Sets a canonical register's full-width value; a register that is not
    /// held does not change anything ([`Emulator::reg`]). A segment register
    /// keeps the low sixteen bits a move writes, the selector the machine
    /// holds.
    pub(super) fn set_reg(&mut self, r: Register, v: u64) {
        if let Some(slot) = seg_slot(r) {
            self.segs[slot] = v & 0xffff;
            return;
        }
        if let Some(at) = gpr_bank_index(r)
            && let Some(slot) = self.regs.get_mut(at)
        {
            *slot = v;
        }
    }
}
