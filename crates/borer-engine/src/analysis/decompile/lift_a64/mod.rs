//! The arm64 lifter: executes one block of A64 instructions over the
//! decompiler's symbolic environment.
//!
//! The arm64 counterpart of [`super::lift`], through the same executor
//! ([`Exec`]): the same [`Env`], [`Expr`] values, [`BlockOut`] and
//! recorded effects, so values stay symbolic until the text needs them and
//! stack slots, stores and writing values out follow the x86 lifter's
//! rules. A register is a [`Key::A64`] variable. The stack pointer is the
//! tracked offset [`Expr::Sp`] while it is one, so a frame's slots are
//! [`Key::Slot`]s; a `w` write zero-extends into its `x` register, a scalar
//! `v` write clears the bits above it, the zero register reads 0 and a
//! write to it vanishes. Pointer authentication and branch target
//! identification change no value. The flags are the x86 lifter's, read
//! through what set them ([`flags`]), and a conditional select is an
//! [`Expr::Ternary`]. In the entry block a store of a register the callee
//! must preserve ([`callee_saved`]) is a save, as the x86 lifter reads a
//! push. An instruction without a model (floating-point and vector
//! arithmetic, system registers, atomics) stays an `/* asm */` comment and
//! forgets what it writes. Calls, returns and jumps are lifted only as far
//! as a block's own effects need: which registers carry a call's arguments
//! and results is the arm64 decompiler's to read.

mod conv;
mod flags;
mod mem;
mod step;

pub(in crate::analysis::decompile) use conv::callee_saved;

use std::collections::btree_map::Entry;

use super::Ctx;
use super::expr::{Cc, Cond, Expr, Flags, Key, Op, Ty, fold, mask, sign_extend};
use super::lift::{
    BlockFacts, BlockOut, Branch, Callee, EffectKind, Env, Exec, LiveFn, Pass, PhiFn, Shown, pack,
};
use crate::analysis::name_of;
use crate::isa::a64::{self, Flow, Insn, Opnd, Reg, Shift};
use crate::isa::x86::ConditionCode;
use crate::program::Program;
use flags::Test;

/// Decodes the instruction at `va`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The address: four-byte aligned, in executable, file-backed
///   memory.
///
/// # Returns
///
/// The instruction, or `None` when the address is misaligned, unmapped or
/// not executable.
pub(in crate::analysis::decompile) fn decode(program: &Program, va: u64) -> Option<Insn> {
    if !va.is_multiple_of(crate::num::from_usize(a64::INSN_LEN))
        || !crate::analysis::is_executable_va(program, va)
    {
        return None;
    }
    let bytes: [u8; a64::INSN_LEN] = program.read_va(va, a64::INSN_LEN)?.try_into().ok()?;
    Some(a64::decode(u32::from_le_bytes(bytes), va))
}

/// Executes one arm64 block from `env`, returning its lines and
/// control-flow facts, as [`super::lift::exec_block`] does an x86 block.
///
/// Flag liveness is computed backwards inside the block, the block's own
/// branch counting as a reader and `flags_out` keeping them live to the
/// end. A conditional branch's condition is read after the phi writes, so
/// it names what the text holds there. The equality a predecessor's
/// branch established holds over the block's reads, and a comment the
/// overlay holds for an instruction precedes its lines. A flags rebase
/// ([`BlockFacts::rebase_flags`]) is an x86 decision and is not applied.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `instrs` - The block's instructions.
/// * `env` - State at the block's entry; updated to the state at its exit.
/// * `pass` - Record text (the emission pass) or only compute state.
/// * `phi` - Values the block must write out at its end, and the liveness
///   oracle used while doing so.
/// * `facts` - Whether a successor reads the flags, the equality the block
///   runs under, and whether it is the entry block.
///
/// # Returns
///
/// The lines and the block's branch, jump and slot facts.
pub(in crate::analysis::decompile) fn exec_block_a64(
    ctx: &mut Ctx<'_>,
    instrs: &[Insn],
    env: &mut Env,
    pass: Pass,
    phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
    facts: BlockFacts<'_>,
) -> BlockOut {
    let start = instrs.first().map_or(0, |i| i.va);
    let mut lift = Lift {
        ex: Exec::new(ctx, env, pass, &facts, start),
    };
    let live = flags::live_after(instrs, facts.flags_out);
    let mut out = BlockOut::default();
    let mut jcc = None;
    for (idx, i) in instrs.iter().enumerate() {
        lift.ex.at = i.va;
        if let Some(c) = lift.ex.ctx.overlay.comments.get(&i.va) {
            lift.ex.lines.push(format!("// {c}"));
        }
        lift.ex.flags_needed = live.get(idx).copied().unwrap_or(u32::MAX);
        let later = instrs.get(idx + 1..).unwrap_or(&[]);
        match i.flow {
            Flow::Next => lift.step(i, later),
            Flow::CondJump => match (flags::test(i), i.target()) {
                (Some(test), Some(to)) => jcc = Some((test, to, next(i))),
                _ => lift.unmodeled(i),
            },
            Flow::Jump => match i.target() {
                Some(t) if lift.ex.ctx.block_starts.contains(&t) => out.goto = Some(t),
                Some(t) => lift.tail_call(t),
                None => lift.jump(i, &mut out),
            },
            Flow::Call => lift.call(i),
            Flow::Return => lift.ret(),
            Flow::Invalid => lift.unmodeled(i),
        }
    }
    lift.finish(out, jcc, facts.flags_out, phi, start)
}

/// The address after an instruction.
///
/// # Arguments
///
/// * `i` - The instruction.
fn next(i: &Insn) -> u64 {
    i.va.wrapping_add(crate::num::from_usize(a64::INSN_LEN))
}

/// Cuts a value to its low `bits`; from 64 bits up it is kept whole.
///
/// # Arguments
///
/// * `e` - The value.
/// * `bits` - The width kept.
fn low(e: Expr, bits: u16) -> Expr {
    if bits >= 64 {
        e
    } else {
        mask(e, (1u64 << bits) - 1)
    }
}

/// The low 64 bits of a value a `v` register holds, which may be wider:
/// its own variable, or a 128-bit load.
///
/// # Arguments
///
/// * `e` - The value.
fn low64(e: Expr) -> Expr {
    match e {
        Expr::Var(Key::A64(Reg::V(_))) | Expr::Deref(_, Ty::U128) => {
            Expr::Cast(Box::new(e), Ty::U64)
        }
        other => other,
    }
}

/// The width in bits an expression carries for an operand width.
///
/// # Arguments
///
/// * `bits` - The operand's width, 8 to 128.
fn width8(bits: u16) -> u8 {
    u8::try_from(bits).unwrap_or(u8::MAX)
}

/// A register operand shifted or extended as the encoding says, with
/// every bit the machine reads and none it does not.
///
/// # Arguments
///
/// * `raw` - The register's whole value.
/// * `bits` - The width it is read at, 32 or 64.
/// * `shift` - The shift or extension.
/// * `amount` - The shift, or the left shift after an extension.
/// * `width` - The operation's width: bits above it do not matter, since
///   the result is cut to it.
fn shifted(raw: Expr, bits: u16, shift: Shift, amount: u8, width: u16) -> Expr {
    let by = Expr::Const(u64::from(amount));
    let shl = |e: Expr| fold(Op::Shl, e, by.clone(), 64);
    match shift {
        Shift::Lsl | Shift::Uxtx | Shift::Sxtx if bits >= width => shl(raw),
        Shift::Lsl | Shift::Uxtx | Shift::Sxtx => shl(low(raw, bits)),
        Shift::Lsr => fold(Op::Shr, low(raw, bits), by, 64),
        Shift::Asr if bits >= 64 => fold(Op::Sar, raw, by, 64),
        Shift::Asr => fold(Op::Sar, sign_extend(raw, width8(bits)), by, 64),
        Shift::Ror if amount == 0 => low(raw, bits),
        Shift::Ror => fold(Op::Ror(width8(bits)), low(raw, bits), by, 64),
        Shift::Uxtb => shl(low(raw, 8)),
        Shift::Uxth => shl(low(raw, 16)),
        Shift::Uxtw => shl(low(raw, 32)),
        Shift::Sxtb => shl(sign_extend(raw, 8)),
        Shift::Sxth => shl(sign_extend(raw, 16)),
        Shift::Sxtw => shl(sign_extend(raw, 32)),
    }
}

/// One block's lifting over the shared executor.
struct Lift<'c, 'a> {
    /// The executor: the environment, the function's state and the lines.
    ex: Exec<'c, 'a>,
}

impl Lift<'_, '_> {
    /// Reads a register's whole value.
    ///
    /// # Arguments
    ///
    /// * `r` - The register: an `x` or `v` register reads as the
    ///   environment holds it (a `w` read is its `x` register's value,
    ///   which a caller cuts where the upper bits matter), the stack
    ///   pointer as its tracked offset, the zero register as 0.
    fn read(&self, r: Reg) -> Expr {
        match r {
            Reg::Zr => Expr::Const(0),
            Reg::Sp => self
                .ex
                .env
                .sp
                .map_or_else(|| self.ex.env.get(Key::A64(Reg::Sp)), Expr::Sp),
            Reg::X(_) | Reg::V(_) => self.ex.assumed(self.ex.env.get(Key::A64(r))),
        }
    }

    /// Writes a register at a width, lazily.
    ///
    /// A `w` write zero-extends into its `x` register and a scalar `v`
    /// write clears the bits above it, so the value is cut to the width; a
    /// write to the zero register vanishes; the stack pointer is tracked as
    /// an offset while the value is one, and held as a value when not.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `bits` - The width written.
    /// * `v` - The value.
    fn write(&mut self, r: Reg, bits: u16, v: Expr) {
        let v = low(v, bits);
        match (r, v) {
            (Reg::Zr, _) => {}
            (Reg::Sp, Expr::Sp(k)) => {
                self.ex.env.sp = Some(k);
                self.ex.env.vals.remove(&Key::A64(Reg::Sp));
            }
            (Reg::Sp, v) => {
                self.ex.env.sp = None;
                self.ex.assign(Key::A64(Reg::Sp), v);
            }
            (Reg::X(_) | Reg::V(_), v) => self.ex.assign(Key::A64(r), v),
        }
    }

    /// Writes the registers an instruction sets at once, in order, every
    /// value read before any changes (a pair load and its write-back), the
    /// early write-out of one waiting until all are recorded, as
    /// [`Exec::reg_write_all`] does.
    ///
    /// # Arguments
    ///
    /// * `writes` - Each register, the width written and its value.
    fn write_all(&mut self, writes: Vec<(Reg, u16, Expr)>) {
        let outer = self.ex.deferred.replace(Vec::new());
        for (r, bits, v) in writes {
            self.write(r, bits, v);
        }
        let waiting = std::mem::replace(&mut self.ex.deferred, outer).unwrap_or_default();
        for k in waiting {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
    }

    /// Reads a source operand: a general register, a shifted or extended
    /// one, or an immediate.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    /// * `width` - The operation's width, 32 or 64.
    ///
    /// # Returns
    ///
    /// The value, whose bits above `width` the caller cuts or does not
    /// depend on; `None` for any other operand.
    fn source(&self, i: &Insn, k: usize, width: u16) -> Option<Expr> {
        match i.operands.get(k).copied()? {
            Opnd::Reg {
                reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
                ..
            } => Some(self.read(reg)),
            Opnd::Shifted {
                reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
                bits,
                shift,
                amount,
            } => Some(shifted(self.read(reg), bits, shift, amount, width)),
            Opnd::Imm(v) => Some(Expr::Const(v)),
            Opnd::Reg { .. }
            | Opnd::Shifted { .. }
            | Opnd::None
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => None,
        }
    }

    /// Lifts an instruction without a model: keeps its assembly as a
    /// comment and forgets every register it may write, the flags and, if
    /// it has a memory operand, what memory held.
    ///
    /// The registers are its first operand, the old value an atomic hands
    /// its second, the `v` register a vector form names in its low five
    /// bits, and a written-back base. It counts as unmodeled whatever it
    /// writes, since a check cannot tell what it left.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    fn unmodeled(&mut self, i: &Insn) {
        let mut written = Vec::new();
        match i.operands[0] {
            Opnd::Reg { reg, .. } => written.push(reg),
            Opnd::Other => written.push(Reg::V(crate::num::lo8(u64::from(i.word & 0x1f)))),
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => {}
        }
        if let (a64::Mnemonic::Atomic(..), Opnd::Reg { reg, .. }) = (i.mnemonic, i.operands[1]) {
            written.push(reg);
        }
        let mut memory = false;
        for o in &i.operands {
            if let Opnd::Mem(m) = o {
                memory = true;
                if m.mode != a64::Mode::Offset {
                    written.push(m.base);
                }
            }
        }
        if memory {
            if let Some(p) = &mut self.ex.ctx.probe {
                p.asm();
            }
            self.ex.protect_memory();
        }
        for r in written {
            match r {
                Reg::Zr => {}
                Reg::Sp => {
                    self.ex.env.sp = None;
                    self.ex.clobber(Key::A64(Reg::Sp));
                }
                Reg::X(_) | Reg::V(_) => self.ex.clobber(Key::A64(r)),
            }
        }
        self.ex.unmodeled += 1;
        self.ex.flags = Flags::Unknown;
        if self.ex.emit {
            self.ex.lines.push(format!("/* asm: {} */", a64::text(i)));
            self.ex.record(EffectKind::Unmodeled);
        }
    }

    /// Lifts a call: writes out everything pending, since the callee may
    /// read any register, slot or memory, records the call with its result
    /// in `x0`, and forgets the registers and flags the call may change.
    ///
    /// # Arguments
    ///
    /// * `i` - The `bl` or `blr`.
    fn call(&mut self, i: &Insn) {
        let callee = match (i.target(), i.operands[0]) {
            (Some(t), _) => Callee::Direct(t),
            (None, Opnd::Reg { reg, .. }) => Callee::Through(self.read(reg)),
            (None, _) => return self.unmodeled(i),
        };
        let pending: Vec<Key> = self.ex.env.vals.keys().copied().collect();
        for k in pending {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
        if self.ex.emit {
            let text = self.callee_text(&callee);
            self.ex.lines.push(format!("x0 = {text}();"));
        }
        self.ex.record_call(
            callee,
            Vec::new(),
            Some(Key::A64(Reg::X(0))),
            None,
            false,
            Shown::Statement,
        );
        for r in conv::clobbered() {
            self.ex.clobber(Key::A64(r));
        }
        self.ex.flags = Flags::Unknown;
    }

    /// The text a call names its callee by.
    ///
    /// # Arguments
    ///
    /// * `callee` - What it calls.
    fn callee_text(&self, callee: &Callee) -> String {
        match callee {
            Callee::Direct(t) => name_of(self.ex.ctx.analysis, self.ex.ctx.overlay, *t),
            Callee::Through(e) => format!("(*{})", e.render(&self.ex.names())),
            Callee::Builtin(..) => String::new(),
        }
    }

    /// Lifts a jump out of the function as a tail call.
    ///
    /// # Arguments
    ///
    /// * `target` - Where it goes.
    fn tail_call(&mut self, target: u64) {
        let callee = Callee::Direct(target);
        if self.ex.emit {
            let text = self.callee_text(&callee);
            self.ex.lines.push(format!("return {text}();"));
        }
        self.ex
            .record_call(callee, Vec::new(), None, None, false, Shown::Tail);
    }

    /// Lifts a jump through a register: the dispatch of a jump table the
    /// analysis resolved, else a computed `goto`.
    ///
    /// # Arguments
    ///
    /// * `i` - The `br`.
    /// * `out` - Where a jump table's target goes.
    fn jump(&mut self, i: &Insn, out: &mut BlockOut) {
        let Opnd::Reg { reg, .. } = i.operands[0] else {
            return self.unmodeled(i);
        };
        let target = self.read(reg);
        if self.ex.ctx.analysis.jump_tables.contains_key(&i.va) {
            out.switch_target = Some(target);
            return;
        }
        if self.ex.emit {
            let line = format!("goto *{};", target.render(&self.ex.names()));
            self.ex.lines.push(line);
        }
        self.ex.record(EffectKind::Jump(target));
    }

    /// Lifts a return of `x0`.
    fn ret(&mut self) {
        let value = self.read(Reg::X(0));
        if self.ex.emit {
            let line = format!("return {};", value.render(&self.ex.names()));
            self.ex.lines.push(line);
        }
        self.ex.record(EffectKind::Return(Some(value)));
    }

    /// The condition a conditional branch is taken under, read where the
    /// block ends.
    ///
    /// # Arguments
    ///
    /// * `test` - What the branch tests.
    fn branch_cond(&self, test: Test) -> Cond {
        use ConditionCode as C;
        match test {
            Test::Flags(c) => flags::condition(&self.ex.flags, c),
            Test::Zero { reg, bits, zero } => Cond {
                cc: Cc(if zero { C::e } else { C::ne }),
                flags: Flags::Cmp(self.read(reg), Expr::Const(0), width8(bits)),
            },
            Test::Bit {
                reg,
                bits,
                bit,
                set,
            } => Cond {
                cc: Cc(if set { C::ne } else { C::e }),
                flags: Flags::Test(self.read(reg), Expr::Const(1 << bit), width8(bits)),
            },
        }
    }

    /// Ends the block as [`super::lift::exec_block`] does: drops dead
    /// flags, places the phis, captures the branch, hands the flags on to a
    /// successor that reads them and records what the block's statements
    /// do.
    ///
    /// # Arguments
    ///
    /// * `out` - What the instructions found so far.
    /// * `jcc` - The block's conditional branch: its test, target and
    ///   fall-through.
    /// * `flags_out` - Some successor reads the flags the block leaves.
    /// * `phi` - Values to write out at the end, and the liveness oracle.
    /// * `start` - The block's first address.
    fn finish(
        mut self,
        mut out: BlockOut,
        jcc: Option<(Test, u64, u64)>,
        flags_out: bool,
        phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
        start: u64,
    ) -> BlockOut {
        if jcc.is_none() && !flags_out {
            self.ex.flags = Flags::Unknown;
        }
        self.ex.flags_needed = u32::MAX;
        if let Some((phi, live)) = phi {
            for k in phi(self.ex.env) {
                self.ex.materialize_phi(k, live);
            }
        }
        if let Some((test, target, fall)) = jcc {
            let cond = self.branch_cond(test);
            out.branch_const = cond.eval().map(|taken| (taken, target, fall));
            self.ex.record(EffectKind::Branch(cond.clone()));
            out.branch = Some(Branch { cond, target, fall });
        }
        let ex = self.ex;
        let crosses = matches!(ex.flags, Flags::Truth(..))
            || !ex.flags.any_var(&|k| matches!(k, Key::Tmp(_)));
        out.tmp_flags = flags_out && !crosses;
        ex.env.flags = if flags_out && crosses {
            ex.flags.clone()
        } else {
            Flags::Unknown
        };
        if ex.emit
            && let Entry::Vacant(first) = ex.ctx.effects.entry(start)
        {
            let mut packed = Vec::new();
            pack(&ex.effects, start, &mut packed);
            first.insert(packed);
        }
        out.lines = ex.lines;
        out.effects = ex.effects;
        out.slot_use = ex.slot_use;
        out.slot_def = ex.slot_def;
        out.call_uses = ex.call_uses;
        out.unmodeled = ex.unmodeled;
        out
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{decode, exec_block_a64};
    use crate::analysis::decompile::lift::{BlockFacts, Env, Pass};
    use crate::analysis::decompile::new_ctx;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// A prologue's saves of the frame record and of a callee-saved
    /// register hold no slot.
    ///
    /// In the entry block those stores, made before anything writes the
    /// registers, are saves, which no line stores, while a register the
    /// callee need not preserve stays a stored value; outside the entry
    /// block every store keeps its value.
    #[test]
    fn a_prologue_saves_the_frame_record_and_callee_saved_registers() {
        let words: [u32; 4] = [
            0xd503_233f, // ASM: paciasp
            0xa9be_7bfd, // ASM: stp x29, x30, [sp, #-0x20]!
            0xf900_0bf3, // ASM: str x19, [sp, #0x10]
            0xf900_0fe0, // ASM: str x0, [sp, #0x18]
        ];
        let mut bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        bytes.resize(0x100, 0);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let p = Program::raw(bytes, Arch::Arm64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let f = a.function(0x1000).expect("the entry is a function");
        let overlay = Overlay::default();
        let instrs: Vec<_> = (0..4).filter_map(|k| decode(&p, 0x1000 + 4 * k)).collect();
        for (entry, want) in [(true, vec![-8]), (false, vec![-32, -24, -16, -8])] {
            let starts = f.blocks.iter().map(|b| b.start).collect();
            let mut ctx = new_ctx(&p, &a, &overlay, f, 64, starts, &[]);
            let mut env = Env::entry();
            let facts = BlockFacts {
                entry,
                ..BlockFacts::default()
            };
            let out = exec_block_a64(&mut ctx, &instrs, &mut env, Pass::Emission, None, facts);
            let held: Vec<i64> = env.slot_bits.keys().copied().collect();
            assert_eq!(held, want, "entry {entry}: {:?}", out.lines);
            assert_eq!(env.sp, Some(-32));
            assert_eq!(out.unmodeled, 0);
        }
    }
}
