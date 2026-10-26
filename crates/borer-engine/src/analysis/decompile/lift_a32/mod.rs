//! The ARM32 lifter: executes one block of A32 or T32 instructions over
//! the decompiler's symbolic environment.
//!
//! The ARM32 counterpart of [`super::lift_a64`], through the same executor
//! ([`Exec`]): a register is a [`Key::A32`] variable, the stack pointer the
//! tracked offset [`Expr::Sp`] while it is one, every value computed at 32
//! bits, and a read of `pc` the constant it is. A single and the double it
//! is half of are separate variables kept in step: a write of one writes
//! the other's matching bits ([`Lift::write`]).
//!
//! The flags are the arm64 lifter's, read through what set them
//! ([`flags`]): `cmp` leaves a compare, `cmn` and `adds` an addition, a
//! logical or shifting instruction the value it computed when the next
//! reader asks only of N and Z, and else the whole `NZCV` word with the
//! shifter's carry. An instruction under a condition that does not move
//! control writes `cond ? new : old` into what it writes; a store under one
//! is an `if` around the store. One under a condition that moves control is
//! a block of its own after the test the block before it ends in
//! ([`crate::analysis::a32`], [`crate::isa::a32::SKIP`]). A call passes the
//! arguments the procedure call standard puts in registers and assigns its
//! result ([`call`]); what a function takes is read from its code
//! ([`mod@shape`]); which registers each instruction reads and writes is
//! [`live`]'s.

mod call;
mod flags;
mod float;
mod live;
mod mem;
mod shape;
mod step;

pub(in crate::analysis::decompile) use flags::{reads_inherited_flags, sets_flags};
pub(in crate::analysis::decompile) use live::effects;
pub(in crate::analysis::decompile) use shape::{
    arg_reg, built as built_shape, callee_shape, entry_env, param_types, ret_lane, shape,
    writes_result,
};

use std::collections::btree_map::Entry;

use super::Ctx;
use super::expr::{Expr, Flags, Key, Op, fold};
use super::lift::{BlockFacts, BlockOut, Branch, EffectKind, Env, Exec, LiveFn, Pass, PhiFn, pack};
use crate::analysis::a32::{decode as decode_at, guarded, skip};
use crate::analysis::{BlockTerm, Function};
use crate::fxmap::FxHashMap;
use crate::isa::a32::{self, Flow, Insn, ItState, Op as AOp, PC, Reg, SKIP, SP};
use crate::program::Program;
use flags::Test;

/// The bits of a word.
const WORD: u64 = 0xffff_ffff;

/// Decodes every block of a function, in block order.
///
/// The blocks are decoded in address order so an `IT` block's conditions
/// carry from one block into the next one it falls into. A block that ends
/// in the test in front of a guarded instruction ([`guarded`]) has that
/// test appended, a branch past the instruction at its address tagged
/// [`SKIP`].
///
/// # Arguments
///
/// * `program` - The image.
/// * `f` - The function.
pub(in crate::analysis::decompile) fn decode_blocks(
    program: &Program,
    f: &Function,
) -> Vec<Vec<Insn>> {
    let mut order: Vec<usize> = (0..f.blocks.len()).collect();
    order.sort_by_key(|&k| f.blocks.get(k).map_or(0, |b| b.start));
    let ends: std::collections::BTreeMap<u64, u64> =
        f.blocks.iter().map(|b| (b.start, b.end)).collect();
    let mut out = vec![Vec::new(); f.blocks.len()];
    let mut it = ItState::default();
    let mut end = None;
    let mut checked = None;
    for k in order {
        let Some(b) = f.blocks.get(k) else { continue };
        if end != Some(b.start) {
            it = ItState::default();
        }
        let held = checked.take() == Some(b.start);
        let mut v = Vec::new();
        let mut va = b.start;
        while va < b.end {
            let Some(mut i) = decode_at(program, va, &mut it) else {
                break;
            };
            if held && i.predicated() {
                i.cond = a32::Cond::Al;
            }
            va = i.next();
            v.push(i);
        }
        if b.term == BlockTerm::Cond
            && v.last().is_some_and(|l| l.flow() == Flow::Next)
            && let Some(first) = decode_at(program, b.end, &mut it.clone()).filter(Insn::predicated)
            && let Some(&run_end) = ends.get(&b.end)
        {
            v.push(skip(&first, run_end));
            checked = Some(b.end);
        }
        end = Some(b.end);
        if let Some(slot) = out.get_mut(k) {
            *slot = v;
        }
    }
    out
}

/// Executes one ARM32 block from `env`, returning its lines and
/// control-flow facts, as [`super::lift_a64::exec_block_a64`] does an
/// arm64 block.
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
pub(in crate::analysis::decompile) fn exec_block_a32(
    ctx: &mut Ctx<'_>,
    instrs: &[Insn],
    env: &mut Env,
    pass: Pass,
    phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
    facts: BlockFacts<'_>,
) -> BlockOut {
    let start = instrs.first().map_or(0, |i| i.va);
    let table_load = table_load(ctx, instrs);
    let mut lift = Lift {
        ex: Exec::new(ctx, env, pass, &facts, start),
        fp_flags: Flags::Unknown,
        table_load,
        table_idx: None,
        flags_out: facts.flags_out,
    };
    let live = flags::live_after(instrs, facts.flags_out);
    let mut out = BlockOut::default();
    let mut jcc = None;
    for (idx, i) in instrs.iter().enumerate() {
        lift.ex.at = i.va & !SKIP;
        if i.va & SKIP == 0
            && let Some(c) = lift.ex.ctx.overlay.comments.get(&i.va)
        {
            lift.ex.lines.push(format!("// {c}"));
        }
        lift.ex.flags_needed = live.get(idx).copied().unwrap_or(u32::MAX);
        match facts.need.and_then(|n| n.get(idx)) {
            Some(need) => lift.ex.regs_needed.get_or_insert_default().clone_from(need),
            None => lift.ex.regs_needed = None,
        }
        let later = instrs.get(idx + 1..).unwrap_or(&[]);
        if guarded(i) && idx != 0 {
            lift.unmodeled(i);
            continue;
        }
        match i.flow() {
            Flow::Next if i.predicated() => lift.predicated(i, later),
            Flow::Next => lift.step(i, later),
            Flow::CondJump => match (flags::test(i), i.target()) {
                (Some(test), Some(to)) => jcc = Some((test, to, i.next() & !SKIP)),
                _ => lift.unmodeled(i),
            },
            Flow::Jump => match i.target() {
                Some(t) if lift.ex.ctx.block_starts.contains(&t) => out.goto = Some(t),
                Some(t) => lift.tail_call(t),
                None => lift.jump(i, &mut out),
            },
            Flow::Call => lift.call(i),
            Flow::Return => lift.ret(i),
            Flow::Invalid => lift.unmodeled(i),
        }
    }
    lift.finish(out, jcc, facts.flags_out, phi, start)
}

/// The load of a jump table's entry in a block that dispatches through a
/// table the analysis resolved with `add pc, rB, rE`: the last indexed
/// load before it.
///
/// # Arguments
///
/// * `ctx` - Per-function state: the analysis's jump tables.
/// * `instrs` - The block's instructions.
fn table_load(ctx: &Ctx<'_>, instrs: &[Insn]) -> Option<u64> {
    let j = instrs.last()?;
    if !matches!(j.op, AOp::Dp { .. }) || !ctx.analysis.jump_tables.contains_key(&j.va) {
        return None;
    }
    instrs
        .iter()
        .rev()
        .find(|i| {
            matches!(
                i.op,
                AOp::Load {
                    addr: a32::Addr {
                        offset: a32::Offset::Reg { .. },
                        ..
                    },
                    ..
                }
            )
        })
        .map(|i| i.va)
}

/// Tells whether an instruction reads the flags.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(in crate::analysis::decompile) fn flags_read(i: &Insn) -> bool {
    flags::reads(i).is_some()
}

/// Returns the registers needed while each instruction of a block is
/// lifted: those some later instruction reads, and those it reads itself.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `instrs` - The block's instructions.
/// * `out` - The registers read after the block, with their lanes.
///
/// # Returns
///
/// One map per instruction, of each needed register's lane.
pub(in crate::analysis::decompile) fn need_after(
    ctx: &Ctx<'_>,
    instrs: &[Insn],
    out: &FxHashMap<Key, u8>,
) -> Vec<FxHashMap<Key, u8>> {
    let effects: Vec<super::lift::Effects> = instrs.iter().map(|i| effects(ctx, i)).collect();
    let mut need = super::lift::need_from(&effects, out);
    for (n, (reads, _)) in need.iter_mut().zip(&effects) {
        for &(k, lane) in reads {
            let held = n.entry(k).or_insert(lane);
            *held = (*held).max(lane);
        }
    }
    need
}

/// Counts the instructions of a block that render as statements.
///
/// The structurer weighs copying a block by the count: not the return,
/// the stack adjustments, nor the reloads of the registers the function
/// preserves.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
pub(in crate::analysis::decompile) fn body_len(instrs: &[Insn]) -> usize {
    let quiet = |i: &Insn| {
        let regs = i.registers();
        let restores = matches!(i.op, AOp::Ldm { .. } | AOp::VLdm { .. } | AOp::Load { .. })
            && regs
                .writes
                .iter()
                .all(|r| *r == SP || super::abi::a32::callee_saved(*r));
        let moves_sp = matches!(i.op, AOp::Dp { rd: SP, .. });
        restores
            || moves_sp
            || i.flow() == Flow::Return
            || matches!(i.op, AOp::Nop | AOp::It { .. })
    };
    instrs.iter().filter(|i| !quiet(i)).count()
}

/// Tells whether two ARM32 blocks make the same test.
///
/// They hold the same instructions up to a conditional branch at the end
/// of each, the branches sending each outcome to the same address (the
/// same condition and targets, or the opposite condition with the taken
/// and fall-through sides swapped).
///
/// # Arguments
///
/// * `a` - One block's instructions.
/// * `b` - The other's.
pub(in crate::analysis::decompile) fn same_test(a: &[Insn], b: &[Insn]) -> bool {
    let (Some((ja, ha)), Some((jb, hb))) = (a.split_last(), b.split_last()) else {
        return false;
    };
    if ha.len() != hb.len()
        || ja.va & SKIP != 0
        || jb.va & SKIP != 0
        || ja.flow() != Flow::CondJump
        || jb.flow() != Flow::CondJump
    {
        return false;
    }
    let same_body = ha.iter().zip(hb).all(|(x, y)| {
        x.va & SKIP == 0
            && y.va & SKIP == 0
            && x.cond == y.cond
            && x.sets == y.sets
            && x.op == y.op
            && (!x.registers().reads.contains(&PC)
                || x.pc() == y.pc()
                || x.literal().zip(y.literal()).is_some_and(|(a, b)| a == b))
    });
    if !same_body {
        return false;
    }
    let (Some(ta), Some(tb)) = (ja.target(), jb.target()) else {
        return false;
    };
    let (fa, fb) = (ja.next() & !SKIP, jb.next() & !SKIP);
    let (same_dir, opp_dir) = match (ja.op, jb.op) {
        (AOp::B { .. }, AOp::B { .. }) => (
            ja.cond == jb.cond,
            ja.cond != a32::Cond::Al && a32::invert(ja.cond) == jb.cond,
        ),
        (
            AOp::Cbz {
                rn: r1,
                nonzero: n1,
                ..
            },
            AOp::Cbz {
                rn: r2,
                nonzero: n2,
                ..
            },
        ) => (
            ja.cond == jb.cond && r1 == r2 && n1 == n2,
            ja.cond == a32::Cond::Al && jb.cond == a32::Cond::Al && r1 == r2 && n1 != n2,
        ),
        _ => (false, false),
    };
    (same_dir && ta == tb && fa == fb) || (opp_dir && ta == fb && fa == tb)
}

/// One block's lifting over the shared executor.
struct Lift<'c, 'a> {
    /// The executor: the environment, the function's state and the lines.
    ex: Exec<'c, 'a>,
    /// What the last `vcmp` left in `FPSCR`'s flags, which a `vmrs` moves
    /// into the APSR's.
    fp_flags: Flags,
    /// The load of the entry of the jump table the block dispatches
    /// through ([`table_load`]).
    table_load: Option<u64>,
    /// The index that load read the entry at.
    table_idx: Option<Expr>,
    /// Whether a successor reads the flags the block leaves.
    flags_out: bool,
}

impl Lift<'_, '_> {
    /// Reads a register as an instruction reads it: `pc` as its value
    /// there, the stack pointer as its tracked offset.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction reading it.
    /// * `r` - The register.
    fn get(&self, i: &Insn, r: Reg) -> Expr {
        match r {
            PC => Expr::Const(i.pc() & WORD),
            SP => self
                .ex
                .env
                .sp
                .map_or_else(|| self.ex.env.get(Key::A32(SP)), Expr::Sp),
            Reg::R(_) | Reg::S(_) | Reg::D(_) => self.ex.assumed(self.ex.env.get(Key::A32(r))),
        }
    }

    /// Writes a register, lazily.
    ///
    /// The stack pointer is tracked as an offset while the value is one.
    /// A single's double is written too, its other half kept; a double
    /// below `d16` writes its two singles.
    ///
    /// # Arguments
    ///
    /// * `r` - The register; never `pc`.
    /// * `v` - The value.
    fn write(&mut self, r: Reg, v: Expr) {
        match (r, v) {
            (SP, Expr::Sp(k)) => {
                self.ex.env.sp = Some(k);
                self.ex.env.vals.remove(&Key::A32(SP));
            }
            (SP, v) => {
                self.ex.env.sp = None;
                self.ex.assign(Key::A32(SP), v);
            }
            (Reg::S(n), v) => {
                let other = Reg::S(n ^ 1);
                let held = self.ex.env.get(Key::A32(other));
                let (lo, hi) = if n % 2 == 0 {
                    (v.clone(), held)
                } else {
                    (held, v.clone())
                };
                self.ex.assign(Key::A32(r), v);
                self.alias(Reg::D(n / 2), Expr::Call("__pair".to_owned(), vec![lo, hi]));
            }
            (Reg::D(n), v) if n < 16 => {
                let lo = super::lift_a64::mem::as_integer_bits(v.clone(), 32);
                let hi = Expr::Call("__hi32".to_owned(), vec![v.clone()]);
                self.ex.assign(Key::A32(r), v);
                self.alias(Reg::S(2 * n), lo);
                self.alias(Reg::S(2 * n + 1), hi);
            }
            (Reg::R(_) | Reg::D(_), v) => self.ex.assign(Key::A32(r), v),
        }
    }

    /// Records the value a register takes as the other view of one an
    /// instruction wrote: a single's double, a double's singles. It is
    /// pending like any value, written out only where something reads it,
    /// and never written out early for its size.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `v` - Its value.
    fn alias(&mut self, r: Reg, v: Expr) {
        let k = Key::A32(r);
        self.ex.env.clobbered.remove(&k);
        self.ex.env.unset.remove(&k);
        self.ex.env.touched.insert(k);
        self.ex.env.vals.insert(k, v);
    }

    /// Writes several registers at once, every value read before any
    /// changes, the early write-out of one waiting until all are recorded.
    ///
    /// # Arguments
    ///
    /// * `writes` - Each register and its value.
    fn write_all(&mut self, writes: Vec<(Reg, Expr)>) {
        let outer = self.ex.deferred.replace(Vec::new());
        for (r, v) in writes {
            self.write(r, v);
        }
        let waiting = std::mem::replace(&mut self.ex.deferred, outer).unwrap_or_default();
        for k in waiting {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
    }

    /// Lifts an instruction without a model: keeps its assembly as a
    /// comment and forgets every register it may write, the flags when it
    /// may set them and, if it may write memory, what memory held.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    fn unmodeled(&mut self, i: &Insn) {
        let memory = matches!(
            i.op,
            AOp::Store { .. }
                | AOp::StoreEx { .. }
                | AOp::StoreDual { .. }
                | AOp::Stm { .. }
                | AOp::VStore { .. }
                | AOp::VStm { .. }
                | AOp::Neon { stores: true, .. }
                | AOp::Unknown
        );
        if memory {
            if let Some(p) = &mut self.ex.ctx.probe {
                p.asm();
            }
            self.ex.protect_memory();
        }
        for r in i.registers().writes {
            let mut keys = vec![Key::A32(r)];
            match r {
                Reg::S(n) => keys.push(Key::A32(Reg::D(n / 2))),
                Reg::D(n) if n < 16 => {
                    keys.extend([Key::A32(Reg::S(2 * n)), Key::A32(Reg::S(2 * n + 1))]);
                }
                Reg::R(_) | Reg::D(_) => {}
            }
            if r == SP {
                self.ex.env.sp = None;
            }
            for k in keys {
                self.ex.clobber(k);
            }
        }
        self.ex.unmodeled += 1;
        if sets_flags(i) || matches!(i.op, AOp::Unknown | AOp::Invalid) {
            self.ex.flags = Flags::Unknown;
        }
        if self.ex.emit {
            self.ex.lines.push(format!("/* asm: {} */", a32::text(i)));
            self.ex.record(EffectKind::Unmodeled);
        }
    }

    /// Lifts an indirect jump: the dispatch of a jump table the analysis
    /// resolved, a tail call through a register, else a computed `goto`.
    ///
    /// # Arguments
    ///
    /// * `i` - The jump.
    /// * `out` - Where a jump table's index goes.
    fn jump(&mut self, i: &Insn, out: &mut BlockOut) {
        if self.ex.ctx.analysis.jump_tables.contains_key(&i.va) {
            let index = if let AOp::Tb { rm, .. } = i.op {
                Some(self.get(i, rm))
            } else if let AOp::Load {
                addr:
                    a32::Addr {
                        offset: a32::Offset::Reg { rm, .. },
                        ..
                    },
                ..
            } = i.op
            {
                Some(self.get(i, rm))
            } else {
                self.table_idx.take()
            };
            if let Some(idx) = index {
                self.ex.switch_idx = Some(idx);
                out.switch_target = None;
                return;
            }
        }
        let target = if let AOp::Bx { rm } = i.op {
            Some(self.get(i, rm))
        } else if let AOp::Dp {
            kind: a32::DpKind::Mov,
            src:
                a32::Operand::Reg {
                    rm,
                    shift: a32::Shift::Lsl,
                    amount: 0,
                },
            ..
        } = i.op
        {
            Some(self.get(i, rm))
        } else {
            None
        };
        let Some(target) = target else {
            return self.unmodeled(i);
        };
        if self.ex.emit {
            let line = format!("goto *{};", target.render(&self.ex.names()));
            self.ex.lines.push(line);
        }
        self.ex.record(EffectKind::Jump(target));
    }

    /// The condition a conditional branch is taken under, read where the
    /// block ends.
    ///
    /// # Arguments
    ///
    /// * `test` - What the branch tests.
    /// * `tested` - The value of the register a `cbz` tests, read before
    ///   the phis.
    fn branch_cond(&self, test: Test, tested: Option<Expr>) -> super::expr::Cond {
        match test {
            Test::Flags(c) => super::lift_a64::flags::condition(&self.ex.flags, c),
            Test::Zero { reg, zero } => flags::zero_test(
                tested.unwrap_or_else(|| self.ex.env.get(Key::A32(reg))),
                zero,
            ),
        }
    }

    /// Ends the block: drops dead flags, places the phis, captures the
    /// branch, hands the flags on to a successor that reads them and
    /// records what the block's statements do.
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
        let tested = match jcc {
            Some((Test::Zero { reg, .. }, ..)) => Some(self.ex.env.get(Key::A32(reg))),
            Some((Test::Flags(_), ..)) | None => None,
        };
        let holds = tested.is_some();
        if holds {
            self.ex.switch_idx = tested;
        }
        if let Some((phi, live)) = phi {
            for k in phi(self.ex.env) {
                self.ex.materialize_phi(k, live);
            }
        }
        let tested = if holds {
            self.ex.switch_idx.take()
        } else {
            None
        };
        if let Some((test, target, fall)) = jcc {
            let cond = self.branch_cond(test, tested);
            out.branch_const = cond.eval().map(|taken| (taken, target, fall));
            self.ex.record(EffectKind::Branch(cond.clone()));
            out.branch = Some(Branch { cond, target, fall });
        }
        let mut ex = self.ex;
        out.switch_idx = ex.switch_idx.take();
        if let Some(idx) = out.switch_idx.as_ref().filter(|_| ex.emit) {
            ex.record(EffectKind::Switch(idx.clone()));
        }
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

/// An address plus a signed offset, at 32 bits.
///
/// # Arguments
///
/// * `base` - The address.
/// * `off` - The offset.
fn offset(base: Expr, off: i64) -> Expr {
    match off.cmp(&0) {
        std::cmp::Ordering::Equal => base,
        std::cmp::Ordering::Greater => fold(Op::Add, base, Expr::Const(off.unsigned_abs()), 32),
        std::cmp::Ordering::Less => fold(Op::Sub, base, Expr::Const(off.unsigned_abs()), 32),
    }
}
