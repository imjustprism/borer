//! Verification of the ARM32 lifter against the ARM32 machine, block by
//! block, as [`super::verify_a64`] checks the arm64 lifter.
//!
//! Each block runs twice from one seeded state: on
//! [`crate::emulate::a32::Machine`], which executes the real instructions,
//! and through the ARM32 lifter ([`super::lift_a32`]), whose symbolic
//! results are evaluated under that state by the shared evaluator
//! ([`super::verify::eval`]) at 32 bits. Five kinds of fact must agree:
//! every core register and the stack pointer; every single and double the
//! lifter holds a value for; every stack slot the lifter holds a value
//! for; every store and byte the block writes off the frame; and whether
//! the block's conditional branch is taken, the test in front of a
//! conditional return or call among them ([`crate::isa::a32::SKIP`]).
//!
//! A block is checked up to its first control transfer. Memory nothing
//! backs reads a hash of its address on both sides. The core registers are
//! random, except that a register the block compares with a constant, or
//! with another register, mostly starts next to it; the VFP registers and
//! the flags start clear on both sides. A block holding an instruction
//! either side does not model is not checked. A pass says the lifting
//! agreed on the seeds tried, not that it is right.

use std::collections::BTreeMap;

use super::expr::Key;
use super::lift::{BlockFacts, Env, Pass};
use super::lift_a32::{decode_blocks, exec_block_a32};
use super::verify::{
    Bench, Fact, GOLDEN, Jcc, Near, Probe, Ran, Read, Rng, STACK_WORDS, State, Verified, in_parts,
    report,
};
use super::{Ctx, new_ctx};
use crate::analysis::{Analysis, Function, Overlay};
use crate::emulate::a32::Machine;
use crate::emulate::{Run, Stop};
use crate::fxmap::FxHashSet;
use crate::isa::a32::{DpKind, Flow, Insn, Op, Operand, Reg, SKIP, SP};
use crate::program::Program;

/// The kinds of fact an ARM32 block's check compares, in report order.
const FACTS: [Fact; 5] = [
    Fact::Register,
    Fact::Vector,
    Fact::Slot,
    Fact::Store,
    Fact::Branch,
];

/// The core registers compared and seeded, `r0` to `r12` and the link
/// register, as the machine names them.
pub(super) const GENERAL: [(&str, u8); 14] = [
    ("r0", 0),
    ("r1", 1),
    ("r2", 2),
    ("r3", 3),
    ("r4", 4),
    ("r5", 5),
    ("r6", 6),
    ("r7", 7),
    ("r8", 8),
    ("r9", 9),
    ("r10", 10),
    ("r11", 11),
    ("r12", 12),
    ("lr", 14),
];

impl Bench for Machine<'_> {
    const SP: &'static str = "sp";

    fn byte_at(&self, at: u64) -> Option<u8> {
        Machine::byte_at(self, at)
    }

    fn register(&self, name: &str) -> Option<u64> {
        Machine::register(self, name)
    }

    fn set_budget(&mut self, budget: usize) {
        Machine::set_budget(self, budget);
    }

    fn stop_at(&mut self, at: Option<u64>) {
        Machine::stop_at(self, at);
    }

    fn run(&mut self, entry: u64) -> Run {
        Machine::run(self, entry)
    }
}

/// Checks the blocks of some functions of an ARM32 program against the
/// ARM32 machine.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed; the same seed checks the same
///   way every time.
///
/// # Returns
///
/// What was compared and every disagreement; nothing when the program is
/// not ARM32 code.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::Analysis;
/// use borer_engine::analysis::decompile::verify_a32::verify;
/// use borer_engine::program::{Arch, Program, Section};
///
/// // ASM: add r0, r0, #1 ; bx lr
/// let code = [0x01, 0x00, 0x80, 0xe2, 0x1e, 0xff, 0x2f, 0xe1];
/// let section = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
/// let mut bytes = code.to_vec();
/// bytes.resize(0x1000, 0);
/// let p = Program::raw(bytes, Arch::Arm, 0, Some(0x1000), vec![section]);
/// let a = Analysis::compute(&p);
/// let v = verify(&p, &a, &[0x1000], 1);
/// assert_eq!(v.checked, 1);
/// assert!(v.mismatches.is_empty());
/// ```
#[must_use]
pub fn verify(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    in_parts(entries, |part| verify_some(program, analysis, part, seed))
}

/// Renders an ARM32 verification as a report, as [`super::verify_a64`]
/// renders an arm64 one.
///
/// # Arguments
///
/// * `v` - What [`verify`] found.
#[must_use]
pub fn verify_tsv(v: &Verified) -> String {
    report(v, &FACTS)
}

/// [`verify`] over some functions on the calling thread.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed.
fn verify_some(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    let mut out = Verified::default();
    let Some(mut pristine) = Machine::new(program, 0) else {
        return out;
    };
    pristine.set_forced(true);
    let overlay = Overlay::default();
    for &entry in entries {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        out.functions += 1;
        let mut ctx = function_ctx(program, analysis, &overlay, f);
        let code = decode_blocks(program, f);
        for (block, instrs) in f.blocks.iter().zip(&code) {
            out.blocks += 1;
            match run(
                &pristine,
                seed,
                &mut ctx,
                entry,
                block.start,
                instrs,
                &mut out,
            ) {
                Ok(ran) => {
                    out.checked += 1;
                    compare(ran, &mut out);
                }
                Err(reason) => *out.skipped.entry(reason).or_default() += 1,
            }
        }
    }
    out
}

/// Builds the decompilation state a function's blocks are lifted in.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions and their blocks.
/// * `overlay` - The names in force (none).
/// * `f` - The function.
fn function_ctx<'a>(
    program: &'a Program,
    analysis: &'a Analysis,
    overlay: &'a Overlay,
    f: &Function,
) -> Ctx<'a> {
    let starts = f.blocks.iter().map(|b| b.start).collect();
    let mut ctx = new_ctx(program, analysis, overlay, f, 32, starts, &[]);
    ctx.symbolic_only = true;
    ctx.flag_readers = vec![false; f.blocks.len()];
    ctx.rebase_flags = vec![None; f.blocks.len()];
    ctx
}

/// Splits a block's instructions at its first control transfer.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
///
/// # Returns
///
/// The straight-line instructions, the conditional branch that ends them
/// when it goes somewhere else than on, and where the straight line stops.
fn straight_line(instrs: &[Insn]) -> (Vec<Insn>, Option<Insn>, Option<u64>) {
    let mut line = Vec::new();
    for i in instrs {
        if i.flow() != Flow::Next {
            let next = i.next() & !SKIP;
            let jcc = (i.flow() == Flow::CondJump
                && i.target().is_some_and(|t| t != next && t != i.va))
            .then_some(*i);
            return (line, jcc, Some(i.va));
        }
        line.push(*i);
    }
    let end = line.last().map(Insn::next);
    (line, None, end)
}

/// Reads the registers a block compares with a constant or with another
/// register, which the seeds then start near.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
fn comparands(instrs: &[Insn]) -> BTreeMap<Key, Near> {
    let mut near = BTreeMap::new();
    for i in instrs {
        let (rn, src) = if let Op::Dp {
            kind: kind @ (DpKind::Cmp | DpKind::Cmn),
            rn,
            src,
            ..
        } = i.op
        {
            (rn, (kind, src))
        } else if let Op::Cbz { rn, .. } = i.op {
            let zero = Operand::Imm {
                value: 0,
                carry: None,
            };
            (rn, (DpKind::Cmp, zero))
        } else {
            continue;
        };
        let Reg::R(a) = rn else { continue };
        match src.1 {
            Operand::Imm { value, .. } => {
                let k = u64::from(value);
                let k = if src.0 == DpKind::Cmn {
                    k.wrapping_neg() & 0xffff_ffff
                } else {
                    k
                };
                near.insert(Key::A32(rn), Near::Constant(k));
            }
            Operand::Reg {
                rm: rm @ Reg::R(b),
                amount: 0,
                ..
            } if b != a => {
                let (lo, hi) = if a < b { (rn, rm) } else { (rm, rn) };
                near.insert(Key::A32(hi), Near::Register(Key::A32(lo)));
            }
            Operand::Reg { .. } | Operand::RegShift { .. } => {}
        }
    }
    near
}

/// Runs one block on the machine and through the lifter from one seeded
/// state.
///
/// # Arguments
///
/// * `pristine` - The image's machine before any run.
/// * `seed` - The verification's seed.
/// * `ctx` - The function's decompilation state, symbolic only.
/// * `entry` - The function's entry.
/// * `start` - The block's start.
/// * `instrs` - The block's instructions.
/// * `out` - Where the instructions the machine lacks are tallied.
///
/// # Errors
///
/// Why the block cannot be checked.
fn run<'p>(
    pristine: &'p Machine<'p>,
    seed: u64,
    ctx: &mut Ctx<'_>,
    entry: u64,
    start: u64,
    instrs: &[Insn],
    out: &mut Verified,
) -> Result<Ran<'p, Machine<'p>, ()>, &'static str> {
    let (line, jcc, end) = straight_line(instrs);
    if line.is_empty() && jcc.is_none() {
        return Err("no straight-line code");
    }
    let Some(end) = end else {
        return Err("no straight-line code");
    };
    let mut rng = Rng(seed ^ start.rotate_left(17) ^ GOLDEN);
    rng.next();
    let fill = rng.next();
    let mut emu = pristine.clone();
    emu.set_budget(line.len() + 1);
    emu.set_fill(Some(fill));
    let mut st = State {
        pristine,
        fill,
        regs: BTreeMap::new(),
        rsp: emu.register("sp").unwrap_or(0),
        stack: BTreeMap::new(),
        width: 32,
        temps: BTreeMap::new(),
        tls_block: 0,
        mir: None,
    };
    let mut all = line;
    all.extend(jcc);
    let near = comparands(&all);
    for (name, n) in GENERAL {
        let key = Key::A32(Reg::R(n));
        let r = rng.next() & 0xffff_ffff;
        let v = match near.get(&key) {
            Some(c) if r & 3 != 0 => c.seed(&st.regs, r) & 0xffff_ffff,
            _ => r,
        };
        emu.set_register(name, v);
        st.regs.insert(key, v);
    }
    for n in 0..32 {
        st.regs.insert(Key::A32(Reg::S(n)), 0);
        st.regs.insert(Key::A32(Reg::D(n)), 0);
    }
    for word in -STACK_WORDS..STACK_WORDS {
        let at = st.rsp.wrapping_add_signed(word * 4);
        for (i, b) in (0u64..).zip(rng.next().to_le_bytes().into_iter().take(4)) {
            emu.poke(at.wrapping_add(i), b);
            st.stack.insert(at.wrapping_add(i), b);
        }
    }
    emu.stop_at(Some(end));
    let begin = instrs.first().map_or(start, |i| i.va);
    let run = emu.run(begin);
    match run.stop {
        Stop::Stopped(at) if at == end => {}
        Stop::Unmodeled(ref what) => {
            let kind = what.split(" at 0x").next().unwrap_or(what);
            *out.unmodeled.entry(kind.to_owned()).or_default() += 1;
            return Err("an instruction the emulator does not model");
        }
        Stop::Fault(_) => return Err("a fault on the emulator"),
        Stop::Budget => return Err("a repeat count past the regions compared"),
        Stop::Returned
        | Stop::MemoryFull(_)
        | Stop::Stopped(_)
        | Stop::Derailed(_)
        | Stop::Exited
        | Stop::Limit(_) => return Err("the emulator stopped early"),
    }
    let stored: FxHashSet<u64> = run.history.iter().map(|w| w.addr).collect();
    ctx.probe = Some(Probe::default());
    let mut env = Env::entry();
    let lifted = exec_block_a32(
        ctx,
        &all,
        &mut env,
        Pass::Dataflow,
        None,
        BlockFacts::default(),
    );
    let probe = ctx.probe.take().unwrap_or_default();
    if lifted.unmodeled > 0 {
        return Err(
            "an instruction the lifter leaves as asm, whose result the expressions after it name but do not compute",
        );
    }
    st.temps = probe.temps;
    Ok(Ran {
        function: entry,
        block: start,
        st,
        emu,
        stored,
        regs: (),
        env,
        effects: probe.effects,
        branch: jcc
            .and_then(|j| {
                Some(Jcc {
                    ip: j.va,
                    target: j.target()?,
                })
            })
            .zip(lifted.branch.map(|b| b.cond)),
    })
}

/// Compares every fact: registers, VFP registers, slots, stores, then the
/// branch.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn compare(mut ran: Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    registers(&ran, out);
    vfp(&ran, out);
    let held = ran.slots(out);
    ran.stores(&held, out);
    if let Some((jcc, cond)) = ran.branch.take() {
        ran.step_branch(jcc, &cond, out);
    }
}

/// Compares `r0` to `r12`, the link register and the stack pointer.
///
/// A register the lifter holds no value for still holds the value it
/// started with. The stack pointer compares as the tracked offset from the
/// starting one, or as the value the lifter holds when it lost the offset.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn registers(ran: &Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    let mut check = |name: &str, emulated: u64, read: Read, expr: Option<String>| {
        let Some(lifted) = out.count(Fact::Register, read) else {
            return;
        };
        if lifted & 0xffff_ffff != emulated {
            ran.disagree(
                out,
                Fact::Register,
                name.to_owned(),
                (emulated, lifted & 0xffff_ffff, 32),
                expr.unwrap_or_else(|| "(unchanged)".to_owned()),
            );
        }
    };
    for (name, n) in GENERAL {
        let key = Key::A32(Reg::R(n));
        let Some(emulated) = ran.emu.register(name) else {
            continue;
        };
        let value = ran.env.vals.get(&key);
        let read = value.map_or_else(
            || Read::Value(ran.st.regs.get(&key).copied().unwrap_or(0)),
            |e| ran.read(e),
        );
        check(name, emulated, read, value.map(|e| format!("{e:?}")));
    }
    let Some(emulated) = ran.emu.register("sp") else {
        return;
    };
    let (read, expr) = match (ran.env.sp, ran.env.vals.get(&Key::A32(SP))) {
        (Some(k), _) => (
            Read::Value(ran.st.rsp.wrapping_add_signed(k) & 0xffff_ffff),
            Some(format!("sp {k:+}")),
        ),
        (None, Some(e)) => (ran.read(e), Some(format!("{e:?}"))),
        (None, None) => (Read::Unreadable, None),
    };
    check("sp", emulated, read, expr);
}

/// Compares every single and double the lifter holds a value for.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn vfp(ran: &Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    for (k, e) in &ran.env.vals {
        let Key::A32(r @ (Reg::S(_) | Reg::D(_))) = *k else {
            continue;
        };
        let name = crate::isa::a32::name(r);
        let Some(emulated) = ran.emu.register(&name) else {
            continue;
        };
        let Some(lifted) = out.count(Fact::Vector, ran.read(e)) else {
            continue;
        };
        let lifted = if matches!(r, Reg::S(_)) {
            lifted & 0xffff_ffff
        } else {
            lifted
        };
        if lifted != emulated {
            ran.disagree(
                out,
                Fact::Vector,
                name,
                (
                    emulated,
                    lifted,
                    if matches!(r, Reg::S(_)) { 32 } else { 64 },
                ),
                format!("{e:?}"),
            );
        }
    }
}
