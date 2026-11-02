//! Verification of the RISC-V lifter against the RISC-V machine, block by
//! block, as [`super::verify_a32`] checks the ARM32 lifter.
//!
//! Each block runs twice from one seeded state: on
//! [`crate::emulate::rv::Machine`], which executes the real instructions,
//! and through the RISC-V lifter ([`super::lift_rv`]), whose symbolic
//! results are evaluated under that state by the shared evaluator
//! ([`super::verify::eval`]) at the register width. Four kinds of fact
//! must agree: every integer register and the stack pointer; every stack
//! slot the lifter holds a value for; every store and byte the block
//! writes off the frame; and whether the block's conditional branch is
//! taken.
//!
//! A block is checked up to its first control transfer. Memory nothing
//! backs reads a hash of its address on both sides. The integer registers
//! are random, except that a register a branch compares with another
//! mostly starts next to it; the float registers start clear on both
//! sides. A block holding an instruction either side does not model is
//! not checked. A pass says the lifting agreed on the seeds tried, not
//! that it is right.

use std::collections::BTreeMap;

use super::expr::Key;
use super::lift::{BlockFacts, Env, Pass};
use super::lift_rv::{decode_blocks, exec_block_rv};
use super::verify::{
    Bench, Fact, GOLDEN, Jcc, Near, Probe, Ran, Read, Rng, STACK_WORDS, State, Verified, in_parts,
    report,
};
use super::{Ctx, new_ctx};
use crate::analysis::{Analysis, Function, Overlay};
use crate::emulate::rv::Machine;
use crate::emulate::{Run, Stop};
use crate::fxmap::FxHashSet;
use crate::isa::rv::{self, Flow, Insn, Op, Reg, SP};
use crate::program::Program;

/// The kinds of fact a RISC-V block's check compares, in report order.
const FACTS: [Fact; 4] = [Fact::Register, Fact::Slot, Fact::Store, Fact::Branch];

/// The integer registers compared and seeded: every one but `x0` and the
/// stack pointer, by number.
fn general() -> impl Iterator<Item = Reg> {
    (1u8..32).filter(|&n| n != 2).map(Reg::X)
}

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

/// Checks the blocks of some functions of a RISC-V program against the
/// RISC-V machine.
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
/// not RISC-V code.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::Analysis;
/// use borer_engine::analysis::decompile::verify_rv::verify;
/// use borer_engine::program::{Arch, Program, Section};
///
/// // ASM: addi a0, a0, 1 ; ret
/// let code = [0x05, 0x05, 0x82, 0x80];
/// let section = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
/// let mut bytes = code.to_vec();
/// bytes.resize(0x1000, 0);
/// let p = Program::raw(bytes, Arch::RiscV64, 0, Some(0x1000), vec![section]);
/// let a = Analysis::compute(&p);
/// let v = verify(&p, &a, &[0x1000], 1);
/// assert_eq!(v.checked, 1);
/// assert!(v.mismatches.is_empty());
/// ```
#[must_use]
pub fn verify(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    in_parts(entries, |part| verify_some(program, analysis, part, seed))
}

/// Renders a RISC-V verification as a report, as [`super::verify_a32`]
/// renders an ARM32 one.
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
    let Some(pristine) = Machine::new(program, 0) else {
        return out;
    };
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
                (entry, block.start),
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
    let bits = super::lift_rv::xlen(program).bits();
    let mut ctx = new_ctx(program, analysis, overlay, f, bits, starts, &[]);
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
            let jcc = (i.flow() == Flow::CondJump
                && i.target().is_some_and(|t| t != i.next() && t != i.va))
            .then_some(*i);
            return (line, jcc, Some(i.va));
        }
        line.push(*i);
    }
    let end = line.last().map(Insn::next);
    (line, None, end)
}

/// Reads the registers a branch compares with another, which the seeds
/// then start near.
///
/// # Arguments
///
/// * `jcc` - The block's conditional branch.
fn comparands(jcc: Option<&Insn>) -> BTreeMap<Key, Near> {
    let mut near = BTreeMap::new();
    if let Some(Op::Branch { rs1, rs2, .. }) = jcc.map(|j| j.op)
        && rs1 != rs2
        && rs1 != rv::ZERO
        && rs2 != rv::ZERO
    {
        let (lo, hi) = if rs1 < rs2 { (rs1, rs2) } else { (rs2, rs1) };
        near.insert(Key::Rv(hi), Near::Register(Key::Rv(lo)));
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
/// * `at` - The function's entry and the block's start.
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
    at: (u64, u64),
    instrs: &[Insn],
    out: &mut Verified,
) -> Result<Ran<'p, Machine<'p>, ()>, &'static str> {
    let (entry, start) = at;
    let (line, jcc, end) = straight_line(instrs);
    let Some(end) = end.filter(|_| !line.is_empty() || jcc.is_some()) else {
        return Err("no straight-line code");
    };
    let xlen = super::lift_rv::xlen(ctx.program);
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
        width: if xlen == rv::Xlen::X32 { 32 } else { 64 },
        temps: BTreeMap::new(),
        tls_block: 0,
        mir: None,
    };
    plant(&mut emu, &mut st, &mut rng, &comparands(jcc.as_ref()));
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
    let mut all = line;
    all.extend(jcc);
    let lifted = exec_block_rv(
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

/// Seeds the machine and the evaluator's state alike.
///
/// The integer registers are random, a register a branch compares mostly
/// next to the other; the float registers are clear; random words fill
/// the stack around the stack pointer.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `st` - The evaluator's state.
/// * `rng` - The seeded generator.
/// * `near` - The registers to start near another ([`comparands`]).
fn plant(
    emu: &mut Machine<'_>,
    st: &mut State<'_, Machine<'_>>,
    rng: &mut Rng,
    near: &BTreeMap<Key, Near>,
) {
    let wide = st.width == 64;
    let word = if wide { u64::MAX } else { 0xffff_ffff };
    for r in general() {
        let key = Key::Rv(r);
        let v = rng.next() & word;
        let v = match near.get(&key) {
            Some(c) if v & 3 != 0 => c.seed(&st.regs, v) & word,
            _ => v,
        };
        emu.set_register(rv::name(r), v);
        st.regs.insert(key, v);
    }
    for n in 0..32 {
        st.regs.insert(Key::Rv(Reg::F(n)), 0);
    }
    let step: i64 = if wide { 8 } else { 4 };
    for w in -STACK_WORDS..STACK_WORDS {
        let slot = st.rsp.wrapping_add_signed(w * step);
        let bytes = rng.next().to_le_bytes();
        for (i, b) in (0u64..).zip(bytes.into_iter().take(if wide { 8 } else { 4 })) {
            emu.poke(slot.wrapping_add(i), b);
            st.stack.insert(slot.wrapping_add(i), b);
        }
    }
}

/// Compares every fact: registers, slots, stores, then the branch.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn compare(mut ran: Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    registers(&ran, out);
    let held = ran.slots(out);
    ran.stores(&held, out);
    if let Some((jcc, cond)) = ran.branch.take() {
        ran.step_branch(jcc, &cond, out);
    }
}

/// Compares every integer register and the stack pointer.
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
    let bits = ran.st.width;
    let word = if bits == 32 { 0xffff_ffff } else { u64::MAX };
    let mut check = |name: &str, emulated: u64, read: Read, expr: Option<String>| {
        let Some(lifted) = out.count(Fact::Register, read) else {
            return;
        };
        if lifted & word != emulated {
            ran.disagree(
                out,
                Fact::Register,
                name.to_owned(),
                (emulated, lifted & word, bits),
                expr.unwrap_or_else(|| "(unchanged)".to_owned()),
            );
        }
    };
    for r in general() {
        let key = Key::Rv(r);
        let Some(emulated) = ran.emu.register(rv::name(r)) else {
            continue;
        };
        let value = ran.env.vals.get(&key);
        let read = value.map_or_else(
            || Read::Value(ran.st.regs.get(&key).copied().unwrap_or(0)),
            |e| ran.read(e),
        );
        check(rv::name(r), emulated, read, value.map(|e| format!("{e:?}")));
    }
    let Some(emulated) = ran.emu.register("sp") else {
        return;
    };
    let (read, expr) = match (ran.env.sp, ran.env.vals.get(&Key::Rv(SP))) {
        (Some(k), _) => (
            Read::Value(ran.st.rsp.wrapping_add_signed(k) & word),
            Some(format!("sp {k:+}")),
        ),
        (None, Some(e)) => (ran.read(e), Some(format!("{e:?}"))),
        (None, None) => (Read::Unreadable, None),
    };
    check("sp", emulated, read, expr);
}
