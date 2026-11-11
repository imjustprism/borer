//! Verification of the RISC-V lifter against the RISC-V machine, block by
//! block, as [`super::verify_a32`] checks the ARM32 lifter.
//!
//! Each block runs twice from one seeded state: on
//! [`crate::emulate::rv::Machine`], which executes the real instructions,
//! and through the RISC-V lifter ([`super::lift_rv`]), whose symbolic
//! results are evaluated under that state by the shared evaluator
//! ([`super::verify::eval`]) at the register width. Five kinds of fact
//! must agree: every integer register and the stack pointer; every float
//! register; every stack slot the lifter holds a value for; every store
//! and byte the block writes off the frame; and whether the block's
//! conditional branch is taken.
//!
//! A block is checked up to its first control transfer. Memory nothing
//! backs reads a hash of its address on both sides. The integer registers
//! are random, except that a register the block compares (a branch, `slt`
//! and its kin) mostly starts next to what it is compared with: the other
//! register, zero for `x0`, or the immediate. The float registers are
//! random too, those the block reads as a single first boxed in ones, and
//! compare at the width the lifter holds them at, any NaN agreeing with
//! any NaN. A block
//! holding an instruction either side does not model is
//! not checked. A pass says the lifting agreed on the seeds tried, not
//! that it is right.

use std::collections::{BTreeMap, BTreeSet};

use super::expr::Key;
use super::floats::agree;
use super::lift::{BlockFacts, Env, Pass};
use super::lift_rv::{decode_blocks, exec_block_rv};
use super::verify::{
    Bench, Fact, GOLDEN, Jcc, Near, Probe, Ran, Read, Rng, STACK_WORDS, State, Verified,
    float_bits, in_parts, low, report,
};
use super::{Ctx, new_ctx};
use crate::analysis::{Analysis, Function, Overlay};
use crate::emulate::rv::Machine;
use crate::emulate::{Run, Stop};
use crate::fxmap::FxHashSet;
use crate::isa::rv::{self, Alu, Flow, Fmt, Insn, Op, Reg, SP};
use crate::program::Program;

/// The kinds of fact a RISC-V block's check compares, in report order.
const FACTS: [Fact; 5] = [
    Fact::Register,
    Fact::Vector,
    Fact::Slot,
    Fact::Store,
    Fact::Branch,
];

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

/// Returns the float registers a block reads as a single before it
/// writes them, which the seeds then box in ones: a single not boxed reads
/// as the canonical NaN on the machine.
///
/// # Arguments
///
/// * `line` - The block's instructions.
fn singles(line: &[Insn]) -> BTreeSet<u8> {
    let mut first = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for i in line {
        let Op::Float(f) = i.op else {
            continue;
        };
        let fmt = f.reads_fmt();
        let regs = i.registers();
        for r in regs.reads {
            if let Reg::F(n) = r
                && seen.insert(n)
                && fmt == Some(Fmt::S)
            {
                first.insert(n);
            }
        }
        for r in regs.writes {
            if let Reg::F(n) = r {
                seen.insert(n);
            }
        }
    }
    first
}

/// Reads the registers a block compares, which the seeds then start near
/// what each is compared with.
///
/// A conditional branch compares two registers, and so do `slt` and
/// `sltu`; `slti` and `sltiu` compare one with an immediate. Two registers
/// start near each other, a register compared with `x0` near zero, and one
/// compared with an immediate near it: a random seed takes such a test one
/// way, so a lift wrong only where the operands meet would agree on every
/// seed.
///
/// # Arguments
///
/// * `instrs` - The block's instructions, its branch included.
fn comparands<'a>(instrs: impl Iterator<Item = &'a Insn>) -> BTreeMap<Key, Near> {
    let mut near = BTreeMap::new();
    for i in instrs {
        let (rs1, with) = if let Op::Branch { rs1, rs2, .. }
        | Op::Reg3 {
            op: Alu::Slt | Alu::Sltu,
            rs1,
            rs2,
            ..
        } = i.op
        {
            (rs1, Ok(rs2))
        } else if let Op::Imm {
            op: Alu::Slt | Alu::Sltu,
            rs1,
            imm,
            ..
        } = i.op
        {
            (rs1, Err(imm.cast_unsigned()))
        } else {
            continue;
        };
        match with {
            Err(k) => {
                near.insert(Key::Rv(rs1), Near::Constant(k));
            }
            Ok(rs2) if rs1 == rs2 => {}
            Ok(rv::ZERO) => {
                near.insert(Key::Rv(rs1), Near::Constant(0));
            }
            Ok(rs2) if rs1 == rv::ZERO => {
                near.insert(Key::Rv(rs2), Near::Constant(0));
            }
            Ok(rs2) => {
                let (lo, hi) = if rs1 < rs2 { (rs1, rs2) } else { (rs2, rs1) };
                near.insert(Key::Rv(hi), Near::Register(Key::Rv(lo)));
            }
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
        reg_ty: BTreeMap::new(),
        tls_block: 0,
        mir: None,
    };
    let near = comparands(line.iter().chain(&jcc));
    plant(&mut emu, &mut st, &mut rng, (&near, &singles(&line)));
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
/// The integer registers are random, a register the block compares mostly
/// next to what it is compared with; the float registers are random, those
/// the block reads as a single first boxed in ones; random words fill the
/// stack around the stack pointer.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `st` - The evaluator's state.
/// * `rng` - The seeded generator.
/// * `(near, singles)` - The registers to start near what they are
///   compared with ([`comparands`]) and the float registers read as
///   singles ([`singles`]).
fn plant(
    emu: &mut Machine<'_>,
    st: &mut State<'_, Machine<'_>>,
    rng: &mut Rng,
    (near, singles): (&BTreeMap<Key, Near>, &BTreeSet<u8>),
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
        let v = rng.next();
        let v = if singles.contains(&n) {
            0xffff_ffff_0000_0000 | (v & 0xffff_ffff)
        } else {
            v
        };
        emu.set_register(rv::name(Reg::F(n)), v);
        st.regs.insert(Key::Rv(Reg::F(n)), v);
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
    floats(&ran, out);
    let held = ran.slots(out);
    ran.stores(&held, out);
    if let Some((jcc, cond)) = ran.branch.take() {
        ran.step_branch(jcc, &cond, out);
    }
}

/// Compares every float register: a single in its low 32 bits, its
/// boxing aside, and any NaN agreeing with any NaN, since the machine
/// makes the canonical one where the evaluator keeps a payload.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn floats(ran: &Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    for n in 0..32 {
        let r = Reg::F(n);
        let key = Key::Rv(r);
        let Some(emulated) = ran.emu.register(rv::name(r)) else {
            continue;
        };
        let value = ran.env.vals.get(&key);
        let read = value.map_or_else(
            || Read::Value(ran.st.regs.get(&key).copied().unwrap_or(0)),
            |e| ran.read(e),
        );
        let Some(lifted) = out.count(Fact::Vector, read) else {
            continue;
        };
        let bits = value.and_then(|e| float_bits(e, &ran.st)).unwrap_or(64);
        if !agree(emulated, lifted, bits, true) {
            ran.disagree(
                out,
                Fact::Vector,
                rv::name(r).to_owned(),
                (emulated & low(bits), lifted & low(bits), bits),
                value.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}")),
            );
        }
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

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Machine, compare, function_ctx, run};
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key};
    use crate::analysis::decompile::lift_rv::decode_blocks;
    use crate::analysis::decompile::verify::Ran;
    use crate::analysis::decompile::verify_testing::{AT, image, tried};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::rv::Reg;
    use crate::isa::x86::ConditionCode;
    use crate::program::Arch;

    /// `ret`.
    const RET: u32 = 0x0000_8067;

    /// Checks the first block of an RV64 routine from seeds 1 to 8
    /// ([`tried`]).
    ///
    /// # Arguments
    ///
    /// * `words` - The routine.
    /// * `spoil` - Makes the lift wrong where a compare's operands meet.
    fn block(words: &[u32], spoil: impl Fn(&mut Ran<'_, Machine<'_>, ()>)) -> (usize, usize) {
        let p = image(Arch::RiscV64, words);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(AT).expect("function");
        let k = f.blocks.iter().position(|b| b.start == AT).expect("block");
        let instrs = decode_blocks(&p, f).swap_remove(k);
        let pristine = Machine::new(&p, 0).expect("machine");
        let mut ctx = function_ctx(&p, &a, &overlay, f);
        let run = |seed, out: &mut _| {
            run(&pristine, seed, &mut ctx, (AT, AT), &instrs, out).expect("run")
        };
        tried(run, compare, spoil)
    }

    /// A branch against `x0` is tried where its register meets zero.
    ///
    /// `bgez a0` goes both ways across the seeds, and a lift of it as
    /// `a0 > 0`, wrong at zero alone, is caught; so is `blez a0`, whose
    /// `x0` is the left operand, lifted as `0 > a0`.
    #[test]
    fn a_branch_against_zero_is_tried_at_zero() {
        let strict = |ran: &mut Ran<'_, Machine<'_>, ()>| {
            let (_, cond) = ran.branch.as_mut().expect("a branch");
            cond.cc = Cc(ConditionCode::g);
        };
        // ASM: bgez a0, 0x1008 ; ret ; ret
        let (taken, caught) = block(&[0x0005_5463, RET, RET], strict);
        assert!((1..8).contains(&taken), "taken from {taken} of 8 seeds");
        assert!(caught > 0, "a0 > 0 agreed with bgez a0 on every seed");
        // ASM: blez a0, 0x1008 ; ret ; ret
        let (taken, caught) = block(&[0x00a0_5463, RET, RET], strict);
        assert!((1..8).contains(&taken), "taken from {taken} of 8 seeds");
        assert!(caught > 0, "0 > a0 agreed with blez a0 on every seed");
    }

    /// A register `slti` or `slt` compares is tried where the operands
    /// meet.
    ///
    /// A lift of either as less than or equal, wrong where the register
    /// equals the immediate or the other register alone, is caught.
    #[test]
    fn a_set_less_than_is_tried_where_its_operands_meet() {
        let (t0, a0, a1) = (Reg::X(5), Reg::X(10), Reg::X(11));
        let or_equal = |with: Expr| {
            move |ran: &mut Ran<'_, Machine<'_>, ()>| {
                let flags = Flags::Cmp(Expr::Var(Key::Rv(a0)), with.clone(), 64);
                let cc = Cc(ConditionCode::le);
                let wrong = Expr::Cond(Box::new(Cond { cc, flags }));
                ran.env.vals.insert(Key::Rv(t0), wrong);
            }
        };
        // ASM: slti t0, a0, 5 ; ret
        let (_, caught) = block(&[0x0055_2293, RET], or_equal(Expr::Const(5)));
        assert!(caught > 0, "a0 <= 5 agreed with slti on every seed");
        // ASM: slt t0, a0, a1 ; ret
        let (_, caught) = block(&[0x00b5_22b3, RET], or_equal(Expr::Var(Key::Rv(a1))));
        assert!(caught > 0, "a0 <= a1 agreed with slt on every seed");
    }
}
