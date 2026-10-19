//! Verification of the arm64 lifter against the arm64 machine, block by
//! block, as [`super::verify`] checks the x86 lifter against the emulator.
//!
//! Each block runs twice from one seeded state: on
//! [`crate::emulate::a64::Machine`], which executes the real instructions,
//! and through the arm64 lifter ([`super::lift_a64`]), whose symbolic
//! results are evaluated under that state by the x86 check's own evaluator
//! ([`super::verify::eval`]), registers keyed as the lifter keys them. Five
//! kinds of fact must agree: every general register and the stack
//! pointer; the low 64 bits of every `v` register; every stack slot the
//! lifter holds a value for; every store and byte the block writes off
//! the frame; and whether the block's conditional branch is taken.
//!
//! Each block is checked up to its first control transfer, the branch
//! included, and a block that is only a conditional branch (a `cbz` after
//! a call) is checked for the branch. Memory nothing backs reads a hash of
//! its address on both
//! sides ([`crate::emulate::fill_byte`]). The general registers are
//! random, except that a register the block compares with a constant, or
//! with another register, mostly starts next to it; the `v` registers and
//! the flags start clear on both sides. A block holding an instruction the
//! lifter writes as a statement (an `mrs` or `msr` of a system register
//! other than `TPIDR_EL0` and `NZCV`, a supervisor call) is not checked,
//! nor one holding an instruction either side does not model. A pass says
//! the lifting agreed on the seeds tried, not that it is right.

use std::collections::BTreeMap;

use super::expr::Key;
use super::lift::{BlockFacts, Env, Pass};
use super::lift_a64::{decode, exec_block_a64};
use super::verify::{
    Bench, Fact, GOLDEN, Jcc, Near, Probe, Ran, Read, Rng, STACK_WORDS, State, Verified, in_parts,
    report,
};
use super::{Ctx, new_ctx};
use crate::analysis::{Analysis, BasicBlock, Function, Overlay};
use crate::emulate::a64::Machine;
use crate::emulate::{Run, Stop};
use crate::fxmap::FxHashSet;
use crate::isa::a64::{self, Flow, Insn, Mnemonic, Opnd, Reg};
use crate::program::Program;

/// The kinds of fact an arm64 block's check compares, in report order.
const FACTS: [Fact; 5] = [
    Fact::Register,
    Fact::Vector,
    Fact::Slot,
    Fact::Store,
    Fact::Branch,
];

/// The general registers compared and seeded, `x0` to `x30`, as the
/// machine names them.
const GENERAL: [&str; 31] = [
    "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14",
    "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27",
    "x28", "x29", "x30",
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

/// Checks the blocks of some functions of an arm64 program against the
/// arm64 machine.
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
/// not arm64 code.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::Analysis;
/// use borer_engine::analysis::decompile::verify_a64::verify;
/// use borer_engine::program::{Arch, Program, Section};
///
/// // ASM: add x0, x0, #1 ; ret
/// let code = [0x00, 0x04, 0x00, 0x91, 0xc0, 0x03, 0x5f, 0xd6];
/// let section = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
/// let mut bytes = code.to_vec();
/// bytes.resize(0x1000, 0);
/// let p = Program::raw(bytes, Arch::Arm64, 0, Some(0x1000), vec![section]);
/// let a = Analysis::compute(&p);
/// let v = verify(&p, &a, &[0x1000], 1);
/// assert_eq!(v.checked, 1);
/// assert!(v.mismatches.is_empty());
/// ```
#[must_use]
pub fn verify(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    in_parts(entries, |part| {
        verify_some(program, analysis, part, seed, false)
    })
}

/// Checks the arm64 lifter against the arm64 machine as [`verify`] does,
/// reading every lifted value through MIR ([`super::mir`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed.
///
/// # Returns
///
/// What was compared and every disagreement.
#[must_use]
pub fn verify_mir(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    in_parts(entries, |part| {
        verify_some(program, analysis, part, seed, true)
    })
}

/// Renders an arm64 verification as a report.
///
/// A `#` summary, a line per kind of fact an arm64 block's check compares,
/// the reasons blocks were not compared, the instructions the machine
/// lacks, then a row per disagreement, at most
/// [`super::verify::LISTED_MAX`].
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
/// * `mir` - Read the lifted values through MIR.
fn verify_some(
    program: &Program,
    analysis: &Analysis,
    entries: &[u64],
    seed: u64,
    mir: bool,
) -> Verified {
    let mut out = Verified::default();
    let Some(sweep) = Sweep::new(program, seed, mir) else {
        return out;
    };
    let overlay = Overlay::default();
    for &entry in entries {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        out.functions += 1;
        let mut ctx = function_ctx(program, analysis, &overlay, f);
        for block in &f.blocks {
            out.blocks += 1;
            if let Err(reason) = sweep.check(&mut ctx, entry, block, &mut out) {
                *out.skipped.entry(reason).or_default() += 1;
            }
        }
    }
    out
}

/// Decodes a block up to its first control transfer.
///
/// # Arguments
///
/// * `program` - The image.
/// * `block` - The block.
///
/// # Returns
///
/// The straight-line instructions; the conditional branch that ends them
/// when it goes somewhere else than on or back to itself; and the address
/// the straight line stops at.
fn straight_line(program: &Program, block: &BasicBlock) -> (Vec<Insn>, Option<Insn>, u64) {
    let mut instrs = Vec::new();
    let mut va = block.start;
    while va < block.end {
        let Some(i) = decode(program, va) else { break };
        let next = va.wrapping_add(crate::num::from_usize(a64::INSN_LEN));
        if i.flow != Flow::Next {
            let jcc = (i.flow == Flow::CondJump
                && i.target().is_some_and(|t| t != next && t != i.va))
            .then_some(i);
            return (instrs, jcc, va);
        }
        va = next;
        instrs.push(i);
    }
    (instrs, None, va)
}

/// Tells whether the lifter writes an instruction as a statement whose
/// results the environment does not hold.
///
/// An `mrs` or `msr` of a system register other than `TPIDR_EL0` and
/// `NZCV`, or a supervisor call, is such a statement.
///
/// # Arguments
///
/// * `i` - The instruction.
fn statement_only(i: &Insn) -> bool {
    (matches!(i.mnemonic, Mnemonic::Mrs | Mnemonic::Msr) && !super::lift_a64::modeled_system(i))
        || (i.op == a64::Op::Syscall && !svc_zero(i))
}

/// `svc #0`, the supervisor call the lifter models as a value in `x0`.
///
/// # Arguments
///
/// * `i` - The instruction.
fn svc_zero(i: &Insn) -> bool {
    i.mnemonic == Mnemonic::Svc && matches!(i.operands.first(), Some(Opnd::Imm(0)))
}

/// Reads the registers a block compares (`cmp`, `cmn`, `tst`, `ccmp`, and
/// a `cbz` or `cbnz` ending it) with a constant or with another register,
/// as [`super::verify`] reads an x86 block's.
///
/// # Arguments
///
/// * `instrs` - The block's instructions, its branch included.
fn comparands(instrs: &[Insn]) -> BTreeMap<Key, Near> {
    let rank = |r: Reg| match r {
        Reg::X(n) => Some(n),
        Reg::Sp | Reg::Zr | Reg::V(_) => None,
    };
    let mut near = BTreeMap::new();
    for i in instrs {
        let compares = matches!(i.mnemonic, Mnemonic::Subs | Mnemonic::Adds | Mnemonic::Ands)
            && matches!(i.operands[0], Opnd::Reg { reg: Reg::Zr, .. });
        let (first, second) = if matches!(i.op, a64::Op::Cbz | a64::Op::Cbnz) {
            (i.operands[0], Opnd::Imm(0))
        } else if compares {
            (i.operands[1], i.operands[2])
        } else if matches!(i.mnemonic, Mnemonic::Ccmp | Mnemonic::Ccmn) {
            (i.operands[0], i.operands[1])
        } else {
            continue;
        };
        let Opnd::Reg { reg: r0, .. } = first else {
            continue;
        };
        let Some(a) = rank(r0) else { continue };
        match second {
            Opnd::Reg { reg: r1, .. } if r1 == r0 => {
                near.insert(Key::A64(r0), Near::Constant(0));
            }
            Opnd::Reg { reg: r1, .. } => {
                if let Some(b) = rank(r1) {
                    let (lo, hi) = if a < b { (r0, r1) } else { (r1, r0) };
                    near.insert(Key::A64(hi), Near::Register(Key::A64(lo)));
                }
            }
            Opnd::Imm(k) => {
                let k = if i.mnemonic == Mnemonic::Adds || i.mnemonic == Mnemonic::Ccmn {
                    k.wrapping_neg()
                } else {
                    k
                };
                near.insert(Key::A64(r0), Near::Constant(k));
            }
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => {}
        }
    }
    near
}

/// Builds the decompilation state a function's blocks are lifted in:
/// nothing written out, and no flags carried between blocks.
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
    let mut ctx = new_ctx(program, analysis, overlay, f, 64, starts, &[]);
    ctx.symbolic_only = true;
    ctx.flag_readers = vec![false; f.blocks.len()];
    ctx.rebase_flags = vec![None; f.blocks.len()];
    ctx
}

/// What every block of one verification shares.
struct Sweep<'p> {
    /// The image's machine before any run, cloned for each block.
    pristine: Machine<'p>,
    /// The verification's seed.
    seed: u64,
    /// Read the lifted values through MIR rather than as expressions.
    mir: bool,
}

impl<'p> Sweep<'p> {
    /// Sets up a verification of one image.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    /// * `seed` - The verification's seed.
    /// * `mir` - Read the lifted values through MIR.
    ///
    /// # Returns
    ///
    /// The sweep, or `None` when the image is not arm64 code.
    fn new(program: &'p Program, seed: u64, mir: bool) -> Option<Self> {
        Some(Self {
            pristine: Machine::new(program, 0)?,
            seed,
            mir,
        })
    }

    /// Runs one block both ways and compares every fact.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's decompilation state, symbolic only.
    /// * `entry` - The function's entry.
    /// * `block` - The block.
    /// * `out` - Where the counts and disagreements go.
    ///
    /// # Errors
    ///
    /// Why the block was not checked.
    fn check(
        &self,
        ctx: &mut Ctx<'_>,
        entry: u64,
        block: &BasicBlock,
        out: &mut Verified,
    ) -> Result<(), &'static str> {
        let ran = self.run(ctx, entry, block, out)?;
        out.checked += 1;
        ran.compare(out);
        Ok(())
    }

    /// Runs one block on the machine and through the lifter from one
    /// seeded state.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's decompilation state, symbolic only.
    /// * `entry` - The function's entry.
    /// * `block` - The block.
    /// * `out` - Where the instructions the machine lacks are tallied.
    ///
    /// # Returns
    ///
    /// Both runs, ready to compare.
    ///
    /// # Errors
    ///
    /// Why the block cannot be checked.
    fn run(
        &self,
        ctx: &mut Ctx<'_>,
        entry: u64,
        block: &BasicBlock,
        out: &mut Verified,
    ) -> Result<Ran<'_, Machine<'p>, ()>, &'static str> {
        let (instrs, jcc, end) = straight_line(ctx.program, block);
        if instrs.is_empty() && jcc.is_none() {
            return Err("no straight-line code");
        }
        if instrs.iter().any(statement_only) {
            return Err("a system instruction the lifter writes as a statement");
        }
        let mut rng = Rng(self.seed ^ block.start.rotate_left(17) ^ GOLDEN);
        rng.next();
        let fill = rng.next();
        let mut emu = self.pristine.clone();
        emu.set_budget(instrs.len() + 1);
        emu.set_fill(Some(fill));
        let mut st = State {
            pristine: &self.pristine,
            fill,
            regs: BTreeMap::new(),
            rsp: emu.register("sp").unwrap_or(0),
            stack: BTreeMap::new(),
            width: 64,
            temps: BTreeMap::new(),
            tls_block: 0,
            mir: None,
        };
        let mut all = instrs;
        all.extend(jcc);
        if self.mir {
            st.mir = Some(all.iter().map(|i| i.va).collect());
        }
        let near = comparands(&all);
        for (n, name) in (0u8..).zip(GENERAL) {
            let key = Key::A64(Reg::X(n));
            let r = rng.next();
            let v = match near.get(&key) {
                Some(c) if r & 3 != 0 => c.seed(&st.regs, r),
                _ => r,
            };
            emu.set_register(name, v);
            st.regs.insert(key, v);
        }
        for n in 0..32 {
            st.regs.insert(Key::A64(Reg::V(n)), 0);
        }
        for word in -STACK_WORDS..STACK_WORDS {
            let at = st.rsp.wrapping_add_signed(word * 8);
            for (i, b) in (0u64..).zip(rng.next().to_le_bytes()) {
                emu.poke(at.wrapping_add(i), b);
                st.stack.insert(at.wrapping_add(i), b);
            }
        }
        emu.stop_at(Some(end));
        let run = emu.run(block.start);
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
            | Stop::Exited => return Err("the emulator stopped early"),
        }
        let stored: FxHashSet<u64> = run.history.iter().map(|w| w.addr).collect();
        ctx.probe = Some(Probe::default());
        let mut env = Env::entry();
        let lifted = exec_block_a64(
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
            block: block.start,
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
}

impl Ran<'_, Machine<'_>, ()> {
    /// Compares every fact: registers, `v` registers, slots, stores, then
    /// the branch.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn compare(mut self, out: &mut Verified) {
        self.registers(out);
        self.vectors(out);
        let held = self.slots(out);
        self.stores(&held, out);
        if let Some((jcc, cond)) = self.branch.take() {
            self.step_branch(jcc, &cond, out);
        }
    }

    /// Compares `x0` to `x30` and the stack pointer, all 64 bits of each.
    ///
    /// A register the lifter holds no value for still holds the value it
    /// started with: the lifter writes every register an instruction it
    /// models changes, and a block holding one it does not model is not
    /// checked. A register a `w` write left narrow holds its value uncut,
    /// the machine's upper half being zero ([`super::lift::Env::narrow`]),
    /// so it compares with that half cleared. The stack pointer compares
    /// as the tracked offset from the starting one, or as the value the
    /// lifter holds when it lost the offset.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn registers(&self, out: &mut Verified) {
        for (n, name) in (0u8..).zip(GENERAL) {
            let key = Key::A64(Reg::X(n));
            let Some(emulated) = self.emu.register(name) else {
                continue;
            };
            let value = self.env.vals.get(&key);
            let read = value.map_or_else(
                || Read::Value(self.st.regs.get(&key).copied().unwrap_or(0)),
                |e| self.read(e),
            );
            let read = match read {
                Read::Value(v) if self.env.narrow.get(&key) == Some(&32) => {
                    Read::Value(v & 0xffff_ffff)
                }
                other => other,
            };
            self.compare_register(out, name, emulated, read, value.map(|e| format!("{e:?}")));
        }
        let Some(emulated) = self.emu.register("sp") else {
            return;
        };
        let (read, expr) = match (self.env.sp, self.env.vals.get(&Key::A64(Reg::Sp))) {
            (Some(k), _) => (
                Read::Value(self.st.rsp.wrapping_add_signed(k)),
                Some(format!("sp {k:+}")),
            ),
            (None, Some(e)) => (self.read(e), Some(format!("{e:?}"))),
            (None, None) => (Read::Unreadable, None),
        };
        self.compare_register(out, "sp", emulated, read, expr);
    }

    /// Counts one register and records it when it disagrees.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the count and disagreement go.
    /// * `name` - The register as the machine names it.
    /// * `emulated` - What the machine left in it.
    /// * `read` - How the lifted value read.
    /// * `expr` - The lifted expression, `None` for a register the lifter
    ///   wrote nothing to.
    fn compare_register(
        &self,
        out: &mut Verified,
        name: &str,
        emulated: u64,
        read: Read,
        expr: Option<String>,
    ) {
        let Some(lifted) = out.count(Fact::Register, read) else {
            return;
        };
        if lifted != emulated {
            self.disagree(
                out,
                Fact::Register,
                name.to_owned(),
                (emulated, lifted, 64),
                expr.unwrap_or_else(|| "(unchanged)".to_owned()),
            );
        }
    }

    /// Compares the low 64 bits of every `v` register: the lane a scalar
    /// float or integer occupies, as [`super::verify`] compares an xmm
    /// register's.
    ///
    /// Both sides start the block with the registers clear, so a register
    /// the lifter wrote nothing to still holds zero. A value the evaluator
    /// cannot read (a 128-bit load) is counted, not compared.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn vectors(&self, out: &mut Verified) {
        let lanes = self.emu.vregs();
        for (n, lane) in (0u8..).zip(lanes) {
            let held = self.env.vals.get(&Key::A64(Reg::V(n)));
            let read = held.map_or(Read::Value(0), |e| self.read(e));
            let Some(lifted) = out.count(Fact::Vector, read) else {
                continue;
            };
            let emulated = u64::try_from(lane & u128::from(u64::MAX)).unwrap_or_default();
            if lifted != emulated {
                let expr = held.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}"));
                self.disagree(
                    out,
                    Fact::Vector,
                    format!("v{n}"),
                    (emulated, lifted, 64),
                    expr,
                );
            }
        }
    }
}
