//! The lift check's driver, written once for every instruction set.
//!
//! [`verify`](super) checks x86 code, and the modules beside it arm64,
//! ARM32 and RISC-V code, each against its own machine. What every one of
//! them does the same way is here: the walk over the functions asked for,
//! each block counted as checked or by why it was not ([`functions`]);
//! the state a block's two runs start from, seeded on the machine and for
//! the evaluator alike ([`Seeded`]); the two runs themselves
//! ([`run_block`]); why a run that stopped elsewhere than meant leaves its
//! block unchecked ([`stopped`]); and the compare of the general
//! registers where each is one whole word ([`registers`]). An instruction
//! set's check adds what is its own: how it reads a block's straight
//! line, the registers it names, the float or vector registers it seeds,
//! and how it compares them.

use std::collections::BTreeMap;

use super::super::Ctx;
use super::super::arch::Lifter;
use super::super::expr::Key;
use super::super::lift::{BlockFacts, Env, Pass};
use super::{
    Bench, Fact, GOLDEN, Jcc, Near, Probe, Ran, Read, Rng, STACK_WORDS, State, Verified,
    function_ctx, low,
};
use crate::analysis::{Analysis, Function, Overlay};
use crate::emulate::Stop;
use crate::program::Program;

/// A block's two runs before they start: the machine and the state the
/// evaluator reads, seeded alike from one generator.
pub(in crate::analysis::decompile) struct Seeded<'p, M> {
    /// The machine: a clone of the image's, which reads the bytes nothing
    /// backs as the state does.
    pub(in crate::analysis::decompile) emu: M,
    /// The state the evaluator reads.
    pub(in crate::analysis::decompile) st: State<'p, M>,
    /// The generator every seed is drawn from, in one order for both.
    pub(in crate::analysis::decompile) rng: Rng,
    /// The width a seed is drawn at, in bits: the register width, unless
    /// the instruction set's check sets another. The x86 check draws 64
    /// bits in 32-bit code too, where a comparand's offset is then picked
    /// from the whole draw and the stack is seeded in 8-byte words.
    pub(in crate::analysis::decompile) drawn: u8,
    /// The function's entry.
    function: u64,
    /// The block's start.
    block: u64,
}

impl<'p, M: Bench> Seeded<'p, M> {
    /// Starts a block's two runs: a generator stirred with the block's
    /// address, the fill of the bytes nothing backs, a clone of the
    /// machine and a state with no register or stack byte seeded yet.
    ///
    /// # Arguments
    ///
    /// * `pristine` - The image's machine before any run.
    /// * `seed` - The verification's seed.
    /// * `(function, block)` - The function's entry and the block's start.
    /// * `width` - The register width, 32 or 64.
    /// * `budget` - The most instructions the block's run may take.
    pub(in crate::analysis::decompile) fn new(
        pristine: &'p M,
        seed: u64,
        (function, block): (u64, u64),
        width: u8,
        budget: usize,
    ) -> Self {
        let mut rng = Rng(seed ^ block.rotate_left(17) ^ GOLDEN);
        rng.next();
        let fill = rng.next();
        let mut emu = pristine.clone();
        emu.set_budget(budget);
        emu.set_fill(Some(fill));
        let st = State {
            pristine,
            fill,
            regs: BTreeMap::new(),
            rsp: emu.register(M::SP).unwrap_or(0),
            stack: BTreeMap::new(),
            width,
            temps: BTreeMap::new(),
            reg_ty: BTreeMap::new(),
            tls_block: 0,
            mir: None,
        };
        Self {
            emu,
            st,
            rng,
            drawn: width,
            function,
            block,
        }
    }

    /// Seeds the general registers, on the machine and in the state alike.
    ///
    /// Each is random, except that a register the block compares mostly
    /// starts next to what it is compared with ([`Near::seed`]).
    ///
    /// # Arguments
    ///
    /// * `regs` - The registers in seeding order, each as the machine
    ///   names it and as the lifter keys it.
    /// * `near` - What the block's comparisons suggest a register start
    ///   next to.
    pub(in crate::analysis::decompile) fn registers(
        &mut self,
        regs: impl IntoIterator<Item = (&'static str, Key)>,
        near: &BTreeMap<Key, Near>,
    ) {
        for (name, key) in regs {
            let r = self.rng.next() & low(self.drawn);
            let v = match near.get(&key) {
                Some(n) if r & 3 != 0 => n.seed(&self.st.regs, r),
                _ => r,
            } & low(self.st.width);
            self.emu.set_register(name, v);
            self.st.regs.insert(key, v);
        }
    }

    /// Seeds [`STACK_WORDS`] random words on each side of the stack
    /// pointer, on the machine and in the state alike.
    pub(in crate::analysis::decompile) fn stack(&mut self) {
        let bytes = self.drawn / 8;
        for word in -STACK_WORDS..STACK_WORDS {
            let at = self.st.rsp.wrapping_add_signed(word * i64::from(bytes));
            let drawn = self.rng.next().to_le_bytes();
            for (i, b) in (0u64..).zip(drawn.into_iter().take(usize::from(bytes))) {
                self.emu.poke(at.wrapping_add(i), b);
                self.st.stack.insert(at.wrapping_add(i), b);
            }
        }
    }
}

/// Runs a seeded block on the machine and through the lifter.
///
/// # Arguments
///
/// * `seeded` - The block's two runs, seeded.
/// * `ctx` - The function's decompilation state, symbolic only.
/// * `(begin, end)` - The address the machine starts at, and the one the
///   block's straight line stops at.
/// * `all` - The instructions lifted: the straight line, then the
///   conditional branch that ends it when there is one.
/// * `jcc` - That branch, as the check steps it on the machine.
/// * `regs` - The register facts of the block's instruction set.
/// * `out` - Where an instruction the machine lacks is tallied.
///
/// # Returns
///
/// Both runs, ready to compare.
///
/// # Errors
///
/// Why the block cannot be checked: the machine stopped elsewhere than
/// where the straight line ends ([`stopped`]), or the lifter left an
/// instruction as asm.
pub(in crate::analysis::decompile) fn run_block<'p, L: Lifter, M: Bench, R>(
    seeded: Seeded<'p, M>,
    ctx: &mut Ctx<'_>,
    (begin, end): (u64, u64),
    all: &[L::Insn],
    jcc: Option<Jcc>,
    regs: R,
    out: &mut Verified,
) -> Result<Ran<'p, M, R>, &'static str> {
    let Seeded {
        mut emu,
        mut st,
        function,
        block,
        ..
    } = seeded;
    emu.stop_at(Some(end));
    let run = emu.run(begin);
    stopped(&run.stop, end, out)?;
    ctx.probe = Some(Probe::default());
    let mut env = Env::entry();
    let lifted = L::exec_block(
        ctx,
        all,
        None,
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
        function,
        block,
        st,
        emu,
        stored: run.history.iter().map(|w| w.addr).collect(),
        regs,
        env,
        effects: probe.effects,
        branch: jcc.zip(lifted.branch.map(|b| b.cond)),
    })
}

/// Tells whether a run stopped at the address the check halted it at.
///
/// # Arguments
///
/// * `stop` - How the run ended.
/// * `at` - The address it was to stop at.
/// * `out` - Where an instruction the machine lacks is tallied.
///
/// # Errors
///
/// Why the block cannot be checked: an instruction the machine does not
/// model, a fault, a repeat past the step budget, or a stop the straight
/// line does not explain.
pub(in crate::analysis::decompile) fn stopped(
    stop: &Stop,
    at: u64,
    out: &mut Verified,
) -> Result<(), &'static str> {
    match stop {
        Stop::Stopped(to) if *to == at => Ok(()),
        Stop::Unmodeled(what) => {
            let kind = what.split(" at 0x").next().unwrap_or(what);
            *out.unmodeled.entry(kind.to_owned()).or_default() += 1;
            Err("an instruction the emulator does not model")
        }
        Stop::Fault(_) => Err("a fault on the emulator"),
        Stop::Budget => Err("a repeat count past the regions compared"),
        Stop::Returned
        | Stop::MemoryFull(_)
        | Stop::Stopped(_)
        | Stop::Derailed(_)
        | Stop::Exited
        | Stop::Limit(_) => Err("the emulator stopped early"),
    }
}

/// Compares every general register and the stack pointer, each whole.
///
/// A register the lifter holds no value for still holds the value it
/// started with: the lifter writes every register an instruction it models
/// changes, and a block holding one it does not model is not checked. A
/// register a 32-bit write left narrow holds its value uncut, the
/// machine's upper half being zero ([`Env::narrow`]), so it compares with
/// that half cleared. The stack pointer compares as the tracked offset
/// from the starting one, or as the value the lifter holds when it lost
/// the offset.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `regs` - The general registers, each as the machine names it and as
///   the lifter keys it.
/// * `sp` - The stack pointer, as the lifter keys it.
/// * `out` - Where the counts and disagreements go.
pub(in crate::analysis::decompile) fn registers<M: Bench, R>(
    ran: &Ran<'_, M, R>,
    regs: impl IntoIterator<Item = (&'static str, Key)>,
    sp: Key,
    out: &mut Verified,
) {
    let (bits, word) = (ran.st.width, low(ran.st.width));
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
    for (name, key) in regs {
        let Some(emulated) = ran.emu.register(name) else {
            continue;
        };
        let read = match ran.lifted(key) {
            Read::Value(v) if ran.env.narrow.get(&key) == Some(&32) => Read::Value(v & low(32)),
            other => other,
        };
        let value = ran.env.vals.get(&key);
        check(name, emulated, read, value.map(|e| format!("{e:?}")));
    }
    let Some(emulated) = ran.emu.register(M::SP) else {
        return;
    };
    let (read, expr) = match (ran.env.sp, ran.env.vals.get(&sp)) {
        (Some(k), _) => (
            Read::Value(ran.st.rsp.wrapping_add_signed(k) & word),
            Some(format!("{} {k:+}", M::SP)),
        ),
        (None, Some(e)) => (ran.read(e), Some(format!("{e:?}"))),
        (None, None) => (Read::Unreadable, None),
    };
    check(M::SP, emulated, read, expr);
}

/// Checks some functions on the calling thread, each in a decompilation
/// state of its own ([`function_ctx`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `blocks` - Checks every block of one function in its state, and
///   counts each ([`Verified::block`]).
///
/// # Returns
///
/// What was compared and every disagreement.
pub(in crate::analysis::decompile) fn functions(
    program: &Program,
    analysis: &Analysis,
    entries: &[u64],
    mut blocks: impl FnMut(&mut Ctx<'_>, &Function, &mut Verified),
) -> Verified {
    let mut out = Verified::default();
    let overlay = Overlay::default();
    for &entry in entries {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        out.functions += 1;
        let mut ctx = function_ctx(program, analysis, &overlay, f);
        blocks(&mut ctx, f, &mut out);
    }
    out
}

impl Verified {
    /// Counts one block: as checked, with its two runs compared, or under
    /// the reason it was not.
    ///
    /// # Arguments
    ///
    /// * `ran` - Both runs, or why the block cannot be checked.
    /// * `compare` - Compares every fact of the two runs.
    pub(in crate::analysis::decompile) fn block<T>(
        &mut self,
        ran: Result<T, &'static str>,
        compare: impl FnOnce(T, &mut Self),
    ) {
        self.blocks += 1;
        match ran {
            Ok(ran) => {
                self.checked += 1;
                compare(ran, self);
            }
            Err(reason) => *self.skipped.entry(reason).or_default() += 1,
        }
    }
}
