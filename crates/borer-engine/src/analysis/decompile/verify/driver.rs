//! The lift check's driver, written once for every instruction set.
//!
//! [`verify`](super) checks x86 code, and the modules beside it arm64,
//! ARM32 and RISC-V code, each against its own machine. What every
//! one of them does the same way is here: the state a block's two runs
//! start from, seeded on the machine and for the evaluator alike
//! ([`Seeded`]); the two runs themselves ([`run_block`]); and why a run
//! that stopped elsewhere than meant leaves its block unchecked
//! ([`stopped`]). An instruction set's check adds what is its own: how it
//! reads a block's straight line, the registers it names, the float or
//! vector registers it seeds, and how it compares them.

use std::collections::BTreeMap;

use super::super::Ctx;
use super::super::arch::Lifter;
use super::super::expr::Key;
use super::super::lift::{BlockFacts, Env, Pass};
use super::{Bench, GOLDEN, Jcc, Near, Probe, Ran, Rng, STACK_WORDS, State, Verified, low};
use crate::emulate::Stop;

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
