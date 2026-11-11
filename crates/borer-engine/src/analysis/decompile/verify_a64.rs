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
//! with another register, mostly starts next to it; the low 64 bits of
//! each `v` register are random too, the rest clear, and the flags start
//! clear on both sides. A block holding an instruction the
//! lifter writes as a statement (an `mrs` or `msr` of a system register
//! other than `TPIDR_EL0` and `NZCV`, a supervisor call) is not checked,
//! nor one holding an instruction either side does not model. A pass says
//! the lifting agreed on the seeds tried, not that it is right.

use std::collections::BTreeMap;

use super::Ctx;
use super::arch::A64;
use super::expr::Key;
use super::lift_a64::decode;
use super::verify::{
    Fact, Jcc, Near, Ran, Rng, Seeded, Verified, bench, functions, registers, run_block,
};
use crate::analysis::{Analysis, BasicBlock};
use crate::emulate::a64::Machine;
use crate::isa::a64::{self, Flow, Insn, Mnemonic, Opnd, Reg};
use crate::program::Program;

/// The general registers compared and seeded, `x0` to `x30`, as the
/// machine names them.
const GENERAL: [&str; 31] = [
    "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14",
    "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27",
    "x28", "x29", "x30",
];

bench!(Machine<'_>, "sp");

/// The general registers compared and seeded, each as the machine names
/// it and as the lifter keys it.
fn general() -> impl Iterator<Item = (&'static str, Key)> {
    (0u8..)
        .zip(GENERAL)
        .map(|(n, name)| (name, Key::A64(Reg::X(n))))
}

/// Checks the blocks of some functions of an arm64 program against the
/// arm64 machine, on the calling thread.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed; the same seed checks the same
///   way every time.
/// * `mir` - Read the lifted values through MIR.
///
/// # Returns
///
/// What was compared and every disagreement; nothing when the program is
/// not arm64 code.
pub(super) fn sweep(
    program: &Program,
    analysis: &Analysis,
    entries: &[u64],
    seed: u64,
    mir: bool,
) -> Verified {
    let Some(sweep) = Sweep::new(program, seed, mir) else {
        return Verified::default();
    };
    functions(program, analysis, entries, |ctx, f, out| {
        for block in &f.blocks {
            let ran = sweep.run(ctx, f.entry, block, out);
            out.block(ran, |ran, out| ran.compare(out));
        }
    })
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

/// Seeds the `v` registers on the machine and in the evaluator's state
/// alike: the low 64 bits of each at random, the rest clear, which is all
/// of a register the evaluator holds.
///
/// They are drawn after every other seed, so the general registers and the
/// stack start as they did while these started clear.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `regs` - The evaluator's registers.
/// * `rng` - The seeded generator.
fn seed_vectors(emu: &mut Machine<'_>, regs: &mut BTreeMap<Key, u64>, rng: &mut Rng) {
    for n in 0..32 {
        let v = rng.next();
        emu.set_vreg(n, u128::from(v));
        regs.insert(Key::A64(Reg::V(n)), v);
    }
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
        let at = (entry, block.start);
        let mut seeded = Seeded::new(&self.pristine, self.seed, at, 64, instrs.len() + 1);
        let mut all = instrs;
        all.extend(jcc);
        if self.mir {
            seeded.st.mir = Some(all.iter().map(|i| i.va).collect());
        }
        seeded.registers(general(), &comparands(&all));
        seeded.stack();
        seed_vectors(&mut seeded.emu, &mut seeded.st.regs, &mut seeded.rng);
        let jcc = jcc.and_then(|j| j.target().map(|target| Jcc { ip: j.va, target }));
        let line = (block.start, end);
        let mut ran = run_block::<A64, _, _>(seeded, ctx, line, &all, jcc, (), out)?;
        ran.st.reg_ty.clone_from(&ctx.reg_ty);
        Ok(ran)
    }
}

impl Ran<'_, Machine<'_>, ()> {
    /// Compares every fact: registers, `v` registers, slots, stores, then
    /// the branch.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn compare(self, out: &mut Verified) {
        registers(&self, general(), Key::A64(Reg::Sp), out);
        self.vectors(out);
        self.finish(out);
    }

    /// Compares the low 64 bits of every `v` register: the lane a scalar
    /// float or integer occupies, as [`super::verify`] compares an xmm
    /// register's.
    ///
    /// A register the lifter wrote nothing to still holds the value it
    /// started with. A value the evaluator cannot read (a 128-bit load) is
    /// counted, not compared.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn vectors(&self, out: &mut Verified) {
        let lanes = self.emu.vregs();
        for (n, lane) in (0u8..).zip(lanes) {
            let key = Key::A64(Reg::V(n));
            let held = self.env.vals.get(&key);
            let Some(lifted) = out.count(Fact::Vector, self.lifted(key)) else {
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

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Machine, Sweep};
    use crate::analysis::decompile::expr::{Expr, Flags, Key, Op, Ty};
    use crate::analysis::decompile::verify::{Ran, function_ctx};
    use crate::analysis::decompile::verify_testing::{AT, image, tried};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::a64::Reg;
    use crate::program::Arch;

    /// `ret`.
    const RET: u32 = 0xd65f_03c0;

    /// Checks the first block of an arm64 routine from seeds 1 to 8
    /// ([`tried`]).
    ///
    /// # Arguments
    ///
    /// * `words` - The routine.
    /// * `spoil` - Makes the lift wrong.
    fn block(words: &[u32], spoil: impl Fn(&mut Ran<'_, Machine<'_>, ()>)) -> (usize, usize) {
        let p = image(Arch::Arm64, words);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(AT).expect("function");
        let first = f.blocks.iter().find(|b| b.start == AT).expect("block");
        let sweeps: Vec<Sweep<'_>> = (1..=8)
            .map(|seed| Sweep::new(&p, seed, false).expect("sweep"))
            .collect();
        let mut ctx = function_ctx(&p, &a, &overlay, f);
        let run = |seed, out: &mut _| {
            let sweep = sweeps.iter().find(|s| s.seed == seed).expect("a seed");
            sweep.run(&mut ctx, AT, first, out).expect("run")
        };
        tried(run, |ran, out| ran.compare(out), spoil)
    }

    /// A float operation is tried on registers that differ.
    ///
    /// `fsub d0, d1, d2` lifted with its operands the other way round is
    /// caught on every seed; from registers that start alike, as they did
    /// when every one started clear, both orders give the same zero.
    #[test]
    fn a_float_difference_the_other_way_round_is_caught() {
        let v = |n| Box::new(Expr::Var(Key::A64(Reg::V(n))));
        let swapped = |ran: &mut Ran<'_, Machine<'_>, ()>| {
            let wrong = Expr::Cast(Box::new(Expr::Bin(Op::FSub, v(2), v(1))), Ty::F64);
            ran.env.vals.insert(Key::A64(Reg::V(0)), wrong);
        };
        // ASM: fsub d0, d1, d2 ; ret
        let (_, caught) = block(&[0x1e62_3820, RET], swapped);
        assert_eq!(caught, 8, "d2 - d1 agreed with fsub d0, d1, d2 on a seed");
    }

    /// A float compare is tried on registers that differ, so its branch
    /// goes both ways.
    ///
    /// `fcmp d0, d1` then `b.gt` is taken from a seed and not from
    /// another, and a lift comparing the two the other way round is caught
    /// on every seed.
    #[test]
    fn a_float_compare_goes_both_ways() {
        let swapped = |ran: &mut Ran<'_, Machine<'_>, ()>| {
            let (_, cond) = ran.branch.as_mut().expect("a branch");
            cond.flags = match std::mem::replace(&mut cond.flags, Flags::Unknown) {
                Flags::Float(a, b, w) => Flags::Float(b, a, w),
                Flags::FCmp(p, a, b, w) => Flags::FCmp(p, b, a, w),
                other => other,
            };
        };
        // ASM: fcmp d0, d1 ; b.gt 0x100c ; ret ; ret
        let (taken, caught) = block(&[0x1e61_2000, 0x5400_004c, RET, RET], swapped);
        assert!((1..8).contains(&taken), "taken from {taken} of 8 seeds");
        assert_eq!(caught, 8, "d1 > d0 agreed with d0 > d1 on a seed");
    }
}
