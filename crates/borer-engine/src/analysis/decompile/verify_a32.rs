//! Verification of the ARM32 lifter against the ARM32 machine, block by
//! block, as [`super::verify_a64`] checks the arm64 lifter.
//!
//! Each block runs twice from one seeded state: on
//! [`crate::emulate::a32::Machine`], which executes the real instructions,
//! and through the ARM32 lifter ([`super::lift_a32`]), whose symbolic
//! results are evaluated under that state by the shared evaluator
//! ([`super::verify::eval`]) at 32 bits. Five kinds of fact must agree:
//! every core register and the stack pointer; every single and double;
//! every stack slot the lifter holds a value for; every store and byte
//! the block writes off the frame; and whether the block's conditional
//! branch is taken, the test in front of a conditional return or call
//! among them ([`crate::isa::a32::SKIP`]).
//!
//! A block is checked up to its first control transfer. Memory nothing
//! backs reads a hash of its address on both sides. The core registers are
//! random, except that a register the block compares with a constant, or
//! with another register, mostly starts next to it; the doubles are random
//! too, a single the half of its double, and the flags start clear on both
//! sides. A block holding an instruction either side does not model is not
//! checked. A pass says the lifting agreed on the seeds tried, not that it
//! is right.

use std::collections::BTreeMap;

use super::Ctx;
use super::arch::A32;
use super::expr::{Key, Ty};
use super::lift_a32::decode_blocks;
use super::verify::{
    Fact, Jcc, Near, Ran, Rng, Seeded, State, Verified, bench, functions, registers, run_block,
};
use crate::analysis::Analysis;
use crate::emulate::a32::Machine;
use crate::isa::a32::{DpKind, Flow, Insn, Op, Operand, Reg, SKIP, SP};
use crate::program::Program;

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

bench!(Machine<'_>, "sp");

/// The core registers compared and seeded, each as the machine names it
/// and as the lifter keys it.
fn general() -> impl Iterator<Item = (&'static str, Key)> {
    GENERAL
        .into_iter()
        .map(|(name, n)| (name, Key::A32(Reg::R(n))))
}

/// Checks the blocks of some functions of an ARM32 program against the
/// ARM32 machine, on the calling thread.
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
pub(super) fn sweep(
    program: &Program,
    analysis: &Analysis,
    entries: &[u64],
    seed: u64,
) -> Verified {
    let Some(mut pristine) = Machine::new(program, 0) else {
        return Verified::default();
    };
    pristine.set_forced(true);
    functions(program, analysis, entries, |ctx, f, out| {
        for (block, instrs) in f.blocks.iter().zip(&decode_blocks(program, f)) {
            let ran = run(&pristine, seed, ctx, f.entry, block.start, instrs, out);
            out.block(ran, compare);
        }
    })
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
/// `cmp`, `cmn`, `tst`, `teq` and a `cbz` or `cbnz` compare; a register
/// compared with itself starts near zero.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
fn comparands(instrs: &[Insn]) -> BTreeMap<Key, Near> {
    let mut near = BTreeMap::new();
    for i in instrs {
        let (rn, src) = if let Op::Dp {
            kind: kind @ (DpKind::Cmp | DpKind::Cmn | DpKind::Tst | DpKind::Teq),
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
            Operand::Reg { rm, amount: 0, .. } if rm == rn => {
                near.insert(Key::A32(rn), Near::Constant(0));
            }
            Operand::Reg { .. } | Operand::RegShift { .. } => {}
        }
    }
    near
}

/// Seeds the VFP registers on the machine and in the evaluator's state
/// alike: each double at random, and each single of `d0` to `d15` as the
/// half of its double it is.
///
/// They are drawn after every other seed, so the core registers and the
/// stack start as they did while these started clear. Each is declared
/// the float its kind is, a single or a double, as the text declares the
/// variable: the evaluator reads a bare one under a float cast as that.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `st` - The evaluator's state.
/// * `rng` - The seeded generator.
fn seed_vfp(emu: &mut Machine<'_>, st: &mut State<'_, Machine<'_>>, rng: &mut Rng) {
    for n in 0..32 {
        let v = rng.next();
        emu.set_register(&crate::isa::a32::name(Reg::D(n)), v);
        let mut set = |r: Reg, v: u64, ty: Ty| {
            st.regs.insert(Key::A32(r), v);
            st.reg_ty.insert(Key::A32(r), ty);
        };
        set(Reg::D(n), v, Ty::F64);
        if n < 16 {
            set(Reg::S(2 * n), v & 0xffff_ffff, Ty::F32);
            set(Reg::S(2 * n + 1), v >> 32, Ty::F32);
        }
    }
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
    let mut seeded = Seeded::new(pristine, seed, (entry, start), 32, line.len() + 1);
    let mut all = line;
    all.extend(jcc);
    seeded.registers(general(), &comparands(&all));
    seeded.stack();
    seed_vfp(&mut seeded.emu, &mut seeded.st, &mut seeded.rng);
    let begin = instrs.first().map_or(start, |i| i.va);
    let jcc = jcc.and_then(|j| j.target().map(|target| Jcc { ip: j.va, target }));
    run_block::<A32, _, _>(seeded, ctx, (begin, end), &all, jcc, (), out)
}

/// Compares every fact: registers, VFP registers, slots, stores, then the
/// branch.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn compare(ran: Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    registers(&ran, general(), Key::A32(SP), out);
    vfp(&ran, out);
    ran.finish(out);
}

/// Compares every single and double, each at its own width.
///
/// A register the lifter holds no value for still holds the value it
/// started with: the lifter writes both views of a VFP register an
/// instruction it models changes, a single's double and a double's
/// singles, so a write a lift drops shows as a register the machine
/// changed.
///
/// # Arguments
///
/// * `ran` - Both runs.
/// * `out` - Where the counts and disagreements go.
fn vfp(ran: &Ran<'_, Machine<'_>, ()>, out: &mut Verified) {
    for r in (0..32).map(Reg::S).chain((0..32).map(Reg::D)) {
        let key = Key::A32(r);
        let value = ran.env.vals.get(&key);
        let name = crate::isa::a32::name(r);
        let Some(emulated) = ran.emu.register(&name) else {
            continue;
        };
        let Some(lifted) = out.count(Fact::Vector, ran.lifted(key)) else {
            continue;
        };
        let bits = if matches!(r, Reg::S(_)) { 32 } else { 64 };
        let lifted = if bits == 32 {
            lifted & 0xffff_ffff
        } else {
            lifted
        };
        if lifted != emulated {
            ran.disagree(
                out,
                Fact::Vector,
                name,
                (emulated, lifted, bits),
                value.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}")),
            );
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Machine, compare, run};
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, Op, Ty};
    use crate::analysis::decompile::lift_a32::decode_blocks;
    use crate::analysis::decompile::verify::{Ran, function_ctx};
    use crate::analysis::decompile::verify_testing::{AT, image, tried};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::a32::Reg;
    use crate::isa::x86::ConditionCode;
    use crate::program::Arch;

    /// `beq` over the next instruction, then `bx lr` twice.
    const BEQ_OVER: [u32; 3] = [0x0a00_0000, 0xe12f_ff1e, 0xe12f_ff1e];

    /// Checks the first block of an A32 routine from seeds 1 to 8
    /// ([`tried`]).
    ///
    /// # Arguments
    ///
    /// * `words` - The routine.
    /// * `spoil` - Makes the lift wrong.
    fn block(words: &[u32], spoil: impl Fn(&mut Ran<'_, Machine<'_>, ()>)) -> (usize, usize) {
        let p = image(Arch::Arm, words);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(AT).expect("function");
        let mut pristine = Machine::new(&p, 0).expect("machine");
        pristine.set_forced(true);
        let k = f.blocks.iter().position(|b| b.start == AT).expect("block");
        let instrs = decode_blocks(&p, f).swap_remove(k);
        let mut ctx = function_ctx(&p, &a, &overlay, f);
        let run =
            |seed, out: &mut _| run(&pristine, seed, &mut ctx, AT, AT, &instrs, out).expect("run");
        tried(run, compare, spoil)
    }

    /// An equality test of two registers, or of one with itself, is tried
    /// where it holds.
    ///
    /// `teq r0, r1` then `beq` goes both ways across the seeds, and a lift
    /// of the branch as taken when `r0` is one above `r1` is caught; so is
    /// `tst r0, r0` then `beq`, lifted as taken when `r0` is one.
    #[test]
    fn an_equality_test_is_tried_where_it_holds() {
        let r = |n| Expr::Var(Key::A32(Reg::R(n)));
        let equals = |other: Expr| {
            move |ran: &mut Ran<'_, Machine<'_>, ()>| {
                let (_, cond) = ran.branch.as_mut().expect("a branch");
                let flags = Flags::Cmp(r(0), other.clone(), 32);
                let cc = Cc(ConditionCode::e);
                *cond = Cond { cc, flags };
            }
        };
        let above = Expr::Bin(Op::Add, Box::new(r(1)), Box::new(Expr::Const(1)));
        // ASM: teq r0, r1 ; beq 0x100c ; bx lr ; bx lr
        let code = [&[0xe130_0001], &BEQ_OVER[..]].concat();
        let (taken, caught) = block(&code, equals(above));
        assert!((1..8).contains(&taken), "taken from {taken} of 8 seeds");
        assert!(caught > 0, "r0 == r1 + 1 agreed with teq on every seed");
        // ASM: tst r0, r0 ; beq 0x100c ; bx lr ; bx lr
        let code = [&[0xe110_0000], &BEQ_OVER[..]].concat();
        let (taken, caught) = block(&code, equals(Expr::Const(1)));
        assert!((1..8).contains(&taken), "taken from {taken} of 8 seeds");
        assert!(caught > 0, "r0 == 1 agreed with tst r0, r0 on every seed");
    }

    /// A lift that drops the write of a VFP register is reported.
    ///
    /// `vmov s0, r0` writes `s0`, and with it `d0`. A lift holding a value
    /// for neither leaves both as they started, which the machine's no
    /// longer are.
    #[test]
    fn a_dropped_vfp_write_is_reported() {
        let dropped = |ran: &mut Ran<'_, Machine<'_>, ()>| {
            for r in [Reg::S(0), Reg::D(0)] {
                let held = ran.env.vals.remove(&Key::A32(r));
                assert!(held.is_some(), "the lift held no value for {r:?}");
            }
        };
        // ASM: vmov s0, r0 ; bx lr
        let (_, caught) = block(&[0xee00_0a10, 0xe12f_ff1e], dropped);
        assert_eq!(caught, 8, "a dropped write agreed on a seed");
    }

    /// A VFP operation is tried on registers that differ.
    ///
    /// `vsub.f64 d0, d1, d2` lifted with its operands the other way round
    /// is caught on every seed, and `vmov r0, s1` reads the upper half of
    /// `d0` on both sides.
    #[test]
    fn a_vfp_difference_the_other_way_round_is_caught() {
        let d = |n| Box::new(Expr::Var(Key::A32(Reg::D(n))));
        let swapped = |ran: &mut Ran<'_, Machine<'_>, ()>| {
            let wrong = Expr::Cast(Box::new(Expr::Bin(Op::FSub, d(2), d(1))), Ty::F64);
            ran.env.vals.insert(Key::A32(Reg::D(0)), wrong);
        };
        // ASM: vsub.f64 d0, d1, d2 ; bx lr
        let (_, caught) = block(&[0xee31_0b42, 0xe12f_ff1e], swapped);
        assert_eq!(caught, 8, "d2 - d1 agreed with vsub d0, d1, d2 on a seed");
        // ASM: vmov r0, s1 ; bx lr
        let (_, caught) = block(&[0xee10_0a90, 0xe12f_ff1e], |_| {});
        assert_eq!(caught, 0, "the lift as it is disagreed on a seed");
    }
}
