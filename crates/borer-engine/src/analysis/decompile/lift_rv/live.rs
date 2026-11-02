//! Register liveness for the RISC-V lifter.
//!
//! The operands give most of it ([`Insn::registers`]). The calling
//! convention gives the rest: a call reads every argument register and
//! writes what it lets a callee change, a jump out of the function reads
//! the arguments as a call does, `ecall` reads `a0` to `a7` and writes
//! `a0`, and a return reads the register its result comes back in.

use super::super::Ctx;
use super::super::abi::rv as rv_abi;
use super::super::expr::Key;
use super::super::lift::{Effects, Lanes};
use crate::isa::rv::{Flow, Insn, Op as ROp, Reg, SP};

/// The lane a register covers, in bits.
///
/// # Arguments
///
/// * `ctx` - The function's state, for the register width.
/// * `r` - The register.
fn lane(ctx: &Ctx<'_>, r: Reg) -> u8 {
    match r {
        Reg::X(_) => super::bits(super::xlen(ctx.program)),
        Reg::F(_) => 64,
    }
}

/// Adds every argument register to the reads: what a call or a jump out
/// of the function may pass.
///
/// # Arguments
///
/// * `ctx` - The function's state.
/// * `reads` - The reads.
fn arguments(ctx: &Ctx<'_>, reads: &mut Lanes) {
    for n in 0..rv_abi::INT_ARGS {
        let r = Reg::X(rv_abi::FIRST_ARG + n);
        reads.push((Key::Rv(r), lane(ctx, r)));
    }
    for n in 0..rv_abi::FLOAT_ARGS {
        reads.push((Key::Rv(Reg::F(rv_abi::FIRST_ARG + n)), 64));
    }
}

/// Returns the registers one instruction reads and writes, with the lane
/// width of each.
///
/// # Arguments
///
/// * `ctx` - The function's state: its block starts, what its return hands
///   back.
/// * `i` - The instruction.
///
/// # Returns
///
/// `(reads, writes)`.
pub(in crate::analysis::decompile) fn effects(ctx: &Ctx<'_>, i: &Insn) -> Effects {
    let regs = i.registers();
    let mut reads: Lanes = regs
        .reads
        .iter()
        .map(|&r| (Key::Rv(r), lane(ctx, r)))
        .collect();
    let mut writes: Lanes = regs
        .writes
        .iter()
        .map(|&r| (Key::Rv(r), lane(ctx, r)))
        .collect();
    match i.flow() {
        Flow::Call => {
            arguments(ctx, &mut reads);
            for r in rv_abi::clobbered() {
                writes.push((Key::Rv(r), lane(ctx, r)));
            }
        }
        Flow::Jump if i.target().is_none_or(|t| !ctx.block_starts.contains(&t)) => {
            arguments(ctx, &mut reads);
        }
        Flow::Return => {
            reads.retain(|(k, _)| *k == Key::Rv(SP));
            if !ctx.unused_result {
                let back = super::call::result_reg(ctx);
                reads.push((Key::Rv(back), lane(ctx, back)));
            }
        }
        Flow::Next if i.op == ROp::Ecall => {
            arguments(ctx, &mut reads);
            let a0 = Reg::X(rv_abi::FIRST_ARG);
            writes.push((Key::Rv(a0), lane(ctx, a0)));
        }
        Flow::Next | Flow::CondJump | Flow::Jump | Flow::Invalid => {}
    }
    (reads, writes)
}
