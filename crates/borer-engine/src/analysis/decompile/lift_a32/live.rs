//! Register liveness for the ARM32 lifter.
//!
//! The operands give most of it ([`Insn::registers`]); a write of a single
//! also writes its double and reads the single beside it, whose bits the
//! double keeps, and a write of a double below `d16` writes both its
//! singles. The procedure call standard gives the rest: a call reads every
//! argument register and writes what it lets a callee change, a jump out
//! of the function reads the arguments as a call does, and a return reads
//! the register its result comes back in.

use super::super::Ctx;
use super::super::abi::a32 as a32_abi;
use super::super::expr::Key;
use super::super::lift::{Effects, Lanes};
use crate::isa::a32::{Flow, Insn, Op as AOp, Reg, SKIP, SP};

/// The lane a register covers, in bits.
///
/// # Arguments
///
/// * `r` - The register.
fn lane(r: Reg) -> u8 {
    match r {
        Reg::D(_) => 64,
        Reg::R(_) | Reg::S(_) => 32,
    }
}

/// Adds every argument register to the reads: what a call or a jump out
/// of the function may pass.
///
/// # Arguments
///
/// * `reads` - The reads.
fn arguments(reads: &mut Lanes) {
    for n in 0..a32_abi::INT_ARGS {
        reads.push((Key::A32(Reg::R(n)), 32));
    }
    for n in 0..a32_abi::FLOAT_SINGLES {
        reads.push((Key::A32(Reg::S(n)), 32));
    }
    for n in 0..a32_abi::FLOAT_SINGLES / 2 {
        reads.push((Key::A32(Reg::D(n)), 64));
    }
}

/// Adds a register write to the writes, with what it writes beside it.
///
/// # Arguments
///
/// * `r` - The register written.
/// * `reads` - The reads, for a single's neighbour.
/// * `writes` - The writes.
fn written(r: Reg, reads: &mut Lanes, writes: &mut Lanes) {
    writes.push((Key::A32(r), lane(r)));
    match r {
        Reg::S(n) => {
            writes.push((Key::A32(Reg::D(n / 2)), 64));
            reads.push((Key::A32(Reg::S(n ^ 1)), 32));
        }
        Reg::D(n) if n < 16 => {
            writes.push((Key::A32(Reg::S(2 * n)), 32));
            writes.push((Key::A32(Reg::S(2 * n + 1)), 32));
        }
        Reg::R(_) | Reg::D(_) => {}
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
    let mut reads: Lanes = regs.reads.iter().map(|&r| (Key::A32(r), lane(r))).collect();
    let mut writes: Lanes = Vec::new();
    for &r in &regs.writes {
        written(r, &mut reads, &mut writes);
    }
    if i.va & SKIP != 0 {
        return (Vec::new(), Vec::new());
    }
    match i.flow() {
        Flow::Call => {
            arguments(&mut reads);
            for r in a32_abi::clobbered() {
                writes.push((Key::A32(r), lane(r)));
            }
        }
        Flow::Jump if i.target().is_some_and(|t| !ctx.block_starts.contains(&t)) => {
            arguments(&mut reads);
        }
        Flow::Jump
            if matches!(i.op, AOp::Bx { .. }) && !ctx.analysis.jump_tables.contains_key(&i.va) =>
        {
            arguments(&mut reads);
        }
        Flow::Return => {
            reads.retain(|(k, _)| *k == Key::A32(SP));
            if !ctx.unused_result {
                let back = super::call::result_key(ctx);
                let width = if back == Key::A32(Reg::D(0)) { 64 } else { 32 };
                reads.push((back, width));
            }
        }
        Flow::Next | Flow::CondJump | Flow::Jump | Flow::Invalid => {}
    }
    (reads, writes)
}
