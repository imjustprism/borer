//! Register liveness for the arm64 lifter.
//!
//! Each instruction reads and writes registers at a lane width, which the
//! backward passes of [`super::super::lift`] turn into the registers live
//! at each block's entry and after each instruction.
//!
//! The operands give most of it ([`Insn::registers`]): an `x` register
//! written at any width is written whole, since a `w` write clears the
//! upper half, and a `v` register written as a scalar is written whole too;
//! a read covers the width the operand names. The procedure call standard
//! gives the rest: a call reads every argument register (`x0` to `x7`, `v0`
//! to `v7` and `x8`, an indirect result's address) and writes what it lets
//! a callee change; a jump out of the function reads the arguments as a
//! call does; a return reads the register the function hands its result
//! back in, and not the link register it returns through, whose restore no
//! line writes.

use super::super::Ctx;
use super::super::expr::Key;
use super::super::lift::{Effects, Lanes};
use super::conv;
use super::shape::{FLOAT_ARGS, INT_ARGS, RESULT_REG};
use crate::isa::a64::{self, Insn, Mnemonic, Opnd, Reg};

/// The lane an `x` register write covers: all of it.
const X_WHOLE: u8 = 64;
/// The lane a `v` register write covers: all of it.
const V_WHOLE: u8 = 128;

/// The variable a register is.
///
/// # Arguments
///
/// * `r` - The register; the zero register is none.
fn key(r: Reg) -> Option<Key> {
    match r {
        Reg::X(_) | Reg::V(_) | Reg::Sp => Some(Key::A64(r)),
        Reg::Zr => None,
    }
}

/// The lane a write of `r` covers: the whole register.
///
/// # Arguments
///
/// * `r` - The register written.
fn written_lane(r: Reg) -> u8 {
    match r {
        Reg::V(_) => V_WHOLE,
        Reg::X(_) | Reg::Sp | Reg::Zr => X_WHOLE,
    }
}

/// Adds every argument register to a block's reads: what a call or a jump
/// out of the function may pass.
///
/// # Arguments
///
/// * `reads` - The reads.
fn arguments(reads: &mut Lanes) {
    for n in 0..INT_ARGS {
        reads.push((Key::A64(Reg::X(n)), X_WHOLE));
    }
    reads.push((Key::A64(Reg::X(RESULT_REG)), X_WHOLE));
    for n in 0..FLOAT_ARGS {
        reads.push((Key::A64(Reg::V(n)), V_WHOLE));
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
        .filter_map(|&(r, bits)| Some((key(r)?, u8::try_from(bits).unwrap_or(V_WHOLE))))
        .collect();
    let mut writes: Lanes = regs
        .writes
        .iter()
        .filter_map(|&r| Some((key(r)?, written_lane(r))))
        .collect();
    match i.op {
        a64::Op::Bl | a64::Op::Blr => {
            arguments(&mut reads);
            writes.extend(conv::clobbered().map(|c| (Key::A64(c), written_lane(c))));
        }
        a64::Op::B if i.target().is_some_and(|t| !ctx.block_starts.contains(&t)) => {
            arguments(&mut reads);
        }
        a64::Op::Ret => {
            reads.clear();
            if !ctx.unused_result {
                let back = if ctx.ret_float { Reg::V(0) } else { Reg::X(0) };
                reads.push((Key::A64(back), ctx.ret_lane));
            }
        }
        a64::Op::Syscall => {
            arguments(&mut reads);
            reads.push((Key::A64(Reg::X(conv::SYSCALL_NUMBER)), X_WHOLE));
            if i.mnemonic == Mnemonic::Svc && matches!(i.operands.first(), Some(Opnd::Imm(0))) {
                reads.push((Key::A64(Reg::X(8)), X_WHOLE));
                reads.push((Key::A64(Reg::X(2)), X_WHOLE));
                writes.push((Key::A64(Reg::X(0)), X_WHOLE));
            }
        }
        a64::Op::B
        | a64::Op::BCond(_)
        | a64::Op::Cbz
        | a64::Op::Cbnz
        | a64::Op::Tbz
        | a64::Op::Tbnz
        | a64::Op::Br
        | a64::Op::Eret
        | a64::Op::Trap
        | a64::Op::Adr
        | a64::Op::Adrp
        | a64::Op::Nop
        | a64::Op::Bti
        | a64::Op::Pac
        | a64::Op::Sve
        | a64::Op::Sme
        | a64::Op::Invalid
        | a64::Op::Other => {}
    }
    (reads, writes)
}
