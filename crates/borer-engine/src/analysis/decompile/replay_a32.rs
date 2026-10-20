//! The check of an ARM32 function's text against the ARM32 machine: what
//! [`replay`](super::replay) asks of an ARM32 block.
//!
//! The replay itself is the shared one ([`Replay`]). What is ARM32's is how
//! a block ends (the test in front of a conditional return or call is a
//! branch, [`crate::isa::a32::SKIP`]), which blocks the replay can check,
//! the registers seeded and compared (`r0` to `r12` and the link
//! register), where a call or a jump goes, and which registers a call
//! changes. The machine runs an instruction under a condition that moves
//! control whatever its condition ([`Machine::set_forced`]), as the text's
//! block after its test reads it. A block of VFP or Advanced SIMD
//! instructions is not checked: the text's singles and doubles are
//! separate variables the machine's shared registers cannot all be seeded
//! from.

use super::arch::A32;
use super::expr::Key;
use super::lift::ArgAt;
use super::lift_a32::{flags_read, sets_flags};
use super::replay::{Code, OUTSIDE_FLOAT, Replay, Rig, Transfer, Witness, word_limits};
use super::verify_a32::GENERAL;
use crate::analysis::Analysis;
use crate::emulate::Stop;
use crate::emulate::a32::Machine;
use crate::isa::a32::{DpKind, Flow, Insn, Op, Operand, Reg, SKIP, Shift};
use crate::program::Program;

impl Rig for Machine<'_> {
    fn poke(&mut self, at: u64, byte: u8) {
        Machine::poke(self, at, byte);
    }

    fn set_register(&mut self, name: &str, value: u64) -> bool {
        Machine::set_register(self, name, value)
    }

    fn set_fill(&mut self, seed: Option<u64>) {
        Machine::set_fill(self, seed);
    }

    fn set_permissive(&mut self) {}

    fn vector(&self, n: usize) -> u128 {
        u128::from(self.doubles().get(n).copied().unwrap_or(0))
    }

    fn set_vector(&mut self, _n: usize, _v: u128) {}
}

/// Tells whether the replay can check an instruction.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Errors
///
/// Why a block holding it is not checked.
fn checked(i: &Insn) -> Result<(), &'static str> {
    match i.op {
        Op::VLoad { .. }
        | Op::VStore { .. }
        | Op::VLdm { .. }
        | Op::VStm { .. }
        | Op::FpBin { .. }
        | Op::FpUn { .. }
        | Op::FpImm { .. }
        | Op::FpCmp { .. }
        | Op::Vcvt { .. }
        | Op::VmovCore { .. }
        | Op::VmovPair { .. }
        | Op::Vmrs { .. }
        | Op::Vmsr { .. }
        | Op::Neon { .. } => Err(OUTSIDE_FLOAT),
        Op::Svc { .. } | Op::Trap | Op::Unknown | Op::Invalid | Op::Mrs { .. } | Op::Msr { .. } => {
            Err("an instruction outside every checked form")
        }
        Op::Dp { .. }
        | Op::Movw { .. }
        | Op::Movt { .. }
        | Op::Adr { .. }
        | Op::Mul { .. }
        | Op::MulLong { .. }
        | Op::Smmul { .. }
        | Op::Smulxy { .. }
        | Op::Div { .. }
        | Op::Clz { .. }
        | Op::Rbit { .. }
        | Op::Rev { .. }
        | Op::Rev16 { .. }
        | Op::Revsh { .. }
        | Op::Bfx { .. }
        | Op::Sat { .. }
        | Op::Bfi { .. }
        | Op::Extend { .. }
        | Op::Load { .. }
        | Op::Store { .. }
        | Op::LoadEx { .. }
        | Op::StoreEx { .. }
        | Op::LoadDual { .. }
        | Op::StoreDual { .. }
        | Op::Ldm { .. }
        | Op::Stm { .. }
        | Op::B { .. }
        | Op::Bl { .. }
        | Op::Blx { .. }
        | Op::BlxReg { .. }
        | Op::Bx { .. }
        | Op::Cbz { .. }
        | Op::Tb { .. }
        | Op::It { .. }
        | Op::Nop => Ok(()),
    }
}

impl Replay for A32 {
    type Rig<'p> = Machine<'p>;

    fn rig<'p>(program: &'p Program, _analysis: &Analysis) -> Option<Machine<'p>> {
        let mut m = Machine::new(program, 0)?;
        m.set_forced(true);
        Some(m)
    }

    fn width(_program: &Program) -> Option<u8> {
        Some(32)
    }

    fn code(w: &Witness) -> Option<&[Vec<Insn>]> {
        match &w.code {
            Code::A32(code) => Some(code.as_slice()),
            Code::X86(_) | Code::A64(_) => None,
        }
    }

    fn regs(_width: u8) -> Vec<(&'static str, Key)> {
        GENERAL
            .iter()
            .map(|&(name, n)| (name, Key::A32(Reg::R(n))))
            .collect()
    }

    fn vectors() -> Vec<Key> {
        Vec::new()
    }

    fn volatile(_w: &Witness) -> Vec<Key> {
        super::abi::a32::clobbered().map(Key::A32).collect()
    }

    fn transfer(i: &Insn) -> Transfer {
        let next = i.next() & !SKIP;
        match i.flow() {
            Flow::Next => Transfer::Next(next),
            Flow::CondJump => match i.target() {
                Some(target) => Transfer::Branch { target, next },
                None => Transfer::Trap,
            },
            Flow::Jump if i.target().is_some() => Transfer::Jump,
            Flow::Jump => Transfer::Indirect,
            Flow::Call => Transfer::Call,
            Flow::Return => Transfer::Return,
            Flow::Invalid => Transfer::Trap,
        }
    }

    fn subset(code: &[Insn]) -> Result<(), &'static str> {
        code.iter().try_for_each(checked)
    }

    fn whole_lanes(_code: &[Insn]) -> bool {
        false
    }

    fn comparands(code: &[Insn], width: u8) -> Vec<u64> {
        let mut pool = word_limits(width);
        for i in code {
            if let Op::Dp {
                src: Operand::Imm { value, .. },
                ..
            } = i.op
            {
                let k = u64::from(value);
                pool.extend([
                    k,
                    k.wrapping_add(1) & 0xffff_ffff,
                    k.wrapping_sub(1) & 0xffff_ffff,
                ]);
            }
        }
        pool.sort_unstable();
        pool.dedup();
        pool
    }

    fn flag_setters(code: &[Insn]) -> (Vec<(u64, bool)>, Vec<u64>) {
        (
            code.iter()
                .filter(|i| i.flow() != Flow::Call && sets_flags(i))
                .map(|i| (i.va, false))
                .collect(),
            code.iter()
                .filter(|i| flags_read(i))
                .map(|i| i.va)
                .collect(),
        )
    }

    fn sets_flags(i: &Insn) -> bool {
        i.flow() != Flow::Call && sets_flags(i)
    }

    fn scans(_code: &[Insn]) -> bool {
        false
    }

    fn budget(code: &[Insn]) -> usize {
        code.len() + 1
    }

    fn target_value(emu: &Machine<'_>, i: &Insn, _width: u8) -> Option<u64> {
        if let Some(t) = i.target() {
            return Some(t);
        }
        let through = if let Op::BlxReg { rm } | Op::Bx { rm } = i.op {
            Some(rm)
        } else if let Op::Dp {
            kind: DpKind::Mov,
            src:
                Operand::Reg {
                    rm,
                    shift: Shift::Lsl,
                    amount: 0,
                },
            ..
        } = i.op
        {
            Some(rm)
        } else {
            None
        };
        if let Some(rm) = through {
            return emu.register(&crate::isa::a32::name(rm));
        }
        let mut step = emu.clone();
        step.set_budget(1);
        step.stop_at(None);
        match step.run(i.va).stop {
            Stop::Budget => Some(step.pc()),
            Stop::Returned
            | Stop::Unmodeled(_)
            | Stop::Fault(_)
            | Stop::MemoryFull(_)
            | Stop::Stopped(_)
            | Stop::Derailed(_)
            | Stop::Exited
            | Stop::Limit(_) => None,
        }
    }

    fn register_value(emu: &Machine<'_>, at: ArgAt, _width: u8) -> Option<u64> {
        match at {
            ArgAt::A32(r @ Reg::R(_)) => emu.register(&crate::isa::a32::name(r)),
            ArgAt::A32(_) | ArgAt::Reg(_) | ArgAt::Stack(..) | ArgAt::Operand | ArgAt::A64(_) => {
                None
            }
        }
    }

    fn dispatch(_emu: &Machine<'_>, _w: &Witness, to: u64, _width: u8) -> Option<u64> {
        Some(to)
    }

    fn kept(_emu: &Machine<'_>, _code: Option<&Vec<Insn>>, _w: &Witness, _width: u8) -> Vec<u64> {
        Vec::new()
    }
}
