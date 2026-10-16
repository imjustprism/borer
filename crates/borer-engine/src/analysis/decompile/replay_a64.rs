//! The check of an arm64 function's text against the arm64 machine: what
//! [`replay`](super::replay) asks of an arm64 block.
//!
//! The replay itself is the x86 one's ([`Replay`]): each block's
//! statements replayed under the lifter's witness and held against the
//! machine's run. What is arm64's is how a block ends, which blocks the
//! replay can check, the registers seeded and compared (`x0` to `x30`, and
//! the `v` registers' low lanes), where a call or a jump goes, and which
//! registers a call changes. A block holding an instruction the lifter
//! writes as a statement of its own (an `mrs` or `msr` of a system
//! register other than `TPIDR_EL0` and `NZCV`, a supervisor call) or a
//! vector form it leaves unmodeled is not checked.

use super::arch::A64;
use super::expr::Key;
use super::lift::ArgAt;
use super::lift_a64::{flags_read, flags_set};
use super::replay::{Code, OUTSIDE_FLOAT, Replay, Rig, Transfer, Witness, word_limits};
use super::verify::Bench;
use crate::emulate::a64::Machine;
use crate::isa::a64::{self, Flow, Insn, Mnemonic, Opnd, Reg};
use crate::program::Program;

/// The general registers the replay seeds and compares, by the machine's
/// names: `x0` first, the register a result comes back in.
const REGS: [(&str, Key); 31] = [
    ("x0", Key::A64(Reg::X(0))),
    ("x1", Key::A64(Reg::X(1))),
    ("x2", Key::A64(Reg::X(2))),
    ("x3", Key::A64(Reg::X(3))),
    ("x4", Key::A64(Reg::X(4))),
    ("x5", Key::A64(Reg::X(5))),
    ("x6", Key::A64(Reg::X(6))),
    ("x7", Key::A64(Reg::X(7))),
    ("x8", Key::A64(Reg::X(8))),
    ("x9", Key::A64(Reg::X(9))),
    ("x10", Key::A64(Reg::X(10))),
    ("x11", Key::A64(Reg::X(11))),
    ("x12", Key::A64(Reg::X(12))),
    ("x13", Key::A64(Reg::X(13))),
    ("x14", Key::A64(Reg::X(14))),
    ("x15", Key::A64(Reg::X(15))),
    ("x16", Key::A64(Reg::X(16))),
    ("x17", Key::A64(Reg::X(17))),
    ("x18", Key::A64(Reg::X(18))),
    ("x19", Key::A64(Reg::X(19))),
    ("x20", Key::A64(Reg::X(20))),
    ("x21", Key::A64(Reg::X(21))),
    ("x22", Key::A64(Reg::X(22))),
    ("x23", Key::A64(Reg::X(23))),
    ("x24", Key::A64(Reg::X(24))),
    ("x25", Key::A64(Reg::X(25))),
    ("x26", Key::A64(Reg::X(26))),
    ("x27", Key::A64(Reg::X(27))),
    ("x28", Key::A64(Reg::X(28))),
    ("x29", Key::A64(Reg::X(29))),
    ("x30", Key::A64(Reg::X(30))),
];

/// How many `v` registers the machine has.
const VECTORS: u8 = 32;

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
        self.vregs().get(n).copied().unwrap_or(0)
    }

    fn set_vector(&mut self, n: usize, v: u128) {
        if let Ok(n) = u8::try_from(n) {
            self.set_vreg(n, v);
        }
    }
}

/// The value a register holds on the machine, as an argument is read.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `r` - The register: an `x` register whole, a `v` register's low 64
///   bits.
fn reg_value(emu: &Machine<'_>, r: Reg) -> Option<u64> {
    match r {
        Reg::X(n) => REGS
            .get(usize::from(n))
            .and_then(|(name, _)| emu.register(name)),
        Reg::V(n) => u64::try_from(Rig::vector(emu, usize::from(n)) & u128::from(u64::MAX)).ok(),
        Reg::Sp => emu.register(<Machine<'_> as Bench>::SP),
        Reg::Zr => Some(0),
    }
}

/// Tells whether the replay can check an instruction: one the lifter
/// models as values, not as a statement of its own nor as a vector form it
/// leaves alone.
///
/// An `mrs` or `msr` of `TPIDR_EL0` or `NZCV` is modeled. Any other system
/// register, and a supervisor call, is a statement of its own.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Errors
///
/// Why a block holding it is not checked.
fn checked(i: &Insn) -> Result<(), &'static str> {
    let own_statement = matches!(i.mnemonic, Mnemonic::Mrs | Mnemonic::Msr | Mnemonic::Svc)
        && !super::lift_a64::modeled_system(i);
    match i.op {
        a64::Op::Syscall | a64::Op::Eret | a64::Op::Trap | a64::Op::Invalid => {
            Err("an instruction outside every checked form")
        }
        a64::Op::Sve | a64::Op::Sme => Err(OUTSIDE_FLOAT),
        a64::Op::Nop | a64::Op::Bti => Ok(()),
        a64::Op::B
        | a64::Op::BCond(_)
        | a64::Op::Cbz
        | a64::Op::Cbnz
        | a64::Op::Tbz
        | a64::Op::Tbnz
        | a64::Op::Bl
        | a64::Op::Br
        | a64::Op::Blr
        | a64::Op::Ret
        | a64::Op::Adr
        | a64::Op::Adrp
        | a64::Op::Pac
        | a64::Op::Other => {
            if own_statement {
                Err("an instruction outside every checked form")
            } else if i.operands.contains(&Opnd::Other) && !super::lift_a64::modeled_system(i) {
                Err(OUTSIDE_FLOAT)
            } else {
                Ok(())
            }
        }
    }
}

impl Replay for A64 {
    type Rig<'p> = Machine<'p>;

    fn rig(program: &Program) -> Option<Machine<'_>> {
        Machine::new(program, 0)
    }

    fn width(_program: &Program) -> Option<u8> {
        Some(64)
    }

    fn code(w: &Witness) -> Option<&[Vec<Insn>]> {
        match &w.code {
            Code::A64(code) => Some(code.as_slice()),
            Code::X86(_) => None,
        }
    }

    fn regs(_width: u8) -> Vec<(&'static str, Key)> {
        REGS.to_vec()
    }

    fn vectors() -> Vec<Key> {
        (0..VECTORS).map(|n| Key::A64(Reg::V(n))).collect()
    }

    fn volatile(_w: &Witness) -> Vec<Key> {
        super::lift_a64::clobbered().map(Key::A64).collect()
    }

    fn transfer(i: &Insn) -> Transfer {
        let next = i.va.wrapping_add(crate::num::from_usize(a64::INSN_LEN));
        match i.flow {
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
            for o in &i.operands {
                if let Opnd::Imm(k) = *o {
                    pool.extend([k, k.wrapping_add(1), k.wrapping_sub(1)]);
                }
            }
        }
        pool.sort_unstable();
        pool.dedup();
        pool
    }

    fn flag_setters(code: &[Insn]) -> (Vec<(u64, bool)>, Vec<u64>) {
        (
            code.iter()
                .filter(|i| i.flow != Flow::Call && flags_set(i))
                .map(|i| (i.va, false))
                .collect(),
            code.iter()
                .filter(|i| flags_read(i))
                .map(|i| i.va)
                .collect(),
        )
    }

    fn sets_flags(i: &Insn) -> bool {
        i.flow != Flow::Call && flags_set(i)
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
        match i.operands[0] {
            Opnd::Reg { reg, .. } => reg_value(emu, reg),
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => None,
        }
    }

    fn register_value(emu: &Machine<'_>, at: ArgAt, _width: u8) -> Option<u64> {
        match at {
            ArgAt::A64(r) => reg_value(emu, r),
            ArgAt::Reg(_) | ArgAt::Stack(..) | ArgAt::Operand => None,
        }
    }

    fn dispatch(_emu: &Machine<'_>, _w: &Witness, to: u64, _width: u8) -> Option<u64> {
        Some(to)
    }

    fn kept(_emu: &Machine<'_>, _code: Option<&Vec<Insn>>, _w: &Witness, _width: u8) -> Vec<u64> {
        Vec::new()
    }
}
