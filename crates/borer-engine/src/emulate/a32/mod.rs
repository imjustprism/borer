//! A bounded ARM32 machine: A32 and T32 code, the integer instructions and
//! the scalar VFP ones.
//!
//! The ARM32 counterpart of [`super::a64::Machine`], with its memory
//! overlay, stop reasons ([`Stop`]), run report ([`Run`]) and method names.
//! It runs what [`crate::isa::a32`] decodes: the data processing with its
//! shifter and flags, the multiplies and divides, the loads and stores in
//! every addressing mode and the block transfers, the branches with their
//! change of instruction set (`bx`, `blx`, a load into `pc`), the `IT`
//! blocks and every instruction's condition, the bit operations, and the
//! scalar VFP arithmetic, moves, compares and conversions. Every other
//! instruction stops the run with [`Stop::Unmodeled`] and its text.
//!
//! A run starts with zeroed registers, the stack pointer at a scratch
//! stack and the link register at an address nothing maps, so the
//! routine's own return ends it as [`Stop::Returned`]. The instruction set
//! of the code a run enters is the program's ([`Program::modes`]); a
//! `svc #0` with `r7` 1 or 248 (Linux `exit`, `exit_group`) ends the run.
//!
//! The decompiler's checks run a block of an instruction under a condition
//! that moves control as the lifter reads it: the instruction runs, its
//! condition tested before it by a check of its own
//! ([`crate::isa::a32::SKIP`]). [`Machine::set_forced`] makes the machine
//! run that way.

use super::store::Store;
use super::{
    HISTORY_MAX, MEMORY_MAX, Run, STACK_BASE_32, STACK_SPAN_32, Stop, Written, image_byte,
};
use crate::isa::Isa;
use crate::isa::a32::{self, Insn, ItState, Mode, Reg, SKIP};
use crate::num::{from_usize, lo8, lo32};
use crate::program::Program;

mod exec;
mod fpu;

/// What the link register holds when a run starts: an address no image,
/// stack or allocation takes, so a transfer to it is the routine returning
/// to its caller.
const RETURN_TO: u64 = 0xfffe_f000;

/// The Linux call numbers of `exit` and `exit_group` under the EABI.
const EXIT_CALLS: [u32; 2] = [1, 248];

/// The Linux call number of `write`, which returns its count.
const WRITE_CALL: u32 = 4;

/// The register a Linux EABI system call takes its number in, `r7`.
const SYSCALL_NR: usize = 7;

/// A word: the mask of an address or a register.
const WORD: u64 = 0xffff_ffff;

/// A register an experiment names as text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Named {
    /// A core register, `r0` to `r14`.
    Core(usize),
    /// A single, `s0` to `s31`.
    Single(u8),
    /// A double, `d0` to `d31`.
    Double(u8),
    /// The flags, as the APSR holds them in bits 28 to 31.
    Nzcv,
    /// `FPSCR`.
    Fpscr,
}

impl Named {
    /// Reads a register name.
    ///
    /// # Arguments
    ///
    /// * `name` - `r0`..`r14`, `sp`, `lr`, `fp`, `ip`, `s0`..`s31`,
    ///   `d0`..`d31`, `nzcv` or `fpscr`, lowercase.
    ///
    /// # Returns
    ///
    /// The register, or `None` for any other text.
    fn parse(name: &str) -> Option<Named> {
        let numbered = |digits: &str, below: u8| {
            let canonical = digits.bytes().all(|b| b.is_ascii_digit())
                && (digits == "0" || !digits.starts_with('0'));
            digits
                .parse::<u8>()
                .ok()
                .filter(|&n| canonical && n < below)
        };
        Some(match name {
            "sp" => Named::Core(13),
            "lr" => Named::Core(14),
            "fp" => Named::Core(11),
            "ip" => Named::Core(12),
            "nzcv" => Named::Nzcv,
            "fpscr" => Named::Fpscr,
            _ => {
                if let Some(n) = name.strip_prefix('r').and_then(|d| numbered(d, 15)) {
                    Named::Core(usize::from(n))
                } else if let Some(n) = name.strip_prefix('s').and_then(|d| numbered(d, 32)) {
                    Named::Single(n)
                } else {
                    Named::Double(name.strip_prefix('d').and_then(|d| numbered(d, 32))?)
                }
            }
        })
    }
}

/// A step-bounded ARM32 machine over one program image.
///
/// A clone is a separate machine over the same image.
#[derive(Debug, Clone)]
pub struct Machine<'a> {
    /// The image whose bytes back memory the routine has not written.
    program: &'a Program,
    /// The core registers `r0` to `r14`; `r15` is [`Machine::pc`].
    r: [u32; 15],
    /// The address of the instruction executing, or the next to execute.
    pc: u64,
    /// Whether the machine is in T32.
    thumb: bool,
    /// The negative flag.
    n: bool,
    /// The zero flag.
    z: bool,
    /// The carry flag: set by an add that carries out and by a subtract
    /// that does not borrow.
    c: bool,
    /// The signed overflow flag.
    v: bool,
    /// The `IT` state.
    it: ItState,
    /// The VFP registers `d0` to `d31`; `s(2n)` is the low half of `dn`
    /// and `s(2n+1)` the high half.
    d: [u64; 32],
    /// `FPSCR`: the floating-point flags in bits 28 to 31.
    fpscr: u32,
    /// Memory the routine wrote, over the image's own bytes.
    mem: Store,
    /// What a load of memory nothing backs reads: [`super::fill_byte`] of this
    /// seed, or a fault when `None`.
    fill: Option<u64>,
    /// Steps a run may take.
    budget: usize,
    /// Steps the current run has taken, one per instruction.
    steps: usize,
    /// An address the run halts at before executing it; one tagged
    /// [`SKIP`] halts at the address it tags.
    stop_at: Option<u64>,
    /// Bytes written, in order, up to [`HISTORY_MAX`].
    history: Vec<Written>,
    /// The address of the last instruction the run decoded.
    last_ip: u64,
    /// Whether an instruction under a condition that moves control runs
    /// whatever its condition ([`Machine::set_forced`]).
    forced: bool,
}

impl<'a> Machine<'a> {
    /// Builds a machine over `program` with a step budget.
    ///
    /// # Arguments
    ///
    /// * `program` - The image whose bytes back unwritten memory.
    /// * `budget` - Most instructions to run before stopping.
    ///
    /// # Returns
    ///
    /// A machine with zeroed registers and flags, the stack pointer at the
    /// scratch stack and the link register at the return sentinel, or
    /// `None` when the image is not ARM32 code.
    #[must_use]
    pub fn new(program: &'a Program, budget: usize) -> Option<Self> {
        if program.arch.isa() != Some(Isa::A32) {
            return None;
        }
        let mut r = [0; 15];
        r[13] = lo32(STACK_BASE_32);
        r[14] = lo32(RETURN_TO);
        Some(Self {
            program,
            r,
            pc: 0,
            thumb: false,
            n: false,
            z: false,
            c: false,
            v: false,
            it: ItState::default(),
            d: [0; 32],
            fpscr: 0,
            mem: Store::default(),
            fill: None,
            budget,
            steps: 0,
            stop_at: None,
            history: Vec::new(),
            last_ip: 0,
            forced: false,
        })
    }

    /// Makes an instruction under a condition that moves control (a
    /// conditional return, call or jump through a register) run whatever
    /// its condition, as the decompiler's blocks read it once the check
    /// in front of it ([`SKIP`]) let control reach it, and makes a run
    /// that starts at an instruction under a condition start with flags
    /// under which it holds: such a run is one of those blocks, the run of
    /// instructions under the condition before the one that moves control.
    /// Every other instruction keeps its condition.
    ///
    /// # Arguments
    ///
    /// * `on` - Whether to run that way.
    pub fn set_forced(&mut self, on: bool) {
        self.forced = on;
    }

    /// Sets an argument where the procedure call standard puts it: `r0` to
    /// `r3`, then the stack, a word each from the stack pointer up.
    ///
    /// # Arguments
    ///
    /// * `index` - Argument position, from zero.
    /// * `value` - The value; its low 32 bits are used.
    pub fn set_arg(&mut self, index: usize, value: u64) {
        if let Some(r) = self.r.get_mut(index).filter(|_| index < 4) {
            *r = lo32(value);
            return;
        }
        let slot = u64::from(self.r[13]).wrapping_add(from_usize(index - 4).wrapping_mul(4));
        for k in 0..4 {
            self.mem
                .set(slot.wrapping_add(k) & WORD, lo8(value >> (k * 8)), false);
        }
    }

    /// Sets a register named as text.
    ///
    /// # Arguments
    ///
    /// * `name` - A name [`Named::parse`] reads.
    /// * `value` - The value; a core register or single keeps its low 32
    ///   bits.
    ///
    /// # Returns
    ///
    /// Whether the name was a register this sets.
    pub fn set_register(&mut self, name: &str, value: u64) -> bool {
        let Some(named) = Named::parse(name) else {
            return false;
        };
        match named {
            Named::Core(n) => {
                if let Some(r) = self.r.get_mut(n) {
                    *r = lo32(value);
                }
            }
            Named::Single(n) => self.set_single(n, lo32(value)),
            Named::Double(n) => self.set_double(n, value),
            Named::Nzcv => self.set_nzcv(lo32(value)),
            Named::Fpscr => self.fpscr = lo32(value),
        }
        true
    }

    /// Reads a register named as text.
    ///
    /// # Arguments
    ///
    /// * `name` - A name [`Machine::set_register`] takes.
    ///
    /// # Returns
    ///
    /// Its value, or `None` for a name that is no register.
    #[must_use]
    pub fn register(&self, name: &str) -> Option<u64> {
        Some(match Named::parse(name)? {
            Named::Core(n) => u64::from(*self.r.get(n)?),
            Named::Single(n) => u64::from(self.single(n)),
            Named::Double(n) => self.double(n),
            Named::Nzcv => u64::from(self.nzcv()),
            Named::Fpscr => u64::from(self.fpscr),
        })
    }

    /// Every core register after a run, `r0` first and `sp` and `lr` last.
    #[must_use]
    pub fn registers(&self) -> Vec<(String, u64)> {
        (0u8..15)
            .map(|n| (a32::name(Reg::R(n)), u64::from(self.r[usize::from(n)])))
            .collect()
    }

    /// The thirty-two doubles after a run, `d0` first.
    #[must_use]
    pub fn doubles(&self) -> [u64; 32] {
        self.d
    }

    /// Sets the address the next run halts at before executing it.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address, or `None` to run to the end.
    pub fn stop_at(&mut self, addr: Option<u64>) {
        self.stop_at = addr;
    }

    /// Raises or lowers the step budget before a run.
    ///
    /// # Arguments
    ///
    /// * `budget` - The new instruction cap.
    pub fn set_budget(&mut self, budget: usize) {
        self.budget = budget;
    }

    /// Writes a byte into memory before a run, not counted as written by
    /// the routine.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `value` - The byte.
    pub fn poke(&mut self, addr: u64, value: u8) {
        self.mem.set(addr & WORD, value, false);
    }

    /// Reads a byte as an instruction fetch reads it: written, else the
    /// image's.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    ///
    /// # Returns
    ///
    /// The byte, or `None` where nothing backs it.
    #[must_use]
    pub fn byte_at(&self, addr: u64) -> Option<u8> {
        self.mem
            .get(addr)
            .or_else(|| image_byte(self.program, addr))
    }

    /// Makes a load of memory nothing backs read [`super::fill_byte`] of a seed
    /// instead of faulting.
    ///
    /// # Arguments
    ///
    /// * `seed` - The fill seed, or `None` to fault.
    pub fn set_fill(&mut self, seed: Option<u64>) {
        self.fill = seed;
    }

    /// The address the machine executes next: where a run stopped.
    #[must_use]
    pub fn pc(&self) -> u64 {
        self.pc
    }

    /// The address of the last instruction the run decoded.
    #[must_use]
    pub fn last_ip(&self) -> u64 {
        self.last_ip
    }

    /// Runs from `entry` until it returns, exhausts the budget, or stops.
    ///
    /// An entry tagged [`SKIP`] first tests the condition of the
    /// instruction at the address it tags, as one step: control goes on to
    /// that instruction when the condition holds and past it when not.
    ///
    /// # Arguments
    ///
    /// * `entry` - The routine's first instruction.
    ///
    /// # Returns
    ///
    /// The stop reason, the step count, how many bytes memory holds below
    /// the stack, and the bytes written in order.
    pub fn run(&mut self, entry: u64) -> Run {
        let tagged = entry & SKIP != 0;
        self.pc = (entry & !SKIP) & WORD & !1;
        self.thumb = self.program.modes.at(self.pc) == Mode::Thumb || entry & 1 == 1;
        self.steps = 0;
        if self.forced && !tagged {
            let saved = self.it;
            if let Some(first) = self.fetch(self.pc).filter(Insn::predicated) {
                self.set_nzcv(satisfying(first.cond));
            }
            self.it = saved;
        }
        let mut skip = tagged;
        let stop = loop {
            let pc = self.pc;
            if !skip
                && let Some(at) = self.stop_at
                && (at == pc || (at & SKIP != 0 && at & !SKIP == pc))
            {
                break Stop::Stopped(at);
            }
            if self.steps >= self.budget {
                break Stop::Budget;
            }
            if on_stack(pc) {
                break Stop::Derailed(pc);
            }
            let it = self.it;
            let Some(insn) = self.fetch(pc) else {
                break Stop::Fault(pc);
            };
            self.last_ip = pc;
            self.steps += 1;
            if skip {
                skip = false;
                if self.holds(insn.cond) {
                    self.it = it;
                } else {
                    self.pc = self.past_run(&insn);
                }
                continue;
            }
            let outcome = if self.runs(&insn) {
                self.step(&insn)
            } else {
                Ok(None)
            };
            match outcome {
                Ok(Some(next)) => self.pc = next,
                Ok(None) => self.pc = insn.next(),
                Err(stop) => break stop,
            }
        };
        Run {
            stop,
            steps: self.steps,
            written: self
                .mem
                .held_below(STACK_BASE_32.wrapping_sub(STACK_SPAN_32)),
            history: std::mem::take(&mut self.history),
        }
    }

    /// The address past the run of instructions under one condition a
    /// test tagged [`SKIP`] stands in front of, when the condition fails:
    /// past every instruction under it, up to and including the first that
    /// moves control. Each is skipped as its failing condition skips it.
    ///
    /// # Arguments
    ///
    /// * `first` - The run's first instruction, already decoded.
    fn past_run(&mut self, first: &Insn) -> u64 {
        let mut at = first.next();
        if first.flow() != a32::Flow::Next {
            return at;
        }
        for _ in 0..a32::RUN_MAX {
            let it = self.it;
            let Some(i) = self
                .fetch(at)
                .filter(|i| i.predicated() && i.cond == first.cond)
            else {
                self.it = it;
                break;
            };
            at = i.next();
            if i.flow() != a32::Flow::Next {
                break;
            }
        }
        at
    }

    /// Decodes the instruction at `pc` in the machine's instruction set,
    /// advancing the `IT` state past it.
    ///
    /// # Arguments
    ///
    /// * `pc` - The address.
    ///
    /// # Returns
    ///
    /// The instruction, or `None` when a byte of it is unbacked or `pc` is
    /// misaligned.
    fn fetch(&mut self, pc: u64) -> Option<Insn> {
        let mut bytes = [0u8; 4];
        let mut got = 0;
        for (k, b) in (0..).zip(bytes.iter_mut()) {
            match self.byte_at(pc.wrapping_add(k)) {
                Some(v) => {
                    *b = v;
                    got += 1;
                }
                None => break,
            }
        }
        let mode = if self.thumb { Mode::Thumb } else { Mode::Arm };
        a32::decode(bytes.get(..got)?, pc, mode, &mut self.it)
    }
}

/// Whether `addr` is in the scratch stack.
///
/// # Arguments
///
/// * `addr` - The address.
fn on_stack(addr: u64) -> bool {
    addr >= STACK_BASE_32.wrapping_sub(STACK_SPAN_32) && addr < STACK_BASE_32.wrapping_add(0x1000)
}

/// Flags under which a condition holds, as the APSR holds them in bits 28
/// to 31.
///
/// # Arguments
///
/// * `c` - The condition.
fn satisfying(c: a32::Cond) -> u32 {
    use a32::Cond;
    /// The N flag.
    const N: u32 = 1 << 31;
    /// The Z flag.
    const Z: u32 = 1 << 30;
    /// The C flag.
    const C: u32 = 1 << 29;
    /// The V flag.
    const V: u32 = 1 << 28;
    match c {
        Cond::Eq | Cond::Le | Cond::Ls => Z,
        Cond::Hs | Cond::Hi => C,
        Cond::Mi | Cond::Lt => N,
        Cond::Vs => V,
        Cond::Ne | Cond::Lo | Cond::Pl | Cond::Vc | Cond::Ge | Cond::Gt | Cond::Al | Cond::Nv => 0,
    }
}
