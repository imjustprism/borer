//! A bounded RISC-V machine: the RV32 and RV64 integer instructions with
//! the M and A extensions, the compressed forms, and the float loads,
//! stores, moves and sign injections.
//!
//! The RISC-V counterpart of [`super::a32::Machine`], with its memory
//! overlay, stop reasons ([`Stop`]), run report ([`Run`]) and method names.
//! It runs what [`crate::isa::rv`] decodes. Every instruction it does not
//! model (the float arithmetic, compares and conversions, the CSRs, the
//! privileged instructions, `fence.i` aside) stops the run with
//! [`Stop::Unmodeled`] and its text: the machine never guesses what an
//! instruction does.
//!
//! A run starts with zeroed registers, the stack pointer at a scratch
//! stack and `ra` at an address nothing maps, so the routine's own `ret`
//! ends it as [`Stop::Returned`]. An `ecall` with `a7` 93 or 94 (Linux
//! `exit`, `exit_group`) ends the run as [`Stop::Exited`]; `write` (64)
//! returns its count and any other call returns zero. An `lr` reserves
//! nothing and an `sc` always succeeds: one hart, nothing in between.

use super::store::Store;
use super::{
    HISTORY_MAX, MEMORY_MAX, Run, STACK_BASE, STACK_BASE_32, STACK_SPAN, STACK_SPAN_32, Stop,
    Written, fill_byte, image_byte,
};
use crate::isa::Isa;
use crate::isa::rv::{self, Insn, Reg, Xlen};
use crate::num::lo8;
use crate::program::Program;

mod exec;

/// What `ra` holds when a 64-bit run starts: an address no image, stack or
/// allocation takes, so a transfer to it is the routine returning.
const RETURN_TO_64: u64 = 0x7fff_ffff_f000;

/// What `ra` holds when a 32-bit run starts.
const RETURN_TO_32: u64 = 0xfffe_f000;

/// The register a Linux system call takes its number in, `a7`.
const SYSCALL_NR: usize = 17;

/// The Linux call numbers of `exit` and `exit_group`.
const EXIT_CALLS: [u64; 2] = [93, 94];

/// The Linux call number of `write`, which returns its count.
const WRITE_CALL: u64 = 64;

/// A step-bounded RISC-V machine over one program image.
///
/// A clone is a separate machine over the same image.
#[derive(Debug, Clone)]
pub struct Machine<'a> {
    /// The image whose bytes back memory the routine has not written.
    program: &'a Program,
    /// The register width.
    xlen: Xlen,
    /// The integer registers `x0` to `x31`; `x0` stays zero.
    x: [u64; 32],
    /// The float registers `f0` to `f31`, as their 64 bits.
    f: [u64; 32],
    /// The address of the instruction executing, or the next to execute.
    pc: u64,
    /// Memory the routine wrote, over the image's own bytes.
    mem: Store,
    /// What a load of memory nothing backs reads: [`fill_byte`] of this
    /// seed, or a fault when `None`.
    fill: Option<u64>,
    /// Steps a run may take.
    budget: usize,
    /// Steps the current run has taken, one per instruction.
    steps: usize,
    /// An address the run halts at before executing it.
    stop_at: Option<u64>,
    /// Bytes written, in order, up to [`HISTORY_MAX`].
    history: Vec<Written>,
    /// The cancel flag in force where the machine was made, looked at
    /// every [`super::CANCEL_EVERY`] steps.
    cancel: Option<crate::cancel::Cancel>,
}

/// Returns the number of the register a name gives.
///
/// # Arguments
///
/// * `name` - An ABI name (`a0`, `sp`, `fa0`), `fp`, or `x0`..`x31` and
///   `f0`..`f31`.
///
/// # Returns
///
/// The register, or `None` for any other text.
fn parse(name: &str) -> Option<Reg> {
    if name == "fp" {
        return Some(Reg::X(8));
    }
    (0u8..32)
        .flat_map(|n| [Reg::X(n), Reg::F(n)])
        .find(|&r| rv::name(r) == name)
        .or_else(|| {
            let numbered = |digits: &str| {
                digits
                    .parse::<u8>()
                    .ok()
                    .filter(|&n| n < 32 && (digits == "0" || !digits.starts_with('0')))
            };
            match name.split_at_checked(1)? {
                ("x", d) => numbered(d).map(Reg::X),
                ("f", d) => numbered(d).map(Reg::F),
                _ => None,
            }
        })
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
    /// A machine with zeroed registers, the stack pointer at the scratch
    /// stack and `ra` at the return sentinel, or `None` when the image is
    /// not RISC-V code.
    #[must_use]
    pub fn new(program: &'a Program, budget: usize) -> Option<Self> {
        let Some(Isa::Rv(xlen)) = program.arch.isa() else {
            return None;
        };
        let mut x = [0; 32];
        x[1] = return_to(xlen);
        x[2] = stack_base(xlen);
        Some(Self {
            program,
            xlen,
            x,
            f: [0; 32],
            pc: 0,
            mem: Store::default(),
            fill: None,
            budget,
            steps: 0,
            stop_at: None,
            history: Vec::new(),
            cancel: crate::cancel::Cancel::current(),
        })
    }

    /// Sets a register named as text.
    ///
    /// # Arguments
    ///
    /// * `name` - A name [`parse`] reads.
    /// * `value` - The value; an integer register keeps the register
    ///   width's low bits.
    ///
    /// # Returns
    ///
    /// Whether the name was a register this sets.
    pub fn set_register(&mut self, name: &str, value: u64) -> bool {
        match parse(name) {
            Some(Reg::X(n)) => self.set_x(usize::from(n), value),
            Some(Reg::F(n)) => {
                if let Some(f) = self.f.get_mut(usize::from(n)) {
                    *f = value;
                }
            }
            None => return false,
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
        match parse(name)? {
            Reg::X(n) => self.x.get(usize::from(n)).copied(),
            Reg::F(n) => self.f.get(usize::from(n)).copied(),
        }
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
        self.mem.set(self.xlen.addr(addr), value, false);
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

    /// Makes a load of memory nothing backs read [`fill_byte`] of a seed
    /// instead of faulting.
    ///
    /// # Arguments
    ///
    /// * `seed` - The fill seed, or `None` to fault.
    pub fn set_fill(&mut self, seed: Option<u64>) {
        self.fill = seed;
    }

    /// Runs from `entry` until it returns, exhausts the budget, or stops.
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
        self.pc = self.xlen.addr(entry) & !1;
        self.steps = 0;
        let stop = loop {
            let pc = self.pc;
            if self.stop_at == Some(pc) {
                break Stop::Stopped(pc);
            }
            if self.steps >= self.budget {
                break Stop::Budget;
            }
            if self.steps.is_multiple_of(super::CANCEL_EVERY)
                && self
                    .cancel
                    .as_ref()
                    .is_some_and(crate::cancel::Cancel::is_raised)
            {
                break Stop::Limit(super::Limit::Time);
            }
            if self.on_stack(pc) {
                break Stop::Derailed(pc);
            }
            let Some(insn) = self.fetch(pc) else {
                break Stop::Fault(pc);
            };
            self.steps += 1;
            match self.step(&insn) {
                Ok(Some(next)) => self.pc = next,
                Ok(None) => self.pc = self.xlen.addr(insn.next()),
                Err(stop) => break stop,
            }
        };
        let (base, span) = match self.xlen {
            Xlen::X32 => (STACK_BASE_32, STACK_SPAN_32),
            Xlen::X64 => (STACK_BASE, STACK_SPAN),
        };
        Run {
            stop,
            steps: self.steps,
            written: self.mem.held_below(base.wrapping_sub(span)),
            history: std::mem::take(&mut self.history),
        }
    }

    /// Tells whether `addr` is in the scratch stack.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    fn on_stack(&self, addr: u64) -> bool {
        let (base, span) = match self.xlen {
            Xlen::X32 => (STACK_BASE_32, STACK_SPAN_32),
            Xlen::X64 => (STACK_BASE, STACK_SPAN),
        };
        addr >= base.wrapping_sub(span) && addr < base.wrapping_add(0x1000)
    }

    /// Decodes the instruction at `pc`.
    ///
    /// # Arguments
    ///
    /// * `pc` - The address.
    ///
    /// # Returns
    ///
    /// The instruction, or `None` when a byte of it is unbacked.
    fn fetch(&self, pc: u64) -> Option<Insn> {
        let mut bytes = [0u8; 4];
        let mut got = 0;
        for (k, b) in (0..).zip(bytes.iter_mut()) {
            match self.byte_at(self.xlen.addr(pc.wrapping_add(k))) {
                Some(v) => {
                    *b = v;
                    got += 1;
                }
                None => break,
            }
        }
        rv::decode(bytes.get(..got)?, pc, self.xlen)
    }

    /// Writes an integer register, cut to the register width; a write to
    /// `x0` vanishes.
    ///
    /// # Arguments
    ///
    /// * `n` - The register's number.
    /// * `v` - The value.
    fn set_x(&mut self, n: usize, v: u64) {
        let v = self.xlen.addr(v);
        if let Some(r) = self.x.get_mut(n).filter(|_| n != 0) {
            *r = v;
        }
    }

    /// Runs a system call: `exit` and `exit_group` end the run, `write`
    /// returns its count and every other returns zero.
    ///
    /// # Errors
    ///
    /// [`Stop::Exited`] for `exit` and `exit_group`.
    fn syscall(&mut self) -> Result<Option<u64>, Stop> {
        let nr = self.x[SYSCALL_NR];
        if EXIT_CALLS.contains(&nr) {
            return Err(Stop::Exited);
        }
        let result = if nr == WRITE_CALL { self.x[12] } else { 0 };
        self.set_x(10, result);
        Ok(None)
    }

    /// Reads a byte as a load reads it: written, else the image's, else the
    /// fill.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    fn load_byte(&self, addr: u64) -> Option<u8> {
        self.byte_at(addr)
            .or_else(|| self.fill.map(|seed| fill_byte(seed, addr)))
    }

    /// Loads `bytes` bytes at `addr`, little-endian.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most eight.
    ///
    /// # Errors
    ///
    /// [`Stop::Fault`] at the first byte nothing backs.
    fn load(&self, addr: u64, bytes: u8) -> Result<u64, Stop> {
        let mut v = 0u64;
        for k in 0..bytes {
            let a = self.xlen.addr(addr.wrapping_add(u64::from(k)));
            v |= u64::from(self.load_byte(a).ok_or(Stop::Fault(a))?) << (8 * k);
        }
        Ok(v)
    }

    /// Stores the low `bytes` bytes of `v`, little-endian, recording each
    /// byte in the write history.
    ///
    /// # Arguments
    ///
    /// * `addr` - The first address.
    /// * `bytes` - How many, at most eight.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when memory would grow past its cap.
    fn store(&mut self, addr: u64, bytes: u8, v: u64) -> Result<(), Stop> {
        for k in 0..bytes {
            let a = self.xlen.addr(addr.wrapping_add(u64::from(k)));
            if self.mem.len() >= MEMORY_MAX && !self.mem.contains(a) {
                return Err(Stop::MemoryFull(a));
            }
            let value = lo8(v >> (8 * k));
            if self.history.len() < HISTORY_MAX {
                self.history.push(Written { addr: a, value });
            }
            let dirty = !self.on_stack(a);
            self.mem.set(a, value, dirty);
        }
        Ok(())
    }
}

/// Returns the return sentinel for a register width.
///
/// # Arguments
///
/// * `xlen` - The width.
fn return_to(xlen: Xlen) -> u64 {
    match xlen {
        Xlen::X32 => RETURN_TO_32,
        Xlen::X64 => RETURN_TO_64,
    }
}

/// Returns the scratch stack's top for a register width.
///
/// # Arguments
///
/// * `xlen` - The width.
fn stack_base(xlen: Xlen) -> u64 {
    match xlen {
        Xlen::X32 => STACK_BASE_32,
        Xlen::X64 => STACK_BASE,
    }
}
