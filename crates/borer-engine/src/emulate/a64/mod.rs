//! A bounded AArch64 emulator for self-contained transforms.
//!
//! The arm64 counterpart of [`super::Emulator`], for the same job: run the
//! small routines that decrypt or unpack data, so their output is read
//! rather than guessed. It shares the x86 machine's memory overlay, stop
//! reasons ([`Stop`]), run report ([`Run`]), caps ([`super::MEMORY_MAX`],
//! [`TRACE_MAX`]) and method names, and models the integer, bitfield,
//! multiply and divide, conditional, memory and branch instructions such
//! routines use ([`alu`], [`mem`]), with the scalar vector moves a compiler
//! puts around them. Every other instruction stops the run with
//! [`Stop::Unmodeled`] and its text: the machine never guesses what an
//! instruction does.
//!
//! A run starts with zeroed registers, the stack pointer at a scratch stack
//! and the link register at an address nothing maps, so the routine's own
//! `ret` ends it as [`Stop::Returned`]. Pointer authentication is the
//! identity (`retaa` returns, `ldraa` loads, `pacia` leaves its register as
//! it is), a store-exclusive always succeeds, an atomic is one load and one
//! store, and `svc #0` with `x8` 93 or 94 (Linux `exit`, `exit_group`) ends
//! the run as [`Stop::Exited`].

use std::collections::VecDeque;

use super::store::Store;
use super::{
    Run, STACK_BASE, STACK_SPAN, Stop, TRACE_MAX, fill_byte, image_byte, lo64, mask, rotate_right,
    sign_extend,
};
use crate::isa::Isa;
use crate::isa::a64::{self, Cond, Insn, Mnemonic, Op, Opnd, Reg};
use crate::num::{from_usize, lo8, lo32, sext32};
use crate::program::Program;
use alu::{Form, Wide};

mod alu;
mod mem;

/// What the link register holds when a run starts: an address no image,
/// stack or allocation takes, so a transfer to it is the routine returning
/// to its caller.
const RETURN_TO: u64 = 0x7fff_ffff_f000;

/// Arguments the procedure call standard passes in registers, `x0` to
/// `x7`; the rest go on the stack.
const ARG_REGS: usize = 8;

/// The stack slot of one stack-passed argument, in bytes.
const ARG_SLOT: u64 = 8;

/// The register number of the link register, `x30`.
const LINK: u8 = 30;

/// The register number of the frame pointer, `x29`.
const FRAME: u8 = 29;

/// The low byte of each halfword, for swapping the bytes of each.
const HALF_LOW_BYTES: u64 = 0x00ff_00ff_00ff_00ff;

/// The register `x8`, which holds the call number at a Linux `svc #0`.
const SYSCALL_NR: usize = 8;

/// The Linux arm64 call numbers of `exit` and `exit_group`, which never
/// return.
// SPEC: Linux include/uapi/asm-generic/unistd.h, __NR_exit 93 and __NR_exit_group 94.
const EXIT_CALLS: [u64; 2] = [93, 94];

/// The system register field (bits 5 to 20) of `TPIDR_EL0`, the thread
/// pointer: `op0` 3, `op1` 3, `CRn` 13, `CRm` 0, `op2` 2.
const SYSREG_TPIDR_EL0: u32 = 0xde82;

/// The system register field of `NZCV`, the condition flags: `op0` 3,
/// `op1` 3, `CRn` 4, `CRm` 2, `op2` 0.
const SYSREG_NZCV: u32 = 0xda10;

/// The names [`Machine::registers`] reports, in register order: the
/// argument and result registers first, the stack pointer last.
const REG_NAMES: [&str; 32] = [
    "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14",
    "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27",
    "x28", "x29", "x30", "sp",
];

/// A register an experiment names as text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Named {
    /// A general register or the stack pointer, at the width the name
    /// reads it: 64 for `x`, 32 for `w`.
    Reg(Reg, u16),
    /// The condition flags, as `NZCV` holds them in bits 28 to 31.
    Nzcv,
    /// The thread pointer `TPIDR_EL0`.
    Tpidr,
}

impl Named {
    /// Reads a register name.
    ///
    /// # Arguments
    ///
    /// * `name` - `x0`..`x30`, `w0`..`w30`, `fp`, `lr`, `sp`, `wsp`, `nzcv`
    ///   or `tpidr_el0`, lowercase.
    ///
    /// # Returns
    ///
    /// The register, or `None` for any other text.
    fn parse(name: &str) -> Option<Named> {
        let numbered = |digits: &str| {
            let canonical = digits.bytes().all(|b| b.is_ascii_digit())
                && (digits == "0" || !digits.starts_with('0'));
            digits
                .parse::<u8>()
                .ok()
                .filter(|&n| canonical && n <= LINK)
        };
        Some(match name {
            "sp" => Named::Reg(Reg::Sp, 64),
            "wsp" => Named::Reg(Reg::Sp, 32),
            "fp" => Named::Reg(Reg::X(FRAME), 64),
            "lr" => Named::Reg(Reg::X(LINK), 64),
            "nzcv" => Named::Nzcv,
            "tpidr_el0" => Named::Tpidr,
            _ => {
                if let Some(n) = name.strip_prefix('x').and_then(numbered) {
                    Named::Reg(Reg::X(n), 64)
                } else {
                    Named::Reg(Reg::X(name.strip_prefix('w').and_then(numbered)?), 32)
                }
            }
        })
    }
}

/// The registers and flags before one traced instruction, for naming what
/// it changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Snapshot {
    /// `x0`..`x30`.
    x: [u64; 31],
    /// The stack pointer.
    sp: u64,
    /// The flags, as `NZCV` holds them.
    nzcv: u64,
}

/// A step-bounded AArch64 machine over one program image.
///
/// A clone is a separate machine over the same image, as with
/// [`super::Emulator`].
#[derive(Debug, Clone)]
pub struct Machine<'a> {
    /// The image whose bytes back memory the routine has not written.
    program: &'a Program,
    /// The general registers `x0`..`x30`; a `w` write zero-extends into
    /// its `x` register.
    x: [u64; 31],
    /// The stack pointer.
    sp: u64,
    /// The address of the instruction executing, or the next to execute.
    pc: u64,
    /// The negative flag.
    n: bool,
    /// The zero flag.
    z: bool,
    /// The carry flag: set by an add that carries out and by a subtract
    /// that does not borrow.
    c: bool,
    /// The signed overflow flag.
    v: bool,
    /// The SIMD and floating-point registers `v0`..`v31`; a scalar write
    /// clears the bits above it.
    vregs: [u128; 32],
    /// The thread pointer, `TPIDR_EL0`.
    tpidr: u64,
    /// Memory the routine wrote, over the image's own bytes, and which of
    /// those bytes it wrote outside the stack.
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
    /// How many trailing instructions the trace keeps; zero traces nothing.
    trace_cap: usize,
    /// One line per traced instruction: where, what, and what it changed.
    trace: VecDeque<String>,
    /// The loads and stores of the step now running, while tracing, as
    /// `(stored, address, width in bytes, value)`.
    step_memory: Vec<(bool, u64, usize, u128)>,
    /// Bytes written, in order, up to [`super::HISTORY_MAX`].
    history: Vec<super::Written>,
    /// The address of the last instruction the run decoded.
    last_ip: u64,
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
    /// `None` when the image is not arm64 code.
    #[must_use]
    pub fn new(program: &'a Program, budget: usize) -> Option<Self> {
        if program.arch.isa() != Some(Isa::A64) {
            return None;
        }
        let mut x = [0; 31];
        if let Some(lr) = x.get_mut(usize::from(LINK)) {
            *lr = RETURN_TO;
        }
        Some(Self {
            program,
            x,
            sp: STACK_BASE,
            pc: 0,
            n: false,
            z: false,
            c: false,
            v: false,
            vregs: [0; 32],
            tpidr: 0,
            mem: Store::default(),
            fill: None,
            budget,
            steps: 0,
            stop_at: None,
            trace_cap: 0,
            trace: VecDeque::new(),
            step_memory: Vec::new(),
            history: Vec::new(),
            last_ip: 0,
        })
    }

    /// Sets an argument where the procedure call standard puts it.
    ///
    /// The first eight integer arguments live in `x0`..`x7`; the rest are
    /// on the stack, eight bytes each from the stack pointer the callee is
    /// entered with. A stack write is setup, not something the code did,
    /// so it stays out of the write history.
    ///
    /// # Arguments
    ///
    /// * `index` - Argument position, from zero.
    /// * `value` - The value.
    pub fn set_arg(&mut self, index: usize, value: u64) {
        if index < ARG_REGS {
            if let Some(r) = self.x.get_mut(index) {
                *r = value;
            }
            return;
        }
        let slot = self
            .sp
            .wrapping_add(from_usize(index - ARG_REGS).wrapping_mul(ARG_SLOT));
        for k in 0..ARG_SLOT {
            self.mem
                .set(slot.wrapping_add(k), lo8(value >> (k * 8)), false);
        }
    }

    /// Sets a register named as text.
    ///
    /// # Arguments
    ///
    /// * `name` - `x0`..`x30`, `w0`..`w30` (zero-extended, as a `w` write
    ///   is), `fp`, `lr`, `sp`, `wsp`, `nzcv` (the flags in bits 28 to 31)
    ///   or `tpidr_el0`.
    /// * `value` - The value.
    ///
    /// # Returns
    ///
    /// Whether the name was a register this sets; a caller reports a
    /// `false` rather than run, since a misspelled name would otherwise
    /// read as a setting that was applied.
    pub fn set_register(&mut self, name: &str, value: u64) -> bool {
        let Some(named) = Named::parse(name) else {
            return false;
        };
        match named {
            Named::Reg(reg, bits) => self.set_reg(reg, bits, u128::from(value)),
            Named::Nzcv => self.set_nzcv(value),
            Named::Tpidr => self.tpidr = value,
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
    /// Its value, a `w` name's the low 32 bits, or `None` for a name that
    /// is no register.
    #[must_use]
    pub fn register(&self, name: &str) -> Option<u64> {
        Some(match Named::parse(name)? {
            Named::Reg(reg, bits) => lo64(mask_wide(self.reg(reg), bits)),
            Named::Nzcv => self.nzcv(),
            Named::Tpidr => self.tpidr,
        })
    }

    /// Every general register after a run, `x0` first and `sp` last.
    ///
    /// # Returns
    ///
    /// `(name, value)` for each of `x0`..`x30` and `sp`.
    #[must_use]
    pub fn registers(&self) -> Vec<(&'static str, u64)> {
        REG_NAMES
            .iter()
            .zip(self.x.iter().chain(std::iter::once(&self.sp)))
            .map(|(name, v)| (*name, *v))
            .collect()
    }

    /// The thirty-two SIMD and floating-point registers after a run, `v0`
    /// first.
    #[must_use]
    pub fn vregs(&self) -> [u128; 32] {
        self.vregs
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

    /// Records the effect of each of the last `steps` instructions, as
    /// [`super::Emulator::set_trace`] does.
    ///
    /// # Arguments
    ///
    /// * `steps` - How many trailing instructions to keep, held to
    ///   [`TRACE_MAX`]; zero turns it off.
    pub fn set_trace(&mut self, steps: usize) {
        self.trace_cap = steps.min(TRACE_MAX);
        self.trace.clear();
    }

    /// The traced instructions, the run's last, in the order they ran.
    #[must_use]
    pub fn trace(&self) -> Vec<String> {
        self.trace.iter().cloned().collect()
    }

    /// Writes a byte into memory before a run: data to a load, code to a
    /// fetch, and not counted as written by the routine.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `value` - The byte.
    pub fn poke(&mut self, addr: u64, value: u8) {
        self.mem.set(addr, value, false);
    }

    /// Reads a byte the routine or a [`Machine::poke`] wrote.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    ///
    /// # Returns
    ///
    /// The byte, or `None` when nothing was written there.
    #[must_use]
    pub fn peek(&self, addr: u64) -> Option<u8> {
        self.mem.get(addr)
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
    /// instead of faulting, as the x86 machine's permissive fill does: a
    /// hash of the address, so a load at a wrong offset reads a different
    /// value. Instruction fetches still fault there.
    ///
    /// # Arguments
    ///
    /// * `seed` - The fill seed, or `None` to fault.
    pub fn set_fill(&mut self, seed: Option<u64>) {
        self.fill = seed;
    }

    /// Reads a byte as a load reads it: written, else the image's, else
    /// the fill.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    ///
    /// # Returns
    ///
    /// The byte, or `None` where the load faults.
    fn load_byte(&self, addr: u64) -> Option<u8> {
        self.byte_at(addr)
            .or_else(|| self.fill.map(|seed| fill_byte(seed, addr)))
    }

    /// Reads up to `n` bytes at `va` as the run sees them, stopping at the
    /// first byte nothing backs.
    ///
    /// # Arguments
    ///
    /// * `va` - The first address.
    /// * `n` - Most bytes to return.
    #[must_use]
    pub fn code_at(&self, va: u64, n: usize) -> Vec<u8> {
        (0..from_usize(n))
            .map_while(|k| self.byte_at(va.wrapping_add(k)))
            .collect()
    }

    /// The address of the last instruction the run decoded: where it
    /// stopped, or the transfer to a faulting address.
    #[must_use]
    pub fn last_ip(&self) -> u64 {
        self.last_ip
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
        self.pc = entry;
        self.steps = 0;
        let stop = loop {
            let pc = self.pc;
            if self.stop_at == Some(pc) {
                break Stop::Stopped(pc);
            }
            if self.steps >= self.budget {
                break Stop::Budget;
            }
            if on_stack(pc) {
                break Stop::Derailed(pc);
            }
            let Some(word) = self.fetch(pc) else {
                break Stop::Fault(pc);
            };
            let insn = a64::decode(word, pc);
            self.last_ip = pc;
            self.steps += 1;
            let before = (self.trace_cap > 0).then(|| self.snapshot());
            self.step_memory.clear();
            let outcome = self.step(&insn);
            if let Some(before) = before {
                self.record(&insn, &before, &outcome);
            }
            match outcome {
                Ok(Some(next)) => self.pc = next,
                Ok(None) => self.pc = pc.wrapping_add(from_usize(a64::INSN_LEN)),
                Err(stop) => break stop,
            }
        };
        Run {
            stop,
            steps: self.steps,
            written: self.mem.held_below(STACK_BASE),
            history: std::mem::take(&mut self.history),
        }
    }

    /// Reads the instruction word at `pc`.
    ///
    /// # Arguments
    ///
    /// * `pc` - The address.
    ///
    /// # Returns
    ///
    /// The little-endian word, or `None` when `pc` is not four-byte
    /// aligned (a PC alignment fault) or a byte of it is unbacked.
    fn fetch(&self, pc: u64) -> Option<u32> {
        if !pc.is_multiple_of(from_usize(a64::INSN_LEN)) {
            return None;
        }
        let mut bytes = [0; a64::INSN_LEN];
        for (k, b) in (0..).zip(bytes.iter_mut()) {
            *b = self.byte_at(pc.wrapping_add(k))?;
        }
        Some(u32::from_le_bytes(bytes))
    }

    /// Executes one instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// `Ok(Some(target))` for a taken branch, `Ok(None)` to fall through.
    ///
    /// # Errors
    ///
    /// The [`Stop`] that ends the run: a return to the caller, an exit, an
    /// instruction the machine does not model, or a fault.
    fn step(&mut self, i: &Insn) -> Result<Option<u64>, Stop> {
        match i.op {
            Op::B | Op::Bl => {
                let to = i.target().ok_or_else(|| unmodeled(i))?;
                if i.op == Op::Bl {
                    self.link(i);
                }
                transfer(to)
            }
            Op::BCond(cond) => branch_if(i, self.holds(cond)),
            Op::Cbz | Op::Cbnz => {
                let zero = self.int(i, 0)? == 0;
                branch_if(i, zero == (i.op == Op::Cbz))
            }
            Op::Tbz | Op::Tbnz => {
                let bit = self.int(i, 1)?;
                let set = self.int(i, 0)?.checked_shr(lo32_count(bit)).unwrap_or(0) & 1 == 1;
                branch_if(i, set == (i.op == Op::Tbnz))
            }
            Op::Br | Op::Blr => {
                let to = self.int(i, 0)?;
                if i.op == Op::Blr {
                    self.link(i);
                }
                transfer(to)
            }
            Op::Ret => {
                let to = match i.operands[0] {
                    Opnd::Reg { .. } => self.int(i, 0)?,
                    Opnd::None
                    | Opnd::Shifted { .. }
                    | Opnd::Imm(_)
                    | Opnd::PcRel(_)
                    | Opnd::Mem(_)
                    | Opnd::Cond(_)
                    | Opnd::Other => self.x.get(usize::from(LINK)).copied().unwrap_or(0),
                };
                transfer(to)
            }
            Op::Adr | Op::Adrp => {
                let (Opnd::Reg { reg, bits }, Opnd::PcRel(at)) = (i.operands[0], i.operands[1])
                else {
                    return Err(unmodeled(i));
                };
                self.set_reg(reg, bits, u128::from(at));
                Ok(None)
            }
            Op::Syscall => self.syscall(i),
            Op::Nop | Op::Bti | Op::Pac => Ok(None),
            Op::Invalid => {
                let executable = self.program.section_at(i.va).is_some_and(|s| s.executable);
                Err(if executable {
                    Stop::Unmodeled(format!("bad opcode at {:#x}", i.va))
                } else {
                    Stop::Fault(i.va)
                })
            }
            Op::Eret | Op::Trap | Op::Sve | Op::Sme => Err(unmodeled(i)),
            Op::Other => self.compute(i),
        }
    }

    /// Executes an instruction that does not move control, by what it
    /// computes: the one table from base instruction to the handler that
    /// models it ([`alu`], [`mem`]).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// `Ok(None)`: execution falls through.
    ///
    /// # Errors
    ///
    /// When the instruction or one of its operands is not modeled, or a
    /// memory access faults.
    fn compute(&mut self, i: &Insn) -> Result<Option<u64>, Stop> {
        match i.mnemonic {
            Mnemonic::Movz => self.move_wide(i, Wide::Zero),
            Mnemonic::Movn => self.move_wide(i, Wide::Not),
            Mnemonic::Movk => self.move_wide(i, Wide::Keep),
            Mnemonic::Add => self.arith(i, Form::Add, false),
            Mnemonic::Adds => self.arith(i, Form::Add, true),
            Mnemonic::Sub => self.arith(i, Form::Sub, false),
            Mnemonic::Subs => self.arith(i, Form::Sub, true),
            Mnemonic::Adc => self.arith(i, Form::Adc, false),
            Mnemonic::Adcs => self.arith(i, Form::Adc, true),
            Mnemonic::Sbc => self.arith(i, Form::Sbc, false),
            Mnemonic::Sbcs => self.arith(i, Form::Sbc, true),
            Mnemonic::And => self.logical(i, |x, y| x & y, false),
            Mnemonic::Ands => self.logical(i, |x, y| x & y, true),
            Mnemonic::Orr => self.logical(i, |x, y| x | y, false),
            Mnemonic::Orn => self.logical(i, |x, y| x | !y, false),
            Mnemonic::Eor => self.logical(i, |x, y| x ^ y, false),
            Mnemonic::Eon => self.logical(i, |x, y| x ^ !y, false),
            Mnemonic::Bic => self.logical(i, |x, y| x & !y, false),
            Mnemonic::Bics => self.logical(i, |x, y| x & !y, true),
            Mnemonic::Ubfm => self.bitfield(i, alu::ubfm),
            Mnemonic::Sbfm => self.bitfield(i, alu::sbfm),
            Mnemonic::Bfm => self.bitfield(i, alu::bfm),
            Mnemonic::Extr => self.extract(i),
            Mnemonic::Lslv => {
                self.binary(i, |x, y, width| mask(x << (y % u64::from(width)), width))
            }
            Mnemonic::Lsrv => self.binary(i, |x, y, width| x >> (y % u64::from(width))),
            Mnemonic::Asrv => self.binary(i, |x, y, width| {
                let by = lo32_count(y % u64::from(width));
                mask((sign_extend(x, width) >> by).cast_unsigned(), width)
            }),
            Mnemonic::Rorv => self.binary(i, |x, y, width| {
                rotate_right(x, lo32_count(y % u64::from(width)), width)
            }),
            Mnemonic::Madd => self.multiply(i, |n, m, a| a.wrapping_add(n.wrapping_mul(m))),
            Mnemonic::Msub => self.multiply(i, |n, m, a| a.wrapping_sub(n.wrapping_mul(m))),
            Mnemonic::Smaddl => self.multiply(i, |n, m, a| {
                a.wrapping_add(sext32(n).wrapping_mul(sext32(m)))
            }),
            Mnemonic::Smsubl => self.multiply(i, |n, m, a| {
                a.wrapping_sub(sext32(n).wrapping_mul(sext32(m)))
            }),
            Mnemonic::Umaddl => self.multiply(i, |n, m, a| a.wrapping_add(n.wrapping_mul(m))),
            Mnemonic::Umsubl => self.multiply(i, |n, m, a| a.wrapping_sub(n.wrapping_mul(m))),
            Mnemonic::Smulh => self.binary(i, |x, y, _| {
                let product = i128::from(x.cast_signed()) * i128::from(y.cast_signed());
                lo64((product >> 64).cast_unsigned())
            }),
            Mnemonic::Umulh => {
                self.binary(i, |x, y, _| lo64((u128::from(x) * u128::from(y)) >> 64))
            }
            Mnemonic::Udiv => self.binary(i, |x, y, _| x.checked_div(y).unwrap_or(0)),
            Mnemonic::Sdiv => self.binary(i, |x, y, width| {
                let (x, y) = (sign_extend(x, width), sign_extend(y, width));
                if y == 0 {
                    0
                } else {
                    mask(x.wrapping_div(y).cast_unsigned(), width)
                }
            }),
            Mnemonic::Clz => self.unary(i, |v, width| {
                u64::from(v.leading_zeros().saturating_sub(64 - width))
            }),
            Mnemonic::Cls => self.unary(i, |v, width| {
                let runs = mask(v ^ (v << 1), width) | 1;
                u64::from(runs.leading_zeros().saturating_sub(64 - width))
            }),
            Mnemonic::Rbit => self.unary(i, |v, width| v.reverse_bits() >> (64 - width)),
            Mnemonic::Rev => self.unary(i, |v, width| v.swap_bytes() >> (64 - width)),
            Mnemonic::Rev16 => self.unary(i, |v, width| {
                mask(
                    ((v & HALF_LOW_BYTES) << 8) | ((v >> 8) & HALF_LOW_BYTES),
                    width,
                )
            }),
            Mnemonic::Rev32 => self.unary(i, |v, _| {
                (u64::from(lo32(v >> 32).swap_bytes()) << 32) | u64::from(lo32(v).swap_bytes())
            }),
            Mnemonic::Csel => self.select(i, |m| m),
            Mnemonic::Csinc => self.select(i, |m| m.wrapping_add(1)),
            Mnemonic::Csinv => self.select(i, |m| !m),
            Mnemonic::Csneg => self.select(i, u64::wrapping_neg),
            Mnemonic::Ccmp => self.compare_if(i, Form::Sub),
            Mnemonic::Ccmn => self.compare_if(i, Form::Add),
            Mnemonic::Fmov => self.fmov(i),
            Mnemonic::Movi => self.movi(i, false),
            Mnemonic::Mvni => self.movi(i, true),
            Mnemonic::Ldr(width) => self.load_one(i, width),
            Mnemonic::Str(width) => self.store_one(i, width),
            Mnemonic::Ldp(width) => self.load_pair(i, width),
            Mnemonic::Stp => self.store_pair(i),
            Mnemonic::Stxr(width) => self.store_exclusive(i, width),
            Mnemonic::Stxp => self.store_exclusive_pair(i),
            Mnemonic::Atomic(op, width) => self.atomic(i, op, width),
            Mnemonic::Cas(width) => self.compare_swap(i, width),
            Mnemonic::Prfm | Mnemonic::Barrier => Ok(()),
            Mnemonic::Mrs | Mnemonic::Msr => self.system(i),
            Mnemonic::Svc | Mnemonic::Other => Err(unmodeled(i)),
        }
        .map(|()| None)
    }

    /// `svc #0`: a Linux system call, of which only the two that end the
    /// process are modeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The `svc`, `hvc` or `smc`.
    ///
    /// # Errors
    ///
    /// [`Stop::Exited`] for `exit` and `exit_group`; an unmodeled stop
    /// naming the call for every other call, and for `hvc`, `smc` and an
    /// `svc` with another immediate (Apple's `svc #0x80`).
    fn syscall(&self, i: &Insn) -> Result<Option<u64>, Stop> {
        if i.mnemonic != Mnemonic::Svc || i.operands[0] != Opnd::Imm(0) {
            return Err(unmodeled(i));
        }
        let nr = self.x.get(SYSCALL_NR).copied().unwrap_or(0);
        Err(if EXIT_CALLS.contains(&nr) {
            Stop::Exited
        } else {
            Stop::Unmodeled(format!(
                "{} with x8={nr} (only exit and exit_group are modeled)",
                a64::text(i)
            ))
        })
    }

    /// `mrs` and `msr` of the thread pointer and the flags, the system
    /// registers a user-mode routine reads and writes.
    ///
    /// Both fields are read from the word: the decoder keeps only four
    /// bits of an `msr`'s register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Errors
    ///
    /// When the register is another one, or the `msr` writes a processor
    /// state field by immediate.
    fn system(&mut self, i: &Insn) -> Result<(), Stop> {
        // SPEC: Arm ARM (DDI 0487) C6.2 MRS/MSR (register): Rt is bits 0..4, o0:op1:CRn:CRm:op2 bits 5..19, with bit 20 set.
        let rt = match i.word & 0x1f {
            0x1f => Reg::Zr,
            n => Reg::X(lo8(u64::from(n))),
        };
        let sysreg = (i.word >> 5) & 0xffff;
        let register_form = (i.word >> 20) & 1 == 1;
        let writes = i.mnemonic == Mnemonic::Msr;
        let value = lo64(self.reg(rt));
        match (sysreg, writes) {
            (SYSREG_TPIDR_EL0, false) => self.set_reg(rt, 64, u128::from(self.tpidr)),
            (SYSREG_NZCV, false) => self.set_reg(rt, 64, u128::from(self.nzcv())),
            (SYSREG_TPIDR_EL0, true) if register_form => self.tpidr = value,
            (SYSREG_NZCV, true) if register_form => self.set_nzcv(value),
            _ => return Err(unmodeled(i)),
        }
        Ok(())
    }

    /// Writes the return address of a call, the instruction after it, to
    /// the link register.
    ///
    /// # Arguments
    ///
    /// * `i` - The `bl` or `blr`.
    fn link(&mut self, i: &Insn) {
        if let Some(lr) = self.x.get_mut(usize::from(LINK)) {
            *lr = i.va.wrapping_add(from_usize(a64::INSN_LEN));
        }
    }

    /// Tells whether a condition holds on the flags.
    ///
    /// # Arguments
    ///
    /// * `cond` - The condition.
    fn holds(&self, cond: Cond) -> bool {
        // SPEC: Arm ARM (DDI 0487) J1, ConditionHolds.
        match cond {
            Cond::Eq => self.z,
            Cond::Ne => !self.z,
            Cond::Hs => self.c,
            Cond::Lo => !self.c,
            Cond::Mi => self.n,
            Cond::Pl => !self.n,
            Cond::Vs => self.v,
            Cond::Vc => !self.v,
            Cond::Hi => self.c && !self.z,
            Cond::Ls => !self.c || self.z,
            Cond::Ge => self.n == self.v,
            Cond::Lt => self.n != self.v,
            Cond::Gt => !self.z && self.n == self.v,
            Cond::Le => self.z || self.n != self.v,
            Cond::Al | Cond::Nv => true,
        }
    }

    /// The flags as `NZCV` holds them, in bits 28 to 31.
    fn nzcv(&self) -> u64 {
        (u64::from(self.n) << 31)
            | (u64::from(self.z) << 30)
            | (u64::from(self.c) << 29)
            | (u64::from(self.v) << 28)
    }

    /// Sets the flags from bits 28 to 31 of a value, as `msr nzcv` does.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn set_nzcv(&mut self, v: u64) {
        self.n = (v >> 31) & 1 == 1;
        self.z = (v >> 30) & 1 == 1;
        self.c = (v >> 29) & 1 == 1;
        self.v = (v >> 28) & 1 == 1;
    }

    /// The whole of a register's storage: a general register zero-extended,
    /// a `v` register's 128 bits.
    ///
    /// # Arguments
    ///
    /// * `r` - The register; [`Reg::Zr`] reads zero.
    fn reg(&self, r: Reg) -> u128 {
        match r {
            Reg::X(n) => self.x.get(usize::from(n)).map_or(0, |&v| u128::from(v)),
            Reg::Sp => u128::from(self.sp),
            Reg::Zr => 0,
            Reg::V(n) => self.vregs.get(usize::from(n)).copied().unwrap_or(0),
        }
    }

    /// Writes a register at a width, zero-extending into the rest of it.
    ///
    /// A `w` write clears the upper half of its `x` register, and a scalar
    /// write to a `v` register clears the bits above it, as the
    /// architecture does; a write to [`Reg::Zr`] is discarded.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `bits` - The width written.
    /// * `v` - The value; bits past `bits` are dropped.
    fn set_reg(&mut self, r: Reg, bits: u16, v: u128) {
        let v = mask_wide(v, bits);
        match r {
            Reg::X(n) => {
                if let Some(slot) = self.x.get_mut(usize::from(n)) {
                    *slot = lo64(v);
                }
            }
            Reg::Sp => self.sp = lo64(v),
            Reg::Zr => {}
            Reg::V(n) => {
                if let Some(slot) = self.vregs.get_mut(usize::from(n)) {
                    *slot = v;
                }
            }
        }
    }

    /// Reads a general-register or immediate operand as an integer.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    ///
    /// # Returns
    ///
    /// A register's value at its width, or the immediate.
    ///
    /// # Errors
    ///
    /// When the operand is anything else, a `v` register among them.
    fn int(&self, i: &Insn, k: usize) -> Result<u64, Stop> {
        match i.operands.get(k).copied().unwrap_or(Opnd::None) {
            Opnd::Reg {
                reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
                bits,
            } => Ok(lo64(mask_wide(self.reg(reg), bits))),
            Opnd::Imm(v) => Ok(v),
            Opnd::Reg { .. }
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => Err(unmodeled(i)),
        }
    }

    /// The registers and flags now, for a trace line.
    fn snapshot(&self) -> Snapshot {
        Snapshot {
            x: self.x,
            sp: self.sp,
            nzcv: self.nzcv(),
        }
    }

    /// Adds one trace line: where, what, and what changed.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction that ran.
    /// * `before` - The registers and flags before it.
    /// * `outcome` - What it did.
    fn record(&mut self, i: &Insn, before: &Snapshot, outcome: &Result<Option<u64>, Stop>) {
        let now = self.snapshot();
        let mut changed: Vec<String> = REG_NAMES
            .iter()
            .zip(before.x.iter().chain(std::iter::once(&before.sp)))
            .zip(now.x.iter().chain(std::iter::once(&now.sp)))
            .filter(|((_, was), is)| was != is)
            .map(|((name, _), is)| format!("{name}={is:#x}"))
            .collect();
        if before.nzcv != now.nzcv {
            changed.push(format!("nzcv={:#x}", now.nzcv >> 28));
        }
        changed.extend(self.step_memory.iter().map(|&(stored, at, width, v)| {
            let verb = if stored { "w" } else { "r" };
            format!("{verb}{width}[{at:#x}]={v:#x}")
        }));
        let note = match outcome {
            Ok(_) if changed.is_empty() => String::from("(no register changed)"),
            Ok(_) => changed.join(" "),
            Err(stop) => format!("stopped: {stop}"),
        };
        if self.trace.len() >= self.trace_cap {
            self.trace.pop_front();
        }
        self.trace
            .push_back(format!("{:#x}  {}    {note}", i.va, a64::text(i)));
    }
}

/// Takes a direct branch when `taken`.
///
/// # Arguments
///
/// * `i` - The conditional branch.
/// * `taken` - Whether its condition holds.
///
/// # Errors
///
/// When the branch names no target.
fn branch_if(i: &Insn, taken: bool) -> Result<Option<u64>, Stop> {
    if taken {
        transfer(i.target().ok_or_else(|| unmodeled(i))?)
    } else {
        Ok(None)
    }
}

/// Ends a transfer: at the return sentinel, the routine has returned to
/// its caller.
///
/// # Arguments
///
/// * `to` - Where control goes.
///
/// # Errors
///
/// [`Stop::Returned`] when `to` is the sentinel.
fn transfer(to: u64) -> Result<Option<u64>, Stop> {
    if to == RETURN_TO {
        Err(Stop::Returned)
    } else {
        Ok(Some(to))
    }
}

/// Whether `addr` is in the scratch stack.
///
/// # Arguments
///
/// * `addr` - The address.
fn on_stack(addr: u64) -> bool {
    addr >= STACK_BASE.wrapping_sub(STACK_SPAN) && addr < STACK_BASE.wrapping_add(STACK_SPAN)
}

/// The stop for an instruction the machine does not model, naming it.
///
/// # Arguments
///
/// * `i` - The instruction.
fn unmodeled(i: &Insn) -> Stop {
    Stop::Unmodeled(a64::text(i))
}

/// Masks a value to its low `bits` bits.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - How many low bits to keep; 128 or more keeps them all.
fn mask_wide(v: u128, bits: u16) -> u128 {
    if bits >= 128 {
        v
    } else {
        v & ((1u128 << bits) - 1)
    }
}

/// A shift count as the `u32` the shift methods take, saturating so an
/// out-of-range count shifts everything out.
///
/// # Arguments
///
/// * `n` - The count.
fn lo32_count(n: u64) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}
