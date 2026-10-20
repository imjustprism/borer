//! A bounded x86-64 emulator for self-contained transforms.
//!
//! Its one job is to run the small routines that decrypt or unpack data, so
//! their output can be read statically instead of guessed. It models the
//! integer subset those routines use, keeps a sparse memory overlay on top of
//! the program image, and stops after a step budget, at a return with an
//! empty call stack, or at anything it cannot model. It is deliberately not a
//! full CPU: a routine that calls out, uses vector math, or faults is left to
//! a real debugger.

use crate::isa::x86::{
    Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register, gpr_bank_index,
    st_depth_mod8, xmm_slot,
};
use crate::num::{from_usize, lo8, lo32};
use crate::program::Program;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub mod a32;
pub mod a64;
mod alu;
mod api;
mod bits;
pub mod calls;
mod fpu;
mod loader;
mod operands;
mod sse;
mod store;
mod strops;

use alu::{Alu, Shift};
use api::{ALLOC_BASE, ALLOC_BASE_32, ArgSlot};
use calls::ApiCall;
use fpu::{FPU_TRIG_RANGE, FpuArith};
use sse::Width;
use store::Store;
use strops::StringOp;

/// Most entries each record of a run keeps.
///
/// The records are the API calls and syscalls it serviced (every region
/// its allocator hands out is one's answer, so they are bounded too) and
/// the indirect jumps it took; a run that would record one more stops
/// with [`Stop::Limit`] instead, so a guest loop cannot grow a record past
/// what a context window or the machine holds.
pub const RECORDS_MAX: usize = 1 << 16;

/// What cut a run short before its step budget did.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Limit {
    /// It serviced [`RECORDS_MAX`] imported API calls and syscalls.
    Calls,
    /// It took [`RECORDS_MAX`] indirect jumps.
    Jumps,
}

impl std::fmt::Display for Limit {
    /// Names the record that filled.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Calls => "api call",
            Self::Jumps => "indirect jump",
        })
    }
}

/// How a run ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stop {
    /// A `ret` with nothing left on the call stack.
    Returned,
    /// The step budget ran out.
    Budget,
    /// An instruction the emulator does not model.
    Unmodeled(String),
    /// A read or write of memory that is not mapped and was never written.
    Fault(u64),
    /// A write that would hold more distinct bytes than [`MEMORY_MAX`]: the
    /// first address it could not write.
    MemoryFull(u64),
    /// The instruction pointer reached a requested stop address.
    Stopped(u64),
    /// Execution left the program's code for the scratch stack: a computed
    /// transfer went to an address that is not code, which a protector's VM or
    /// anti-emulation guard produces when the run fed it a value the real
    /// process would have but the emulator cannot.
    Derailed(u64),
    /// A `syscall` for `exit` or `exit_group`: the program asked the kernel
    /// to end it, and the kernel does not return.
    Exited,
    /// A record of the run filled before its step budget ran out.
    Limit(Limit),
}

impl std::fmt::Display for Stop {
    /// Renders the reason in words, with addresses in hex.
    ///
    /// A report reads `fault at 0x7fff00000028 after 12 steps`: the enum's
    /// own syntax (`Fault(0x7fff00000028)`, `Unmodeled("Xgetbv")`) leaked
    /// the type into a sentence, and the derived `Debug` printed an address
    /// as an unreadable decimal.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Returned => f.write_str("returned"),
            Self::Budget => f.write_str("budget exhausted"),
            Self::Unmodeled(what) => write!(f, "unmodeled {what}"),
            Self::Fault(at) => write!(f, "fault at {at:#x}"),
            Self::MemoryFull(at) => write!(f, "memory full at {at:#x}"),
            Self::Stopped(at) => write!(f, "stopped at {at:#x}"),
            Self::Derailed(at) => write!(f, "derailed at {at:#x}"),
            Self::Exited => write!(f, "the program exited"),
            Self::Limit(what) => write!(f, "stopped: {what} limit ({RECORDS_MAX} recorded)"),
        }
    }
}

/// A byte the emulator produced, with where the routine wrote it.
#[derive(Debug, Clone)]
pub struct Written {
    /// The address written.
    pub addr: u64,
    /// The byte value.
    pub value: u8,
}

/// Bytes kept in the write history, so a long run cannot fill memory.
const HISTORY_MAX: usize = 1 << 16;

/// Most distinct bytes memory holds, written, poked and planted alike; at
/// tens of bytes of map each, a run stays under about a gigabyte.
pub const MEMORY_MAX: usize = 1 << 24;

/// Most instructions a trace keeps, so one asked-for trace cannot slow a
/// hundred-million-step run to a crawl recording all of it.
pub const TRACE_MAX: usize = 4096;

/// Returns the x86-64 Linux name of a syscall number.
///
/// The table holds the numbers a bootstrap reaches for: memory and
/// mapping, process and thread control, the tracing and identity probes,
/// files and descriptors, and the clock. Unlisted numbers are reported bare
/// rather than guessed. The numbers are those of
/// `arch/x86/entry/syscalls/syscall_64.tbl` in the Linux source.
///
/// # Arguments
///
/// * `nr` - The number in `rax` at the `syscall`.
///
/// # Returns
///
/// The name, or `None` for a number this table does not list.
#[must_use]
pub fn linux_syscall_name(nr: u64) -> Option<&'static str> {
    Some(match nr {
        0 => "read",
        1 => "write",
        2 => "open",
        3 => "close",
        4 => "stat",
        5 => "fstat",
        8 => "lseek",
        9 => "mmap",
        10 => "mprotect",
        11 => "munmap",
        12 => "brk",
        13 => "rt_sigaction",
        14 => "rt_sigprocmask",
        16 => "ioctl",
        17 => "pread64",
        21 => "access",
        22 => "pipe",
        23 => "select",
        24 => "sched_yield",
        25 => "mremap",
        28 => "madvise",
        32 => "dup",
        33 => "dup2",
        35 => "nanosleep",
        39 => "getpid",
        41 => "socket",
        42 => "connect",
        43 => "accept",
        44 => "sendto",
        45 => "recvfrom",
        49 => "bind",
        50 => "listen",
        56 => "clone",
        57 => "fork",
        58 => "vfork",
        59 => "execve",
        60 => "exit",
        61 => "wait4",
        62 => "kill",
        63 => "uname",
        72 => "fcntl",
        89 => "readlink",
        96 => "gettimeofday",
        101 => "ptrace",
        102 => "getuid",
        110 => "getppid",
        157 => "prctl",
        158 => "arch_prctl",
        186 => "gettid",
        200 => "tkill",
        202 => "futex",
        218 => "set_tid_address",
        228 => "clock_gettime",
        230 => "clock_nanosleep",
        231 => "exit_group",
        234 => "tgkill",
        257 => "openat",
        262 => "newfstatat",
        273 => "set_robust_list",
        302 => "prlimit64",
        318 => "getrandom",
        319 => "memfd_create",
        322 => "execveat",
        334 => "rseq",
        435 => "clone3",
        _ => return None,
    })
}

/// A run of adjacent pages a profiled run read equally often.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageRun {
    /// The first page's address.
    pub first: u64,
    /// How many pages the run spans.
    pub pages: u64,
    /// Loads from each page.
    pub each: u64,
    /// The instruction that made the first page's first load.
    pub by: u64,
}

impl PageRun {
    /// Returns the address one past the run's last page.
    #[must_use]
    pub const fn end(&self) -> u64 {
        self.first.saturating_add(self.pages.saturating_mul(PAGE))
    }
}

/// The result of a run.
#[derive(Debug, Clone)]
pub struct Run {
    /// Why the run ended.
    pub stop: Stop,
    /// Steps taken: instructions executed, iterations of a `rep` string
    /// instruction past its first, API calls serviced, and transfers
    /// best-effort mode skipped, each of which spends one of the budget.
    pub steps: usize,
    /// How many bytes memory holds below the stack when the run ends: what
    /// the routine wrote there, and what was set up there before it ran.
    pub written: usize,
    /// Bytes the routine wrote, in the order it wrote them, capped.
    ///
    /// Memory keeps only the final state, so a routine that fills one
    /// buffer several times over leaves only the last fill there. A decoder
    /// does exactly that, and its earlier outputs are the interesting ones.
    pub history: Vec<Written>,
}

/// A step-bounded machine over one program image.
///
/// A clone is a separate machine over the same image: cloning one that is
/// set up but has not run is cheaper than building another the same way.
#[derive(Debug, Clone)]
pub struct Emulator<'a> {
    /// The image whose bytes back memory the routine has not written.
    program: &'a Program,
    /// 32 or 64.
    bitness: u32,
    /// Stack word in bytes: what a push moves the stack pointer by.
    word: usize,
    /// Top of the scratch stack the run is handed.
    stack_base: u64,
    /// Bytes on either side of the stack base treated as stack.
    stack_span: u64,
    /// The synthetic thread block: what `fs` (32-bit) or `gs` (64-bit)
    /// resolves to, so `fs:[0]` reads the exception chain head and
    /// `gs:[0x60]` the process block rather than faulting on address zero.
    teb: u64,
    /// The sixteen general-purpose registers, `rax` first.
    regs: [u64; 16],
    /// Memory the routine wrote, over the image's own bytes, and which of
    /// those bytes it wrote outside the stack: the bytes a packer decrypts
    /// into memory. Pre-run [`Emulator::poke`] does not mark these.
    mem: Store,
    /// The zero flag, from the last flag-setting result.
    flags_zero: bool,
    /// The carry flag, from the last add or subtract.
    flags_carry: bool,
    /// The sign flag, from the last flag-setting result.
    flags_sign: bool,
    /// The parity flag: set when the low byte of the last flag-setting
    /// result has an even number of ones, and by an unordered floating
    /// compare, which is what `jp` after `ucomisd` tests for a NaN.
    flags_parity: bool,
    /// The direction flag: string operations step backward when set.
    flags_df: bool,
    /// The overflow flag, or `None` when the last instruction to touch the
    /// flags did not compute it.
    ///
    /// A signed comparison is the difference between the sign and overflow
    /// flags, so guessing one of them takes a branch the machine would not.
    /// Unknown makes a signed jump stop the run instead, which is a diagnosis
    /// rather than a wrong answer.
    flags_over: Option<bool>,
    /// Steps a run may take.
    budget: usize,
    /// Steps the current run has taken: one per instruction, and one more
    /// per iteration of a `rep` string instruction past its first.
    steps: usize,
    /// Most distinct bytes `mem` may hold: [`MEMORY_MAX`], lowered only by
    /// a test that fills it.
    memory_max: usize,
    /// `(from, to)` of every indirect jump taken: a VM dispatch's jumps to
    /// its handlers are here, which is the virtual instruction trace.
    jumps: Vec<(u64, u64)>,
    /// How many trailing instructions the trace keeps, and the lines kept.
    ///
    /// A trace answers what a loop does to its state, which reading the
    /// final registers cannot: the same instruction runs a thousand times
    /// and only the last result survives. Off unless asked for, because
    /// recording every step costs more than running one.
    trace_cap: usize,
    /// The value whose first appearance in the run is watched for, and the
    /// instruction that produced it.
    ///
    /// A run's result names a value the analyst did not expect; where that
    /// value was born is the question the registers at the end cannot
    /// answer, and reading the whole run for it is what this watch does
    /// instead. Off unless asked for, because it reads every step's writes.
    origin: Option<u64>,
    /// `(the instruction's address, its disassembly)`, the first that left
    /// the watched value in a register or in memory.
    origin_at: Option<(u64, String)>,
    /// Addresses the step now running has written, for the origin watch.
    ///
    /// The write history stops at [`HISTORY_MAX`] entries so a long run
    /// cannot fill memory, and a bootstrap that writes megabytes leaves the
    /// cap behind long before the value an analyst asks about is born; the
    /// watch keeps its own per-step addresses instead, which is all it
    /// needs and costs nothing when nothing is watched.
    step_writes: Vec<u64>,
    /// One line per traced instruction: where, what, and what it changed.
    trace: VecDeque<String>,
    /// The loads and stores of the step now running, while tracing, as
    /// `(stored, address, width, value)`: what a trace line says the
    /// instruction read and wrote, which its register changes cannot show
    /// for a routine that keeps its state in memory.
    step_memory: std::cell::RefCell<Vec<(bool, u64, usize, u64)>>,
    /// Whether the run counts where its steps go: each instruction address
    /// executed and each page read off the stack.
    ///
    /// A run that exhausts its budget says only that it did; the question
    /// that follows is which loop ate the budget and what it was reading,
    /// and a trailing trace answers neither once the loop body outgrows it.
    /// Off unless asked for, because it touches a map on every step.
    profiling: bool,
    /// Times control landed at each address by a jump, call or return
    /// rather than by falling through, while profiling: the heads of the
    /// straight lines the run executed.
    hits: crate::fxmap::FxHashMap<u64, u64>,
    /// The address the last instruction falls through to, so the profile
    /// tells a landing from a fall-through.
    fall_through: u64,
    /// Reads off the stack per 4 KiB page, while profiling, with the
    /// instruction that made the page's first load: the loop a profile
    /// names as reading a region is found from it. Interior mutability
    /// because a load is a read of the machine, not a change.
    page_reads: std::cell::RefCell<crate::fxmap::FxHashMap<u64, (u64, u64)>>,
    /// Addresses set up before the run by [`Emulator::poke`].
    ///
    /// Kept apart from `dirty` so a deliberate patch is not reported as code
    /// the program unpacked, while still being fetched as code: an experiment
    /// that nops a check out has to see the nops execute.
    patched: BTreeSet<u64>,
    /// The first address the run both wrote and then executed: a packer's
    /// original entry point, where its unpacked code begins.
    oep: Option<u64>,
    /// The address of the last instruction the run decoded: where it stopped,
    /// or the instruction that transferred to a faulting address.
    last_ip: u64,
    /// The stub each `GetProcAddress` name was handed, so asking for one
    /// name again answers the same stub instead of adding another.
    resolved: BTreeMap<String, u64>,
    /// Synthetic stub address to imported API name. The import table is
    /// prefilled so each slot holds its stub; a call to a stub is modeled as
    /// that API rather than executed, the way the OS would service it.
    /// Shared between clones until one adds a stub: the set-up machine a
    /// replay clones holds every name the image imports.
    apis: std::sync::Arc<BTreeMap<u64, String>>,
    /// The imported APIs and syscalls the run serviced, in order, each with
    /// its decoded arguments and result: what the program asked the
    /// operating system to do as it ran.
    calls: Vec<ApiCall>,
    /// Next address a modeled allocator hands out ([`Emulator::allocate`]).
    alloc_next: u64,
    /// The regions allocation handed out, as `(base, one past the end)`:
    /// zero-backed before the run writes them, so a pointer the emulator
    /// itself returned never faults where the OS would not.
    allocs: Vec<(u64, u64)>,
    /// Best-effort mode: a call or jump to memory nothing maps is skipped
    /// (treated as a stub returning zero) and an unmapped read returns zero,
    /// rather than faulting, so a packer's bootstrap runs past the imports the
    /// OS loader would resolve. Off by default, because it can fabricate
    /// progress; the trace reports how many transfers it skipped.
    permissive: bool,
    /// Whether the caller's frame above the stack base reads as zero
    /// ([`ARGS_SPAN`] bytes): on for a run an agent asked for, off for the
    /// decompiler's replays, which judge a statement by where it faults.
    args_backed: bool,
    /// What an unmapped read returns in permissive mode: [`fill_byte`] of
    /// this seed, or zero when `None`.
    fill: Option<u64>,
    /// Calls and jumps skipped in permissive mode.
    skipped: usize,
    /// Anti-analysis APIs answered benignly, by name.
    neutralized: BTreeSet<String>,
    /// Bytes written, in order, up to [`HISTORY_MAX`].
    history: Vec<Written>,
    /// The cycle counter `rdtsc` reads, advanced a little per read.
    ticks: u64,
    /// An address the run halts at before executing, for stepping a routine
    /// to a chosen point and reading the state there.
    stop_at: Option<u64>,
    /// The sixteen 128-bit vector registers, `xmm0` first.
    ///
    /// A compiler moves and clears these constantly, so a machine without
    /// them stops on the first `movaps` and reports nothing: across a
    /// hundred functions of one real binary, vector moves were 29 of the 33
    /// unmodeled stops.
    xmm: [u128; 16],
    /// The upper 128 bits of the sixteen vector registers, `ymm0` first.
    ///
    /// The ISA's `ymm0..15` are `xmm0..15` plus these halves, so a 256-bit
    /// register read is its register's `xmm` lane and this half above it.
    /// Only the instructions whose two 128-bit halves compute independently
    /// touch them; anything that crosses the boundary stays unmodeled. A
    /// ymm memory access moves the low lane alone (the width the
    /// decompiler's type tree models and the block verifier compares), so
    /// these halves ride along in register-to-register moves and never
    /// reach memory; a VEX.128 write the hardware would zero the upper
    /// half with leaves the half as the last 256-bit write left it.
    ymm_hi: [u128; 16],
    /// The x87 register stack, as doubles, with `fpu_top` naming `st(0)`.
    ///
    /// The hardware keeps eighty-bit values. A double is exact for every
    /// integer these routines load and close enough for the rest, and the
    /// difference cannot reach an address or a byte of recovered text, which
    /// is what the emulator exists to produce.
    fpu: [f64; 8],
    /// Index of `st(0)` in `fpu`, decremented by a push as the hardware does.
    fpu_top: usize,
    /// The six segment registers `es` first, as zero-extended selectors.
    ///
    /// A block a routine moves a segment register in is rare in user mode,
    /// but a check of the lifting needs the move to land somewhere both
    /// sides can read. The base the processor would add to a segmented
    /// address is not modeled: addresses stay flat, as they are in the
    /// flat model every modern operating system runs.
    segs: [u64; 6],
}

/// The byte a permissive run reads at an address nothing backs, under a
/// fill seed ([`Emulator::set_fill`]).
///
/// A hash of the address, so two reads of one address agree and reads of
/// two addresses differ: a load at the wrong offset reads a different
/// value, where an all-zero fill would read the same zero.
///
/// # Arguments
///
/// * `seed` - The fill seed.
/// * `a` - The address.
///
/// # Returns
///
/// The byte, the same for the same seed and address.
#[must_use]
pub fn fill_byte(seed: u64, a: u64) -> u8 {
    let mut z = seed ^ a.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    lo8(z ^ (z >> 31))
}

/// One image byte as the OS loader would map it, before the run's writes.
///
/// The static image backs only section file bytes. The loader maps more:
/// a section's virtual size beyond its file bytes is zero-filled, and the
/// PE headers are mapped at the image base below the first section. A
/// packer's bootstrap reads both (the headers to walk its own imports, the
/// zero-filled tail as scratch), so serving them lets the run continue
/// where a file-only view would fault.
///
/// The headers are the file bytes before the first section's, padded to
/// a page; the rest of the gap below the first section is not mapped.
/// Reading on through the file there served a section's bytes at an
/// address nothing loads them at: with sections 64 KiB apart, `[ebp +
/// 0x14]` 0x3468 bytes into the image read code from file offset
/// 0x3468, where the process would fault.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
///
/// # Returns
///
/// The byte, or `None` when no mapping the loader would make covers `va`.
fn image_byte(program: &Program, va: u64) -> Option<u8> {
    if let Some(b) = program.read_va_upto(va, 1).and_then(|s| s.first().copied()) {
        return Some(b);
    }
    if program.sections.iter().any(|s| {
        let mapped = s.vsize.max(s.file_size).wrapping_add(PAGE - 1) & !(PAGE - 1);
        va >= s.va.0 && va - s.va.0 < mapped
    }) {
        return Some(0);
    }
    let base = program.image_base;
    let first = program.sections.iter().map(|s| s.va.0).min();
    if va < base || first.is_none_or(|f| va >= f) {
        return None;
    }
    let headers = program
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .map(|s| s.file_off.0)
        .min()
        .unwrap_or(0);
    let off = va - base;
    if off < headers {
        return usize::try_from(off)
            .ok()
            .and_then(|o| program.bytes.get(o).copied());
    }
    (off < headers.wrapping_add(PAGE - 1) & !(PAGE - 1)).then_some(0)
}

/// Base address of the scratch stack the emulator gives a routine.
const STACK_BASE: u64 = 0x7fff_0000_0000;
/// Top of the scratch stack on a 32-bit target: high in the user half of
/// the address space and clear of any image.
const STACK_BASE_32: u64 = 0x7fff_0000;
/// Stack reserve on a 32-bit target, where the address space is small.
const STACK_SPAN_32: u64 = 0x0100_0000;
/// Where the synthetic thread block lives on a 64-bit target: what `gs`
/// resolves to, since Windows keeps the TEB there.
const TEB_64: u64 = 0x7fff_e000_0000;
/// Where the synthetic thread block lives on a 32-bit target: what `fs`
/// resolves to.
const TEB_32: u64 = 0x7ffd_e000;
/// Bytes of thread block and process block planted at the TEB address.
const TEB_SPAN: u64 = 0x2000;

/// Where a thread block keeps the fields the emulator plants, as offsets
/// from its base; the exception chain head is the first word of either.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TebLayout {
    /// The stack base.
    stack_base: u64,
    /// The stack limit.
    stack_limit: u64,
    /// The block's own address.
    this: u64,
    /// The process block's address.
    peb: u64,
    /// The TLS array pointer.
    tls_array: u64,
}

/// Windows' 32-bit thread block.
const TEB_LAYOUT_32: TebLayout = TebLayout {
    stack_base: 0x4,
    stack_limit: 0x8,
    this: 0x18,
    peb: 0x30,
    tls_array: 0x2c,
};

/// Windows' 64-bit thread block.
const TEB_LAYOUT_64: TebLayout = TebLayout {
    stack_base: 0x8,
    stack_limit: 0x10,
    this: 0x30,
    peb: 0x60,
    tls_array: 0x58,
};

/// Offset of the process block from the thread block, past its span.
const PEB_AT: u64 = 0x1000;

/// The page size the loader rounds section virtual extents up to when mapping.
const PAGE: u64 = 0x1000;

/// Bytes above the stack base that read as zero.
///
/// They are the return address slot and the caller's frame, where a
/// routine finds its stack arguments and its home space. A run given no
/// arguments read them there and faulted, so `emulate` of any function
/// taking a stack argument stopped at once.
const ARGS_SPAN: u64 = 0x1000;

/// Bytes below [`STACK_BASE`] treated as stack, not materialized code.
///
/// Writes here are the routine's own stack frames; they are excluded from the
/// unpacking trace so a deep call chain does not read as decrypted code. The
/// reserve is generous because best-effort mode lets the stack pointer drift
/// far as it skips calls, and a real unpacked payload never lands this close
/// to the stack base (it goes to the image or to allocated memory far below).
const STACK_SPAN: u64 = 0x4000_0000;

/// The registers a readout reports, in calling-convention order.
///
/// `rax` first because it holds the result, then the argument registers, then
/// the rest, then `rsp`.
const READOUT_ORDER: [&str; 16] = [
    "rax", "rcx", "rdx", "r8", "r9", "rbx", "rsi", "rdi", "rbp", "r10", "r11", "r12", "r13", "r14",
    "r15", "rsp",
];

/// The registers a 32-bit readout reports: the eight the target has, in the
/// same order, `eax` first and `esp` last.
const READOUT_ORDER_32: [&str; 8] = ["eax", "ecx", "edx", "ebx", "esi", "edi", "ebp", "esp"];

/// Applies `f` to each pair of `bits`-wide lanes of two vectors.
///
/// # Arguments
///
/// * `l` - The left vector.
/// * `r` - The right vector.
/// * `bits` - Lane width, 8 through 64.
/// * `f` - The per-lane operation.
///
/// # Returns
///
/// The vector of per-lane results, each truncated to the lane width.
fn packed(l: u128, r: u128, bits: u32, f: impl Fn(u64, u64) -> u64) -> u128 {
    let mask = (1u128 << bits) - 1;
    let mut out = 0u128;
    for lane in 0..128 / bits {
        let shift = lane * bits;
        let a = lo64((l >> shift) & mask);
        let b = lo64((r >> shift) & mask);
        out |= (u128::from(f(a, b)) & mask) << shift;
    }
    out
}

/// Answers `cpuid` for one leaf as a plain, unvirtualized machine.
///
/// A protected binary reads `cpuid` twice: once for the feature bits it needs
/// and once for the hypervisor bit and vendor leaves that say it is being
/// watched. Fixed values answer both without inventing a different machine
/// per run, which the determinism contract requires. The hypervisor-present
/// bit is clear and the hypervisor vendor leaves read as absent, because
/// nothing here is one.
///
/// # Arguments
///
/// * `leaf` - The value in `eax` on entry.
///
/// # Returns
///
/// `(eax, ebx, ecx, edx)` for the leaf; zeros for a leaf not modeled.
fn cpuid_leaf(leaf: u32) -> (u32, u32, u32, u32) {
    match leaf {
        0 => (0x16, 0x756e_6547, 0x6c65_746e, 0x4965_6e69),
        1 => (0x0009_06e9, 0x0010_0800, 0x7ffa_fbbf, 0x0fab_fbff),
        0x8000_0000 => (0x8000_0008, 0, 0, 0),
        0x8000_0001 => (0, 0, 0x0000_0121, 0x2c10_0800),
        _ => (0, 0, 0, 0),
    }
}

/// Resolves a lowercase 64-bit general register name.
///
/// The one table the setter, the reader and the readout share, so a register
/// that can be set can also be read back and never goes missing from one of
/// the three.
///
/// # Arguments
///
/// * `name` - The lowercase name, `rax` through `r15` or `rsp`.
///
/// # Returns
///
/// The register, or `None` when the name is not one.
fn named_register(name: &str) -> Option<Register> {
    Some(match name {
        "rax" | "eax" => Register::RAX,
        "rbx" | "ebx" => Register::RBX,
        "rcx" | "ecx" => Register::RCX,
        "rdx" | "edx" => Register::RDX,
        "rsi" | "esi" => Register::RSI,
        "rdi" | "edi" => Register::RDI,
        "rbp" | "ebp" => Register::RBP,
        "rsp" | "esp" => Register::RSP,
        "r8" => Register::R8,
        "r9" => Register::R9,
        "r10" => Register::R10,
        "r11" => Register::R11,
        "r12" => Register::R12,
        "r13" => Register::R13,
        "r14" => Register::R14,
        "r15" => Register::R15,
        _ => return None,
    })
}

/// The registers a readout reports for a target width.
///
/// # Arguments
///
/// * `bitness` - 32 or 64.
fn readout_order(bitness: u32) -> &'static [&'static str] {
    if bitness == 32 {
        &READOUT_ORDER_32
    } else {
        &READOUT_ORDER
    }
}

impl<'a> Emulator<'a> {
    /// Returns the stack pointer a machine over `program` starts with,
    /// without building one.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    ///
    /// # Returns
    ///
    /// The `rsp` [`Emulator::new`] sets, or `None` when the image's
    /// bitness is unknown.
    #[must_use]
    pub fn entry_sp(program: &Program) -> Option<u64> {
        Some(if program.arch.bitness()? == 32 {
            STACK_BASE_32
        } else {
            STACK_BASE
        })
    }

    /// Builds an emulator over `program` with a step budget.
    ///
    /// # Arguments
    ///
    /// * `program` - The image whose bytes back unwritten memory.
    /// * `budget` - Most instructions to run before stopping.
    ///
    /// # Returns
    ///
    /// A machine with zeroed registers and a scratch stack pointer, or `None`
    /// when the image's bitness is unknown.
    #[must_use]
    pub fn new(program: &'a Program, budget: usize) -> Option<Self> {
        let bitness = program.arch.bitness()?;
        let (word, stack_base, stack_span, teb, alloc_next) = if bitness == 32 {
            (4, STACK_BASE_32, STACK_SPAN_32, TEB_32, ALLOC_BASE_32)
        } else {
            (8, STACK_BASE, STACK_SPAN, TEB_64, ALLOC_BASE)
        };
        let mut emu = Self {
            program,
            bitness,
            word,
            stack_base,
            stack_span,
            teb,
            regs: [0; 16],
            mem: Store::default(),
            flags_zero: false,
            flags_carry: false,
            flags_sign: false,
            flags_df: false,
            flags_parity: false,
            flags_over: None,
            budget,
            steps: 0,
            memory_max: MEMORY_MAX,
            jumps: Vec::new(),
            patched: BTreeSet::new(),
            trace_cap: 0,
            trace: VecDeque::new(),
            step_memory: std::cell::RefCell::new(Vec::new()),
            profiling: false,
            hits: crate::fxmap::FxHashMap::default(),
            fall_through: 0,
            page_reads: std::cell::RefCell::new(crate::fxmap::FxHashMap::default()),
            origin: None,
            origin_at: None,
            step_writes: Vec::new(),
            oep: None,
            last_ip: 0,
            apis: std::sync::Arc::default(),
            resolved: BTreeMap::new(),
            calls: Vec::new(),
            alloc_next,
            allocs: Vec::new(),
            permissive: false,
            args_backed: false,
            fill: None,
            skipped: 0,
            neutralized: BTreeSet::new(),
            history: Vec::new(),
            ticks: 0,
            stop_at: None,
            xmm: [0; 16],
            ymm_hi: [0; 16],
            fpu: [0.0; 8],
            fpu_top: 0,
            segs: [0; 6],
        };
        emu.set_reg(Register::RSP, stack_base);
        emu.plant_teb();
        emu.plant_loader();
        emu.mem.freeze();
        Some(emu)
    }

    /// Plants a thread block and a process block the way an unwatched
    /// process finds them.
    ///
    /// The exception chain head is empty, the stack bounds are the scratch
    /// stack's, the self pointer points back, the process block pointer
    /// leads to a zeroed page, and `BeingDebugged` in it is zero. The
    /// offsets are Windows' own for each width. The bytes are planted as
    /// pre-run memory, so they are neither dirty nor a fault.
    fn plant_teb(&mut self) {
        let layout = self.teb_layout();
        self.mem.plant(self.teb, (0..TEB_SPAN).map(|_| 0));
        let (teb, word) = (self.teb, self.word);
        self.plant(teb, u64::MAX, word);
        self.plant(teb + layout.stack_base, self.stack_base, word);
        self.plant(
            teb + layout.stack_limit,
            self.stack_base.wrapping_sub(self.stack_span),
            word,
        );
        self.plant(teb + layout.this, teb, word);
        self.plant(teb + layout.peb, teb + PEB_AT, word);
    }

    /// The thread block layout of the target's width.
    ///
    /// # Returns
    ///
    /// Windows' own offsets for the fields the emulator plants.
    fn teb_layout(&self) -> TebLayout {
        if self.bitness == 32 {
            TEB_LAYOUT_32
        } else {
            TEB_LAYOUT_64
        }
    }

    /// Writes a value as setup rather than as something the routine did.
    ///
    /// The bytes stay out of the write history and the dirty set, so they
    /// are neither reported as code the program unpacked nor read back as
    /// its output; a fetch still sees them.
    ///
    /// # Arguments
    ///
    /// * `addr` - Where to write.
    /// * `v` - The value, little-endian.
    /// * `bytes` - How many of its low bytes.
    fn plant(&mut self, addr: u64, v: u64, bytes: usize) {
        self.mem
            .plant(addr, (0..from_usize(bytes)).map(|k| lo8(v >> (k * 8))));
    }

    /// Masks a value to the target's register width.
    ///
    /// # Arguments
    ///
    /// * `v` - A 64-bit value.
    fn narrow(&self, v: u64) -> u64 {
        if self.bitness == 32 {
            v & 0xffff_ffff
        } else {
            v
        }
    }

    /// Assembles the tracked flags into an `x86` `RFLAGS`/`EFLAGS` word.
    ///
    /// Only the flags the model tracks are set: carry, parity, zero, sign,
    /// overflow and direction, plus the always-one reserved bit. An overflow
    /// the last instruction did not compute reads as clear. Used by `pushf`
    /// so the value a later `popf` restores round-trips the flags that gate
    /// branches.
    fn rflags(&self) -> u64 {
        let mut v = 0x2u64;
        v |= u64::from(self.flags_carry);
        v |= u64::from(self.flags_parity) << 2;
        v |= u64::from(self.flags_zero) << 6;
        v |= u64::from(self.flags_sign) << 7;
        v |= u64::from(self.flags_df) << 10;
        v |= u64::from(self.flags_over.unwrap_or(false)) << 11;
        v
    }

    /// Sets the tracked flags from an `x86` `RFLAGS`/`EFLAGS` word.
    ///
    /// The inverse of [`Emulator::rflags`], for `popf`: it reads back carry,
    /// parity, zero, sign, overflow and direction and leaves the untracked
    /// bits alone.
    ///
    /// # Arguments
    ///
    /// * `v` - The flags word popped from the stack.
    fn set_rflags(&mut self, v: u64) {
        self.flags_carry = v & 1 != 0;
        self.flags_parity = v >> 2 & 1 != 0;
        self.flags_zero = v >> 6 & 1 != 0;
        self.flags_sign = v >> 7 & 1 != 0;
        self.flags_df = v >> 10 & 1 != 0;
        self.flags_over = Some(v >> 11 & 1 != 0);
    }

    /// Backs the caller's frame above the stack base with zeros, so a
    /// routine given no stack arguments reads zeros there instead of
    /// faulting at its first one.
    pub fn back_arguments(&mut self) {
        self.args_backed = true;
    }

    /// Turns on best-effort mode: skip transfers to unmapped memory and read
    /// zero from it, rather than faulting, so a bootstrap runs past the
    /// runtime imports a static view cannot resolve.
    pub fn set_permissive(&mut self, on: bool) {
        self.permissive = on;
    }

    /// Makes a permissive run read [`fill_byte`] of a seed from memory
    /// nothing backs, instead of zero.
    ///
    /// # Arguments
    ///
    /// * `seed` - The fill seed, or `None` for zero.
    pub fn set_fill(&mut self, seed: Option<u64>) {
        self.fill = seed;
    }

    /// How many calls and jumps best-effort mode skipped.
    #[must_use]
    pub fn skipped(&self) -> usize {
        self.skipped
    }

    /// The indirect jumps taken during the run, `(from, to)` in order.
    ///
    /// A virtualized function's dispatch jumps through a table to each
    /// handler; filtered to the dispatch's address, these are the virtual
    /// instructions the run executed, in order.
    #[must_use]
    pub fn indirect_jumps(&self) -> &[(u64, u64)] {
        &self.jumps
    }

    /// The packer's original entry point, if the run reached unpacked code.
    ///
    /// This is the first address the run both wrote and then executed: the
    /// decrypted code a packer jumps to once it has rebuilt the real program.
    /// `None` when nothing written was executed before the run stopped.
    #[must_use]
    pub fn oep(&self) -> Option<u64> {
        self.oep
    }

    /// The regions the run materialized, as `(start, len)` in address order.
    ///
    /// Each is a contiguous run of bytes the routine wrote outside the stack:
    /// a block a packer decrypted into memory. Adjacent written bytes coalesce
    /// into one region so a decrypted page reads as a single span.
    #[must_use]
    pub fn materialized(&self) -> Vec<(u64, u64)> {
        let mut regions: Vec<(u64, u64)> = Vec::new();
        for addr in self.mem.dirty() {
            match regions.last_mut() {
                Some(last) if last.0 + last.1 == addr => last.1 += 1,
                _ => regions.push((addr, 1)),
            }
        }
        regions
    }

    /// Whether the run executed any byte it had written: self-modifying code.
    #[must_use]
    pub fn self_modified(&self) -> bool {
        self.oep.is_some()
    }

    /// The address of the last instruction the run decoded.
    ///
    /// On a fault this is the instruction that stopped the run, or the one
    /// whose control transfer landed on the faulting address: the blocker an
    /// unpacking or devirtualization trace could not get past.
    #[must_use]
    pub fn last_ip(&self) -> u64 {
        self.last_ip
    }

    /// Sets an argument where the program's calling convention puts it.
    ///
    /// The convention is the one the decompiler names `a1`..`aN` by on this
    /// program ([`abi::conv`](crate::analysis::decompile::abi::conv)): on a PE the first four arguments live in
    /// `rcx`, `rdx`, `r8` and `r9`, on an ELF or Mach-O the first six in
    /// `rdi`, `rsi`, `rdx`, `rcx`, `r8` and `r9`, and in 32-bit code none.
    /// The rest are on the stack as the callee sees it on entry, past the
    /// slot the return address occupies and any shadow space. Writing those
    /// is what lets a routine of more arguments than registers be set up at
    /// all, and the write is setup rather than something the code did, so
    /// it stays out of the write history a recovered string is read from.
    ///
    /// # Arguments
    ///
    /// * `index` - Argument position, from zero.
    /// * `value` - The value.
    pub fn set_arg(&mut self, index: usize, value: u64) {
        match self.arg_slot(index) {
            ArgSlot::Register(r) => self.set_reg(r, value),
            ArgSlot::Stack(slot) => self.plant(slot, value, self.word),
        }
    }

    /// Sets a register named as text (`rcx`, `r8`, `rdi`), 64-bit only.
    ///
    /// # Arguments
    ///
    /// * `name` - The lowercase 64-bit register name.
    /// * `value` - The value.
    ///
    /// # Returns
    ///
    /// Whether the name was a known 64-bit general register. A caller driving
    /// an experiment should report a `false` rather than run, because a
    /// misspelled name would otherwise read as a setting that was applied.
    pub fn set_register(&mut self, name: &str, value: u64) -> bool {
        let Some(reg) = named_register(name) else {
            return false;
        };
        self.set_reg(reg, value);
        true
    }

    /// Reads a general register after a run.
    ///
    /// # Arguments
    ///
    /// * `name` - The lowercase 64-bit register name.
    ///
    /// # Returns
    ///
    /// Its value, or `None` when the name is not a 64-bit general register.
    #[must_use]
    pub fn register(&self, name: &str) -> Option<u64> {
        named_register(name).map(|r| self.reg(r))
    }

    /// Every general register after a run, in a fixed order.
    ///
    /// The order is the calling-convention order so a reader finds arguments
    /// and the result where they expect: `rax`, then `rcx`, `rdx`, `r8`, `r9`
    /// (the argument registers), then the rest, with `rsp` last because a
    /// routine that faulted on its own stack is diagnosed from it.
    ///
    /// # Returns
    ///
    /// `(name, value)` for each, `rax` first.
    #[must_use]
    pub fn registers(&self) -> Vec<(&'static str, u64)> {
        readout_order(self.bitness)
            .iter()
            .filter_map(|n| named_register(n).map(|r| (*n, self.reg(r))))
            .collect()
    }

    /// The x87 register stack after a run, as the machine holds it.
    ///
    /// # Returns
    ///
    /// The index of `st(0)` and the eight registers as doubles, so
    /// `st(n)` is `regs[(top + n) % 8]`; a register at or below the
    /// stack's depth holds `0.0`, the value a pop leaves.
    #[must_use]
    pub fn x87(&self) -> (usize, [f64; 8]) {
        (self.fpu_top, self.fpu)
    }

    /// The sixteen vector registers after a run, `xmm0` first.
    ///
    /// # Returns
    ///
    /// The low 128 bits of each register, which is all the emulator holds:
    /// an upper `ymm` half reads as zero.
    #[must_use]
    pub fn xmm(&self) -> [u128; 16] {
        self.xmm
    }

    /// Sets one vector register's low 128 bits before a run.
    ///
    /// Lets a caller seed the vector registers the way
    /// [`Emulator::set_register`] seeds the general ones, so a check can
    /// start both sides of a run from one state.
    ///
    /// # Arguments
    ///
    /// * `n` - The register's index, `xmm0` being zero; an index past the
    ///   sixteen sets nothing.
    /// * `v` - The bits.
    pub fn set_xmm(&mut self, n: usize, v: u128) {
        if let Some(slot) = self.xmm.get_mut(n) {
            *slot = v;
        }
    }

    /// The six segment registers after a run, `es` first.
    ///
    /// Held as the zero-extended selector each move writes, so a check can
    /// compare a segment register the machine moved; both sides of a check
    /// start them clear.
    ///
    /// # Returns
    ///
    /// Each register's selector, in the order [`SEG_ORDER`] names.
    #[must_use]
    pub fn segments(&self) -> [u64; 6] {
        self.segs
    }

    /// The address of the thread block's TLS array field.
    ///
    /// A segment-prefixed read of it (`gs:[0x58]` on a 64-bit target,
    /// `fs:[0x2c]` on a 32-bit one) loads the pointer the OS thread keeps
    /// there; the emulator plants the field as zero like the rest of the
    /// block's unplanted span, so a run that walks the array reads the
    /// bytes its state holds at the addresses that walk lands on. Exposed
    /// so the verification's evaluator can walk the same addresses and
    /// compare what a lifted TLS slot read against the machine's bytes.
    ///
    /// # Returns
    ///
    /// The field's address, in the synthetic thread block.
    #[must_use]
    pub fn tls_array_at(&self) -> u64 {
        self.teb.wrapping_add(self.teb_layout().tls_array)
    }

    /// Sets the address the next run halts at before executing it.
    ///
    /// Lets a routine be run to a chosen point, a branch or a call site, so
    /// the state there can be read without running to the end.
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

    /// Records the effect of each of the next `steps` instructions.
    ///
    /// A run reports its final state, which answers what a routine computed
    /// but not how. A trace answers the how: one line per instruction saying
    /// where it was, what it was, and which registers it changed. It keeps
    /// the last instructions, because the ones before a run stopped are the
    /// diagnosis and the ones from its start are had by giving the run a
    /// small `steps=` budget; a loop can run for as long as its budget
    /// allows, and the trace follows it to the end.
    ///
    /// # Arguments
    ///
    /// * `steps` - How many trailing instructions to keep, held to
    ///   [`TRACE_MAX`]; zero turns it off.
    pub fn set_trace(&mut self, steps: usize) {
        self.trace_cap = steps.min(TRACE_MAX);
        self.trace.clear();
    }

    /// Counts where the run's steps go: instructions executed per address
    /// and reads off the stack per 4 KiB page ([`Emulator::profile`]).
    ///
    /// # Arguments
    ///
    /// * `on` - Whether to count.
    pub fn set_profile(&mut self, on: bool) {
        self.profiling = on;
        self.hits.clear();
        self.page_reads.borrow_mut().clear();
    }

    /// The profile of the last run: the `top` addresses control landed at
    /// most often, and the `top` runs of pages read off the stack.
    ///
    /// Pages merge into one run where they are adjacent and were read the
    /// same number of times, so a routine that walks a megabyte one byte at
    /// a time reads as one range rather than two hundred equal rows. Both
    /// lists are largest first, ties by address, so the answer is
    /// deterministic.
    ///
    /// # Arguments
    ///
    /// * `top` - How many of each to return.
    ///
    /// # Returns
    ///
    /// `(hot addresses as (address, landings), page runs)`.
    #[must_use]
    pub fn profile(&self, top: usize) -> (Vec<(u64, u64)>, Vec<PageRun>) {
        let mut hot: Vec<(u64, u64)> = self.hits.iter().map(|(&a, &n)| (a, n)).collect();
        hot.sort_unstable_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(&y.0)));
        hot.truncate(top);
        let mut pages: Vec<(u64, (u64, u64))> = self
            .page_reads
            .borrow()
            .iter()
            .map(|(&a, &n)| (a, n))
            .collect();
        pages.sort_unstable();
        let mut runs: Vec<PageRun> = Vec::new();
        for (page, (n, by)) in pages {
            match runs.last_mut() {
                Some(run) if run.each == n && run.end() == page => {
                    run.pages += 1;
                }
                _ => runs.push(PageRun {
                    first: page,
                    pages: 1,
                    each: n,
                    by,
                }),
            }
        }
        runs.sort_unstable_by(|x, y| {
            (y.pages * y.each)
                .cmp(&(x.pages * x.each))
                .then(x.first.cmp(&y.first))
        });
        runs.truncate(top);
        (hot, runs)
    }

    /// The traced instructions, the run's last, in the order they ran.
    #[must_use]
    pub fn trace(&self) -> Vec<String> {
        self.trace.iter().cloned().collect()
    }

    /// Watches for a value's first appearance in registers or memory.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to watch for, or `None` to watch for nothing.
    pub fn set_origin(&mut self, value: Option<u64>) {
        self.origin = value;
        self.origin_at = None;
    }

    /// Where the watched value first appeared, when it did.
    ///
    /// # Returns
    ///
    /// `(the instruction's address, its disassembly)` of the first step
    /// that left the watched value in a register or in memory, or `None`
    /// when nothing was watched or the value never appeared.
    #[must_use]
    pub fn origin(&self) -> Option<(u64, String)> {
        self.origin_at.clone()
    }

    /// Names the loads and stores one step made, in the order it made them.
    ///
    /// # Arguments
    ///
    /// * `touched` - `(stored, address, width, value)` per access.
    ///
    /// # Returns
    ///
    /// `r<width>[addr]=value` per load and `w<width>[addr]=value` per
    /// store, or an empty string.
    fn memory_note(touched: &[(bool, u64, usize, u64)]) -> String {
        touched
            .iter()
            .map(|&(stored, at, width, v)| {
                let verb = if stored { "w" } else { "r" };
                format!("{verb}{width}[{at:#x}]={v:#x}")
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Names the registers that differ between two snapshots.
    ///
    /// # Arguments
    ///
    /// * `before` - The register file before the instruction.
    /// * `after` - The register file after it.
    ///
    /// # Returns
    ///
    /// `name=value` for each changed register, or an empty string.
    fn register_changes(bitness: u32, before: &[u64; 16], after: &[u64; 16]) -> String {
        readout_order(bitness)
            .iter()
            .filter_map(|name| {
                let r = named_register(name)?;
                let at = gpr_bank_index(r)?;
                let (was, now) = (before.get(at)?, after.get(at)?);
                (was != now).then(|| format!("{name}={now:#x}"))
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Writes a byte into the emulator's memory before a run.
    ///
    /// The byte is data to a load and code to a fetch, so a write over an
    /// instruction is executed if the run reaches it: that is how a check is
    /// patched out and the routine run again without it. The write is not
    /// counted as code the program materialized.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `value` - The byte.
    pub fn poke(&mut self, addr: u64, value: u8) {
        self.mem.set(addr, value, false);
        self.patched.insert(addr);
    }

    /// Reads a byte the routine has written, or `None` if it wrote none there.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    #[must_use]
    pub fn peek(&self, addr: u64) -> Option<u8> {
        self.mem.get(addr)
    }

    /// Reads a byte as a load reads it: written, else the image's, else
    /// the fill a permissive run reads.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    ///
    /// # Returns
    ///
    /// The byte, or `None` where a load faults.
    #[must_use]
    pub fn byte_at(&self, addr: u64) -> Option<u8> {
        self.byte(addr).or_else(|| {
            self.permissive
                .then(|| self.fill.map_or(0, |seed| fill_byte(seed, addr)))
        })
    }

    /// Reads up to `n` bytes at `va` as the run sees them, for disassembly.
    ///
    /// Written bytes take precedence over the image, so decrypted code reads
    /// as itself. Stops at the first byte backed by neither.
    ///
    /// # Arguments
    ///
    /// * `va` - The first address.
    /// * `n` - Most bytes to return.
    #[must_use]
    pub fn code_at(&self, va: u64, n: usize) -> Vec<u8> {
        (0..from_usize(n))
            .map_while(|k| self.byte(va.wrapping_add(k)))
            .collect()
    }

    /// The byte at `a` as the run sees it: written over the image.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    ///
    /// # Returns
    ///
    /// The byte, or `None` when neither memory nor the image backs it.
    fn byte(&self, a: u64) -> Option<u8> {
        self.mem
            .get(a)
            .or_else(|| image_byte(self.program, a))
            .or_else(|| (self.in_alloc(a) || self.in_stack(a)).then_some(0))
    }

    /// Whether `a` lies in a region the modeled allocator handed out.
    fn in_alloc(&self, a: u64) -> bool {
        self.allocs.iter().any(|(base, end)| a >= *base && a < *end)
    }

    /// Whether `a` lies on the scratch stack's span, whose untouched pages
    /// read as zero the way an OS stack's do for a stack probe.
    fn in_stack(&self, a: u64) -> bool {
        let deep = self.stack_base.saturating_sub(self.stack_span);
        let above = if self.args_backed { ARGS_SPAN } else { 1 };
        (deep..self.stack_base.saturating_add(above)).contains(&a)
    }

    /// The record of this run that is full, when one is.
    ///
    /// # Returns
    ///
    /// The calls or the indirect jumps when either holds [`RECORDS_MAX`]
    /// entries, or `None` while both have room.
    fn filled(&self) -> Option<Limit> {
        if self.calls.len() >= RECORDS_MAX {
            Some(Limit::Calls)
        } else {
            (self.jumps.len() >= RECORDS_MAX).then_some(Limit::Jumps)
        }
    }

    /// Runs from `entry` until it returns, exhausts the budget, or stops.
    ///
    /// # Arguments
    ///
    /// * `entry` - The routine's first instruction.
    ///
    /// # Returns
    ///
    /// The stop reason, the step count, and every byte written, in address
    /// order.
    pub fn run(&mut self, entry: u64) -> Run {
        let mut ip = entry;
        self.steps = 0;
        let stop = loop {
            if self.stop_at == Some(ip) {
                break Stop::Stopped(ip);
            }
            if self.steps >= self.budget {
                break Stop::Budget;
            }
            if let Some(limit) = self.filled() {
                break Stop::Limit(limit);
            }
            if self.apis.contains_key(&ip) {
                self.steps += 1;
                match self.service_api(ip) {
                    Ok(ret) => {
                        ip = ret;
                        continue;
                    }
                    Err(stop) => break stop,
                }
            }
            if self.oep.is_none() && self.mem.is_dirty(ip) {
                self.oep = Some(ip);
            }
            if self.on_stack(ip) {
                break Stop::Derailed(ip);
            }
            let Some(bytes) = self.fetch(ip) else {
                if self.permissive && self.reg(Register::RSP) < self.stack_base {
                    self.steps += 1;
                    self.skipped += 1;
                    match self.pop() {
                        Ok(ra) => {
                            ip = ra;
                            continue;
                        }
                        Err(stop) => break stop,
                    }
                }
                break Stop::Fault(ip);
            };
            let mut decoder = Decoder::with_ip(self.bitness, &bytes, ip, DecoderOptions::NONE);
            let instr = decoder.decode();
            if instr.is_invalid() {
                let executable = self.program.section_at(ip).is_some_and(|s| s.executable);
                break if executable {
                    Stop::Unmodeled(format!("bad opcode at {ip:#x}"))
                } else {
                    Stop::Fault(ip)
                };
            }
            self.last_ip = ip;
            self.steps += 1;
            if self.profiling && ip != self.fall_through {
                *self.hits.entry(ip).or_insert(0) += 1;
            }
            let watched = self.trace_cap > 0;
            let before = if watched { self.regs } else { [0; 16] };
            self.step_writes.clear();
            if watched {
                self.step_memory.borrow_mut().clear();
            }
            let outcome = self.step(&instr);
            if self.origin.is_some() && self.origin_at.is_none() && self.born() {
                self.origin_at = Some((ip, format!("{instr}")));
            }
            if watched {
                if self.trace.len() >= self.trace_cap {
                    self.trace.pop_front();
                }
                let changed = Self::register_changes(self.bitness, &before, &self.regs);
                let touched = Self::memory_note(&self.step_memory.borrow());
                let note = match &outcome {
                    Ok(_) if changed.is_empty() && touched.is_empty() => {
                        String::from("(no register changed)")
                    }
                    Ok(_) if changed.is_empty() => touched,
                    Ok(_) if touched.is_empty() => changed,
                    Ok(_) => format!("{changed} {touched}"),
                    Err(stop) => format!("stopped: {stop}"),
                };
                self.trace.push_back(format!("{ip:#x}  {instr}    {note}"));
            }
            self.fall_through = instr.next_ip();
            match outcome {
                Ok(Some(next)) => ip = next,
                Ok(None) => ip = instr.next_ip(),
                Err(stop) => break stop,
            }
        };
        Run {
            stop,
            steps: self.steps,
            written: self.mem.held_below(self.stack_base),
            history: std::mem::take(&mut self.history),
        }
    }

    /// Executes one instruction.
    ///
    /// # Returns
    ///
    /// `Ok(Some(target))` for a taken jump, `Ok(None)` to fall through, or
    /// `Err(stop)` to end the run.
    ///
    /// # Errors
    ///
    /// The [`Stop`] that ends the run: a return, an unmodeled instruction, or
    /// a fault.
    fn step(&mut self, i: &Instruction) -> Result<Option<u64>, Stop> {
        let m = i.mnemonic();
        match m {
            Mnemonic::Nop | Mnemonic::Endbr64 | Mnemonic::Endbr32 => Ok(None),
            Mnemonic::Pause
            | Mnemonic::Prefetch
            | Mnemonic::Prefetchw
            | Mnemonic::Prefetcht0
            | Mnemonic::Prefetcht1
            | Mnemonic::Prefetcht2
            | Mnemonic::Prefetchnta
            | Mnemonic::Lfence
            | Mnemonic::Mfence
            | Mnemonic::Sfence
            | Mnemonic::Monitorx
            | Mnemonic::Mwaitx => Ok(None),
            Mnemonic::Clc | Mnemonic::Stc | Mnemonic::Cmc => {
                self.flags_carry = match m {
                    Mnemonic::Clc => false,
                    Mnemonic::Stc => true,
                    _ => !self.flags_carry,
                };
                Ok(None)
            }
            Mnemonic::Lahf => {
                let ah = u64::from(self.flags_sign) << 7
                    | u64::from(self.flags_zero) << 6
                    | u64::from(self.flags_parity) << 2
                    | 0x2
                    | u64::from(self.flags_carry);
                self.set_reg_sized(Register::AH, ah);
                Ok(None)
            }
            Mnemonic::Sahf => {
                let ah = self.reg_sized(Register::AH);
                self.flags_sign = ah >> 7 & 1 == 1;
                self.flags_zero = ah >> 6 & 1 == 1;
                self.flags_parity = ah >> 2 & 1 == 1;
                self.flags_carry = ah & 1 == 1;
                Ok(None)
            }
            Mnemonic::Jrcxz | Mnemonic::Jecxz => {
                let count = if m == Mnemonic::Jrcxz {
                    self.reg(Register::RCX)
                } else {
                    self.reg(Register::RCX) & 0xffff_ffff
                };
                Ok((count == 0).then(|| branch_target(i)).flatten())
            }
            Mnemonic::Mov | Mnemonic::Movzx => {
                let v = self.source(i)?;
                self.store(i, v)?;
                Ok(None)
            }
            Mnemonic::Movsx | Mnemonic::Movsxd => {
                let v = self.source(i)?;
                let from = if i.op1_kind() == OpKind::Register {
                    i.op1_register().size() * 8
                } else {
                    mem_bytes(i) * 8
                };
                let from = u32::try_from(from).unwrap_or(64);
                let v = u64::from_ne_bytes(sign_extend(v, from).to_ne_bytes());
                self.store(i, v)?;
                Ok(None)
            }
            Mnemonic::Lea => {
                let addr = self.mem_addr(i)?;
                self.write_reg_op(i, addr);
                Ok(None)
            }
            Mnemonic::Push => {
                let v = self.source(i)?;
                self.push(v)?;
                Ok(None)
            }
            Mnemonic::Pusha | Mnemonic::Pushad => {
                let order = [
                    Register::EAX,
                    Register::ECX,
                    Register::EDX,
                    Register::EBX,
                    Register::ESP,
                    Register::EBP,
                    Register::ESI,
                    Register::EDI,
                ];
                let saved: Vec<u64> = order.iter().map(|&r| self.reg(r)).collect();
                for v in saved {
                    self.push(v)?;
                }
                Ok(None)
            }
            Mnemonic::Popa | Mnemonic::Popad => {
                let mut restored: Vec<u64> = Vec::with_capacity(8);
                for _ in 0..8 {
                    restored.push(self.pop()?);
                }
                let order = [
                    Register::EDI,
                    Register::ESI,
                    Register::EBP,
                    Register::ESP,
                    Register::EBX,
                    Register::EDX,
                    Register::ECX,
                    Register::EAX,
                ];
                for (k, &r) in order.iter().enumerate() {
                    if r != Register::ESP {
                        self.set_reg(r, restored[k]);
                    }
                }
                Ok(None)
            }
            Mnemonic::Pop => {
                let v = self.pop()?;
                self.store(i, v)?;
                Ok(None)
            }
            Mnemonic::Leave => {
                let frame = self.reg(Register::RBP);
                self.set_reg(Register::RSP, frame);
                let saved = self.pop()?;
                self.set_reg(Register::RBP, saved);
                Ok(None)
            }
            Mnemonic::Cld | Mnemonic::Std => {
                self.flags_df = m == Mnemonic::Std;
                Ok(None)
            }
            Mnemonic::Pushf | Mnemonic::Pushfd | Mnemonic::Pushfq => {
                self.push(self.rflags())?;
                Ok(None)
            }
            Mnemonic::Popf | Mnemonic::Popfd | Mnemonic::Popfq => {
                let v = self.pop()?;
                self.set_rflags(v);
                Ok(None)
            }
            _ if let Some((op, bytes)) = StringOp::of(m)
                && !has_vector_operand(i) =>
            {
                self.string_op(i, op, bytes)
            }
            _ if let Some(op) = Alu::of(m) => self.alu(i, op),
            Mnemonic::Inc | Mnemonic::Dec => {
                let a = self.dest(i)?;
                let r = if m == Mnemonic::Inc {
                    a.wrapping_add(1)
                } else {
                    a.wrapping_sub(1)
                };
                self.set_flags(r, op_bits(i));
                self.store(i, r)?;
                Ok(None)
            }
            Mnemonic::Neg | Mnemonic::Not => {
                let a = self.dest(i)?;
                let r = if m == Mnemonic::Neg {
                    0u64.wrapping_sub(a)
                } else {
                    !a
                };
                if m == Mnemonic::Neg {
                    let bits = op_bits(i);
                    let a = mask(a, bits);
                    self.flags_carry = a != 0;
                    self.set_flags(r, bits);
                    self.flags_over = Some(a == 1 << (bits - 1));
                }
                self.store(i, r)?;
                Ok(None)
            }
            Mnemonic::Imul if i.op_count() == 2 => {
                let a = self.dest(i)?;
                let b = self.source(i)?;
                self.truncating_multiply(i, a, b)
            }
            Mnemonic::Imul if i.op_count() == 3 => {
                let b = self.operand(i, 1)?;
                let c = self.operand(i, 2)?;
                self.truncating_multiply(i, b, c)
            }
            Mnemonic::Mul | Mnemonic::Imul if i.op_count() == 1 => self.widening_multiply(i, m),
            Mnemonic::Bt | Mnemonic::Bts | Mnemonic::Btr | Mnemonic::Btc => self.bit_test(i, m),
            Mnemonic::Bsf
            | Mnemonic::Bsr
            | Mnemonic::Tzcnt
            | Mnemonic::Lzcnt
            | Mnemonic::Popcnt => self.bit_count(i, m),
            Mnemonic::Bswap => self.byte_swap(i),
            Mnemonic::Shlx | Mnemonic::Shrx | Mnemonic::Sarx | Mnemonic::Rorx | Mnemonic::Andn => {
                self.bmi(i, m)
            }
            Mnemonic::Shld | Mnemonic::Shrd => self.double_shift(i, m),
            _ if let Some(op) = Shift::of(m) => self.shift(i, op),
            Mnemonic::Jmp => {
                let to = self.transfer_target(i)?;
                if indirect(i) {
                    self.jumps.push((i.ip(), to));
                }
                if self.unresolved(to) {
                    self.skipped += 1;
                    return self.pop().map(Some);
                }
                Ok(Some(to))
            }
            Mnemonic::Call => {
                let to = self.transfer_target(i)?;
                if self.unresolved(to) {
                    self.skipped += 1;
                    self.set_reg(Register::RAX, 0);
                    return Ok(None);
                }
                self.push(i.next_ip())?;
                Ok(Some(to))
            }
            Mnemonic::Ret => {
                if self.reg(Register::RSP) >= self.stack_base {
                    return Err(Stop::Returned);
                }
                let ra = self.pop()?;
                if i.op_count() == 1 {
                    let sp = self.narrow(
                        self.reg(Register::RSP)
                            .wrapping_add(u64::from(i.immediate16())),
                    );
                    self.set_reg(Register::RSP, sp);
                }
                Ok(Some(ra))
            }
            _ if is_jcc(m) => {
                if self.condition(m, m)? {
                    branch_target(i)
                        .map(Some)
                        .ok_or_else(|| Stop::Unmodeled(format!("indirect {m:?}")))
                } else {
                    Ok(None)
                }
            }
            Mnemonic::Loop | Mnemonic::Loope | Mnemonic::Loopne => {
                let rcx = self.narrow(self.reg(Register::RCX).wrapping_sub(1));
                self.set_reg(Register::RCX, rcx);
                let again = match m {
                    Mnemonic::Loope => self.flags_zero,
                    Mnemonic::Loopne => !self.flags_zero,
                    _ => true,
                };
                if rcx != 0 && again {
                    Ok(branch_target(i))
                } else {
                    Ok(None)
                }
            }
            Mnemonic::Movaps
            | Mnemonic::Movups
            | Mnemonic::Movapd
            | Mnemonic::Movupd
            | Mnemonic::Movdqa
            | Mnemonic::Movdqu => {
                let v = self.vector_operand(i, 1)?;
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Movss | Mnemonic::Movsd | Mnemonic::Movd | Mnemonic::Movq
                if i.op_count() == 2 =>
            {
                self.scalar_move(i, Width::of_scalar(m))?;
                Ok(None)
            }
            Mnemonic::Movlps | Mnemonic::Movlpd | Mnemonic::Movhps | Mnemonic::Movhpd
                if i.op_count() == 2 =>
            {
                let high = matches!(m, Mnemonic::Movhps | Mnemonic::Movhpd);
                let shift = if high { 64 } else { 0 };
                let half = u128::from(u64::MAX) << shift;
                if i.op0_kind() == OpKind::Register && xmm_slot(i.op0_register()).is_some() {
                    let src = u128::from(self.load(self.mem_addr(i)?, 8)?) << shift;
                    let keep = self.vector_operand(i, 0)? & !half;
                    self.vector_store(i, keep | src)?;
                } else {
                    let v = lo64(self.vector_operand(i, 1)? >> shift);
                    self.store(i, v)?;
                }
                Ok(None)
            }
            Mnemonic::Paddb
            | Mnemonic::Paddw
            | Mnemonic::Paddd
            | Mnemonic::Paddq
            | Mnemonic::Psubb
            | Mnemonic::Psubw
            | Mnemonic::Psubd
            | Mnemonic::Psubq
            | Mnemonic::Pmuludq
                if i.op_count() == 2 =>
            {
                let l = self.vector_operand(i, 0)?;
                let r = self.vector_operand(i, 1)?;
                let v = match m {
                    Mnemonic::Pmuludq => packed(l, r, 64, |a, b| {
                        u64::from(lo32(a)).wrapping_mul(u64::from(lo32(b)))
                    }),
                    Mnemonic::Psubb | Mnemonic::Psubw | Mnemonic::Psubd | Mnemonic::Psubq => {
                        packed(l, r, lane_bits(m), u64::wrapping_sub)
                    }
                    _ => packed(l, r, lane_bits(m), u64::wrapping_add),
                };
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Psllw
            | Mnemonic::Pslld
            | Mnemonic::Psllq
            | Mnemonic::Psrlw
            | Mnemonic::Psrld
            | Mnemonic::Psrlq
                if i.op_count() == 2 =>
            {
                let l = self.vector_operand(i, 0)?;
                let count = if i.op_kind(1) == OpKind::Immediate8 {
                    u64::from(i.immediate8())
                } else {
                    lo64(self.vector_operand(i, 1)?)
                };
                let bits = lane_bits(m);
                let right = matches!(m, Mnemonic::Psrlw | Mnemonic::Psrld | Mnemonic::Psrlq);
                let v = packed(l, 0, bits, |a, _| {
                    if count >= u64::from(bits) {
                        0
                    } else if right {
                        a >> count
                    } else {
                        a << count
                    }
                });
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Punpcklbw
            | Mnemonic::Punpcklwd
            | Mnemonic::Punpckldq
            | Mnemonic::Punpcklqdq
            | Mnemonic::Punpckhbw
            | Mnemonic::Punpckhwd
            | Mnemonic::Punpckhdq
            | Mnemonic::Punpckhqdq
                if i.op_count() == 2 =>
            {
                let bits = lane_bits(m);
                let high = matches!(
                    m,
                    Mnemonic::Punpckhbw
                        | Mnemonic::Punpckhwd
                        | Mnemonic::Punpckhdq
                        | Mnemonic::Punpckhqdq
                );
                let dst = self.vector_operand(i, 0)?;
                let src = self.vector_operand(i, 1)?;
                let lanes = 64 / bits;
                let first = if high { lanes } else { 0 };
                let mask = (1u128 << bits) - 1;
                let mut v = 0u128;
                for k in 0..lanes {
                    let from = (first + k) * bits;
                    v |= ((dst >> from) & mask) << (2 * k * bits);
                    v |= ((src >> from) & mask) << ((2 * k + 1) * bits);
                }
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Cbw | Mnemonic::Cwde | Mnemonic::Cdqe => {
                let (from, to): (usize, usize) = match m {
                    Mnemonic::Cbw => (1, 2),
                    Mnemonic::Cwde => (2, 4),
                    _ => (4, 8),
                };
                let narrow = self.reg_sized(sized_ax(from));
                let wide = sign_extend(narrow, width_bits(from)).cast_unsigned();
                self.set_reg_sized(sized_ax(to), wide);
                Ok(None)
            }
            Mnemonic::Cwd | Mnemonic::Cdq | Mnemonic::Cqo => {
                let bytes: usize = match m {
                    Mnemonic::Cwd => 2,
                    Mnemonic::Cdq => 4,
                    _ => 8,
                };
                let acc = self.reg_sized(sized_ax(bytes));
                let negative = sign_extend(acc, width_bits(bytes)) < 0;
                let spread = if negative { u64::MAX } else { 0 };
                self.set_reg_sized(remainder(bytes), spread);
                Ok(None)
            }
            Mnemonic::Packuswb | Mnemonic::Packsswb | Mnemonic::Packssdw if i.op_count() == 2 => {
                let wide: u32 = if m == Mnemonic::Packssdw { 32 } else { 16 };
                let narrow = wide / 2;
                let signed_out = m != Mnemonic::Packuswb;
                let dst = self.vector_operand(i, 0)?;
                let src = self.vector_operand(i, 1)?;
                let wmask = (1u128 << wide) - 1;
                let nmask = (1u128 << narrow) - 1;
                let lanes = 128 / wide;
                let mut v = 0u128;
                for (slot, from) in [(0u32, dst), (1, src)] {
                    for k in 0..lanes {
                        let lane = lo64((from >> (k * wide)) & wmask);
                        let signed = sign_extend(lane, wide);
                        let clamped = if signed_out {
                            let top = (1i64 << (narrow - 1)) - 1;
                            signed.clamp(-top - 1, top).cast_unsigned() & lo64(nmask)
                        } else {
                            let top = (1i64 << narrow) - 1;
                            signed.clamp(0, top).cast_unsigned()
                        };
                        let at = (slot * lanes + k) * narrow;
                        v |= u128::from(clamped) << at;
                    }
                }
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Shufps | Mnemonic::Shufpd
                if i.op_count() == 3 && i.op_kind(2) == OpKind::Immediate8 =>
            {
                let dst = self.vector_operand(i, 0)?;
                let src = self.vector_operand(i, 1)?;
                let sel = i.immediate8();
                let v = if m == Mnemonic::Shufps {
                    let mut v = 0u128;
                    for slot in 0..4u32 {
                        let from = if slot < 2 { dst } else { src };
                        let pick = u32::from(sel >> (slot * 2)) & 3;
                        v |= ((from >> (pick * 32)) & 0xffff_ffff) << (slot * 32);
                    }
                    v
                } else {
                    let lo = (dst >> (u32::from(sel & 1) * 64)) & u128::from(u64::MAX);
                    let hi = (src >> (u32::from(sel >> 1 & 1) * 64)) & u128::from(u64::MAX);
                    lo | (hi << 64)
                };
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Pshufd if i.op_count() == 3 && i.op_kind(2) == OpKind::Immediate8 => {
                let src = self.vector_operand(i, 1)?;
                let sel = i.immediate8();
                let mut v = 0u128;
                for slot in 0..4u32 {
                    let pick = u32::from(sel >> (slot * 2)) & 3;
                    let word = (src >> (pick * 32)) & 0xffff_ffff;
                    v |= word << (slot * 32);
                }
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Fld | Mnemonic::Fild => self.fpu_load(i, m),
            Mnemonic::Fld1 | Mnemonic::Fldz => {
                self.fpush(if m == Mnemonic::Fld1 { 1.0 } else { 0.0 });
                Ok(None)
            }
            Mnemonic::Fst
            | Mnemonic::Fstp
            | Mnemonic::Fist
            | Mnemonic::Fistp
            | Mnemonic::Fisttp => self.fpu_store(i, m),
            _ if let Some(op) = FpuArith::of(m) => self.fpu_arith(i, m, op),
            Mnemonic::Fxch => {
                let other = match i.op_count() {
                    0 => 1,
                    n => st_depth_mod8(i.op_register(n - 1)),
                };
                let (a, b) = (self.st(0), self.st(other));
                self.set_st(0, b);
                self.set_st(other, a);
                Ok(None)
            }
            Mnemonic::Fchs | Mnemonic::Fabs => {
                let v = if m == Mnemonic::Fchs {
                    -self.st(0)
                } else {
                    self.st(0).abs()
                };
                self.set_st(0, v);
                Ok(None)
            }
            Mnemonic::Frndint => {
                self.set_st(0, self.st(0).round_ties_even());
                Ok(None)
            }
            Mnemonic::Fsincos | Mnemonic::Fptan => {
                let x = self.st(0);
                if !(x.is_finite() && x.abs() >= FPU_TRIG_RANGE) {
                    let (below, top) = if m == Mnemonic::Fsincos {
                        (x.sin(), x.cos())
                    } else {
                        (x.tan(), 1.0)
                    };
                    self.set_st(0, below);
                    self.fpush(top);
                }
                Ok(None)
            }
            Mnemonic::Cpuid => {
                let leaf = lo32(self.reg(Register::RAX));
                let (a, b, c, d) = cpuid_leaf(leaf);
                self.set_reg(Register::RAX, u64::from(a));
                self.set_reg(Register::RBX, u64::from(b));
                self.set_reg(Register::RCX, u64::from(c));
                self.set_reg(Register::RDX, u64::from(d));
                if leaf == 1 || leaf & 0xffff_0000 == 0x4000_0000 {
                    self.neutralized.insert(format!("cpuid({leaf:#x})"));
                }
                Ok(None)
            }
            Mnemonic::Syscall => self.linux_syscall(i),
            Mnemonic::Movlhps | Mnemonic::Movhlps if i.op_count() == 2 => {
                let lo = u128::from(u64::MAX);
                let src = self.vector_operand(i, 1)?;
                let dst = self.vector_operand(i, 0)?;
                let v = if m == Mnemonic::Movlhps {
                    (dst & lo) | ((src & lo) << 64)
                } else {
                    (dst & !lo) | (src >> 64)
                };
                self.vector_store(i, v)?;
                Ok(None)
            }
            Mnemonic::Cmpxchg if i.op_count() == 2 && i.op_kind(1) == OpKind::Register => {
                let bits = op_bits(i);
                let dst = mask(self.operand(i, 0)?, bits);
                let src = self.operand(i, 1)?;
                let acc = sized_ax(operand_bytes(i, 0));
                let a = mask(self.reg_sized(acc), bits);
                let diff = a.wrapping_sub(dst);
                self.flags_carry = a < dst;
                self.set_flags(diff, bits);
                let signed = |v: u64| v >> (bits - 1) & 1 == 1;
                self.flags_over = Some(signed(a) != signed(dst) && signed(diff) != signed(a));
                if a == dst {
                    self.store(i, src)?;
                } else {
                    self.set_reg_sized(acc, dst);
                }
                Ok(None)
            }
            Mnemonic::Div | Mnemonic::Idiv if i.op_count() == 1 => {
                let d = self.operand(i, 0)?;
                if d == 0 {
                    return Err(Stop::Unmodeled(String::from("divide by zero")));
                }
                let w = operand_bytes(i, 0);
                let bits = width_bits(w);
                let dividend = if w == 1 {
                    u128::from(self.reg_sized(Register::AX))
                } else {
                    u128::from(self.reg_sized(remainder(w))) << bits
                        | u128::from(self.reg_sized(sized_ax(w)))
                };
                let fits = if m == Mnemonic::Div {
                    let (q, r) = (dividend / u128::from(d), dividend % u128::from(d));
                    (q >> bits == 0).then_some((lo64(q), lo64(r)))
                } else {
                    let spread = 128 - 2 * bits;
                    let n = (dividend << spread).cast_signed() >> spread;
                    let v = i128::from(sign_extend(d, bits));
                    let half = 1i128 << (bits - 1);
                    n.checked_div(v)
                        .zip(n.checked_rem(v))
                        .filter(|(q, _)| (-half..half).contains(q))
                        .map(|(q, r)| (lo64(q.cast_unsigned()), lo64(r.cast_unsigned())))
                };
                let Some((q, r)) = fits else {
                    return Err(Stop::Unmodeled(String::from("divide overflow")));
                };
                self.set_reg_sized(sized_ax(w), q);
                self.set_reg_sized(remainder(w), r);
                Ok(None)
            }
            Mnemonic::Xchg if i.op_count() == 2 && i.op_kind(1) == OpKind::Register => {
                let l = self.operand(i, 0)?;
                let r = self.operand(i, 1)?;
                self.set_reg_sized(i.op1_register(), l);
                self.store(i, r)?;
                Ok(None)
            }
            Mnemonic::Rdtsc | Mnemonic::Rdtscp => {
                self.ticks = self.ticks.wrapping_add(0x40);
                let t = self.ticks;
                self.set_reg(Register::RAX, t & 0xffff_ffff);
                self.set_reg(Register::RDX, t >> 32);
                if m == Mnemonic::Rdtscp {
                    self.set_reg(Register::RCX, 0);
                }
                self.neutralized.insert(format!("{m:?}").to_lowercase());
                Ok(None)
            }
            Mnemonic::Xadd if i.op_count() == 2 && i.op_kind(1) == OpKind::Register => {
                let bits = op_bits(i);
                let a = mask(self.operand(i, 0)?, bits);
                let b = mask(self.operand(i, 1)?, bits);
                let sum = mask(a.wrapping_add(b), bits);
                self.flags_carry = u128::from(a) + u128::from(b) >= 1u128 << bits;
                self.set_flags(sum, bits);
                let signed = |v: u64| v >> (bits - 1) & 1 == 1;
                self.flags_over = Some(signed(a) == signed(b) && signed(sum) != signed(a));
                self.set_reg_sized(i.op1_register(), a);
                self.store(i, sum)?;
                Ok(None)
            }
            _ if let Some(cond) = setcc_condition(m) => {
                let taken = self.condition(m, cond)?;
                self.store(i, u64::from(taken))?;
                Ok(None)
            }
            _ if let Some(cond) = cmovcc_condition(m) => {
                if self.condition(m, cond)? {
                    let v = self.operand(i, 1)?;
                    self.store(i, v)?;
                } else if self.bitness == 64
                    && i.op0_kind() == OpKind::Register
                    && i.op0_register().size() == 4
                {
                    let v = self.reg_sized(i.op0_register());
                    self.store(i, v)?;
                }
                Ok(None)
            }
            other => self
                .vector_op(i, other)
                .unwrap_or_else(|| Err(Stop::Unmodeled(format!("{other:?}")))),
        }
    }

    /// Whether a conditional jump is taken under the current flags.
    ///
    /// The signed conditions read the sign flag against the overflow flag,
    /// and the zero flag decides the ones that include equality: `jg` after
    /// comparing a value with itself is not taken, which reading the sign
    /// flag alone gets wrong. A condition resting on a flag the last
    /// instruction did not compute is not guessed.
    ///
    /// # Arguments
    ///
    /// * `m` - The conditional jump's mnemonic.
    ///
    /// # Returns
    ///
    /// Whether it is taken, or `None` when the flags do not say.
    fn jcc_taken(&self, m: Mnemonic) -> Option<bool> {
        let (z, c, s) = (self.flags_zero, self.flags_carry, self.flags_sign);
        Some(match m {
            Mnemonic::Je => z,
            Mnemonic::Jne => !z,
            Mnemonic::Jb => c,
            Mnemonic::Jae => !c,
            Mnemonic::Jbe => c || z,
            Mnemonic::Ja => !c && !z,
            Mnemonic::Js => s,
            Mnemonic::Jns => !s,
            Mnemonic::Jg => !z && s == self.flags_over?,
            Mnemonic::Jge => s == self.flags_over?,
            Mnemonic::Jl => s != self.flags_over?,
            Mnemonic::Jle => z || s != self.flags_over?,
            Mnemonic::Jo => self.flags_over?,
            Mnemonic::Jno => !self.flags_over?,
            Mnemonic::Jp => self.flags_parity,
            Mnemonic::Jnp => !self.flags_parity,
            _ => return None,
        })
    }
}

/// The near branch target of a direct jump, if it is one.
///
/// # Arguments
///
/// * `i` - The jump.
fn branch_target(i: &Instruction) -> Option<u64> {
    match i.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            Some(i.near_branch_target())
        }
        _ => None,
    }
}

/// Whether a transfer is indirect (through a register or memory), the shape a
/// VM dispatch uses.
///
/// # Arguments
///
/// * `i` - The jump or call.
fn indirect(i: &Instruction) -> bool {
    matches!(i.op0_kind(), OpKind::Register | OpKind::Memory)
}

/// The operand width in bits, from operand 0.
///
/// # Arguments
///
/// * `i` - The instruction.
fn op_bits(i: &Instruction) -> u32 {
    match i.op0_kind() {
        OpKind::Register => reg_bits(i.op0_register()),
        OpKind::Memory => u32::try_from(mem_bytes(i) * 8).unwrap_or(64),
        _ => 64,
    }
}

/// Masks `v` to `bits` low bits.
fn mask(v: u64, bits: u32) -> u64 {
    if bits >= 64 {
        v
    } else {
        v & ((1u64 << bits) - 1)
    }
}

/// The low 64 bits of a 128-bit value.
///
/// One lane of a vector, or the half of a double-width product or sum
/// that fits a register.
///
/// # Arguments
///
/// * `v` - The value.
#[expect(
    clippy::cast_possible_truncation,
    reason = "the low bits are the point"
)]
const fn lo64(v: u128) -> u64 {
    v as u64
}

/// A register's width in bits.
///
/// # Arguments
///
/// * `r` - The register.
fn reg_bits(r: Register) -> u32 {
    width_bits(r.size())
}

/// An operand's width in bits, from its width in bytes.
///
/// # Arguments
///
/// * `bytes` - The width in bytes; an operand is at most sixteen, so the
///   product always fits and the fallback is never taken.
fn width_bits(bytes: usize) -> u32 {
    u32::try_from(bytes * 8).unwrap_or(64)
}

/// Whether any operand is a vector register: the SSE forms of `movsd` and
/// `cmpsd`, which share a mnemonic with the string steps.
///
/// # Arguments
///
/// * `i` - The instruction.
fn has_vector_operand(i: &Instruction) -> bool {
    (0..i.op_count()).any(|k| is_vector(i.op_register(k)))
}

/// The lane width of a packed integer instruction, from its suffix: `b`
/// is 8, `w` 16, `d` 32 and `q` 64; an unpack names both widths and takes
/// the narrower.
///
/// # Arguments
///
/// * `m` - The mnemonic.
pub(super) fn lane_bits(m: Mnemonic) -> u32 {
    use Mnemonic as M;
    match m {
        M::Paddb
        | M::Psubb
        | M::Vpaddb
        | M::Vpsubb
        | M::Punpcklbw
        | M::Punpckhbw
        | M::Pcmpeqb
        | M::Pcmpgtb
        | M::Vpcmpeqb
        | M::Vpcmpgtb => 8,
        M::Paddw
        | M::Psubw
        | M::Vpaddw
        | M::Vpsubw
        | M::Psllw
        | M::Psrlw
        | M::Psraw
        | M::Vpsraw
        | M::Punpcklwd
        | M::Punpckhwd
        | M::Pcmpeqw
        | M::Pcmpgtw
        | M::Vpcmpeqw
        | M::Vpcmpgtw => 16,
        M::Paddd
        | M::Psubd
        | M::Vpaddd
        | M::Vpsubd
        | M::Pslld
        | M::Psrld
        | M::Psrad
        | M::Vpsrad
        | M::Punpckldq
        | M::Punpckhdq
        | M::Pcmpeqd
        | M::Pcmpgtd
        | M::Vpcmpeqd
        | M::Vpcmpgtd => 32,
        _ => 64,
    }
}

/// Sign-extends the low `bits` of `v` to a full `i64`.
fn sign_extend(v: u64, bits: u32) -> i64 {
    if bits >= 64 {
        return v.cast_signed();
    }
    let shift = 64 - bits;
    (v << shift).cast_signed() >> shift
}

/// Rotates the low `bits` of `v` left by `count`.
fn rotate_left(v: u64, count: u32, bits: u32) -> u64 {
    let c = count % bits;
    if c == 0 {
        return v;
    }
    mask((v << c) | (v >> (bits - c)), bits)
}

/// Rotates the low `bits` of `v` right by `count`.
fn rotate_right(v: u64, count: u32, bits: u32) -> u64 {
    let c = count % bits;
    if c == 0 {
        return v;
    }
    mask((v >> c) | (v << (bits - c)), bits)
}

/// The byte width a memory operand reads or writes.
fn mem_bytes(i: &Instruction) -> usize {
    i.memory_size().size().max(1)
}

/// The full 64-bit register a sub-register belongs to.
fn canon(r: Register) -> Register {
    if r.is_gpr() { r.full_register() } else { r }
}

/// The segment registers the emulator holds, `es` first, one per slot of
/// [`Emulator::segments`].
pub(crate) const SEG_ORDER: [Register; 6] = [
    Register::ES,
    Register::CS,
    Register::SS,
    Register::DS,
    Register::FS,
    Register::GS,
];

/// The slot a segment register occupies in [`Emulator::segments`].
///
/// # Arguments
///
/// * `r` - The register.
///
/// # Returns
///
/// The slot, or `None` for a register that is not a segment one.
fn seg_slot(r: Register) -> Option<usize> {
    SEG_ORDER.iter().position(|&s| s == r)
}

/// Whether `r` is a vector register: marks the SSE forms of `movsd`/`cmpsd`.
fn is_vector(r: Register) -> bool {
    r.is_xmm() || r.is_ymm() || r.is_zmm()
}

/// Returns the bit a register starts at within its full register: 8 for
/// `ah`, `bh`, `ch` and `dh`, which name bits 8 to 15, and 0 for every other.
///
/// # Arguments
///
/// * `r` - The register as the instruction names it.
fn lane_shift(r: Register) -> u32 {
    if matches!(r, Register::AH | Register::BH | Register::CH | Register::DH) {
        8
    } else {
        0
    }
}

/// The accumulator sub-register of the given byte width.
///
/// # Arguments
///
/// * `bytes` - The width, 1, 2, 4 or 8.
fn sized_ax(bytes: usize) -> Register {
    match bytes {
        1 => Register::AL,
        2 => Register::AX,
        4 => Register::EAX,
        _ => Register::RAX,
    }
}

/// Maps a `setcc` to the `jcc` that reads the same flags.
///
/// A checksum ends in `sete al` or `setne al` as often as it ends in a
/// branch, and stopping there leaves the run with nothing to report.
///
/// # Arguments
///
/// * `m` - The mnemonic.
///
/// # Returns
///
/// The matching conditional jump, or `None` when `m` is not a `setcc`.
fn setcc_condition(m: Mnemonic) -> Option<Mnemonic> {
    Some(match m {
        Mnemonic::Sete => Mnemonic::Je,
        Mnemonic::Setne => Mnemonic::Jne,
        Mnemonic::Setb => Mnemonic::Jb,
        Mnemonic::Setae => Mnemonic::Jae,
        Mnemonic::Setbe => Mnemonic::Jbe,
        Mnemonic::Seta => Mnemonic::Ja,
        Mnemonic::Sets => Mnemonic::Js,
        Mnemonic::Setns => Mnemonic::Jns,
        Mnemonic::Setg => Mnemonic::Jg,
        Mnemonic::Setge => Mnemonic::Jge,
        Mnemonic::Setl => Mnemonic::Jl,
        Mnemonic::Setle => Mnemonic::Jle,
        Mnemonic::Seto => Mnemonic::Jo,
        Mnemonic::Setno => Mnemonic::Jno,
        Mnemonic::Setp => Mnemonic::Jp,
        Mnemonic::Setnp => Mnemonic::Jnp,
        _ => return None,
    })
}

/// Maps a `cmovcc` to the `jcc` that reads the same flags.
///
/// # Arguments
///
/// * `m` - The mnemonic.
///
/// # Returns
///
/// The matching conditional jump, or `None` when `m` is not a `cmovcc`.
fn cmovcc_condition(m: Mnemonic) -> Option<Mnemonic> {
    Some(match m {
        Mnemonic::Cmove => Mnemonic::Je,
        Mnemonic::Cmovne => Mnemonic::Jne,
        Mnemonic::Cmovb => Mnemonic::Jb,
        Mnemonic::Cmovae => Mnemonic::Jae,
        Mnemonic::Cmovbe => Mnemonic::Jbe,
        Mnemonic::Cmova => Mnemonic::Ja,
        Mnemonic::Cmovs => Mnemonic::Js,
        Mnemonic::Cmovns => Mnemonic::Jns,
        Mnemonic::Cmovg => Mnemonic::Jg,
        Mnemonic::Cmovge => Mnemonic::Jge,
        Mnemonic::Cmovl => Mnemonic::Jl,
        Mnemonic::Cmovle => Mnemonic::Jle,
        Mnemonic::Cmovo => Mnemonic::Jo,
        Mnemonic::Cmovno => Mnemonic::Jno,
        Mnemonic::Cmovp => Mnemonic::Jp,
        Mnemonic::Cmovnp => Mnemonic::Jnp,
        _ => return None,
    })
}

/// The index of an `ymm` register: `ymm0..15` share storage with
/// `xmm0..15`, whose lanes the upper halves in [`Emulator::ymm_hi`] extend.
///
/// # Arguments
///
/// * `r` - The register.
///
/// # Returns
///
/// Its index, or `None` when `r` is not one of the sixteen `ymm` registers.
fn ymm_index(r: Register) -> Option<usize> {
    (r >= Register::YMM0 && r <= Register::YMM15).then(|| r as usize - Register::YMM0 as usize)
}
/// An operand's width in bytes: the register's, or the memory access's.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `n` - The operand index.
fn operand_bytes(i: &Instruction, n: u32) -> usize {
    if i.op_kind(n) == OpKind::Register {
        i.op_register(n).size()
    } else {
        mem_bytes(i)
    }
}

/// The register a division leaves its remainder in, by operand width.
///
/// # Arguments
///
/// * `bytes` - The width, 1, 2, 4 or 8.
fn remainder(bytes: usize) -> Register {
    match bytes {
        1 => Register::AH,
        2 => Register::DX,
        4 => Register::EDX,
        _ => Register::RDX,
    }
}

/// Whether a mnemonic is a conditional jump the emulator evaluates.
fn is_jcc(m: Mnemonic) -> bool {
    matches!(
        m,
        Mnemonic::Je
            | Mnemonic::Jne
            | Mnemonic::Jb
            | Mnemonic::Jae
            | Mnemonic::Jbe
            | Mnemonic::Ja
            | Mnemonic::Js
            | Mnemonic::Jns
            | Mnemonic::Jg
            | Mnemonic::Jge
            | Mnemonic::Jl
            | Mnemonic::Jle
            | Mnemonic::Jo
            | Mnemonic::Jno
            | Mnemonic::Jp
            | Mnemonic::Jnp
    )
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::fpu::{extended_to_f64, f64_to_extended};
    use super::{Emulator, PageRun, Stop, TRACE_MAX, fill_byte, lo8};
    use crate::program::{Arch, BinaryFormat, Program, Section};

    /// Vector moves and clears run instead of stopping the machine.
    ///
    /// A compiler emits these constantly, so a machine without them stops on
    /// the first `movaps`: across a hundred functions of one real binary,
    /// vector moves were 29 of the 33 unmodeled stops.
    ///
    /// # Panics
    ///
    /// When the run does not reach the return.
    #[test]
    fn vector_moves_and_clears_run() {
        // ASM: xorps xmm0,xmm0; movaps xmm1,xmm0; movss xmm2,xmm1; ret
        let code: &[u8] = &[
            0x0f, 0x57, 0xc0, 0x0f, 0x28, 0xc8, 0xf3, 0x0f, 0x10, 0xd1, 0xc3,
        ];
        returned(image(code, &[]));
    }

    /// A `setcc` writes the flag it tests instead of stopping the machine.
    ///
    /// # Panics
    ///
    /// When the run does not reach the return, or the byte is not the flag.
    #[test]
    fn setcc_writes_the_condition() {
        // ASM: xor eax,eax; cmp eax,0; sete al; ret
        let code: &[u8] = &[0x31, 0xc0, 0x83, 0xf8, 0x00, 0x0f, 0x94, 0xc0, 0xc3];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(1));
    }

    /// A division divides its whole dividend with its sign.
    ///
    /// `idiv` after `cdq` divides the negative `eax` as negative, a byte
    /// `div` divides all of `ax`, and a quotient too wide for its register
    /// stops the run where the CPU raises a divide error. Taking only `eax`,
    /// unsigned, answered `-7 / 2` with `0x7ffffffc` remainder `1`.
    ///
    /// # Panics
    ///
    /// When a quotient or remainder differs from the CPU's, or the
    /// overflowing division runs on.
    #[test]
    fn a_division_divides_the_whole_signed_dividend() {
        // ASM: mov eax,-7; cdq; mov ecx,2; idiv ecx; ret
        let code: &[u8] = &[
            0xb8, 0xf9, 0xff, 0xff, 0xff, 0x99, 0xb9, 0x02, 0x00, 0x00, 0x00, 0xf7, 0xf9, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(0xffff_fffd), "quotient -3");
        assert_eq!(emu.register("rdx"), Some(0xffff_ffff), "remainder -1");

        // ASM: mov ax,0x107; mov cl,2; div cl; ret
        let code: &[u8] = &[0x66, 0xb8, 0x07, 0x01, 0xb1, 0x02, 0xf6, 0xf1, 0xc3];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(0x0183), "263 / 2: al 131, ah 1");

        // ASM: mov edx,2; mov eax,0; mov ecx,1; div ecx; ret
        let code: &[u8] = &[
            0xba, 0x02, 0x00, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0xb9, 0x01, 0x00, 0x00,
            0x00, 0xf7, 0xf1, 0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert!(
            matches!(&run.stop, Stop::Unmodeled(why) if why == "divide overflow"),
            "{:?}",
            run.stop
        );
    }

    /// `neg` sets the flags of `0 - operand`.
    ///
    /// An absolute value is `neg` then `cmovs`, and `neg` then `sbb` turns
    /// "not zero" into a mask; with the flags left as they were, both took
    /// whatever the instruction before had set.
    ///
    /// # Panics
    ///
    /// When the sign or carry after `neg` is not the subtraction's.
    #[test]
    fn neg_sets_the_flags_of_a_subtraction_from_zero() {
        // ASM: mov eax,5; neg eax; sets cl; setc dl; ret
        let code: &[u8] = &[
            0xb8, 0x05, 0x00, 0x00, 0x00, 0xf7, 0xd8, 0x0f, 0x98, 0xc1, 0x0f, 0x92, 0xc2, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rcx"), Some(1), "-5 is negative");
        assert_eq!(emu.register("rdx"), Some(1), "5 is not zero, so carry");
    }

    /// `ah`, `bh`, `ch` and `dh` are bits 8 to 15 of their register.
    ///
    /// Read as the low byte, `movzx ecx, ah` answered `al`; written as the
    /// low byte, `div cl` put its remainder over its quotient.
    ///
    /// # Panics
    ///
    /// When a high byte reads or writes any other bits.
    #[test]
    fn a_high_byte_register_is_bits_8_to_15() {
        // ASM: mov eax,0x1234; movzx ecx,ah; mov bh,0x56; mov bl,0x78; ret
        let code: &[u8] = &[
            0xb8, 0x34, 0x12, 0x00, 0x00, 0x0f, 0xb6, 0xcc, 0xb7, 0x56, 0xb3, 0x78, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rcx"), Some(0x12));
        assert_eq!(emu.register("rbx").map(|v| v & 0xffff), Some(0x5678));
    }

    /// A stop reason reads as words with its address in hex, not as the
    /// enum's syntax or a decimal.
    ///
    /// # Panics
    ///
    /// When a reason reads as a variant or an address as decimal.
    #[test]
    fn a_stop_reason_reads_as_words_in_hex() {
        for (stop, words) in [
            (Stop::Fault(0x7fff_0000_0028), "fault at 0x7fff00000028"),
            (Stop::Stopped(0x1400), "stopped at 0x1400"),
            (Stop::Derailed(0x2000), "derailed at 0x2000"),
            (Stop::Unmodeled("Xgetbv".to_owned()), "unmodeled Xgetbv"),
            (Stop::Returned, "returned"),
            (Stop::Budget, "budget exhausted"),
            (Stop::Exited, "the program exited"),
            (
                Stop::Limit(super::Limit::Calls),
                "stopped: api call limit (65536 recorded)",
            ),
        ] {
            assert_eq!(stop.to_string(), words);
        }
    }

    /// A `syscall` is answered instead of stopping an ELF's bootstrap.
    ///
    /// `mmap` hands out a region the following store writes through,
    /// `write` returns its count, an unknown number answers zero with the
    /// run continuing, and the exit numbers end the program.
    ///
    /// # Panics
    ///
    /// When any answer, the clobbered `rcx`, or the exit differs.
    #[test]
    fn a_syscall_is_answered_and_the_exit_numbers_end_the_program() {
        // ASM: mov eax,9; xor edi,edi; mov esi,0x1000; xor edx,edx;
        //      mov r10d,0x22; xor r8d,r8d; xor r9d,r9d; syscall;
        //      mov rsi,rax; mov dword [rsi],0x44434241; mov eax,[rsi]; ret
        let code: &[u8] = &[
            0xb8, 0x09, 0x00, 0x00, 0x00, 0x31, 0xff, 0xbe, 0x00, 0x10, 0x00, 0x00, 0x31, 0xd2,
            0x41, 0xba, 0x22, 0x00, 0x00, 0x00, 0x45, 0x31, 0xc0, 0x45, 0x31, 0xc9, 0x0f, 0x05,
            0x48, 0x89, 0xc6, 0xc7, 0x06, 0x41, 0x42, 0x43, 0x44, 0x8b, 0x06, 0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        assert_eq!(
            emu.register("rax"),
            Some(0x4443_4241),
            "the store wrote through the mmap answer"
        );
        assert_eq!(
            emu.peek(super::ALLOC_BASE),
            Some(0x41),
            "mmap handed out the allocator's first region"
        );
        assert_eq!(
            emu.register("rcx"),
            Some(0x101c),
            "syscall left its return address in rcx"
        );
        assert_eq!(
            emu.api_calls()
                .iter()
                .map(|c| (c.syscall, c.api.as_str()))
                .collect::<Vec<_>>(),
            vec![(Some(9), "mmap")],
            "the number seen was noted"
        );

        // ASM: mov eax,1; mov edi,1; xor esi,esi; mov edx,5; syscall;
        //      mov r8d,eax; mov eax,999; syscall; mov r9d,eax; ret
        let code: &[u8] = &[
            0xb8, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x31, 0xf6, 0xba, 0x05,
            0x00, 0x00, 0x00, 0x0f, 0x05, 0x41, 0x89, 0xc0, 0xb8, 0xe7, 0x03, 0x00, 0x00, 0x0f,
            0x05, 0x41, 0x89, 0xc1, 0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        assert_eq!(emu.register("r8"), Some(5), "write returned its count");
        assert_eq!(
            emu.register("r9"),
            Some(0),
            "an unknown number answered zero and the run continued"
        );
        assert!(
            emu.api_calls()
                .iter()
                .any(|c| c.syscall == Some(999) && c.api == "sys_999")
        );
        assert!(emu.neutralized().is_empty(), "{:?}", emu.neutralized());

        // ASM: mov eax,60; xor edi,edi; syscall; mov eax,1; ret
        let code: &[u8] = &[
            0xb8, 0x3c, 0x00, 0x00, 0x00, 0x31, 0xff, 0x0f, 0x05, 0xb8, 0x01, 0x00, 0x00, 0x00,
            0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Exited, "{run:?}");
    }
    /// A byte written before the run executes as code when the run reaches it.
    ///
    /// This is what patching a check away rests on: the bytes go through the
    /// same memory a load reads, so instruction fetch has to see them too,
    /// and a fetch that shortcut to the image would run the original.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the patch did not execute.
    #[test]
    fn a_patched_instruction_executes() {
        let p = image(&[0x31, 0xc0, 0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        for (k, b) in [0xb8, 0x34, 0x12, 0x00, 0x00, 0xc3].into_iter().enumerate() {
            emu.poke(0x1000 + k as u64, b);
        }
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        assert_eq!(emu.register("rax"), Some(0x1234));
    }
    /// A patch is not reported as code the program unpacked.
    ///
    /// The unpacking trace answers "what did this program write and then
    /// run", and an experiment's own patch is not part of that answer.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the patch reads as unpacked code.
    #[test]
    fn a_patch_is_not_unpacked_code() {
        let p = image(&[0x31, 0xc0, 0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.poke(0x1000, 0xc3);
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        assert_eq!(emu.oep(), None, "a patch read as an unpacked entry point");
    }
    /// A run starting at the top of the address space faults, and does not panic.
    ///
    /// The fetch window there runs past the end of the address space, which
    /// is not a range a set can be asked for.
    ///
    /// # Panics
    ///
    /// When the run does not fault.
    #[test]
    fn an_entry_at_the_top_of_memory_faults() {
        let p = image(&[0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.poke(0x1000, 0x90);
        let run = emu.run(u64::MAX);
        assert!(matches!(run.stop, Stop::Fault(_)), "{}", run.stop);
    }
    /// Every register that can be set can be read back, and a typo is refused.
    ///
    /// # Panics
    ///
    /// When a name sets nothing, is missing from the readout, or a typo is
    /// accepted as a register.
    #[test]
    fn the_register_names_agree() {
        let p = image(&[0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        for (i, name) in super::READOUT_ORDER.iter().enumerate() {
            assert!(emu.set_register(name, i as u64), "{name} sets nothing");
            assert_eq!(emu.register(name), Some(i as u64), "{name} reads back");
        }
        let reported: Vec<&str> = emu.registers().iter().map(|(n, _)| *n).collect();
        assert_eq!(reported, super::READOUT_ORDER.to_vec());
        for typo in ["eaxx", "zzz", "", "RAX", "rsp "] {
            assert!(!emu.set_register(typo, 1), "{typo} was accepted");
        }
        assert!(emu.set_register("eax", 7), "the 32-bit spelling sets rax");
        assert_eq!(emu.register("rax"), Some(7));
    }
    /// An argument past the fourth lands in the stack slot the callee reads.
    ///
    /// The Microsoft x64 convention puts arguments five and up on the stack,
    /// so a routine of more than four arguments cannot be set up at all
    /// without writing them there.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the argument did not arrive.
    #[test]
    fn a_fifth_argument_goes_on_the_stack() {
        // ASM: mov rax,[rsp+0x28]; ret  -- reads argument index 4
        let p = image(&[0x48, 0x8b, 0x44, 0x24, 0x28, 0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_arg(4, 0xdead_beef);
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        assert_eq!(emu.register("rax"), Some(0xdead_beef));
    }
    /// `jg` is not taken when the compared values are equal.
    ///
    /// Reading the sign flag alone makes "greater" true for equal operands,
    /// because equality leaves the sign flag clear. The zero flag is what
    /// separates them, so a routine that loops while a counter is greater
    /// than a limit ran one iteration too many, silently.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the branch was taken.
    #[test]
    fn a_greater_than_branch_is_not_taken_on_equality() {
        // ASM: xor eax,eax; cmp eax,eax; jg .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let code: &[u8] = &[
            0x31, 0xc0, 0x39, 0xc0, 0x7f, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02,
            0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(1), "the branch was taken");
    }

    /// A signed comparison reads the overflow flag, not the sign flag.
    ///
    /// Comparing -128 with 1 as bytes leaves the sign flag clear and the
    /// overflow flag set, so "less" is true only for a machine that has both.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the branch was not taken.
    #[test]
    fn a_less_than_branch_reads_the_overflow_flag() {
        // ASM: mov al,0x80; cmp al,1; jl .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let code: &[u8] = &[
            0xb0, 0x80, 0x3c, 0x01, 0x7c, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02,
            0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(2), "the branch was not taken");
    }

    /// A one-bit shift's overflow decides the jump that reads it.
    ///
    /// `shl eax, 1` of `0x40000000` makes `0x80000000`: the carry out is
    /// clear and the result's sign set, so the overflow the SDM defines
    /// for a count of one — the result's sign xored with the carry — is
    /// set, and `jo` is taken where the run used to stop.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the branch was not taken.
    #[test]
    fn a_one_bit_shifts_overflow_decides_its_jump() {
        // ASM: mov eax,0x40000000; shl eax,1; jo .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let code: &[u8] = &[
            0xb8, 0x00, 0x00, 0x00, 0x40, 0xd1, 0xe0, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(2), "the branch was not taken");
    }

    /// The overflow the one-bit right shifts leave is the SDM's.
    ///
    /// `shr` sets it to the sign of the operand it halved, so halving
    /// `0x80000000` sets it and `jo` is taken; `sar` clears it, so the
    /// `jo` after halving the same operand arithmetically is not.
    ///
    /// # Panics
    ///
    /// When a run does not return, or either branch went the wrong way.
    #[test]
    fn the_one_bit_right_shifts_overflow_is_the_sdms() {
        // ASM: mov eax,0x80000000; shr eax,1; jo .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let shr: &[u8] = &[
            0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xe8, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(shr, &[]));
        assert_eq!(emu.register("rax"), Some(2), "shr's overflow was clear");

        // ASM: mov eax,0x80000000; sar eax,1; jo .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let sar: &[u8] = &[
            0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xf8, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(sar, &[]));
        assert_eq!(emu.register("rax"), Some(1), "sar's overflow was set");
    }

    /// A signed jump on flags nothing computed stops instead of guessing.
    ///
    /// The overflow of a shift by more than one bit is undefined, which
    /// the emulator leaves unknown. Picking a direction would send the run
    /// down a path the machine might not take, and every answer after that
    /// would belong to the wrong path.
    ///
    /// # Panics
    ///
    /// When the run does not stop, or stops for another reason.
    #[test]
    fn a_signed_jump_on_unknown_flags_stops() {
        // ASM: mov eax,5; shl eax,2; jg +1; ret; ret
        let code: &[u8] = &[
            0xb8, 0x05, 0x00, 0x00, 0x00, 0xc1, 0xe0, 0x02, 0x7f, 0x01, 0xc3, 0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        match run.stop {
            Stop::Unmodeled(ref what) => {
                assert!(what.contains("did not set"), "{what}");
            }
            other => panic!("expected an unmodeled stop, got {other}"),
        }
    }

    /// Lane-wise addition wraps within the lane instead of carrying across.
    ///
    /// A keystream written with SSE mixes several words at once, and a carry
    /// leaking into the next lane would corrupt every word after it.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the lane did not wrap.
    #[test]
    fn a_packed_add_wraps_inside_its_lane() {
        // ASM: mov rax,-1; movq xmm0,rax; mov rax,2; movq xmm1,rax;
        //      paddq xmm0,xmm1; movq rax,xmm0; ret
        let code: &[u8] = &[
            0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x66, 0x48, 0x0f, 0x6e,
            0xc0, 0x48, 0xc7, 0xc0, 0x02, 0x00, 0x00, 0x00, 0x66, 0x48, 0x0f, 0x6e, 0xc8, 0x66,
            0x0f, 0xd4, 0xc1, 0x66, 0x48, 0x0f, 0x7e, 0xc0, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(1));
    }

    /// Widening the accumulator keeps its sign.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the value was zero-extended.
    #[test]
    fn the_accumulator_widens_with_its_sign() {
        // ASM: mov eax,0xffffffff; cdqe; ret
        let code: &[u8] = &[0xb8, 0xff, 0xff, 0xff, 0xff, 0x48, 0x98, 0xc3];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(u64::MAX));
    }

    /// `cpuid` answers as a plain machine, the same way every run.
    ///
    /// # Panics
    ///
    /// When the vendor is wrong, a hypervisor is reported, or two calls of
    /// the same leaf disagree.
    #[test]
    fn cpuid_reports_a_machine_with_no_hypervisor() {
        let (max, b, c, d) = super::cpuid_leaf(0);
        assert!(max >= 1);
        let vendor: Vec<u8> = [b, d, c].iter().flat_map(|w| w.to_le_bytes()).collect();
        assert_eq!(String::from_utf8_lossy(&vendor), "GenuineIntel");
        assert_eq!(super::cpuid_leaf(1).2 >> 31, 0, "a hypervisor was reported");
        assert_eq!(super::cpuid_leaf(0x4000_0000), (0, 0, 0, 0));
        assert_eq!(super::cpuid_leaf(1), super::cpuid_leaf(1));
    }

    /// A trace keeps the run's last instructions and says what each changed.
    ///
    /// Final registers answer what a routine computed, not how: a loop's
    /// thousand iterations leave one result. The trace follows the run to
    /// its end, so the instructions before it stopped are the ones on
    /// record, and a run's start is watched by giving it a small budget.
    ///
    /// # Panics
    ///
    /// When the trace is the wrong length or does not name the change.
    #[test]
    fn a_trace_records_what_each_step_changed() {
        // ASM: mov eax,5; inc rcx; inc rcx; ret
        let code: &[u8] = &[
            0xb8, 0x05, 0x00, 0x00, 0x00, 0x48, 0xff, 0xc1, 0x48, 0xff, 0xc1, 0xc3,
        ];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_trace(2);
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
        let trace = emu.trace();
        assert_eq!(trace.len(), 2, "{trace:?}");
        assert!(trace[0].contains("rcx=0x2"), "the second inc: {}", trace[0]);
        assert!(trace[1].contains("stopped"), "the return: {}", trace[1]);
        assert!(trace[0].contains("0x1008"), "{}", trace[0]);
    }

    /// A trace follows a loop to its last iteration, not its first.
    ///
    /// A ring that kept the head would show the counter starting out; one
    /// that keeps the tail shows the iteration the run stopped in, which is
    /// the one a diagnosis reads.
    ///
    /// # Panics
    ///
    /// When the traced lines are not the loop's last iterations.
    #[test]
    fn a_trace_keeps_the_tail_of_a_loop() {
        // ASM: mov ecx,3; L: dec ecx; jnz L; ret
        let code: &[u8] = &[0xb9, 0x03, 0x00, 0x00, 0x00, 0xff, 0xc9, 0x75, 0xfc, 0xc3];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_trace(3);
        emu.run(0x1000);
        let trace = emu.trace();
        assert_eq!(trace.len(), 3, "{trace:?}");
        assert!(
            !trace.iter().any(|l| l.contains("mov")),
            "the loop's head is not the tail: {trace:?}"
        );
        assert!(
            trace.iter().any(|l| l.contains("rcx=0x0")),
            "the final count: {trace:?}"
        );
        assert!(
            trace[2].contains("stopped"),
            "the run's last instruction is its return: {trace:?}"
        );
    }

    /// The origin watch names the instruction that first produced a value.
    ///
    /// A run's result names a value the analyst did not expect; the watch
    /// answers where it was born, in a register or in memory, so the next
    /// question (what fed that instruction) has an address to start from.
    ///
    /// # Panics
    ///
    /// When the birth is missed or misnamed.
    #[test]
    fn an_origin_watch_names_the_birth_instruction() {
        // ASM: mov eax,0x46; shl rax,32; ret
        let code: &[u8] = &[0xb8, 0x46, 0x00, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x20, 0xc3];
        let p = image(code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_origin(Some(0x46_0000_0000));
        emu.run(0x1000);
        let (at, instr) = emu.origin().expect("the shift births the value");
        assert_eq!(at, 0x1005, "{at:#x}");
        assert!(instr.contains("shl"), "{instr}");
    }

    /// A value assembled in memory by two narrow stores is born by the
    /// store that completes it, without ever sitting in a register.
    ///
    /// # Panics
    ///
    /// When the birth is missed or misnamed.
    #[test]
    fn an_origin_watch_catches_a_value_assembled_in_memory() {
        // ASM: mov dword [0x2000],0; mov eax,0x46; mov [0x2004],eax; ret
        let code: &[u8] = &[
            0xc7, 0x05, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, // ASM: mov dword ptr [0x2000],0
            0xb8, 0x46, 0x00, 0x00, 0x00, // ASM: mov eax,0x46
            0xa3, 0x04, 0x20, 0x00, 0x00, // ASM: mov [0x2004],eax
            0xc3, // ASM: ret
        ];
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let data = Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false);
        let p = Program::raw(code.to_vec(), Arch::X86, 0, Some(0x1000), vec![text, data]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_origin(Some(0x46_0000_0000));
        emu.run(0x1000);
        let (at, instr) = emu.origin().expect("the second store births the value");
        assert_eq!(at, 0x100f, "{at:#x}");
        assert!(instr.contains("mov"), "{instr}");
    }

    /// Nothing is recorded unless a trace was asked for.
    ///
    /// # Panics
    ///
    /// When an untraced run records anything.
    #[test]
    fn an_untraced_run_records_nothing() {
        let p = image(&[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let _ = emu.run(0x1000);
        assert!(emu.trace().is_empty());
    }

    /// A shift sets the carry flag from the bit it shifted out.
    ///
    /// The flag was left holding whatever the last arithmetic put there, so
    /// a bit test written as a shift and a carry branch read a stale answer.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the branch was not taken.
    #[test]
    fn a_shift_sets_the_carry_it_shifted_out() {
        // ASM: mov eax,3; shr eax,1; jb .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let code: &[u8] = &[
            0xb8, 0x03, 0x00, 0x00, 0x00, 0xd1, 0xe8, 0x72, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(2), "the carry was not set");
    }

    /// A shift count is taken modulo the operand's width.
    ///
    /// A 32-bit shift by 33 shifts by one. Masking every count at 64-bit
    /// width instead cleared the register.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the count was not reduced.
    #[test]
    fn a_shift_count_wraps_at_the_operand_width() {
        // ASM: mov eax,1; shl eax,33; ret
        let code: &[u8] = &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc1, 0xe0, 0x21, 0xc3];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(2));
    }

    /// A rotate through carry carries the flag back into the operand.
    ///
    /// The carry flag is one more bit of the value, which is how a bignum
    /// add and a compiler's 128-bit shift are built.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the carry did not come back in.
    #[test]
    fn a_rotate_through_carry_reads_the_flag() {
        // ASM: mov eax,0x80000000; shl eax,1; rcl eax,1; ret
        // The shift leaves zero with carry set; the rotate brings it back.
        let code: &[u8] = &[0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xe0, 0xd1, 0xd0, 0xc3];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(1));
    }

    /// The x87 stack loads, divides and stores an integer.
    ///
    /// A run that met a floating-point divide used to stop there. The
    /// hardware keeps eighty-bit values and this keeps doubles, which is
    /// exact for the integers these routines load.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the quotient is wrong.
    #[test]
    fn the_x87_stack_divides_and_stores() {
        // ASM: fild dword [0x2000]; fidiv dword [0x2004];
        //      fistp dword [0x2008]; mov eax,[0x2008]; ret
        let code: &[u8] = &[
            0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xda, 0x34, 0x25, 0x04, 0x20, 0x00, 0x00,
            0xdb, 0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, 0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00,
            0xc3,
        ];
        let data: &[u8] = &[0x64, 0, 0, 0, 0x07, 0, 0, 0];
        let emu = returned(image(code, data));
        assert_eq!(emu.register("rax"), Some(14));
    }

    /// `fxch` swaps `st(0)` with the register it names, and bare `fxch`
    /// with `st(1)`.
    ///
    /// # Panics
    ///
    /// When the run does not return, or a value lands in the wrong slot.
    #[test]
    fn fxch_swaps_st0_with_the_register_it_names() {
        // ASM: fild dword [0x2000]; fild dword [0x2004]; fild dword [0x2008];
        //      fxch st2; fistp dword [0x200c]; fxch; fistp dword [0x2010];
        //      fistp dword [0x2014]; ret
        let code: &[u8] = &[
            0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00,
            0xdb, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, 0xd9, 0xca, 0xdb, 0x1c, 0x25, 0x0c, 0x20,
            0x00, 0x00, 0xd9, 0xc9, 0xdb, 0x1c, 0x25, 0x10, 0x20, 0x00, 0x00, 0xdb, 0x1c, 0x25,
            0x14, 0x20, 0x00, 0x00, 0xc3,
        ];
        let data: &[u8] = &[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0];
        let emu = returned(image(code, data));
        assert_eq!(emu.peek(0x200c), Some(1));
        assert_eq!(emu.peek(0x2010), Some(3));
        assert_eq!(emu.peek(0x2014), Some(2));
    }

    /// A 16-bit address reads `di`, not `edi`, and wraps at 64 KiB.
    ///
    /// `edi` holds `0xabcd2001`, so `[di-1]` is `0x2000`: the displacement
    /// is the word `0xffff`, and only the wrap makes it minus one.
    ///
    /// # Panics
    ///
    /// When the run does not return, or the byte was not added to.
    #[test]
    fn a_16_bit_address_reads_di_and_wraps() {
        // ASM: mov edi,0xabcd2001; mov dh,5; add [di-1],dh; ret
        let code: &[u8] = &[
            0xbf, 0x01, 0x20, 0xcd, 0xab, 0xb6, 0x05, 0x67, 0x00, 0x75, 0xff, 0xc3,
        ];
        let emu = returned(image32(code, &[7]));
        assert_eq!(emu.peek(0x2000), Some(12));
    }

    /// `pop es` pops into the segment register, never into `eax`.
    ///
    /// The decoder numbers `es` 0 among the segment registers, as it numbers
    /// `rax` among the general ones, and the pop once wrote the low word of
    /// `eax`.
    ///
    /// # Panics
    ///
    /// When the run does not return, or `eax` changed.
    #[test]
    fn a_segment_register_is_not_eax() {
        // ASM: mov eax,0x11223344; push 0x5566; pop es; ret
        let code: &[u8] = &[
            0xb8, 0x44, 0x33, 0x22, 0x11, 0x68, 0x66, 0x55, 0x00, 0x00, 0x07, 0xc3,
        ];
        let emu = returned(image32(code, &[]));
        assert_eq!(emu.register("eax"), Some(0x1122_3344));
    }

    /// Builds a raw 32-bit image with `code` at 0x1000 and `data` at 0x2000.
    fn image32(code: &[u8], data: &[u8]) -> Program {
        let mut p = image(code, data);
        p.arch = Arch::X86;
        p.is_64 = false;
        p
    }

    /// A 32-bit routine reads its arguments off the stack and returns.
    ///
    /// `mov eax,[esp+4]; add eax,[esp+8]; ret` with 2 and 3 in the slots
    /// answers 5, the stack pointer is back where it started, and the readout
    /// names the registers the target has.
    #[test]
    fn a_32_bit_routine_takes_stack_arguments() {
        let p = image32(&[0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3], &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_arg(0, 2);
        emu.set_arg(1, 3);
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Returned, "{run:?}");
        assert_eq!(emu.register("eax"), Some(5));
        assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
        assert_eq!(emu.registers().first().map(|(n, _)| *n), Some("eax"));
    }

    /// A 32-bit allocation steps over an image loaded where allocations
    /// start, and fails as the OS would once the space below the API stubs
    /// is spent, rather than run into the stubs and the stack above them.
    #[test]
    fn allocations_step_over_the_image_and_stop_at_the_stubs() {
        let mut p = image32(&[0xc3], &[]);
        p.image_base = super::ALLOC_BASE_32;
        for s in &mut p.sections {
            s.va.0 += super::ALLOC_BASE_32;
        }
        let mut emu = Emulator::new(&p, 1).expect("emulator");
        let regions: Vec<u64> = std::iter::repeat_with(|| emu.allocate())
            .take_while(|&a| a != 0)
            .take(1000)
            .collect();
        assert_eq!(
            regions.first(),
            Some(&(super::ALLOC_BASE_32 + super::api::ALLOC_STRIDE))
        );
        assert!(
            regions
                .windows(2)
                .all(|w| w[1] - w[0] == super::api::ALLOC_STRIDE)
        );
        assert_eq!(
            regions.last().map(|a| a + super::api::ALLOC_STRIDE),
            Some(super::api::API_STUB_BASE_32)
        );
        assert_eq!(emu.allocate(), 0);
    }

    /// `ret imm16` releases the caller's stack arguments, not just the return
    /// address.
    ///
    /// `push 0; push 0; call callee; ret` with `callee: ret 10h` leaves the
    /// stack pointer back at its start: the return pops the address and the
    /// immediate releases the two pushed words. This is the stdcall epilogue
    /// and the shape a packer's depacker returns through; ignoring the
    /// immediate desynchronizes every later access to the caller's stack.
    #[test]
    fn ret_with_an_immediate_releases_arguments() {
        let code = [
            0x6a, 0x00, 0x6a, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xc2, 0x10, 0x00,
        ];
        let emu = returned(image(&code, &[]));
        assert_eq!(emu.register("rsp"), Some(super::STACK_BASE));
    }

    /// The 32-bit stdcall `ret imm16` releases its arguments too.
    ///
    /// The same shape with `ret 8` on a 32-bit image, where each push and the
    /// return address are four bytes, returns the stack pointer to its start.
    #[test]
    fn ret_with_an_immediate_releases_arguments_32() {
        let code = [
            0x6a, 0x00, 0x6a, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xc2, 0x08, 0x00,
        ];
        let emu = returned(image32(&code, &[]));
        assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
    }

    /// `pushf`/`popf` round-trip the flags a branch reads.
    ///
    /// The zero flag is set, saved, cleared, then restored from the stack; the
    /// `je` afterward is taken because the pop brought the flag back. A
    /// protector saves and restores the flags this way around its own work, and
    /// before this the run stopped at the first `pushfq` a VM used.
    #[test]
    fn pushf_and_popf_round_trip_the_flags() {
        let code = [
            0x31, 0xc0, 0x9c, 0x83, 0xf8, 0x01, 0x9d, 0x74, 0x06, 0xb8, 0xaa, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0xbb, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(&code, &[]));
        assert_eq!(
            emu.register("eax"),
            Some(0xbb),
            "the pop did not restore ZF"
        );
    }

    /// The 32-bit `pushfd`/`popfd` round-trip the flags too.
    #[test]
    fn pushfd_and_popfd_round_trip_the_flags() {
        let code = [
            0x31, 0xc0, 0x9c, 0x83, 0xf8, 0x01, 0x9d, 0x74, 0x06, 0xb8, 0xaa, 0x00, 0x00, 0x00,
            0xc3, 0xb8, 0xbb, 0x00, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image32(&code, &[]));
        assert_eq!(
            emu.register("eax"),
            Some(0xbb),
            "the pop did not restore ZF"
        );
    }

    /// `fisttp` stores the truncated integer of `st(0)` and pops the stack.
    ///
    /// `fld qword [2.9]; fisttp qword [out]; ret` leaves 2 at `out`: the SSE3
    /// truncating integer store, which a Themida VM handler uses and the
    /// emulator once rejected as unmodeled.
    #[test]
    fn fisttp_truncates_and_pops() {
        let code = [
            0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xdd, 0x0d, 0x04, 0x10, 0x00, 0x00, 0xc3,
        ];
        let data = [0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x07, 0x40];
        let emu = returned(image(&code, &data));
        assert_eq!(
            emu.peek(0x2010),
            Some(2),
            "fisttp did not truncate 2.9 to 2"
        );
        assert_eq!(emu.peek(0x2011), Some(0), "the stored integer is not clean");
    }

    /// `fistp` rounds to nearest even and stores at the operand's width,
    /// and a value the width cannot hold stores the integer indefinite.
    #[test]
    fn fistp_rounds_to_nearest_even_at_the_operand_width() {
        let code = [
            0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xdb, 0x1d, 0x1c, 0x10, 0x00, 0x00, 0xdd, 0x05,
            0xf6, 0x0f, 0x00, 0x00, 0xdf, 0x1d, 0x16, 0x10, 0x00, 0x00, 0xdd, 0x05, 0xf2, 0x0f,
            0x00, 0x00, 0xdb, 0x1d, 0x12, 0x10, 0x00, 0x00, 0xc3,
        ];
        let mut data = Vec::new();
        data.extend_from_slice(&2.5f64.to_le_bytes());
        data.extend_from_slice(&3.5f64.to_le_bytes());
        data.extend_from_slice(&1e20f64.to_le_bytes());
        data.extend_from_slice(&[0xee; 32]);
        let emu = returned(image(&code, &data));
        let dword = |emu: &Emulator<'_>, at: u64| -> u32 {
            u32::from_le_bytes([
                emu.peek(at).unwrap_or(0),
                emu.peek(at + 1).unwrap_or(0),
                emu.peek(at + 2).unwrap_or(0),
                emu.peek(at + 3).unwrap_or(0),
            ])
        };
        assert_eq!(dword(&emu, 0x2028), 2, "2.5 rounds to the even 2");
        assert_eq!(
            (emu.peek(0x202e), emu.peek(0x202f)),
            (Some(4), Some(0)),
            "3.5 rounds to the even 4 in a word"
        );
        assert!(
            emu.peek(0x2030).is_none_or(|b| b == 0xee),
            "a word store leaves the byte after it"
        );
        assert_eq!(dword(&emu, 0x2036), 0x8000_0000, "1e20 is the indefinite");
    }

    /// `fild word` and `fiadd word` read two bytes, sign-extended.
    ///
    /// The load was clamped to four bytes, so a word operand took the two
    /// bytes after it as its high half: `-2` followed by `0x7fff` read as
    /// `0x7ffffffe`, and the sum overflowed the dword store into the
    /// integer indefinite.
    #[test]
    fn fild_word_and_fiadd_word_read_two_bytes_sign_extended() {
        // ASM: fild dword [0x2004]; fiadd word [0x2000]; fistp dword [0x2008];
        //      fild word [0x2000]; fistp dword [0x200c];
        //      mov eax,[0x2008]; mov ebx,[0x200c]; ret
        let code: &[u8] = &[
            0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00, 0xde, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00,
            0xdb, 0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, 0xdf, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00,
            0xdb, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00, 0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00,
            0x8b, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00, 0xc3,
        ];
        let data: &[u8] = &[0xfe, 0xff, 0xff, 0x7f, 0x0a, 0x00, 0x00, 0x00];
        let emu = returned(image(code, data));
        assert_eq!(emu.register("rax"), Some(8), "10 + (-2)");
        assert_eq!(emu.register("rbx"), Some(0xffff_fffe), "-2 as a dword");
    }

    /// `fsincos` leaves the sine and pushes the cosine, `fptan` leaves the
    /// tangent and pushes 1.0, and `frndint` rounds to nearest even.
    #[test]
    fn the_x87_transcendentals_run() {
        let code = [
            0xdd, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // ASM: fld qword [0x2000]
            0xd9, 0xfb, // ASM: fsincos
            0xdd, 0x1c, 0x25, 0x10, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2010]
            0xdd, 0x1c, 0x25, 0x18, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2018]
            0xdd, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // ASM: fld qword [0x2000]
            0xd9, 0xf2, // ASM: fptan
            0xdd, 0x1c, 0x25, 0x20, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2020]
            0xdd, 0x1c, 0x25, 0x28, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2028]
            0xdd, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, // ASM: fld qword [0x2008]
            0xd9, 0xfc, // ASM: frndint
            0xdd, 0x1c, 0x25, 0x30, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2030]
            0x48, 0x8b, 0x04, 0x25, 0x10, 0x20, 0x00, 0x00, // ASM: mov rax,[0x2010]
            0x48, 0x8b, 0x1c, 0x25, 0x18, 0x20, 0x00, 0x00, // ASM: mov rbx,[0x2018]
            0x48, 0x8b, 0x0c, 0x25, 0x20, 0x20, 0x00, 0x00, // ASM: mov rcx,[0x2020]
            0x48, 0x8b, 0x14, 0x25, 0x28, 0x20, 0x00, 0x00, // ASM: mov rdx,[0x2028]
            0x48, 0x8b, 0x34, 0x25, 0x30, 0x20, 0x00, 0x00, // ASM: mov rsi,[0x2030]
            0xc3, // ASM: ret
        ];
        let mut data = Vec::new();
        data.extend_from_slice(&0.5f64.to_le_bytes());
        data.extend_from_slice(&2.5f64.to_le_bytes());
        let emu = returned(image(&code, &data));
        assert_eq!(emu.register("rax"), Some(0.5f64.cos().to_bits()));
        assert_eq!(emu.register("rbx"), Some(0.5f64.sin().to_bits()));
        assert_eq!(emu.register("rcx"), Some(1.0f64.to_bits()));
        assert_eq!(emu.register("rdx"), Some(0.5f64.tan().to_bits()));
        assert_eq!(emu.register("rsi"), Some(2.0f64.to_bits()));
    }

    /// `fld tbyte` reads the extended format and `fstp tbyte` writes it back.
    ///
    /// 1.5 is `0xc000_0000_0000_0000` under exponent `0x3fff`; read as its
    /// low eight bytes it was the double -2.0.
    #[test]
    fn fld_and_fstp_tbyte_carry_the_extended_format() {
        // ASM: fld tbyte [0x2000]; fstp tbyte [0x2010]; fld tbyte [0x2010];
        //      fstp qword [0x2020]; mov rax,[0x2020]; ret
        let code: &[u8] = &[
            0xdb, 0x2c, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb, 0x3c, 0x25, 0x10, 0x20, 0x00, 0x00,
            0xdb, 0x2c, 0x25, 0x10, 0x20, 0x00, 0x00, 0xdd, 0x1c, 0x25, 0x20, 0x20, 0x00, 0x00,
            0x48, 0x8b, 0x04, 0x25, 0x20, 0x20, 0x00, 0x00, 0xc3,
        ];
        let extended: [u8; 10] = [0, 0, 0, 0, 0, 0, 0, 0xc0, 0xff, 0x3f];
        let emu = returned(image(code, &extended));
        assert_eq!(emu.register("rax"), Some(1.5f64.to_bits()));
        let written: Vec<u8> = (0..10).filter_map(|k| emu.peek(0x2010 + k)).collect();
        assert_eq!(written, extended, "fstp tbyte wrote the ten bytes back");
    }

    /// The extended format holds every double exactly, and a mantissa
    /// wider than a double's rounds to nearest even.
    #[test]
    fn the_extended_format_round_trips_doubles_and_rounds_wider_mantissas() {
        for v in [
            0.0,
            -0.0,
            1.0,
            1.5,
            -3.25,
            1e300,
            -1e-300,
            f64::MIN_POSITIVE,
            5e-324,
            f64::MAX,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            let (mantissa, high) = f64_to_extended(v);
            assert_eq!(
                extended_to_f64(mantissa, high).to_bits(),
                v.to_bits(),
                "{v}"
            );
        }
        let (mantissa, high) = f64_to_extended(f64::NAN);
        assert!(extended_to_f64(mantissa, high).is_nan());
        assert_eq!(f64_to_extended(1.5), (0xc000_0000_0000_0000, 0x3fff));
        assert_eq!(f64_to_extended(-2.0), (0x8000_0000_0000_0000, 0xc000));
        assert_eq!(
            extended_to_f64(u64::MAX, 0x3fff),
            2.0,
            "2 - 2^-63 rounds up"
        );
        assert_eq!(
            extended_to_f64(1 << 63 | 1 << 10, 0x3fff),
            1.0,
            "a tie rounds to the even 1"
        );
        assert_eq!(
            extended_to_f64(1 << 63 | 1 << 10 | 1, 0x3fff),
            1.0 + f64::EPSILON,
            "above the tie rounds up"
        );
        assert_eq!(
            extended_to_f64(1 << 63, 0x7ffe),
            f64::INFINITY,
            "past a double"
        );
        assert_eq!(
            extended_to_f64(1 << 63, 1),
            0.0,
            "below a double's denormals"
        );
        assert_eq!(extended_to_f64(1 << 62, 0), 0.0, "an extended denormal");
        assert_eq!(extended_to_f64(1 << 63, 0x7fff), f64::INFINITY);
        assert!(extended_to_f64(1 << 63 | 1 << 62, 0x7fff).is_nan());
    }

    /// Execution that lands on the scratch stack is a derailed run.
    ///
    /// `mov rax,rsp; jmp rax` transfers into the stack, where no code lives.
    /// A protector's VM produces exactly this when the run feeds it a value the
    /// real process would have but the emulator cannot, so the stop reads as a
    /// guard that won rather than a byte that happened to be unmapped.
    #[test]
    fn execution_on_the_stack_is_a_derail() {
        let code = [0x48, 0x89, 0xe0, 0xff, 0xe0];
        let p = image(&code, &[]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Derailed(_)), "{run:?}");
    }

    /// The segment reads of a 32-bit prologue answer as an unwatched process.
    ///
    /// `mov eax,fs:[0]; push eax; mov fs:[0],esp; pop eax; mov fs:[0],eax;
    /// mov eax,fs:[0x18]; mov ecx,fs:[0x30]; movzx eax,byte [ecx+2]; ret`
    /// runs to its return with `eax` zero, since nothing is attached, and
    /// `ecx` holding the process block.
    #[test]
    fn a_32_bit_thread_block_answers_segment_reads() {
        let code = [
            0x64, 0xa1, 0x00, 0x00, 0x00, 0x00, 0x50, 0x64, 0x89, 0x25, 0x00, 0x00, 0x00, 0x00,
            0x58, 0x64, 0xa3, 0x00, 0x00, 0x00, 0x00, 0x64, 0xa1, 0x18, 0x00, 0x00, 0x00, 0x64,
            0x8b, 0x0d, 0x30, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x41, 0x02, 0xc3,
        ];
        let emu = returned(image32(&code, &[]));
        assert_eq!(emu.register("eax"), Some(0));
        assert_eq!(emu.register("ecx"), Some(super::TEB_32 + 0x1000));
    }

    /// `loopne` runs while the counter and the zero flag allow:
    /// `mov ecx,5; mov eax,0; L: inc eax; cmp eax,3; loopne L; ret` leaves
    /// `eax` at 3 and `ecx` at 2.
    #[test]
    fn loopne_stops_on_the_zero_flag() {
        let code = [
            0xb9, 0x05, 0x00, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x40, 0x83, 0xf8, 0x03,
            0xe0, 0xfa, 0xc3,
        ];
        let emu = returned(image32(&code, &[]));
        assert_eq!(emu.register("eax"), Some(3));
        assert_eq!(emu.register("ecx"), Some(2));
    }

    /// Below the first section only the headers are mapped.
    ///
    /// A read there past the headers faults rather than returning the file
    /// bytes at that offset, which belong to a section loaded elsewhere.
    #[test]
    fn only_the_headers_are_mapped_below_the_first_section() {
        let mut bytes = vec![0u8; 0x3000];
        bytes[0x10..0x14].copy_from_slice(&[0x4d, 0x5a, 0x90, 0x00]);
        let code: &[u8] = &[
            0x8b, 0x04, 0x25, 0x10, 0x00, 0x00, 0x10, 0x8b, 0x1c, 0x25, 0x00, 0x08, 0x00, 0x10,
            0x8b, 0x0c, 0x25, 0x00, 0x14, 0x00, 0x10, 0xc3,
        ];
        bytes[0x400..0x400 + code.len()].copy_from_slice(code);
        bytes[0x1400..0x1404].copy_from_slice(&[1, 2, 3, 4]);
        let text = Section::mapped(".text", 0x1001_0000, 0x400, 0x2c00, false, true);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0x1000_0000,
            Some(0x1001_0000),
            vec![text],
        );
        p.format = BinaryFormat::Pe;
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1001_0000);
        assert!(
            matches!(run.stop, Stop::Fault(0x1000_1400)),
            "a read past the headers faults: {:?}",
            run.stop
        );
        assert_eq!(emu.register("rax"), Some(0x0090_5a4d), "the headers read");
        assert_eq!(
            emu.register("rbx"),
            Some(0),
            "the header page's tail reads zero"
        );
    }

    /// Builds a raw x86-64 image with `code` at 0x1000 and `data` at 0x2000.
    pub(super) fn image(code: &[u8], data: &[u8]) -> Program {
        let mut bytes = vec![0u8; 0x3000];
        bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
        bytes[0x2000..0x2000 + data.len()].copy_from_slice(data);
        let flat = Section::mapped(".flat", 0, 0, 0x3000, true, true);
        Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![flat])
    }

    /// A routine reading its stack arguments and home space, none of them
    /// given, reads zeros and runs on once the frame is backed, as it would
    /// over a caller's frame, and faults as before when it is not.
    ///
    /// # Panics
    ///
    /// When the backed read faults or the unbacked one does not.
    #[test]
    fn stack_arguments_nobody_set_read_as_zero() {
        // ASM: mov rax,[rsp+0x28]; add rax,[rsp+8]; ret
        let code = [
            0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x03, 0x44, 0x24, 0x08, 0xc3,
        ];
        let p = image(&code, &[]);
        let mut strict = Emulator::new(&p, 200).expect("emulator");
        assert!(matches!(strict.run(0x1000).stop, Stop::Fault(_)));
        let mut emu = Emulator::new(&p, 200).expect("emulator");
        emu.back_arguments();
        assert!(matches!(emu.run(0x1000).stop, Stop::Returned));
        assert_eq!(emu.register("rax"), Some(0));
    }

    /// The stack pointer read without a machine is the one a new machine
    /// starts with, at both widths.
    ///
    /// # Panics
    ///
    /// When the two differ.
    #[test]
    fn the_entry_stack_pointer_is_the_new_machines() {
        let mut p = image(&[0xc3], &[]);
        for arch in [Arch::X86_64, Arch::X86] {
            p.arch = arch;
            let built = Emulator::new(&p, 0).and_then(|e| e.register("rsp"));
            assert_eq!(Emulator::entry_sp(&p), built);
            assert!(built.is_some());
        }
    }

    /// Runs `p` from 0x1000 to its `ret` and returns the machine.
    pub(super) fn returned(p: Program) -> Emulator<'static> {
        let p = Box::leak(Box::new(p));
        let mut emu = Emulator::new(p, 200).expect("emulator");
        let run = emu.run(0x1000);
        assert!(matches!(run.stop, Stop::Returned), "{:?}", run.stop);
        emu
    }

    /// The emulator runs a real XOR-decrypt loop and produces the plaintext.
    ///
    /// The routine takes `rcx=dst, rdx=src, r8=len, r9=key` and XORs each
    /// source byte with the key into the destination, the shape a crypter's
    /// string decoder has. Given the ciphertext of "secret payload!!" under
    /// key 0x5a, the bytes it writes to the destination are the plaintext.
    #[test]
    fn runs_an_xor_decrypt_loop() {
        let code = [
            0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04,
            0x11, 0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
        ];
        let enc = [
            0x29u8, 0x3f, 0x39, 0x28, 0x3f, 0x2e, 0x7a, 0x2a, 0x3b, 0x23, 0x36, 0x35, 0x3b, 0x3e,
            0x7b, 0x7b,
        ];
        let p = image(&code, &enc);
        let mut emu = Emulator::new(&p, 10_000).expect("bitness");
        emu.set_arg(0, 0x2800);
        emu.set_arg(1, 0x2000);
        emu.set_arg(2, enc.len() as u64);
        emu.set_arg(3, 0x5a);
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Returned, "run did not return: {run:?}");
        let out: String = (0..enc.len())
            .filter_map(|k| emu.peek(0x2800 + k as u64))
            .map(char::from)
            .collect();
        assert_eq!(out, "secret payload!!", "{run:?}");
    }

    /// A profile counts loop landings and the pages a loop reads, and a
    /// trace line names the loads and stores its instruction made.
    ///
    /// The decrypt loop above lands at its head once per iteration after the
    /// first, which falls into it, and reads its sixteen source bytes from
    /// the one data page, every load made by the head's `movzx`.
    #[test]
    fn a_profile_names_the_loop_and_its_reads_and_a_trace_its_memory() {
        let code = [
            0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04,
            0x11, 0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
        ];
        let enc = [0x29u8; 16];
        let p = image(&code, &enc);
        let mut emu = Emulator::new(&p, 10_000).expect("bitness");
        emu.set_profile(true);
        emu.set_trace(TRACE_MAX);
        emu.set_arg(0, 0x2800);
        emu.set_arg(1, 0x2000);
        emu.set_arg(2, 16);
        emu.set_arg(3, 0x5a);
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Returned, "{run:?}");
        let (hot, pages) = emu.profile(4);
        assert_eq!(
            hot.first(),
            Some(&(0x1003, 15)),
            "the loop head is landed at by every back edge: {hot:?}"
        );
        assert_eq!(
            pages,
            vec![PageRun {
                first: 0x2000,
                pages: 1,
                each: 16,
                by: 0x1003,
            }],
            "one page read sixteen times, first by the head's load"
        );
        let trace = emu.trace();
        assert!(
            trace.iter().any(|l| l.contains("r1[0x2000]=0x29")),
            "the first load is named with its value: {trace:?}"
        );
        assert!(
            trace.iter().any(|l| l.contains("w1[0x280f]=0x73")),
            "the last store is named with its value"
        );
    }

    /// Adjacent pages read equally often merge into one run, and a page read
    /// a different number of times starts its own.
    #[test]
    fn a_profile_merges_equal_adjacent_pages() {
        // ASM: mov al,[0x2000]; mov al,[0x2000]; mov al,[0x3000];
        //      mov al,[0x3000]; mov al,[0x4000]; ret
        let code: &[u8] = &[
            0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00,
            0x8a, 0x04, 0x25, 0x00, 0x30, 0x00, 0x00, 0x8a, 0x04, 0x25, 0x00, 0x30, 0x00, 0x00,
            0x8a, 0x04, 0x25, 0x00, 0x40, 0x00, 0x00, 0xc3,
        ];
        let mut bytes = vec![0u8; 0x5000];
        bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
        let flat = Section::mapped(".flat", 0, 0, 0x5000, true, true);
        let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![flat]);
        let mut emu = Emulator::new(&p, 100).expect("emulator");
        emu.set_profile(true);
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Returned, "{run:?}");
        let (_, pages) = emu.profile(8);
        assert_eq!(
            pages,
            vec![
                PageRun {
                    first: 0x2000,
                    pages: 2,
                    each: 2,
                    by: 0x1000,
                },
                PageRun {
                    first: 0x4000,
                    pages: 1,
                    each: 1,
                    by: 0x101c,
                },
            ],
            "two equal adjacent pages merge; the odd one stands alone"
        );
    }

    /// A syscall number the table lists is named; one it does not stays bare.
    #[test]
    fn linux_syscall_numbers_are_named_where_listed() {
        assert_eq!(super::linux_syscall_name(10), Some("mprotect"));
        assert_eq!(super::linux_syscall_name(101), Some("ptrace"));
        assert_eq!(super::linux_syscall_name(231), Some("exit_group"));
        assert_eq!(super::linux_syscall_name(999), None);
    }

    /// Three-operand `imul` is modeled: a key schedule that multiplies runs.
    #[test]
    fn runs_a_three_operand_imul() {
        let code = [
            0x48u8, 0xc7, 0xc0, 0x07, 0x00, 0x00, 0x00, 0x48, 0x6b, 0xc0, 0x06, 0x88, 0x04, 0x25,
            0x00, 0x28, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(&code, &[]));
        assert_eq!(emu.peek(0x2800), Some(42), "imul result wrong");
    }

    /// The carry flag is the carry out of the operand width, not the register.
    ///
    /// `add al, al` with `al = 0x80` overflows the byte and must set carry, so
    /// the following `adc bl, bl` yields 1. A packer's bit reader pulls each
    /// bit out of this carry; computing it from the 64-bit register instead
    /// would leave carry clear and corrupt the decompressed stream.
    #[test]
    fn carry_is_taken_at_the_operand_width() {
        let code = [
            0xb0, 0x80, 0x00, 0xc0, 0x10, 0xdb, 0x88, 0x1c, 0x25, 0x00, 0x28, 0x00, 0x00, 0xc3,
        ];
        let emu = returned(image(&code, &[]));
        assert_eq!(emu.peek(0x2800), Some(1), "8-bit carry was dropped");
    }

    /// A loop of syscalls or of indirect jumps stops when its record is
    /// full, not at the step budget with every call and jump kept.
    ///
    /// # Panics
    ///
    /// When a record grows past the cap or the run ends another way.
    #[test]
    fn a_record_that_fills_stops_the_run() {
        // ASM: mov eax,39; syscall; jmp 0x1000
        let calls = image(&[0xb8, 0x27, 0x00, 0x00, 0x00, 0x0f, 0x05, 0xeb, 0xf7], &[]);
        let mut emu = Emulator::new(&calls, 1_000_000).expect("emulator");
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Limit(super::Limit::Calls), "{}", run.stop);
        assert_eq!(emu.api_calls().len(), super::RECORDS_MAX);
        // ASM: lea rax,[rip-7]; jmp rax
        let jumps = image(&[0x48, 0x8d, 0x05, 0xf9, 0xff, 0xff, 0xff, 0xff, 0xe0], &[]);
        let mut emu = Emulator::new(&jumps, 1_000_000).expect("emulator");
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Limit(super::Limit::Jumps), "{}", run.stop);
        assert_eq!(emu.indirect_jumps().len(), super::RECORDS_MAX);
    }

    /// A run that never returns stops at its step budget rather than looping
    /// forever.
    #[test]
    fn a_tight_loop_stops_at_the_budget() {
        let p = image(&[0xeb, 0xfe], &[]);
        let mut emu = Emulator::new(&p, 500).expect("bitness");
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Budget);
        assert_eq!(run.steps, 500);
    }

    /// A best-effort run whose stack pointer has left the stack spends its
    /// budget on the returns it skips, rather than popping its way up the
    /// address space for free.
    ///
    /// `mov rsp,0x100000000; ret` returns to zero, which nothing maps, and
    /// each skip after it pops another zero. When a skip cost no step, a run
    /// of 272 steps on one mutated image popped 134 million words over 25
    /// seconds before the image header's base field sent it somewhere
    /// mapped; without that field it would have run on until the stack.
    #[test]
    fn skipped_returns_spend_the_budget() {
        let code = [
            0x48, 0xbc, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0xc3,
        ];
        let mut bytes = vec![0u8; 0x1000];
        bytes[..code.len()].copy_from_slice(&code);
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut emu = Emulator::new(&p, 1000).expect("emulator");
        emu.set_permissive(true);
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Budget, "{run:?}");
        assert_eq!(run.steps, 1000);
        assert_eq!(emu.skipped(), 998);
    }

    /// Each iteration of a `rep` string instruction past its first spends a
    /// step.
    ///
    /// A count of 64 million under a budget of five stops after three
    /// stores, with the counter and pointer where an interrupt would leave
    /// them. When an iteration cost nothing, this `rep stosw` ran its whole count
    /// under a budget of five: over a second and 750 megabytes on a real
    /// library, for a run that promised five steps.
    #[test]
    fn a_rep_iteration_spends_a_step() {
        let code = [
            0xb9, 0xff, 0xff, 0xff, 0x03, 0xbf, 0x00, 0x28, 0x00, 0x00, 0x66, 0xf3, 0xab, 0xc3,
        ];
        let p = image(&code, &[]);
        let mut emu = Emulator::new(&p, 5).expect("emulator");
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::Budget, "{run:?}");
        assert_eq!(run.steps, 5);
        assert_eq!(emu.register("rcx"), Some(0x03ff_fffc));
        assert_eq!(emu.register("rdi"), Some(0x2806));
        assert_eq!(run.history.len(), 6);
    }

    /// In 32-bit code a string instruction's pointer wraps at four
    /// gigabytes.
    ///
    /// Two `stosb` from `edi = 0xffffffff` write the top byte and then byte
    /// zero, and leave `edi` at 1, where it once ran on to `0x100000001`.
    #[test]
    fn a_32_bit_string_pointer_wraps() {
        let code = [0xbf, 0xff, 0xff, 0xff, 0xff, 0xb0, 0x5a, 0xaa, 0xaa, 0xc3];
        let p = image32(&code, &[]);
        let mut emu = Emulator::new(&p, 20).expect("emulator");
        assert_eq!(emu.run(0x1000).stop, Stop::Returned);
        assert_eq!(emu.register("edi"), Some(1));
        assert_eq!(emu.peek(0xffff_ffff), Some(0x5a));
        assert_eq!(emu.peek(0), Some(0x5a));
        assert_eq!(emu.peek(0x1_0000_0000), None);
    }

    /// A run that would hold more distinct bytes than its cap stops at the
    /// first byte past it, budget or not.
    #[test]
    fn memory_stops_growing_at_its_cap() {
        let code = [
            0xb9, 0x00, 0x10, 0x00, 0x00, 0xbf, 0x00, 0x28, 0x00, 0x00, 0xf3, 0xaa, 0xc3,
        ];
        let p = image(&code, &[]);
        let mut emu = Emulator::new(&p, 100_000).expect("emulator");
        emu.memory_max = emu.mem.len() + 16;
        let run = emu.run(0x1000);
        assert_eq!(run.stop, Stop::MemoryFull(0x2810), "{run:?}");
        assert_eq!(emu.mem.len(), emu.memory_max);
        assert_eq!(emu.register("rcx"), Some(0x0ff0));
    }

    /// A permissive run with a fill seed reads a hash of the address from
    /// memory nothing backs, so loads at two offsets differ; without the
    /// seed it reads zero, and without permissive mode it faults.
    #[test]
    fn an_unbacked_read_reads_the_fill() {
        let code = [
            0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x50, 0x48, 0x8b, 0x1c, 0x25, 0x08, 0x00,
            0x00, 0x50, 0xc3,
        ];
        let p = image(&code, &[]);
        let word = |at: u64| {
            (0..8)
                .rev()
                .fold(0u64, |v, k| (v << 8) | u64::from(fill_byte(7, at + k)))
        };
        let mut emu = Emulator::new(&p, 10).expect("emulator");
        emu.set_permissive(true);
        emu.set_fill(Some(7));
        assert_eq!(emu.run(0x1000).stop, Stop::Returned);
        assert_eq!(emu.register("rax"), Some(word(0x5000_0000)));
        assert_eq!(emu.register("rbx"), Some(word(0x5000_0008)));
        assert_ne!(word(0x5000_0000), word(0x5000_0008));
        assert_eq!(emu.byte_at(0x5000_0003), Some(fill_byte(7, 0x5000_0003)));
        let mut zero = Emulator::new(&p, 10).expect("emulator");
        zero.set_permissive(true);
        assert_eq!(zero.run(0x1000).stop, Stop::Returned);
        assert_eq!(zero.register("rax"), Some(0));
        let mut strict = Emulator::new(&p, 10).expect("emulator");
        assert_eq!(strict.run(0x1000).stop, Stop::Fault(0x5000_0000));
    }

    /// The emulator never panics, whatever bytes it is pointed at.
    ///
    /// The engine must not panic on input, so running over arbitrary bytes
    /// from many offsets must always end in a [`Stop`], never an index or
    /// arithmetic panic. This runs thousands of pseudo-random images and
    /// asserts every run returns.
    #[test]
    fn never_panics_on_arbitrary_bytes() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..3000 {
            let mut code = vec![0u8; 256];
            for b in &mut code {
                *b = lo8(next() >> 24);
            }
            let p = image(&code, &[]);
            for start in 0..8u64 {
                let mut emu = Emulator::new(&p, 400).expect("bitness");
                let run = emu.run(0x1000 + start);
                let _ = run.steps;
            }
        }
    }
}
