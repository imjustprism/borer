//! A bounded x86-64 emulator for self-contained transforms.
//!
//! Its one job is to run the small routines that decrypt or unpack data, so
//! their output can be read statically instead of guessed. It models the
//! integer subset those routines use, keeps a sparse memory overlay on top of
//! the program image, and stops after a step budget, at a return with an
//! empty call stack, or at anything it cannot model. It is deliberately not a
//! full CPU: a routine that calls out, uses vector math, or faults is left to
//! a real debugger.

use crate::analysis::decompile::lift;
use crate::isa::x86::{
    Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register, gpr_bank_index,
    st_depth_mod8, xmm_slot,
};
use crate::num::{from_usize, lo8, lo16, lo32};
use crate::program::Program;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub mod a64;
mod bits;
pub mod calls;
mod loader;
mod sse;
mod store;

use calls::ApiCall;
use sse::{Rounding, Width};
use store::Store;

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
    /// Synthetic stub address to imported API name. The import table is
    /// prefilled so each slot holds its stub; a call to a stub is modeled as
    /// that API rather than executed, the way the OS would service it.
    apis: BTreeMap<u64, String>,
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

/// Base of the synthetic addresses that stand in for imported functions.
///
/// Distinct from image, stack and allocations so a call to one is recognized
/// as an API call; the slots of the import table are prefilled with these.
const API_STUB_BASE: u64 = 0x7ffd_0000_0000;

/// Base of the API stubs on a 32-bit target: below the scratch stack and
/// clear of any image, where a system library would load, so a four-byte
/// import slot holds all of a stub address.
const API_STUB_BASE_32: u64 = 0x7e00_0000;

/// Base of the memory a modeled allocator returns, bumped per call.
const ALLOC_BASE: u64 = 0x6000_0000_0000;

/// Base of the memory a modeled allocator returns on a 32-bit target: above
/// the bases an executable and a DLL are linked at, below the API stubs, so
/// a four-byte pointer holds all of it.
const ALLOC_BASE_32: u64 = 0x6000_0000;

/// Most bytes one modeled `memcpy`, `memmove` or `memset` moves, so a
/// wild length cannot fill the memory map.
const API_COPY_MAX: usize = 0x1_0000;

/// Address space one modeled allocation takes, whatever size it asked for.
const ALLOC_STRIDE: u64 = 0x0010_0000;

/// Most iterations one `rep` string instruction runs before it reads as a
/// runaway on uninitialized state and stops the run.
const REP_MAX: u64 = 0x0400_0000;

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
        va >= s.va && va - s.va < mapped
    }) {
        return Some(0);
    }
    let base = program.image_base;
    let first = program.sections.iter().map(|s| s.va).min();
    if va < base || first.is_none_or(|f| va >= f) {
        return None;
    }
    let headers = program
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .map(|s| s.file_off)
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
        // Highest basic leaf, then "GenuineIntel" split across ebx, edx, ecx.
        0 => (0x16, 0x756e_6547, 0x6c65_746e, 0x4965_6e69),
        // A Skylake-era family/model/stepping, then the usual feature bits.
        // Bit 31 of ecx, "running under a hypervisor", is clear.
        1 => (0x0009_06e9, 0x0010_0800, 0x7ffa_fbbf, 0x0fab_fbff),
        // Extended leaves: the highest one, and no long-mode surprises.
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

/// Where an argument lives on entry: a 64-bit convention puts the first few
/// in registers and the rest on the stack, a 32-bit convention all of them
/// on the stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgSlot {
    /// One of the convention's argument registers.
    Register(Register),
    /// A stack address past the return address the call pushed.
    Stack(u64),
}

/// An arithmetic or logic instruction: what it computes from operand 0 and
/// its source, and the flags it leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Alu {
    /// `add`.
    Add,
    /// `adc`: an add with the carry in.
    Adc,
    /// `sub`.
    Sub,
    /// `sbb`: a subtract with the carry in.
    Sbb,
    /// `xor`.
    Xor,
    /// `and`.
    And,
    /// `or`.
    Or,
    /// `cmp`: a subtract that writes only the flags.
    Cmp,
    /// `test`: an and that writes only the flags.
    Test,
}

impl Alu {
    /// The operation a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation, or `None` when `m` is not one of these.
    fn of(m: Mnemonic) -> Option<Alu> {
        Some(match m {
            Mnemonic::Add => Alu::Add,
            Mnemonic::Adc => Alu::Adc,
            Mnemonic::Sub => Alu::Sub,
            Mnemonic::Sbb => Alu::Sbb,
            Mnemonic::Xor => Alu::Xor,
            Mnemonic::And => Alu::And,
            Mnemonic::Or => Alu::Or,
            Mnemonic::Cmp => Alu::Cmp,
            Mnemonic::Test => Alu::Test,
            _ => return None,
        })
    }
}

/// A shift or rotate of operand 0 by a count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shift {
    /// `shl`: left, zeros in.
    Shl,
    /// `shr`: right, zeros in.
    Shr,
    /// `sar`: right, the sign in.
    Sar,
    /// `rol`: a rotate left.
    Rol,
    /// `ror`: a rotate right.
    Ror,
    /// `rcl`: a rotate left through the carry.
    Rcl,
    /// `rcr`: a rotate right through the carry.
    Rcr,
}

impl Shift {
    /// The shift a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The shift, or `None` when `m` is not one of these.
    fn of(m: Mnemonic) -> Option<Shift> {
        Some(match m {
            Mnemonic::Shl => Shift::Shl,
            Mnemonic::Shr => Shift::Shr,
            Mnemonic::Sar => Shift::Sar,
            Mnemonic::Rol => Shift::Rol,
            Mnemonic::Ror => Shift::Ror,
            Mnemonic::Rcl => Shift::Rcl,
            Mnemonic::Rcr => Shift::Rcr,
            _ => return None,
        })
    }
}

/// A string instruction: what one step does between `[rsi]`, `[rdi]` and
/// the accumulator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringOp {
    /// `movs`: copies an element from `[rsi]` to `[rdi]`.
    Movs,
    /// `stos`: stores the accumulator at `[rdi]`.
    Stos,
    /// `lods`: loads the accumulator from `[rsi]`.
    Lods,
    /// `scas`: compares the accumulator with `[rdi]`.
    Scas,
    /// `cmps`: compares `[rsi]` with `[rdi]`.
    Cmps,
}

impl StringOp {
    /// The operation and element width a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation and its element in bytes, or `None` when `m` is not a
    /// string instruction.
    fn of(m: Mnemonic) -> Option<(StringOp, usize)> {
        Some(match m {
            Mnemonic::Movsb => (StringOp::Movs, 1),
            Mnemonic::Movsw => (StringOp::Movs, 2),
            Mnemonic::Movsd => (StringOp::Movs, 4),
            Mnemonic::Movsq => (StringOp::Movs, 8),
            Mnemonic::Stosb => (StringOp::Stos, 1),
            Mnemonic::Stosw => (StringOp::Stos, 2),
            Mnemonic::Stosd => (StringOp::Stos, 4),
            Mnemonic::Stosq => (StringOp::Stos, 8),
            Mnemonic::Lodsb => (StringOp::Lods, 1),
            Mnemonic::Lodsw => (StringOp::Lods, 2),
            Mnemonic::Lodsd => (StringOp::Lods, 4),
            Mnemonic::Lodsq => (StringOp::Lods, 8),
            Mnemonic::Scasb => (StringOp::Scas, 1),
            Mnemonic::Scasw => (StringOp::Scas, 2),
            Mnemonic::Scasd => (StringOp::Scas, 4),
            Mnemonic::Scasq => (StringOp::Scas, 8),
            Mnemonic::Cmpsb => (StringOp::Cmps, 1),
            Mnemonic::Cmpsw => (StringOp::Cmps, 2),
            Mnemonic::Cmpsd => (StringOp::Cmps, 4),
            Mnemonic::Cmpsq => (StringOp::Cmps, 8),
            _ => return None,
        })
    }
}

/// What the memory operand of an x87 instruction holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FpuOperand {
    /// A signed integer of the operand's width: `fild`, `fist`, `fiadd`
    /// and kin.
    Integer,
    /// A single or a double: `fld`, `fst`, `fadd` and kin.
    Float,
}

impl FpuOperand {
    /// What the memory operand of an x87 mnemonic holds.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    fn of(m: Mnemonic) -> FpuOperand {
        match m {
            Mnemonic::Fild
            | Mnemonic::Fist
            | Mnemonic::Fistp
            | Mnemonic::Fisttp
            | Mnemonic::Fiadd
            | Mnemonic::Fisub
            | Mnemonic::Fisubr
            | Mnemonic::Fimul
            | Mnemonic::Fidiv
            | Mnemonic::Fidivr => FpuOperand::Integer,
            _ => FpuOperand::Float,
        }
    }
}

/// What an x87 arithmetic instruction computes between `st(dst)` and its
/// operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FpuArith {
    /// `fadd`, `faddp`, `fiadd`.
    Add,
    /// `fsub`, `fsubp`, `fisub`.
    Sub,
    /// `fsubr`, `fsubrp`, `fisubr`: the operand minus `st(dst)`, which is
    /// the whole reason the reversed forms exist.
    SubReversed,
    /// `fmul`, `fmulp`, `fimul`.
    Mul,
    /// `fdiv`, `fdivp`, `fidiv`.
    Div,
    /// `fdivr`, `fdivrp`, `fidivr`: the operand over `st(dst)`.
    DivReversed,
}

impl FpuArith {
    /// The operation a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation, or `None` when `m` is not x87 arithmetic.
    fn of(m: Mnemonic) -> Option<FpuArith> {
        Some(match m {
            Mnemonic::Fadd | Mnemonic::Faddp | Mnemonic::Fiadd => FpuArith::Add,
            Mnemonic::Fsub | Mnemonic::Fsubp | Mnemonic::Fisub => FpuArith::Sub,
            Mnemonic::Fsubr | Mnemonic::Fsubrp | Mnemonic::Fisubr => FpuArith::SubReversed,
            Mnemonic::Fmul | Mnemonic::Fmulp | Mnemonic::Fimul => FpuArith::Mul,
            Mnemonic::Fdiv | Mnemonic::Fdivp | Mnemonic::Fidiv => FpuArith::Div,
            Mnemonic::Fdivr | Mnemonic::Fdivrp | Mnemonic::Fidivr => FpuArith::DivReversed,
            _ => return None,
        })
    }

    /// Applies the operation.
    ///
    /// # Arguments
    ///
    /// * `lhs` - `st(dst)`.
    /// * `rhs` - The operand.
    fn apply(self, lhs: f64, rhs: f64) -> f64 {
        match self {
            FpuArith::Add => lhs + rhs,
            FpuArith::Sub => lhs - rhs,
            FpuArith::SubReversed => rhs - lhs,
            FpuArith::Mul => lhs * rhs,
            FpuArith::Div => lhs / rhs,
            FpuArith::DivReversed => rhs / lhs,
        }
    }
}

/// Whether an x87 instruction pops the stack after its work: the `p`
/// forms, and `fisttp`, which always pops after its truncating store.
///
/// # Arguments
///
/// * `m` - The mnemonic.
fn fpu_pops(m: Mnemonic) -> bool {
    matches!(
        m,
        Mnemonic::Fstp
            | Mnemonic::Fistp
            | Mnemonic::Fisttp
            | Mnemonic::Faddp
            | Mnemonic::Fsubp
            | Mnemonic::Fsubrp
            | Mnemonic::Fmulp
            | Mnemonic::Fdivp
            | Mnemonic::Fdivrp
    )
}

/// The magnitude from which `fsincos` and `fptan` take no operand: 2^63.
const FPU_TRIG_RANGE: f64 = 9_223_372_036_854_775_808.0;

/// Bytes of the x87 extended format: an eighty-bit value.
const EXTENDED_BYTES: usize = 10;

/// Bias of the extended format's fifteen-bit exponent.
const EXTENDED_BIAS: i64 = 16383;

/// The extended exponent field of an infinity or a NaN.
const EXTENDED_SPECIAL: u16 = 0x7fff;

/// Bias of a double's eleven-bit exponent.
const DOUBLE_BIAS: i64 = 1023;

/// The double nearest an x87 extended value.
///
/// The format is a sign, a fifteen-bit exponent biased by
/// [`EXTENDED_BIAS`] and a 64-bit mantissa whose top bit is the explicit
/// integer bit. The mantissa rounds to the double's 53 bits, to nearest
/// even, and the exponent then scales it, so a magnitude past a double
/// overflows to an infinity and one below its denormals underflows to
/// zero. A zero exponent is a denormal, scaled as the exponent one. The
/// special exponent is an infinity when the fraction is clear and a NaN
/// otherwise.
///
/// # Arguments
///
/// * `mantissa` - The low eight bytes.
/// * `high` - The top two, in the low sixteen bits: the sign bit over the
///   exponent.
fn extended_to_f64(mantissa: u64, high: u64) -> f64 {
    let high = lo16(high);
    let exponent = high & EXTENDED_SPECIAL;
    let magnitude = if exponent == EXTENDED_SPECIAL {
        if mantissa << 1 == 0 {
            f64::INFINITY
        } else {
            f64::NAN
        }
    } else {
        #[expect(
            clippy::cast_precision_loss,
            reason = "the 64-bit mantissa rounds to the double's 53 bits, which is the conversion"
        )]
        let rounded = mantissa as f64;
        scale(rounded, i64::from(exponent.max(1)) - EXTENDED_BIAS - 63)
    };
    if high & 0x8000 == 0 {
        magnitude
    } else {
        -magnitude
    }
}

/// `v` times two to the `e`.
///
/// Multiplying by a power of two is exact while the result is a normal
/// double, so only the step that leaves that range rounds. The exponent is
/// applied in the steps a double's own exponent can hold.
///
/// # Arguments
///
/// * `v` - The value.
/// * `e` - The binary exponent, of any size.
fn scale(v: f64, e: i64) -> f64 {
    let (mut v, mut e) = (v, e);
    while e != 0 {
        let step = e.clamp(1 - DOUBLE_BIAS, DOUBLE_BIAS);
        v *= f64::from_bits((step + DOUBLE_BIAS).cast_unsigned() << 52);
        e -= step;
    }
    v
}

/// An x87 extended value equal to a double.
///
/// Exact, since the extended format holds every double: a denormal is
/// normalized under its explicit integer bit, and an infinity or a NaN
/// keeps its fraction under the special exponent.
///
/// # Arguments
///
/// * `v` - The value.
///
/// # Returns
///
/// The low eight bytes and the top two, as [`extended_to_f64`] takes them.
fn f64_to_extended(v: f64) -> (u64, u64) {
    let bits = v.to_bits();
    let sign = (bits >> 63) << 15;
    let fraction = bits & ((1 << 52) - 1);
    let exponent = i64::from(lo16(bits >> 52) & 0x7ff);
    let normal = 1 << 63 | fraction << 11;
    let (mantissa, exponent) = match exponent {
        0 if fraction == 0 => (0, 0),
        0 => {
            let unnormal = fraction << 11;
            let shift = unnormal.leading_zeros();
            (
                unnormal << shift,
                1 + EXTENDED_BIAS - DOUBLE_BIAS - i64::from(shift),
            )
        }
        0x7ff => (normal, i64::from(EXTENDED_SPECIAL)),
        e => (normal, e + EXTENDED_BIAS - DOUBLE_BIAS),
    };
    (mantissa, sign | exponent.cast_unsigned())
}

impl<'a> Emulator<'a> {
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
            apis: BTreeMap::new(),
            calls: Vec::new(),
            alloc_next,
            allocs: Vec::new(),
            permissive: false,
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
        for k in 0..TEB_SPAN {
            self.mem.set(self.teb.wrapping_add(k), 0, false);
        }
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
        for k in 0..from_usize(bytes) {
            self.mem.set(addr.wrapping_add(k), lo8(v >> (k * 8)), false);
        }
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
        let mut v = 0x2u64; // bit 1 reads as one on every x86.
        v |= u64::from(self.flags_carry); // CF, bit 0
        v |= u64::from(self.flags_parity) << 2; // PF
        v |= u64::from(self.flags_zero) << 6; // ZF
        v |= u64::from(self.flags_sign) << 7; // SF
        v |= u64::from(self.flags_df) << 10; // DF
        v |= u64::from(self.flags_over.unwrap_or(false)) << 11; // OF
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
    /// program ([`lift::conv`]): on a PE the first four arguments live in
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

    /// Reads the `n`th argument of the API being serviced.
    ///
    /// On a 64-bit target the first few travel in the registers of the
    /// program's convention; on a 32-bit one every argument sits on the
    /// stack above the return address the call pushed, which the stack
    /// pointer still points at when the stub is entered.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    fn api_arg(&self, n: usize) -> u64 {
        match self.arg_slot(n) {
            ArgSlot::Register(r) => self.reg(r),
            ArgSlot::Stack(slot) => self.load(slot, self.word).unwrap_or(0),
        }
    }

    /// Where the `n`th argument lives as the callee sees it on entry.
    ///
    /// The registers are those of the program's convention ([`lift::conv`]);
    /// the stack slots count from the one past the return address, which
    /// the stack pointer still points at, and past any shadow space.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    fn arg_slot(&self, n: usize) -> ArgSlot {
        let conv = lift::conv(self.program, self.bitness);
        if let Some(r) = conv.args.get(n) {
            return ArgSlot::Register(*r);
        }
        let word = from_usize(self.word);
        let past = from_usize(n.saturating_sub(conv.args.len()));
        ArgSlot::Stack(
            self.reg(Register::RSP)
                .wrapping_add(word)
                .wrapping_add(conv.shadow.unsigned_abs())
                .wrapping_add(past.wrapping_mul(word)),
        )
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

    /// Prefills the import table so each slot holds a stub for its API.
    ///
    /// The OS loader writes the address of each imported function into its
    /// import-address-table slot; a packer then reads those slots and calls
    /// through them. This writes a distinct synthetic address into every slot
    /// and remembers which API it stands for, so a call reaching that address
    /// is serviced by [`Emulator::service_api`] instead of faulting on the zero
    /// a static image leaves there. The writes are setup, not materialized
    /// code, so they are not reported as unpacked.
    pub fn install_imports(&mut self) {
        let slots: Vec<(u64, String)> = self
            .program
            .symbols
            .iter()
            .filter(|s| s.kind == crate::program::SymbolKind::Import && s.addr != 0)
            .map(|s| (s.addr, s.name.clone()))
            .collect();
        for (i, (slot, name)) in slots.into_iter().enumerate() {
            let stub = self.api_stub(i);
            self.plant(slot, stub, self.word);
            self.apis.insert(stub, name);
        }
    }

    /// The synthetic address of the `index`th API stub, at the target's
    /// pointer width so an import slot holds all of it.
    ///
    /// # Arguments
    ///
    /// * `index` - The stub's ordinal among those handed out.
    fn api_stub(&self, index: usize) -> u64 {
        let base = if self.bitness == 32 {
            API_STUB_BASE_32
        } else {
            API_STUB_BASE
        };
        base.wrapping_add(from_usize(index) * 8)
    }

    /// The imported APIs and syscalls the run serviced, in order, each with
    /// its decoded arguments and result.
    #[must_use]
    pub fn api_calls(&self) -> &[ApiCall] {
        &self.calls
    }

    /// The byte at `a` only when a write or the image states it: zero
    /// backing left out, so a checker can tell a known byte from an
    /// untouched one.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    #[must_use]
    pub fn byte_stated(&self, a: u64) -> Option<u8> {
        self.mem.get(a).or_else(|| image_byte(self.program, a))
    }

    /// The most recent region the modeled allocator handed out, if any.
    #[must_use]
    pub fn last_alloc(&self) -> Option<u64> {
        self.allocs.last().map(|(base, _)| *base)
    }

    /// The names of the serviced calls, in order: the order and names a
    /// check compares and a count sums, without the decoded arguments.
    #[must_use]
    pub fn api_names(&self) -> Vec<&str> {
        self.calls.iter().map(|c| c.api.as_str()).collect()
    }

    /// Reads a printable string from memory as a load reads it, for decoding
    /// a string argument of a serviced call.
    ///
    /// # Arguments
    ///
    /// * `addr` - The pointer.
    /// * `wide` - Whether the characters are 16-bit.
    ///
    /// # Returns
    ///
    /// The text, or `None` when the address is zero, nothing is mapped, or
    /// no printable character is there ([`calls::read_text`]).
    fn read_memory_text(&self, addr: u64, wide: bool) -> Option<String> {
        calls::read_text(addr, wide, calls::TEXT_MAX, |a| self.byte_at(a))
    }

    /// Services a call that reached an imported function's stub.
    ///
    /// The run transferred to a synthetic stub address, so the call already
    /// pushed its return address; this models the API's effect on `rax` and
    /// hands back the address to resume at. Only the handful of APIs a packer
    /// leans on to stage its payload are modeled with intent (a memory
    /// allocator hands out a fresh region, or the address a `VirtualAlloc`
    /// asks for, a module lookup returns the image base); the rest return
    /// zero so the run continues and stops somewhere the output can name.
    ///
    /// # Arguments
    ///
    /// * `stub` - The stub address the call reached.
    ///
    /// # Returns
    ///
    /// The address to continue at: the caller's return address.
    ///
    /// # Errors
    ///
    /// A fault when the stack holds no return address to pop.
    fn service_api(&mut self, stub: u64) -> Result<u64, Stop> {
        let full = self.apis.get(&stub).cloned().unwrap_or_default();
        let api = crate::analysis::bare_name(&full);
        let format = self.program.format;
        let bits = u8::try_from(self.bitness).unwrap_or(64);
        let caller = self.load(self.reg(Register::RSP), self.word).unwrap_or(0);
        let args = calls::decode_api_args(
            api,
            format,
            bits,
            |n| self.api_arg(n),
            |addr, wide| self.read_memory_text(addr, wide),
        );
        let void = calls::returns_void(api, format);
        let rcx = self.api_arg(0);
        let rv: u64 = if api.starts_with("GetModuleHandle") || api.starts_with("LoadLibrary") {
            // A module handle is the image base; a loaded library, a non-null
            // handle the bootstrap only checks against zero.
            self.program.image_base
        } else if api.starts_with("GetProcAddress") {
            // Hand back a fresh stub so a later call through it is modeled too.
            let next = self.api_stub(self.apis.len());
            self.apis.insert(next, format!("{full}:resolved"));
            next
        } else if api.starts_with("VirtualAlloc") || api == "HeapAlloc" || api == "malloc" {
            let requested = match api {
                "VirtualAlloc" => rcx,
                "VirtualAllocEx" => self.api_arg(1),
                _ => 0,
            };
            if requested == 0 {
                self.allocate()
            } else {
                requested
            }
        } else if api == "memcpy" || api == "memmove" {
            // Copy through the machine's own memory, gathered before it is
            // written so an overlapping move behaves as the OS's does.
            let (src, len) = (self.api_arg(1), self.api_arg(2));
            let len = usize::try_from(len).unwrap_or(0).min(API_COPY_MAX);
            let bytes: Vec<u8> = (0..len)
                .map(|k| self.byte(src.wrapping_add(from_usize(k))).unwrap_or(0))
                .collect();
            for (k, b) in bytes.into_iter().enumerate() {
                self.write(rcx.wrapping_add(from_usize(k)), u64::from(b), 1)?;
            }
            rcx
        } else if api == "memset" {
            let (dst, len) = (self.api_arg(1), self.api_arg(2));
            let len = usize::try_from(len).unwrap_or(0).min(API_COPY_MAX);
            let fill = lo8(rcx);
            for k in 0..len {
                self.write(dst.wrapping_add(from_usize(k)), u64::from(fill), 1)?;
            }
            rcx
        } else if api.starts_with("VirtualProtect") || api.starts_with("VirtualFree") {
            1
        } else {
            self.neutralize(api).unwrap_or_default()
        };
        self.set_reg(Register::RAX, rv);
        self.calls.push(ApiCall {
            api: api.to_owned(),
            syscall: None,
            args,
            ret: (!void).then_some(rv),
            caller,
        });
        let ret = self.pop()?;
        if self.bitness == 32 {
            // INVARIANT: a 32-bit Win32 API pops its own arguments, and a
            // stub that leaves them makes every later slot one frame off.
            use crate::analysis::prototypes::{arity, is_c_runtime, msvc_prototype};
            let dll = full.split_once('!').map_or("", |(d, _)| d);
            let popped = msvc_prototype(api)
                .map(|p| if p.callee_pops { p.params } else { 0 })
                .or_else(|| arity(api).filter(|_| !is_c_runtime(dll)))
                .unwrap_or(0);
            let sp = self
                .reg(Register::RSP)
                .wrapping_add(u64::from(popped) * self.word as u64);
            self.set_reg(Register::RSP, sp);
        }
        Ok(ret)
    }

    /// Hands out the region a modeled allocator returns.
    ///
    /// Regions are [`ALLOC_STRIDE`] apart, from the target's allocation base
    /// up to its API stubs, and step over the image wherever it sits in
    /// between, so no pointer handed out is one the image, the stubs or the
    /// scratch stack above them also answer for. A 32-bit target runs out
    /// after a few hundred regions, and the call then fails as the OS would.
    ///
    /// # Returns
    ///
    /// The region's base, or zero, the null pointer of a failed allocation,
    /// when no region is left below the stubs.
    fn allocate(&mut self) -> u64 {
        let (base, sections) = (self.program.image_base, &self.program.sections);
        let start = sections.iter().map(|s| s.va).fold(base, u64::min);
        let end = sections
            .iter()
            .map(|s| s.va.saturating_add(s.vsize.max(s.file_size)))
            .fold(base, u64::max);
        let mut at = self.alloc_next;
        if at < end && at.saturating_add(ALLOC_STRIDE) > start {
            let Some(past) = end.checked_next_multiple_of(ALLOC_STRIDE) else {
                return 0;
            };
            at = past;
        }
        match at.checked_add(ALLOC_STRIDE) {
            Some(next) if next <= self.api_stub(0) => {
                self.alloc_next = next;
                self.allocs.push((at, next));
                at
            }
            _ => 0,
        }
    }

    /// Answers an anti-analysis query the way an unwatched process would.
    ///
    /// Every emulation feature dies the moment a target checks for a
    /// debugger: the run takes the detection path and reports on code that
    /// never executes in anger. These answers are the ones a process sees
    /// when nothing is attached, and each is recorded so the analyst learns
    /// the target's anti-analysis inventory as a side effect of running it.
    ///
    /// # Arguments
    ///
    /// * `api` - The imported function's bare name.
    ///
    /// # Returns
    ///
    /// The value to leave in `rax`, or `None` when the API is not one of
    /// these and the caller should apply its own default.
    fn neutralize(&mut self, api: &str) -> Option<u64> {
        let (rdx, r8, r9) = (self.api_arg(1), self.api_arg(2), self.api_arg(3));
        let rv = match api {
            // No debugger is present, and the flag the caller reads says so.
            "IsDebuggerPresent" => 0,
            "CheckRemoteDebuggerPresent" => {
                self.write_zeros(rdx, 4);
                1
            }
            // ProcessDebugPort, ProcessDebugObjectHandle and ProcessDebugFlags
            // all read as "not being debugged" when the buffer is zero, except
            // ProcessDebugFlags, where zero means "being debugged"; the classes
            // that matter here are the pointer-shaped ones, so zero the buffer
            // and report success.
            "NtQueryInformationProcess" | "ZwQueryInformationProcess" => {
                self.write_zeros(r8, r9.min(64));
                0
            }
            // ThreadHideFromDebugger succeeds and changes nothing.
            "NtSetInformationThread" | "ZwSetInformationThread" => 0,
            // A thread context with no hardware breakpoints set.
            "NtGetContextThread" | "ZwGetContextThread" | "GetThreadContext" => {
                self.write_zeros(rdx.wrapping_add(0x48), 0x30);
                1
            }
            "NtQuerySystemInformation" | "ZwQuerySystemInformation" => {
                self.write_zeros(rdx, r8.min(64));
                0
            }
            "OutputDebugStringA" | "OutputDebugStringW" => 0,
            _ => return None,
        };
        self.neutralized.insert(api.to_owned());
        Some(rv)
    }

    /// Writes `len` zero bytes at `addr`, bounded so a wild pointer cannot
    /// fill the map.
    ///
    /// # Arguments
    ///
    /// * `addr` - Where to write; a zero address writes nothing.
    /// * `len` - How many bytes, capped at 256.
    fn write_zeros(&mut self, addr: u64, len: u64) {
        if addr == 0 {
            return;
        }
        for k in 0..len.min(256) {
            self.mem.set(addr.wrapping_add(k), 0, false);
        }
    }

    /// Answers a `syscall` the way a kernel that runs nothing would.
    ///
    /// A `syscall` in an ELF is a numbered Linux kernel entry, `rax` the
    /// number and the arguments in `rdi`, `rsi`, `rdx`, `r10`, `r8` and `r9`
    /// (the x86-64 ABI), and full kernel emulation is out of scope. The
    /// honest static model is the loader's benign-answer pattern: `mmap`
    /// hands out one of the modeled allocator's regions (or honors a
    /// non-null hint, which the kernel is allowed to), `write` returns the
    /// count it was asked to write, and `exit`/`exit_group` end the program;
    /// every other number returns zero so the run continues, as an unlisted
    /// Windows API does. Each serviced call is recorded in order with its
    /// number, name and arguments ([`calls::decode_syscall_args`]), so a
    /// report names what the program asked the kernel for; it is not also
    /// one of the [`Emulator::neutralized`] answers, which a report lists
    /// apart, so each call is told once.
    ///
    /// # Arguments
    ///
    /// * `i` - The `syscall` instruction.
    ///
    /// # Returns
    ///
    /// `Ok(None)`: the kernel is modeled as returning, so execution falls
    /// through past the `syscall`.
    ///
    /// # Errors
    ///
    /// [`Stop::Exited`] for the exit numbers, which never return.
    fn linux_syscall(&mut self, i: &Instruction) -> Result<Option<u64>, Stop> {
        let (nr, rdi, rdx) = (
            self.reg(Register::RAX),
            self.reg(Register::RDI),
            self.reg(Register::RDX),
        );
        let name = linux_syscall_name(nr);
        let api = name.map_or_else(|| format!("sys_{nr}"), ToOwned::to_owned);
        let args = name.map_or_else(Vec::new, |n| {
            calls::decode_syscall_args(
                n,
                u8::try_from(self.bitness).unwrap_or(64),
                |k| self.syscall_arg(k),
                |addr, wide| self.read_memory_text(addr, wide),
            )
        });
        let rv = match nr {
            // mmap: a fresh mapped region, or the address it hinted at.
            9 => {
                if rdi == 0 {
                    self.allocate()
                } else {
                    rdi
                }
            }
            // write: a successful write returns its count.
            1 => rdx,
            // exit and exit_group: the kernel does not come back.
            60 | 231 => return Err(Stop::Exited),
            _ => 0,
        };
        self.set_reg(Register::RAX, rv);
        self.calls.push(ApiCall {
            api,
            syscall: Some(nr),
            args,
            ret: Some(rv),
            caller: i.ip(),
        });
        if self.bitness == 64 {
            // SPEC: Intel SDM Vol. 2B, SYSCALL: RCX takes the return address and R11 RFLAGS.
            self.set_reg(Register::RCX, i.next_ip());
            self.set_reg(Register::R11, self.rflags());
        }
        Ok(None)
    }

    /// Reads the `n`th argument of a Linux `syscall` from the register the
    /// kernel ABI puts it in.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    ///
    /// # Returns
    ///
    /// The register value, or zero past the sixth argument.
    fn syscall_arg(&self, n: usize) -> u64 {
        // SPEC: Linux x86-64 syscall ABI: rdi, rsi, rdx, r10, r8, r9.
        let regs = [
            Register::RDI,
            Register::RSI,
            Register::RDX,
            Register::R10,
            Register::R8,
            Register::R9,
        ];
        regs.get(n).map_or(0, |r| self.reg(*r))
    }

    /// The anti-analysis APIs this run answered benignly, in name order.
    #[must_use]
    pub fn neutralized(&self) -> Vec<&str> {
        self.neutralized.iter().map(String::as_str).collect()
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
        (deep..=self.stack_base).contains(&a)
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
            // Code never executes on the scratch stack. A transfer that lands
            // there is a derailed run, not an instruction to decode: a
            // protector's VM computed a target from a value the emulator could
            // not reproduce, or a corrupted return address sent control into
            // the stack. Reported apart from a plain fault so the ceiling reads
            // as "the guard won", not "a byte was unmapped".
            if self.on_stack(ip) {
                break Stop::Derailed(ip);
            }
            let Some(bytes) = self.fetch(ip) else {
                // In best-effort mode a jump into unmapped memory returns to
                // the caller instead of ending the run.
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
                // Reading data as code is a jump gone wrong, not an
                // instruction the machine lacks, and saying so keeps the two
                // apart when a run's stop reason is the diagnosis.
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
            // Hints and fences change nothing a single thread can observe. A
            // wait for a store (`mwaitx`) may wake at once, as the hardware
            // is allowed to, so a spin that polls after it just goes round.
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
                // SPEC: Intel SDM Vol. 2A, LAHF: AH = SF:ZF:0:AF:0:PF:1:CF; the adjust flag is not tracked and reads clear.
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
            // SPEC: Intel SDM Vol. 2A, PUSH A/PUSHD: the eight general
            // registers are pushed in order EAX, ECX, EDX, EBX, ESP (the
            // value BEFORE the push), EBP, ESI, EDI, and POP A restores
            // them in reverse, skipping the stored ESP. Every packer stub
            // opens with this pair, so an unpack run dies at its first
            // instruction without them.
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
                // The fifth word is the stored ESP, which POP A discards.
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
            // A protector saves and restores the flags around its own
            // arithmetic (`pushf; ...; popf`). The model tracks the flags that
            // gate branches, so it assembles them into a `RFLAGS` word to push
            // and reads them back on the pop; the bits it does not track
            // (parity, adjust) ride along as zero, which no depacker branches
            // on. Without this the run stops at the first `pushfq` a VM uses.
            Mnemonic::Pushf | Mnemonic::Pushfd | Mnemonic::Pushfq => {
                self.push(self.rflags())?;
                Ok(None)
            }
            Mnemonic::Popf | Mnemonic::Popfd | Mnemonic::Popfq => {
                let v = self.pop()?;
                self.set_rflags(v);
                Ok(None)
            }
            // `movsd` and `cmpsd` name both a string step and an SSE scalar
            // operation; the string forms address memory through rsi and rdi
            // and take no vector register.
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
                    // SPEC: Intel SDM Vol. 2B, NEG: the flags are those of `0 - operand`, CF set unless the operand is 0.
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
                    // A tail call into an unresolved import: return instead.
                    self.skipped += 1;
                    return self.pop().map(Some);
                }
                Ok(Some(to))
            }
            Mnemonic::Call => {
                let to = self.transfer_target(i)?;
                if self.unresolved(to) {
                    // An unresolved import call: skip it, yielding zero.
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
                // `ret imm16` releases the caller's stack arguments after
                // popping the return address: stdcall/`__fastcall` cleanup, and
                // the form a packer's depacker returns through
                // (`push...; call unpack; ret 20h`). Dropping the immediate
                // leaves the caller reading its own pushed words back as the
                // callee's results, so the next indirect call faults on a zero.
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
                // A half move carries eight bytes into or out of one half of
                // a vector register and leaves the other half alone. A
                // compiler emits them to load a pair of values, so a routine
                // that copies a small struct stops on the first one.
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
                // Lane-wise integer math. A keystream written with SSE mixes
                // several words at once, so a decoder built this way stops on
                // its first packed add without these.
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
                // A lane shifted by its own width or more becomes zero, as
                // the hardware does, which is what a mixer's rotate relies on.
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
                // Interleave one half of each operand, lane by lane: the
                // destination's lane, then the source's, then the next pair.
                // `l` takes the low halves and `h` the high ones. A widening
                // step in vector code is built from these, so a routine that
                // packs bytes into words stops on the first one.
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
                // Widen the accumulator, keeping its sign: the step a compiler
                // emits before using a smaller value as an index.
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
                // Spread the accumulator's sign across the remainder register,
                // which is what a signed division is set up with.
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
                // Narrow every lane to half its width, clamping rather than
                // truncating, the destination's lanes first and the source's
                // after. The counterpart to an unpack, and the last step of a
                // vector routine that writes bytes.
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
                // The destination's own lanes fill its low half and the
                // source's fill its high half, each picked by the immediate.
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
                // Each pair of immediate bits picks one of the source's four
                // doublewords for the matching slot of the destination.
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
            // The x87 stack, as far as a decoder or a checksum uses it. The
            // hardware keeps eighty-bit values; this keeps doubles, which is
            // exact for every integer these routines load and enough for the
            // rest, and the difference cannot reach an address or a byte of
            // recovered text.
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
                // SPEC: Intel SDM Vol. 2A, FXCH: swaps ST(0) with ST(i), ST(1) with no operand; iced lists ST(i) last.
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
                // SPEC: Intel SDM Vol. 2A, FRNDINT: rounds ST(0) to an integer as the control word says, to nearest even by default, the mode `fistp` here stores with.
                self.set_st(0, self.st(0).round_ties_even());
                Ok(None)
            }
            Mnemonic::Fsincos | Mnemonic::Fptan => {
                // SPEC: Intel SDM Vol. 2A, FSINCOS and FPTAN: an operand of magnitude 2^63 or more sets C2 and leaves the stack alone; any other is replaced by its sine and the cosine pushed, or by its tangent and 1.0 pushed.
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
                // Answered as a plain machine, the same way the anti-debug
                // APIs are: a routine that branches on a feature bit gets a
                // usable answer, and one looking for a hypervisor is told
                // there is none. The values are fixed, so a run is repeatable.
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
            // A `syscall` in an ELF is a numbered Linux kernel entry, and the
            // kernel it asks is modeled the way an unlisted import is: the
            // few numbers a bootstrap leans on are answered with intent, the
            // rest benignly, and the exit numbers end the program.
            Mnemonic::Syscall => self.linux_syscall(i),
            Mnemonic::Movlhps | Mnemonic::Movhlps if i.op_count() == 2 => {
                // Both move one half of the source into the other half of the
                // destination: `movlhps` the source's low into the
                // destination's high, `movhlps` the source's high into the
                // destination's low.
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
                // The accumulator is compared with the destination: equal and
                // the source lands in the destination, unequal and the
                // destination lands in the accumulator. A lock-free update
                // spins on this, so answering it lets the loop leave.
                // SPEC: Intel SDM Vol. 2A, CMPXCHG: the flags are those of
                // comparing the accumulator with the destination, every
                // flag the compare sets and not the zero flag alone.
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
                // SPEC: Intel SDM Vol. 2A, DIV/IDIV: a byte divisor divides AX, a wider one DX:AX, EDX:EAX or RDX:RAX; a quotient that does not fit is #DE.
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
                // INVARIANT: the quotient fits the operand width and the
                // remainder is smaller than the divisor, so each register
                // write keeps every bit it holds.
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
                // A small, monotonic tick: a timing check compares two reads
                // and treats a large gap as a debugger, so a counter that
                // barely advances is what an unwatched process sees.
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
                // The destination takes the sum and the source takes the old
                // destination, which is how a lock-free counter reads its own
                // previous value. `store` honours the operand's width.
                // SPEC: Intel SDM Vol. 2B, XADD: the flags are those of the
                // addition itself, so a signed branch after it reads the
                // sum's sign and overflow, not whatever sat in the flags.
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
                    // SPEC: in 64-bit mode a 32-bit `cmovcc` clears the upper
                    // half of its destination even when the condition is false.
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

    /// An arithmetic or logic instruction that writes operand 0 and flags.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - What it computes.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn alu(&mut self, i: &Instruction, op: Alu) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        // Mask to the operand width so the carry is the carry out of that
        // width, not of a 64-bit register: `add dl,dl` with dl >= 0x80 must
        // set carry, which a packer's bit reader depends on.
        let a = u128::from(mask(self.dest(i)?, bits));
        let b = u128::from(mask(self.source(i)?, bits));
        let cin = u128::from(self.flags_carry);
        let top = 1u128 << bits;
        let (r, carry) = match op {
            Alu::Add => {
                let s = a + b;
                (lo64(s), s >= top)
            }
            Alu::Adc => {
                let s = a + b + cin;
                (lo64(s), s >= top)
            }
            Alu::Sub | Alu::Cmp => (lo64(a.wrapping_sub(b)), a < b),
            Alu::Sbb => (lo64(a.wrapping_sub(b).wrapping_sub(cin)), a < b + cin),
            Alu::Xor => (lo64(a ^ b), false),
            Alu::And | Alu::Test => (lo64(a & b), false),
            Alu::Or => (lo64(a | b), false),
        };
        let r = mask(r, bits);
        self.flags_carry = carry;
        self.set_flags(r, bits);
        // Signed overflow: an add overflows when equal signs produce a
        // different one, a subtract when opposite signs produce the sign of
        // the subtrahend. The logical operations clear it.
        let signed = |v: u128| v >> (bits - 1) & 1 == 1;
        self.flags_over = Some(match op {
            Alu::Add | Alu::Adc => signed(a) == signed(b) && signed(u128::from(r)) != signed(a),
            Alu::Sub | Alu::Cmp | Alu::Sbb => {
                signed(a) != signed(b) && signed(u128::from(r)) != signed(a)
            }
            Alu::Xor | Alu::And | Alu::Or | Alu::Test => false,
        });
        if !matches!(op, Alu::Cmp | Alu::Test) {
            self.store(i, r)?;
        }
        Ok(None)
    }

    /// A shift or rotate of operand 0 by operand 1.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - Which shift.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn shift(&mut self, i: &Instruction, op: Shift) -> Result<Option<u64>, Stop> {
        let a = self.dest(i)?;
        let bits = op_bits(i);
        // The count is taken modulo the operand's width, not always 64: a
        // 32-bit shift by 33 shifts by one, and reading it as 33 clears the
        // register instead.
        let modulo = if bits == 64 { 0x3f } else { 0x1f };
        let count = lo32(self.source(i)? & modulo);
        // A shift by zero leaves every flag alone, so nothing may be written.
        if count == 0 {
            self.store(i, mask(a, bits))?;
            return Ok(None);
        }
        let v = mask(a, bits);
        let top = bits.saturating_sub(1);
        let (r, carry) = match op {
            Shift::Shl => (
                v.wrapping_shl(count),
                // The last bit shifted out of the top.
                count <= bits && (v >> (bits - count)) & 1 == 1,
            ),
            Shift::Shr => (v.wrapping_shr(count), (v >> (count - 1).min(63)) & 1 == 1),
            Shift::Sar => (
                (sign_extend(a, bits) >> count.min(63)).cast_unsigned(),
                (sign_extend(a, bits) >> (count - 1).min(63)) & 1 == 1,
            ),
            Shift::Rol => {
                let r = rotate_left(v, count, bits);
                (r, r & 1 == 1)
            }
            Shift::Ror => {
                let r = rotate_right(v, count, bits);
                (r, (r >> top) & 1 == 1)
            }
            // A rotate through carry turns the carry flag into one more bit
            // of the operand, so the rotation is over `bits + 1` places. A
            // bignum add and a compiler's 128-bit shift are built from these.
            Shift::Rcl | Shift::Rcr => {
                let width = bits + 1;
                let n = count % width;
                let wide = (u128::from(self.flags_carry) << bits) | u128::from(v);
                let rotated = if op == Shift::Rcl {
                    (wide << n) | (wide >> (width - n))
                } else {
                    (wide >> n) | (wide << (width - n))
                };
                let out = (rotated >> bits) & 1 == 1;
                (mask(lo64(rotated), bits), out)
            }
        };
        let r = mask(r, bits);
        self.flags_carry = carry;
        self.set_flags(r, bits);
        // SPEC: Intel SDM Vol. 2B, SHL/SHR/SAR/ROL/ROR/RCL/RCR: the
        // overflow of a shift or rotate is defined only for a count of
        // one. A left shift and the rotates xors the result's sign with
        // the carry out, a right shift xors the halved operand's sign with
        // the result's (the zero shifted in), an arithmetic right shift
        // clears it, and `ror`/`rcr` xor the result's two top bits. A
        // larger count leaves it undefined, which stays unknown here
        // rather than guessed.
        let msb = |x: u64| x >> top & 1 == 1;
        self.flags_over = (count == 1).then(|| match op {
            Shift::Shl | Shift::Rol | Shift::Rcl => msb(r) != carry,
            Shift::Shr => msb(v) != msb(r),
            Shift::Sar => false,
            Shift::Ror | Shift::Rcr => msb(r) != (r >> (top - 1) & 1 == 1),
        });
        self.store(i, r)?;
        Ok(None)
    }

    /// Reads operand 0 as a value (for read-modify-write instructions).
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    fn dest(&mut self, i: &Instruction) -> Result<u64, Stop> {
        self.operand(i, 0)
    }

    /// Reads the source operand: operand 1 for two-operand forms, else 0.
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    fn source(&mut self, i: &Instruction) -> Result<u64, Stop> {
        let idx = u32::from(i.op_count() > 1);
        self.operand(i, idx)
    }

    /// Reads operand `n`.
    ///
    /// # Errors
    ///
    /// When the operand is a kind the emulator does not model, or faults.
    fn operand(&mut self, i: &Instruction, n: u32) -> Result<u64, Stop> {
        match i.op_kind(n) {
            OpKind::Register => Ok(self.reg_sized(i.op_register(n))),
            OpKind::Immediate8 => Ok(u64::from(i.immediate8())),
            OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate32to64
            | OpKind::Immediate64 => Ok(i.immediate(n)),
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.load(addr, mem_bytes(i))
            }
            other => Err(Stop::Unmodeled(format!("operand {other:?}"))),
        }
    }

    /// Reads operand `n` as a 128-bit vector.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `n` - The operand index.
    ///
    /// # Errors
    ///
    /// When the operand is neither a vector register nor memory.
    fn vector_operand(&mut self, i: &Instruction, n: u32) -> Result<u128, Stop> {
        match i.op_kind(n) {
            OpKind::Register => match xmm_slot(i.op_register(n)) {
                Some(k) => Ok(self.xmm[k]),
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op_register(n)))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                let lo = self.load(addr, 8)?;
                let hi = self.load(addr.wrapping_add(8), 8)?;
                Ok(u128::from(lo) | (u128::from(hi) << 64))
            }
            other => Err(Stop::Unmodeled(format!("vector operand {other:?}"))),
        }
    }

    /// Writes a 128-bit vector to operand 0.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// When operand 0 is neither a vector register nor memory, or memory
    /// would grow past its cap.
    fn vector_store(&mut self, i: &Instruction, v: u128) -> Result<(), Stop> {
        match i.op0_kind() {
            OpKind::Register => match xmm_slot(i.op0_register()) {
                Some(k) => {
                    self.xmm[k] = v;
                    Ok(())
                }
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op0_register()))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.write(addr, lo64(v), 8)?;
                self.write(addr.wrapping_add(8), lo64(v >> 64), 8)
            }
            other => Err(Stop::Unmodeled(format!("vector store {other:?}"))),
        }
    }

    /// Moves the low `width` bytes between a vector register and elsewhere.
    ///
    /// `movss`, `movsd`, `movd` and `movq` carry a scalar in the bottom of a
    /// vector register. A read from memory clears the rest of the register,
    /// as the hardware does; a move between two vector registers leaves the
    /// upper bytes of the destination alone.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `width` - The lane carried.
    ///
    /// # Errors
    ///
    /// When neither operand is a vector register, which is not a form these
    /// mnemonics take.
    fn scalar_move(&mut self, i: &Instruction, width: Width) -> Result<(), Stop> {
        let dst_vec = i.op0_kind() == OpKind::Register && xmm_slot(i.op0_register()).is_some();
        let src_vec = i.op_kind(1) == OpKind::Register && xmm_slot(i.op_register(1)).is_some();
        // Between registers `movss`/`movsd` merge the lane into the rest of
        // the destination; `movd`/`movq` zero the rest.
        let merge = matches!(i.mnemonic(), Mnemonic::Movss | Mnemonic::Movsd);
        let mask = width.lane();
        if dst_vec {
            let src = if src_vec {
                self.vector_operand(i, 1)? & mask
            } else {
                u128::from(self.operand(i, 1)?) & mask
            };
            let keep = if src_vec && merge {
                self.vector_operand(i, 0)? & !mask
            } else {
                0
            };
            self.vector_store(i, keep | src)?;
            return Ok(());
        }
        if src_vec {
            let v = lo64(self.vector_operand(i, 1)? & mask);
            return self.store(i, v);
        }
        Err(Stop::Unmodeled(format!("scalar move {:?}", i.mnemonic())))
    }

    /// Writes `v` to operand 0, register or memory.
    ///
    /// # Errors
    ///
    /// When operand 0 is a kind the emulator cannot write, or memory would
    /// grow past its cap.
    fn store(&mut self, i: &Instruction, v: u64) -> Result<(), Stop> {
        match i.op0_kind() {
            OpKind::Register => {
                self.write_reg_op(i, v);
                Ok(())
            }
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.write(addr, v, mem_bytes(i))
            }
            other => Err(Stop::Unmodeled(format!("store {other:?}"))),
        }
    }

    /// Writes `v` to the register named by operand 0, honoring its width.
    fn write_reg_op(&mut self, i: &Instruction, v: u64) {
        self.set_reg_sized(i.op0_register(), v);
    }

    /// The destination of an indirect jump or call: the register's value, or
    /// the pointer loaded from the memory operand (a dispatch's jump table).
    ///
    /// # Arguments
    ///
    /// * `i` - The indirect jump or call.
    ///
    /// # Errors
    ///
    /// A fault when the table entry is unmapped, or unmodeled for a form that
    /// is neither register nor memory.
    fn indirect_target(&self, i: &Instruction) -> Result<u64, Stop> {
        match i.op0_kind() {
            OpKind::Register => Ok(self.reg(canon(i.op0_register()))),
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.load(addr, self.word)
            }
            other => Err(Stop::Unmodeled(format!("indirect {other:?}"))),
        }
    }

    /// The destination of a jump or call: its direct target, else
    /// [`Emulator::indirect_target`].
    ///
    /// # Arguments
    ///
    /// * `i` - The jump or call.
    ///
    /// # Errors
    ///
    /// As [`Emulator::indirect_target`].
    fn transfer_target(&self, i: &Instruction) -> Result<u64, Stop> {
        branch_target(i).map_or_else(|| self.indirect_target(i), Ok)
    }

    /// Whether a condition holds under the current flags.
    ///
    /// # Arguments
    ///
    /// * `m` - The instruction's mnemonic, named in the stop.
    /// * `cond` - The conditional jump that reads the same flags.
    ///
    /// # Errors
    ///
    /// Unmodeled when the condition rests on a flag nothing computed.
    fn condition(&self, m: Mnemonic, cond: Mnemonic) -> Result<bool, Stop> {
        self.jcc_taken(cond)
            .ok_or_else(|| Stop::Unmodeled(format!("{m:?} on flags it did not set")))
    }

    /// The effective address of a memory operand.
    ///
    /// A 16-bit address ([`crate::disasm::addresses_16_bit`]) reads the
    /// 16-bit registers and wraps at 64 KiB before the segment base is added.
    ///
    /// # Errors
    ///
    /// Never; kept fallible for symmetry with the operand readers.
    fn mem_addr(&self, i: &Instruction) -> Result<u64, Stop> {
        if i.memory_base() == Register::RIP || i.memory_base() == Register::EIP {
            return Ok(i.ip_rel_memory_address());
        }
        let sixteen = crate::disasm::addresses_16_bit(i);
        let read = |r: Register| {
            if sixteen {
                self.reg_sized(r)
            } else {
                self.reg(canon(r))
            }
        };
        let base = if i.memory_base() == Register::None {
            0
        } else {
            read(i.memory_base())
        };
        let index = if i.memory_index() == Register::None {
            0
        } else {
            read(i.memory_index()).wrapping_mul(u64::from(i.memory_index_scale()))
        };
        let offset = base
            .wrapping_add(index)
            .wrapping_add(i.memory_displacement64());
        let offset = if sixteen { offset & 0xffff } else { offset };
        let segment = match (self.bitness, i.segment_prefix()) {
            (32, Register::FS) | (64, Register::GS) => self.teb,
            _ => 0,
        };
        Ok(self.narrow(offset.wrapping_add(segment)))
    }

    /// Whether anything backs `addr`: a written byte or the mapped image.
    ///
    /// Used in best-effort mode to tell a real transfer target from an import
    /// slot the OS loader would have filled, which stays zero or unmapped here.
    fn mapped(&self, addr: u64) -> bool {
        self.byte(addr).is_some()
    }

    /// Whether best-effort mode skips a transfer to `to`: nothing maps it
    /// and it is not an API stub, so it is an import the OS loader would
    /// have resolved.
    ///
    /// # Arguments
    ///
    /// * `to` - The transfer target.
    fn unresolved(&self, to: u64) -> bool {
        self.permissive && !self.apis.contains_key(&to) && !self.mapped(to)
    }

    /// Reads up to sixteen instruction bytes at `ip`, written bytes over image.
    ///
    /// The fetch consults memory the run has written before the static image,
    /// so code a packer decrypts into memory executes as the decrypted bytes,
    /// not the encrypted ones on disk. Code written into space the image never
    /// mapped (a packer's virtual-only section) is fetched from memory alone.
    ///
    /// # Returns
    ///
    /// The bytes to decode, or `None` when neither memory nor image backs `ip`.
    fn fetch(&self, ip: u64) -> Option<Vec<u8>> {
        // The window saturates rather than wrapping: a range whose start is
        // past its end is not a valid range to ask a set for.
        let window = ip..ip.saturating_add(16);
        if !self.mem.any_dirty(window.clone())
            && self.patched.range(window).next().is_none()
            && let Some(s) = self.program.read_va_upto(ip, 16)
        {
            return Some(s.to_vec());
        }
        let out = self.code_at(ip, 16);
        (!out.is_empty()).then_some(out)
    }

    /// Loads `bytes` bytes from `addr`, little-endian.
    ///
    /// # Errors
    ///
    /// A fault when a byte is neither written nor backed by the image.
    fn load(&self, addr: u64, bytes: usize) -> Result<u64, Stop> {
        if self.profiling && !self.on_stack(addr) {
            let mut pages = self.page_reads.borrow_mut();
            let entry = pages.entry(addr & !(PAGE - 1)).or_insert((0, self.last_ip));
            entry.0 += 1;
        }
        let mut v = 0u64;
        for k in 0..from_usize(bytes) {
            let a = addr.wrapping_add(k);
            let byte = self.byte_at(a).ok_or(Stop::Fault(a))?;
            v |= u64::from(byte) << (k * 8);
        }
        if self.trace_cap > 0 {
            self.step_memory.borrow_mut().push((false, addr, bytes, v));
        }
        Ok(v)
    }

    /// Writes the low `bytes` bytes of `v` to `addr`, little-endian.
    ///
    /// A write outside the stack is recorded as materialized: the bytes a
    /// packer decrypts into memory, which [`Emulator::run`] can then execute.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when a byte not yet held would take memory past
    /// its cap; the bytes before it are written.
    fn write(&mut self, addr: u64, v: u64, bytes: usize) -> Result<(), Stop> {
        if self.trace_cap > 0 {
            self.step_memory.borrow_mut().push((true, addr, bytes, v));
        }
        for k in 0..from_usize(bytes) {
            let a = addr.wrapping_add(k);
            if self.mem.len() >= self.memory_max && !self.mem.contains(a) {
                return Err(Stop::MemoryFull(a));
            }
            let byte = lo8(v >> (k * 8));
            if self.history.len() < HISTORY_MAX {
                self.history.push(Written {
                    addr: a,
                    value: byte,
                });
            }
            if self.origin.is_some() {
                self.step_writes.push(a);
            }
            self.mem.set(a, byte, !self.on_stack(a));
        }
        Ok(())
    }

    /// Whether the step that just ran birthed the watched value.
    ///
    /// A value is born the moment it exists whole: in any general register,
    /// or in memory at any alignment a write of this step touched, so a
    /// value built by two narrow stores is born by the one that completes
    /// it, whatever earlier steps wrote the other half. The instruction's
    /// own fetch does not count.
    ///
    /// # Returns
    ///
    /// Whether the watched value appeared.
    fn born(&self) -> bool {
        let Some(watch) = self.origin else {
            return false;
        };
        if self.regs.contains(&watch) {
            return true;
        }
        self.step_writes.iter().any(|a| {
            (0..8).any(|back| {
                let at = a.wrapping_sub(back);
                (0..8).all(|k| self.byte(at.wrapping_add(k)) == Some(lo8(watch >> (k * 8))))
            })
        })
    }

    /// Reads `st(n)`.
    ///
    /// # Arguments
    ///
    /// * `n` - Depth from the top of the stack.
    fn st(&self, n: usize) -> f64 {
        self.fpu
            .get((self.fpu_top + n) % self.fpu.len())
            .copied()
            .unwrap_or(0.0)
    }

    /// Writes `st(n)`.
    ///
    /// # Arguments
    ///
    /// * `n` - Depth from the top of the stack.
    /// * `v` - The value.
    fn set_st(&mut self, n: usize, v: f64) {
        let at = (self.fpu_top + n) % self.fpu.len();
        if let Some(slot) = self.fpu.get_mut(at) {
            *slot = v;
        }
    }

    /// Pushes a value, which moves the top down as the hardware does.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn fpush(&mut self, v: f64) {
        self.fpu_top = (self.fpu_top + self.fpu.len() - 1) % self.fpu.len();
        self.set_st(0, v);
    }

    /// Pops the top of the stack, discarding it.
    fn fpop(&mut self) {
        self.set_st(0, 0.0);
        self.fpu_top = (self.fpu_top + 1) % self.fpu.len();
    }

    /// Reads the memory operand of an x87 instruction as a double.
    ///
    /// The hardware keeps eighty-bit values; this keeps doubles, which is
    /// exact for every integer these routines load and enough for the
    /// rest, and the difference cannot reach an address or a byte of
    /// recovered text. An integer operand is a word, a dword or a qword,
    /// sign-extended; a float operand is a single, a double or the
    /// eighty-bit extended format, which [`extended_to_f64`] rounds.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `operand` - What the memory holds.
    ///
    /// # Errors
    ///
    /// A fault when the operand is unmapped.
    fn fpu_memory(&self, i: &Instruction, operand: FpuOperand) -> Result<f64, Stop> {
        let addr = self.mem_addr(i)?;
        let width = i.memory_size().size();
        Ok(match operand {
            FpuOperand::Integer => {
                let width = width.clamp(2, 8);
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "fild and its kin round the integer to the double this keeps for an x87 value"
                )]
                let loaded = sign_extend(self.load(addr, width)?, width_bits(width)) as f64;
                loaded
            }
            FpuOperand::Float if width == EXTENDED_BYTES => {
                extended_to_f64(self.load(addr, 8)?, self.load(addr.wrapping_add(8), 2)?)
            }
            FpuOperand::Float if width == 4 => f64::from(f32::from_bits(lo32(self.load(addr, 4)?))),
            FpuOperand::Float => f64::from_bits(self.load(addr, 8)?),
        })
    }

    /// `fld` and `fild`: pushes `st(n)`, a float or an integer from memory.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// A fault when the operand is unmapped.
    fn fpu_load(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let v = if i.op0_kind() == OpKind::Register {
            self.st(st_depth_mod8(i.op0_register()))
        } else {
            self.fpu_memory(i, FpuOperand::of(m))?
        };
        self.fpush(v);
        Ok(None)
    }

    /// `fst`, `fstp`, `fist`, `fistp` and `fisttp`: `st(0)` into `st(n)`,
    /// or into memory as a float or an integer, popping for the `p` forms.
    ///
    /// An integer store takes the operand's own width (a word, a dword or
    /// a qword) and rounds the way the control word says, to nearest even
    /// by default; only `fisttp` truncates. A value the width cannot hold
    /// is the integer indefinite, as for `cvtsd2si`. A float store is a
    /// single, a double or the eighty-bit extended format, which
    /// [`f64_to_extended`] writes exactly.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when the store would take memory past its cap;
    /// the write cannot fault.
    fn fpu_store(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let v = self.st(0);
        if i.op0_kind() == OpKind::Register {
            self.set_st(st_depth_mod8(i.op0_register()), v);
        } else {
            let addr = self.mem_addr(i)?;
            let width = i.memory_size().size();
            if FpuOperand::of(m) == FpuOperand::Integer {
                let size = width.clamp(2, 8);
                let rounding = if m == Mnemonic::Fisttp {
                    Rounding::Truncate
                } else {
                    Rounding::Nearest
                };
                self.write(addr, sse::float_to_int(v, width_bits(size), rounding), size)?;
            } else if width == EXTENDED_BYTES {
                let (mantissa, high) = f64_to_extended(v);
                self.write(addr, mantissa, 8)?;
                self.write(addr.wrapping_add(8), high, 2)?;
            } else if width == 4 {
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "fst to a single rounds the double by design"
                )]
                let single = v as f32;
                self.write(addr, u64::from(single.to_bits()), 4)?;
            } else {
                self.write(addr, v.to_bits(), 8)?;
            }
        }
        if fpu_pops(m) {
            self.fpop();
        }
        Ok(None)
    }

    /// The x87 arithmetic: `st(dst)` and an operand combined by `op`.
    ///
    /// The operand is `st(n)` when it is a register, else memory holding
    /// an integer for the `fi` forms and a float otherwise; the destination
    /// is `st(0)` unless the instruction names another.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    /// * `op` - What it computes.
    ///
    /// # Errors
    ///
    /// A fault when a memory operand is unmapped.
    fn fpu_arith(
        &mut self,
        i: &Instruction,
        m: Mnemonic,
        op: FpuArith,
    ) -> Result<Option<u64>, Stop> {
        let (dst, rhs) = if i.op_count() == 0 {
            (0usize, self.st(1))
        } else if i.op0_kind() == OpKind::Register {
            let a = st_depth_mod8(i.op0_register());
            if i.op_count() > 1 && i.op_kind(1) == OpKind::Register {
                let b = st_depth_mod8(i.op_register(1));
                if a == 0 {
                    (0, self.st(b))
                } else {
                    (a, self.st(0))
                }
            } else {
                (0, self.st(a))
            }
        } else {
            (0, self.fpu_memory(i, FpuOperand::of(m))?)
        };
        let v = op.apply(self.st(dst), rhs);
        self.set_st(dst, v);
        if fpu_pops(m) {
            self.fpop();
        }
        Ok(None)
    }

    /// Whether `addr` is in the scratch stack the emulator hands the routine.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    fn on_stack(&self, addr: u64) -> bool {
        addr >= self.stack_base.wrapping_sub(self.stack_span)
            && addr < self.stack_base.wrapping_add(self.stack_span)
    }

    /// Pushes a word onto the scratch stack.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when the word would take memory past its cap.
    fn push(&mut self, v: u64) -> Result<(), Stop> {
        let sp = self.narrow(self.reg(Register::RSP).wrapping_sub(self.word as u64));
        self.set_reg(Register::RSP, sp);
        self.write(sp, v, self.word)
    }

    /// Pops a word from the scratch stack.
    ///
    /// # Errors
    ///
    /// A fault when the stack word was never written.
    fn pop(&mut self) -> Result<u64, Stop> {
        let sp = self.reg(Register::RSP);
        let v = self.load(sp, self.word)?;
        self.set_reg(
            Register::RSP,
            self.narrow(sp.wrapping_add(self.word as u64)),
        );
        Ok(v)
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

    /// Runs a string instruction, repeating it when it carries a `rep` prefix.
    ///
    /// `rep movs` is how a packer copies its decrypted payload into place, so
    /// modeling the string operations is what lets the run materialize a whole
    /// image rather than a handful of bytes. The direction flag chooses the
    /// step's sign; `repe`/`repne` forms stop early on the zero flag. In
    /// 32-bit code the pointers wrap at four gigabytes, as the processor's
    /// do. An implausibly large count reads as a runaway on uninitialized
    /// state and stops the run rather than spinning.
    ///
    /// Each iteration past the first spends a step of the budget (the
    /// instruction's own step pays for the first), so the budget bounds a
    /// run's string work as it bounds its instructions: a hostile `rep stos`
    /// under a budget of five once ran for over a second and wrote 750
    /// megabytes. An iteration the budget cannot pay for stops the run with
    /// the counter and pointers stepped as far as the iterations it paid
    /// for, where an interrupt would leave them.
    ///
    /// # Arguments
    ///
    /// * `i` - The string instruction.
    /// * `op` - What one step does.
    /// * `bytes` - The element width.
    ///
    /// # Errors
    ///
    /// A fault when a load or store leaves mapped memory, [`Stop::Budget`]
    /// when the budget runs out mid-repeat, and [`Stop::MemoryFull`] when
    /// memory would grow past its cap.
    fn string_op(
        &mut self,
        i: &Instruction,
        op: StringOp,
        bytes: usize,
    ) -> Result<Option<u64>, Stop> {
        let size = from_usize(bytes);
        let bits = width_bits(bytes);
        let step = if self.flags_df {
            0u64.wrapping_sub(size)
        } else {
            size
        };
        // Only `scas`/`cmps` consult the zero flag to stop early; `movs`,
        // `stos` and `lods` repeat the full count. iced reports `repe` for the
        // same `f3` byte that means plain `rep` on the latter, so the early
        // exit is gated on the instruction actually being a compare.
        let zf_sensitive = matches!(op, StringOp::Scas | StringOp::Cmps);
        let repe = zf_sensitive && i.has_repe_prefix();
        let repne = zf_sensitive && i.has_repne_prefix();
        let rep = i.has_rep_prefix() || i.has_repe_prefix() || i.has_repne_prefix();
        let mut count = if rep { self.reg(Register::RCX) } else { 1 };
        if count > REP_MAX {
            return Err(Stop::Unmodeled("rep count too large".to_owned()));
        }
        let mut paid = true;
        while count > 0 {
            if !paid {
                if self.steps >= self.budget {
                    return Err(Stop::Budget);
                }
                self.steps += 1;
            }
            paid = false;
            let si = self.reg(Register::RSI);
            let di = self.reg(Register::RDI);
            let (next_si, next_di) = (
                self.narrow(si.wrapping_add(step)),
                self.narrow(di.wrapping_add(step)),
            );
            match op {
                StringOp::Movs => {
                    let v = self.load(si, bytes)?;
                    self.write(di, v, bytes)?;
                    self.set_reg(Register::RSI, next_si);
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Stos => {
                    self.write(di, self.reg(Register::RAX), bytes)?;
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Lods => {
                    let v = self.load(si, bytes)?;
                    self.set_reg_sized(sized_ax(bytes), v);
                    self.set_reg(Register::RSI, next_si);
                }
                StringOp::Scas => {
                    let a = mask(self.reg(Register::RAX), bits);
                    let b = self.load(di, bytes)?;
                    self.set_flags(a.wrapping_sub(b), bits);
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Cmps => {
                    let a = self.load(si, bytes)?;
                    let b = self.load(di, bytes)?;
                    self.set_flags(a.wrapping_sub(b), bits);
                    self.set_reg(Register::RSI, next_si);
                    self.set_reg(Register::RDI, next_di);
                }
            }
            count -= 1;
            if rep {
                self.set_reg(Register::RCX, count);
                if repe && !self.flags_zero {
                    break;
                }
                if repne && self.flags_zero {
                    break;
                }
            }
        }
        Ok(None)
    }

    /// Writes `v` into register `r` honoring its named width.
    fn set_reg_sized(&mut self, r: Register, v: u64) {
        let bits = reg_bits(r);
        let full = canon(r);
        let cur = self.reg(full);
        let placed = if bits >= 32 {
            mask(v, bits)
        } else {
            let at = lane_shift(r);
            (cur & !(mask(u64::MAX, bits) << at)) | (mask(v, bits) << at)
        };
        self.set_reg(full, placed);
    }

    /// Sets the zero, sign and parity flags from a result of `bits` width.
    ///
    /// Overflow goes unknown here and an instruction that computes it assigns
    /// it after, so an instruction the emulator models without overflow
    /// cannot leave a stale one behind for a signed jump to read.
    fn set_flags(&mut self, r: u64, bits: u32) {
        let v = mask(r, bits);
        self.flags_zero = v == 0;
        self.flags_sign = v >> (bits - 1) & 1 == 1;
        self.flags_parity = lo8(v).count_ones().is_multiple_of(2);
        self.flags_over = None;
    }

    /// Reads a register at its named width.
    fn reg_sized(&self, r: Register) -> u64 {
        let bits = reg_bits(r);
        mask(self.reg(canon(r)) >> lane_shift(r), bits)
    }

    /// The full-width value of a canonical register.
    ///
    /// The general registers and the six segment registers are held (a
    /// segment as its zero-extended selector, [`Emulator::segments`]). Any
    /// other register (a debug or control one, which `mov eax, dr7` names)
    /// reads as zero: the decoder numbers each register within its own kind,
    /// so `dr0` shares `rax`'s number, and indexing by it read and wrote
    /// `rax`.
    fn reg(&self, r: Register) -> u64 {
        if let Some(slot) = seg_slot(r) {
            return self.segs[slot];
        }
        let Some(at) = gpr_bank_index(r) else {
            return 0;
        };
        self.regs.get(at).copied().unwrap_or(0)
    }

    /// Sets a canonical register's full-width value; a register that is not
    /// held does not change anything ([`Emulator::reg`]). A segment register
    /// keeps the low sixteen bits a move writes, the selector the machine
    /// holds.
    fn set_reg(&mut self, r: Register, v: u64) {
        if let Some(slot) = seg_slot(r) {
            self.segs[slot] = v & 0xffff;
            return;
        }
        if let Some(at) = gpr_bank_index(r)
            && let Some(slot) = self.regs.get_mut(at)
        {
            *slot = v;
        }
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
    use super::{
        Emulator, PageRun, Stop, TRACE_MAX, extended_to_f64, f64_to_extended, fill_byte, lo8,
    };
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
            0x0f, 0x57, 0xc0, // xorps xmm0,xmm0
            0x0f, 0x28, 0xc8, // movaps xmm1,xmm0
            0xf3, 0x0f, 0x10, 0xd1, // movss xmm2,xmm1
            0xc3, // ret
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
        let code: &[u8] = &[
            0x31, 0xc0, // xor eax,eax
            0x83, 0xf8, 0x00, // cmp eax,0
            0x0f, 0x94, 0xc0, // sete al
            0xc3, // ret
        ];
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
            0xb8, 0xf9, 0xff, 0xff, 0xff, // mov eax,-7
            0x99, // cdq
            0xb9, 0x02, 0x00, 0x00, 0x00, // mov ecx,2
            0xf7, 0xf9, // idiv ecx
            0xc3, // ret
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(0xffff_fffd), "quotient -3");
        assert_eq!(emu.register("rdx"), Some(0xffff_ffff), "remainder -1");

        // ASM: mov ax,0x107; mov cl,2; div cl; ret
        let code: &[u8] = &[
            0x66, 0xb8, 0x07, 0x01, // mov ax,0x107
            0xb1, 0x02, // mov cl,2
            0xf6, 0xf1, // div cl
            0xc3, // ret
        ];
        let emu = returned(image(code, &[]));
        assert_eq!(emu.register("rax"), Some(0x0183), "263 / 2: al 131, ah 1");

        // ASM: mov edx,2; mov eax,0; mov ecx,1; div ecx; ret
        let code: &[u8] = &[
            0xba, 0x02, 0x00, 0x00, 0x00, // mov edx,2
            0xb8, 0x00, 0x00, 0x00, 0x00, // mov eax,0
            0xb9, 0x01, 0x00, 0x00, 0x00, // mov ecx,1
            0xf7, 0xf1, // div ecx
            0xc3, // ret
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
            0xb8, 0x05, 0x00, 0x00, 0x00, // mov eax,5
            0xf7, 0xd8, // neg eax
            0x0f, 0x98, 0xc1, // sets cl
            0x0f, 0x92, 0xc2, // setc dl
            0xc3, // ret
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
            0xb8, 0x34, 0x12, 0x00, 0x00, // mov eax,0x1234
            0x0f, 0xb6, 0xcc, // movzx ecx,ah
            0xb7, 0x56, // mov bh,0x56
            0xb3, 0x78, // mov bl,0x78
            0xc3, // ret
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
            0xb8, 0x09, 0x00, 0x00, 0x00, // mov eax,9
            0x31, 0xff, // xor edi,edi
            0xbe, 0x00, 0x10, 0x00, 0x00, // mov esi,0x1000
            0x31, 0xd2, // xor edx,edx
            0x41, 0xba, 0x22, 0x00, 0x00, 0x00, // mov r10d,0x22
            0x45, 0x31, 0xc0, // xor r8d,r8d
            0x45, 0x31, 0xc9, // xor r9d,r9d
            0x0f, 0x05, // syscall
            0x48, 0x89, 0xc6, // mov rsi,rax
            0xc7, 0x06, 0x41, 0x42, 0x43, 0x44, // mov dword [rsi],0x44434241
            0x8b, 0x06, // mov eax,[rsi]
            0xc3, // ret
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
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xbf, 0x01, 0x00, 0x00, 0x00, // mov edi,1
            0x31, 0xf6, // xor esi,esi
            0xba, 0x05, 0x00, 0x00, 0x00, // mov edx,5
            0x0f, 0x05, // syscall
            0x41, 0x89, 0xc0, // mov r8d,eax
            0xb8, 0xe7, 0x03, 0x00, 0x00, // mov eax,999
            0x0f, 0x05, // syscall
            0x41, 0x89, 0xc1, // mov r9d,eax
            0xc3, // ret
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
            0xb8, 0x3c, 0x00, 0x00, 0x00, // mov eax,60
            0x31, 0xff, // xor edi,edi
            0x0f, 0x05, // syscall
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
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
        // ASM at 0x1000: xor eax,eax; ret  -- patched to: mov eax,0x1234; ret
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
            0x31, 0xc0, // xor eax,eax
            0x39, 0xc0, // cmp eax,eax
            0x7f, 0x06, // jg .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
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
            0xb0, 0x80, // mov al,0x80
            0x3c, 0x01, // cmp al,1
            0x7c, 0x06, // jl .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
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
            0xb8, 0x00, 0x00, 0x00, 0x40, // mov eax,0x40000000
            0xd1, 0xe0, // shl eax,1
            0x70, 0x06, // jo .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
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
            0xb8, 0x00, 0x00, 0x00, 0x80, // mov eax,0x80000000
            0xd1, 0xe8, // shr eax,1
            0x70, 0x06, // jo .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
        ];
        let emu = returned(image(shr, &[]));
        assert_eq!(emu.register("rax"), Some(2), "shr's overflow was clear");

        // ASM: mov eax,0x80000000; sar eax,1; jo .taken; mov eax,1; ret
        //      .taken: mov eax,2; ret
        let sar: &[u8] = &[
            0xb8, 0x00, 0x00, 0x00, 0x80, // mov eax,0x80000000
            0xd1, 0xf8, // sar eax,1
            0x70, 0x06, // jo .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
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
            0xb8, 0x05, 0x00, 0x00, 0x00, // mov eax,5
            0xc1, 0xe0, 0x02, // shl eax,2
            0x7f, 0x01, // jg +1
            0xc3, // ret
            0xc3, // ret
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
            0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // mov rax,-1
            0x66, 0x48, 0x0f, 0x6e, 0xc0, // movq xmm0,rax
            0x48, 0xc7, 0xc0, 0x02, 0x00, 0x00, 0x00, // mov rax,2
            0x66, 0x48, 0x0f, 0x6e, 0xc8, // movq xmm1,rax
            0x66, 0x0f, 0xd4, 0xc1, // paddq xmm0,xmm1
            0x66, 0x48, 0x0f, 0x7e, 0xc0, // movq rax,xmm0
            0xc3, // ret
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
        let code: &[u8] = &[
            0xb8, 0xff, 0xff, 0xff, 0xff, // mov eax,0xffffffff
            0x48, 0x98, // cdqe
            0xc3, // ret
        ];
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
            0xb8, 0x03, 0x00, 0x00, 0x00, // mov eax,3
            0xd1, 0xe8, // shr eax,1
            0x72, 0x06, // jb .taken
            0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
            0xc3, // ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // .taken: mov eax,2
            0xc3, // ret
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
        let code: &[u8] = &[
            0xb8, 0x00, 0x00, 0x00, 0x80, // mov eax,0x80000000
            0xd1, 0xe0, // shl eax,1
            0xd1, 0xd0, // rcl eax,1
            0xc3, // ret
        ];
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
            0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // fild dword [0x2000]
            0xda, 0x34, 0x25, 0x04, 0x20, 0x00, 0x00, // fidiv dword [0x2004]
            0xdb, 0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, // fistp dword [0x2008]
            0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, // mov eax,[0x2008]
            0xc3, // ret
        ];
        // 100 at 0x2000 and 7 at 0x2004; 100 / 7 is 14 once truncated.
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
            0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // fild dword [0x2000]
            0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00, // fild dword [0x2004]
            0xdb, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, // fild dword [0x2008]
            0xd9, 0xca, // fxch st2
            0xdb, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00, // fistp dword [0x200c]
            0xd9, 0xc9, // fxch
            0xdb, 0x1c, 0x25, 0x10, 0x20, 0x00, 0x00, // fistp dword [0x2010]
            0xdb, 0x1c, 0x25, 0x14, 0x20, 0x00, 0x00, // fistp dword [0x2014]
            0xc3, // ret
        ];
        // 1, 2 and 3 loaded in turn: `fxch st2` brings the 1 up, the bare
        // `fxch` then swaps the 2 under the 3.
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
            s.va += super::ALLOC_BASE_32;
        }
        let mut emu = Emulator::new(&p, 1).expect("emulator");
        let regions: Vec<u64> = std::iter::repeat_with(|| emu.allocate())
            .take_while(|&a| a != 0)
            .take(1000)
            .collect();
        assert_eq!(
            regions.first(),
            Some(&(super::ALLOC_BASE_32 + super::ALLOC_STRIDE))
        );
        assert!(
            regions
                .windows(2)
                .all(|w| w[1] - w[0] == super::ALLOC_STRIDE)
        );
        assert_eq!(
            regions.last().map(|a| a + super::ALLOC_STRIDE),
            Some(super::API_STUB_BASE_32)
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
        // 0x1000 push 0; push 0; call 0x100a; 0x1009 ret; 0x100a ret 10h
        let code = [
            0x6a, 0x00, // push 0
            0x6a, 0x00, // push 0
            0xe8, 0x01, 0x00, 0x00, 0x00, // call +1 (0x100a)
            0xc3, // ret  (return lands here; rsp == base -> Returned)
            0xc2, 0x10, 0x00, // callee: ret 10h
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
            0x6a, 0x00, // push 0
            0x6a, 0x00, // push 0
            0xe8, 0x01, 0x00, 0x00, 0x00, // call +1 (0x100a)
            0xc3, // ret
            0xc2, 0x08, 0x00, // callee: ret 8
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
        // xor eax,eax; pushfq; cmp eax,1; popfq; je +6; mov eax,0xAA; ret;
        // mov eax,0xBB; ret
        let code = [
            0x31, 0xc0, // xor eax,eax  (ZF=1)
            0x9c, // pushfq
            0x83, 0xf8, 0x01, // cmp eax,1  (ZF=0)
            0x9d, // popfq  (ZF=1)
            0x74, 0x06, // je +6
            0xb8, 0xaa, 0x00, 0x00, 0x00, // mov eax,0xAA (branch not taken)
            0xc3, // ret
            0xb8, 0xbb, 0x00, 0x00, 0x00, // mov eax,0xBB (branch taken)
            0xc3, // ret
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
            0x31, 0xc0, // xor eax,eax  (ZF=1)
            0x9c, // pushfd
            0x83, 0xf8, 0x01, // cmp eax,1  (ZF=0)
            0x9d, // popfd  (ZF=1)
            0x74, 0x06, // je +6
            0xb8, 0xaa, 0x00, 0x00, 0x00, // mov eax,0xAA
            0xc3, // ret
            0xb8, 0xbb, 0x00, 0x00, 0x00, // mov eax,0xBB
            0xc3, // ret
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
            0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, // fld qword [rip+0xffa] = [0x2000]
            0xdd, 0x0d, 0x04, 0x10, 0x00, 0x00, // fisttp qword [rip+0x1004] = [0x2010]
            0xc3, // ret
        ];
        // 2.9 as an IEEE-754 double, little-endian.
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
            0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, // fld qword [0x2000] = 2.5
            0xdb, 0x1d, 0x1c, 0x10, 0x00, 0x00, // fistp dword [0x2028]
            0xdd, 0x05, 0xf6, 0x0f, 0x00, 0x00, // fld qword [0x2008] = 3.5
            0xdf, 0x1d, 0x16, 0x10, 0x00, 0x00, // fistp word [0x202e]
            0xdd, 0x05, 0xf2, 0x0f, 0x00, 0x00, // fld qword [0x2010] = 1e20
            0xdb, 0x1d, 0x12, 0x10, 0x00, 0x00, // fistp dword [0x2036]
            0xc3, // ret
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
            0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00, // fild dword [0x2004]
            0xde, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // fiadd word [0x2000]
            0xdb, 0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, // fistp dword [0x2008]
            0xdf, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // fild word [0x2000]
            0xdb, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00, // fistp dword [0x200c]
            0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, // mov eax,[0x2008]
            0x8b, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00, // mov ebx,[0x200c]
            0xc3, // ret
        ];
        // -2 as a word at 0x2000, 0x7fff after it, 10 as a dword at 0x2004.
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
            0xdb, 0x2c, 0x25, 0x00, 0x20, 0x00, 0x00, // fld tbyte [0x2000]
            0xdb, 0x3c, 0x25, 0x10, 0x20, 0x00, 0x00, // fstp tbyte [0x2010]
            0xdb, 0x2c, 0x25, 0x10, 0x20, 0x00, 0x00, // fld tbyte [0x2010]
            0xdd, 0x1c, 0x25, 0x20, 0x20, 0x00, 0x00, // fstp qword [0x2020]
            0x48, 0x8b, 0x04, 0x25, 0x20, 0x20, 0x00, 0x00, // mov rax,[0x2020]
            0xc3, // ret
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
        // mov rax,rsp; jmp rax
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
            0x8b, 0x04, 0x25, 0x10, 0x00, 0x00, 0x10, // mov eax,[0x10000010]
            0x8b, 0x1c, 0x25, 0x00, 0x08, 0x00, 0x10, // mov ebx,[0x10000800]
            0x8b, 0x0c, 0x25, 0x00, 0x14, 0x00, 0x10, // mov ecx,[0x10001400]
            0xc3, // ret
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
        emu.set_arg(0, 0x2800); // dst
        emu.set_arg(1, 0x2000); // src
        emu.set_arg(2, enc.len() as u64); // len
        emu.set_arg(3, 0x5a); // key
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
            0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // mov al,[0x2000]
            0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // mov al,[0x2000]
            0x8a, 0x04, 0x25, 0x00, 0x30, 0x00, 0x00, // mov al,[0x3000]
            0x8a, 0x04, 0x25, 0x00, 0x30, 0x00, 0x00, // mov al,[0x3000]
            0x8a, 0x04, 0x25, 0x00, 0x40, 0x00, 0x00, // mov al,[0x4000]
            0xc3, // ret
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
            0xb0, 0x80, // mov al, 0x80
            0x00, 0xc0, // add al, al   (-> 0x00, carry out of bit 7)
            0x10, 0xdb, // adc bl, bl   (-> 0 + 0 + carry = 1)
            0x88, 0x1c, 0x25, 0x00, 0x28, 0x00, 0x00, // mov [0x2800], bl
            0xc3, // ret
        ];
        let emu = returned(image(&code, &[]));
        assert_eq!(emu.peek(0x2800), Some(1), "8-bit carry was dropped");
    }

    /// A run that never returns stops at its step budget rather than looping
    /// forever.
    #[test]
    fn a_tight_loop_stops_at_the_budget() {
        // jmp $  (eb fe)
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
            0x48, 0xbc, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // mov rsp,0x100000000
            0xc3, // ret
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
            0xb9, 0xff, 0xff, 0xff, 0x03, // mov ecx,0x3ffffff
            0xbf, 0x00, 0x28, 0x00, 0x00, // mov edi,0x2800
            0x66, 0xf3, 0xab, // rep stosw
            0xc3, // ret
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
        let code = [
            0xbf, 0xff, 0xff, 0xff, 0xff, // mov edi,0xffffffff
            0xb0, 0x5a, // mov al,0x5a
            0xaa, // stosb
            0xaa, // stosb
            0xc3, // ret
        ];
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
            0xb9, 0x00, 0x10, 0x00, 0x00, // mov ecx,0x1000
            0xbf, 0x00, 0x28, 0x00, 0x00, // mov edi,0x2800
            0xf3, 0xaa, // rep stosb
            0xc3, // ret
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
            0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x50, // mov rax,[0x50000000]
            0x48, 0x8b, 0x1c, 0x25, 0x08, 0x00, 0x00, 0x50, // mov rbx,[0x50000008]
            0xc3, // ret
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
                // Any stop reason is fine; the point is that it returned.
                let _ = run.steps;
            }
        }
    }
}
