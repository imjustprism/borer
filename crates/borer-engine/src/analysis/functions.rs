//! Recursive-descent function discovery and basic-block recovery (x86/x64).
//!
//! Phase 1 walks from the entry point, the symbols and the function ranges
//! the file declares (exception table, sized symbols), following near
//! branches, treating near call targets as new functions, treating a jump
//! into a known function start as a tail call, stopping after calls to
//! functions that never return (a known-name list plus discovery: a call
//! immediately followed by another function's start), and resolving bounded
//! jump tables at indirect jumps. A jump table's own targets are case
//! blocks of the function that jumps to them: one that a data pointer or
//! padding seeded, and that nothing calls, is dropped at the end. Phase 2
//! seeds from data pointers (vtables,
//! callbacks) that point at executable code outside every function found so
//! far. Phase 3 seeds from the code addresses instructions take but never
//! call: a callback registered with `lea rcx, [thunk]; jmp atexit` is
//! reached no other way. Phases 4 and 5
//! seed from the byte after every run of padding - `int3` or `nop`, of any
//! length - and from the aligned start of every gap no function covers,
//! round after round until a round adds nothing. Phase 1's seeds are facts;
//! the rest are guesses, and a walk from a guess is kept only when it looks
//! like a function ([`Seed`]). The walk is fuel-capped so hostile input
//! cannot run away.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::thread::{Scope, ScopedJoinHandle};

use crate::isa::x86::{
    Code, ConditionCode, Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind,
    Register,
};

use super::switch_index::{TableBound, check_bound, index_bound, table_index};
use super::{
    Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, RefSite, dedup_sorted, is_imm,
    le_word, pointer_size, read_u32, read_u64, read_word,
};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::num::{from_usize, saturating_usize};
use crate::program::{Program, Section};

/// Smallest instruction budget for one full analysis pass.
const FUEL_MIN: u64 = 2_000_000;
/// Most instructions in an MSVC epilogue helper: the unlink, the pops, the
/// frame's release and the return.
const EPILOG_INSTRS_MAX: usize = 12;
/// Most instructions in the `/GS` cookie check: the compare, the two
/// tests of the x64 form, the rotates back and the jump to the report.
const COOKIE_CHECK_INSTRS_MAX: usize = 10;
/// Most instructions in a Rust panic entry: the frame, the arguments it
/// lays out for the message and the call that never returns.
const PANIC_INSTRS_MAX: usize = 24;
/// The messages Rust's panic entries format, each with the entry's name;
/// an entry loads its message's address, often a format template whose
/// first byte is the literal's length.
const PANIC_MESSAGES: [(&str, &str); 15] = [
    ("index out of bounds: the len is ", "panic_bounds_check"),
    ("attempt to add with overflow", "panic_const_add_overflow"),
    (
        "attempt to subtract with overflow",
        "panic_const_sub_overflow",
    ),
    (
        "attempt to multiply with overflow",
        "panic_const_mul_overflow",
    ),
    (
        "attempt to divide with overflow",
        "panic_const_div_overflow",
    ),
    (
        "attempt to calculate the remainder with overflow",
        "panic_const_rem_overflow",
    ),
    (
        "attempt to negate with overflow",
        "panic_const_neg_overflow",
    ),
    (
        "attempt to shift left with overflow",
        "panic_const_shl_overflow",
    ),
    (
        "attempt to shift right with overflow",
        "panic_const_shr_overflow",
    ),
    ("attempt to divide by zero", "panic_const_div_by_zero"),
    (
        "attempt to calculate the remainder with a divisor of zero",
        "panic_const_rem_by_zero",
    ),
    (
        "misaligned pointer dereference: address must be a multiple of ",
        "panic_misaligned_pointer_dereference",
    ),
    (
        "called `Option::unwrap()` on a `None` value",
        "option_unwrap_failed",
    ),
    ("range start index ", "slice_start_index_len_fail"),
    ("range end index ", "slice_end_index_len_fail"),
];
/// The 32-bit stack probe's opening, `push ecx; lea ecx,[esp+4]; sub
/// ecx,eax`: MSVC's `_chkstk` and `_alloca_probe` are that in every
/// runtime version.
const CHKSTK_X86: [u8; 7] = [0x51, 0x8d, 0x4c, 0x24, 0x04, 0x2b, 0xc8];
/// Budget per byte of executable, file-backed memory.
///
/// An instruction is at least one byte, shared tails are decoded once per
/// function reaching them, and every guess - the byte after each of sixty
/// thousand padding runs in a Rust binary - is walked whether or not it is
/// kept. Four per byte ran out on borer's own binary a third of the way
/// through its gap seeds.
const FUEL_PER_CODE_BYTE: u64 = 16;
/// Largest budget whatever the section table claims (a few seconds of decoding).
const FUEL_MAX: u64 = 200_000_000;
/// Farthest an `__except` filter or handler is walked from its function's
/// entry; one farther is only claimed ([`Walked::far_handlers`]).
///
/// PGO moves most handlers to the section's cold end, among other
/// functions' cold chunks and the tables a linker without `.rdata` keeps in
/// `.text`; a handler's last call there may never return and the walk run
/// on through a table as code, which then reads as covered and seeds
/// nothing: in 32-bit `KernelBase` a quarter of all functions were lost
/// that way.
const HANDLER_REACH: u64 = 0x1_0000;
/// Farthest past its call a `__finally` block lies when the trylevel
/// restored right before the call says that is what the call enters: the
/// block sits after the function's body, however long.
const FINALLY_CALL_REACH: u64 = 0x4000;
/// Farthest past its call a `__finally` block the call enters lies.
///
/// The compiler places the block right after the protected code. The
/// helpers that also open on their caller's frame, `__SEH_epilog4` and
/// `__EH_epilog3`, are told apart by their shape wherever they lie.
const FINALLY_REACH: u64 = 0x80;
/// Most instructions one guessed walk may decode before it is given up.
///
/// A guess that lands on data can decode its way into real code and on
/// through it, and nothing that walk decodes is kept when it is rejected,
/// so the next guess into the same data walks it all again. In 32-bit
/// `KernelBase`, which keeps its strings in `.text`, seventy guesses at
/// string literals decoded 275 thousand instructions each and spent the
/// whole budget, and 1,795 real functions were never reached. No function
/// a compiler emits comes near this many.
pub(super) const GUESS_WALK_MAX: u64 = 1 << 16;
/// Cap on recorded reference sites per target.
///
/// A hub such as the security cookie check is called from nearly every
/// function; past this many sites the list tells an agent nothing more,
/// while every other target keeps all of its references. A program-wide cap
/// once dropped most data references of a large binary, and with them the
/// strings a function could be named from.
const XREF_SITES_PER_TARGET: usize = 65_536;
/// Fewest entries of a batch worth walking across the cores.
const WAVE_MIN: usize = 64;
/// Most entries of a wave walked before their results are committed.
///
/// A wave's walks all read the starts as they stood when the wave began,
/// so a wave's results are the same whatever the batch they are walked
/// in; what the batch bounds is the memory the results of walks not yet
/// committed occupy. The gap round of a borer.exe whose headers named no
/// function walked 113,501 padding seeds in one wave, 86 million decoded
/// instructions held at once, nine gigabytes; a walk through code with no
/// declared starts runs to its cap, so a batch is a few walks per core.
const WAVE_BATCH: usize = 64;

/// Cap on the guessed seeds of one round: pointers, padding and gaps.
///
/// A Rust binary of twenty thousand functions carries as many padding
/// runs again for its funclets, and a round that stops collecting at
/// twenty thousand never reaches the end of the section. The fuel bounds
/// the walking; this only bounds the list.
pub(super) const SEEDS_MAX: usize = 250_000;
/// Longest chain of tail-call splits, and of code-seed rounds; every split
/// round only shrinks functions, and every seed round only adds them.
pub(super) const SPLIT_ROUNDS_MAX: usize = 8;
/// Largest jump table accepted (bound immediate).
pub(super) const TABLE_ENTRIES_MAX: u64 = 4096;
/// Farthest a case may lie from its jump in a table sized loosely.
///
/// A mask, or a check the index may not be tied to, only bounds the index,
/// so the table can end before it does, and the data after it reads as
/// offsets to anywhere: in one Rust binary, the entries past a ten-case
/// table's end pointed 7 MB away, into the middle of other functions'
/// instructions.
const LOOSE_REACH: u64 = 0x10_0000;
/// Most rounds of gap seeding; each round only ever adds functions.
pub(super) const GAP_ROUNDS_MAX: usize = 64;
/// Fewest functions a round of gap seeding must add for another to follow.
const ROUND_ADDS_MIN: usize = 4;

/// Where a walk's seed came from, for how much its result is trusted.
///
/// The entry point, a symbol, a declared range and a near-call target are
/// facts: something says code starts there. A pointer in data, the byte
/// after padding and the start of an uncovered gap are guesses, and a walk
/// from a guess is kept only when it looks like a function - it decoded
/// nothing that is not code, and it found a way out. That is the rule the
/// disassemblers with the best measured precision apply to their pattern
/// hits (FETCH's validation, for one), and without it every
/// padding byte followed by junk becomes a function of one instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Seed {
    /// Something says code starts here.
    Fact,
    /// A pointer in data names it: one `ret` is still a function here, since
    /// an empty virtual method is exactly that.
    Pointer,
    /// A relocated word inside executable code names it: a pointer too, but
    /// one kept among code, where an SEH scope table also names the
    /// `__except` blocks that run on their function's frame.
    Reloc,
    /// The byte after padding: a lone instruction is padding or a stray
    /// byte, unless it is a `jmp` thunk.
    Padding,
    /// The start of a gap nothing covers, with no padding to vouch for it:
    /// only a body of some length is believed.
    Gap,
}

/// Fewest instructions a walk from a bare gap must decode to be a function.
///
/// A syscall stub is six; anything shorter with no witness at all is more
/// often a stray byte that happens to decode than a function.
const GAP_INSTRS_MIN: usize = 4;

/// Bare names of functions that never return to their caller (C runtime,
/// C++ ABI, Windows API and MSVC runtime, Rust runtime, the kernel's bug
/// check, and the Go runtime's ways of not coming back).
const NORETURN_NAMES: &[&str] = &[
    "abort",
    "exit",
    "_exit",
    "_Exit",
    "quick_exit",
    "__assert_fail",
    "__stack_chk_fail",
    "longjmp",
    "_longjmp",
    "siglongjmp",
    "__longjmp_chk",
    "err",
    "errx",
    "verr",
    "verrx",
    "_Unwind_Resume",
    "__cxa_throw",
    "__cxa_rethrow",
    "__cxa_bad_cast",
    "__cxa_bad_typeid",
    "__cxa_call_unexpected",
    "__cxa_pure_virtual",
    "std::terminate",
    "std::unexpected",
    "ExitProcess",
    "ExitThread",
    "FreeLibraryAndExitThread",
    "RtlRaiseException",
    "_CxxThrowException",
    "__report_gsfailure",
    "__report_rangecheckfailure",
    "__report_securityfailure",
    "_invalid_parameter_noinfo_noreturn",
    "_invoke_watson",
    "__std_terminate",
    "_purecall",
    "_amsg_exit",
    "terminate",
    "rust_panic",
    "alloc::alloc::handle_alloc_error",
    "alloc::raw_vec::capacity_overflow",
    "std::process::abort",
    "std::process::exit",
    "KeBugCheck",
    "KeBugCheckEx",
    "runtime.gopanic",
    "runtime.throw",
    "runtime.fatal",
    "runtime.fatalthrow",
    "runtime.fatalpanic",
    "runtime.abort",
    "runtime.goexit1",
    "runtime.morestack",
];

/// Tells whether a (bare, demangled) function name denotes a function that never returns.
///
/// # Arguments
///
/// * `name` - The name as [`crate::search::demangled_name`] renders it, without a `dll!` prefix.
pub(super) fn is_noreturn_name(name: &str) -> bool {
    NORETURN_NAMES.contains(&name)
        || name.starts_with("core::panicking::")
        || name.starts_with("std::panicking::begin_panic")
        || name.starts_with("std::__throw_")
        || name.ends_with("::unwrap_failed")
}

/// What the walk remembers about one decoded instruction.
#[derive(Debug, Clone)]
struct InstrRec {
    /// Address of the following instruction.
    next: u64,
    /// Control-flow class from iced.
    flow: FlowControl,
    /// Near branch or call target, when the operand is a near branch.
    target: Option<u64>,
    /// Structural fingerprint of the instruction ([`fingerprint`]).
    print: u64,
    /// Shape of the instruction: mnemonic and operand kinds only.
    shape: u64,
}

/// What the records of a walk say about an address, kept as each record
/// is pushed so a question about them is one lookup rather than a scan.
///
/// The questions - which call a return address belongs to, which
/// instruction control comes from, the straight line before a call - were
/// each answered by scanning every record, at every call and every
/// indirect jump of the walk: a walk of forty thousand instructions
/// through code with no declared starts scanned a billion records, and a
/// batch of such walks took twelve seconds. Every answer here is the one
/// the scan gave over the same records.
#[derive(Default)]
struct Recorded {
    /// By the address an instruction falls through to.
    by_next: FxHashMap<u64, FallsInto>,
    /// By the address a near branch names: the last decoded conditional or
    /// unconditional branch to it.
    last_branch_to: FxHashMap<u64, u64>,
}

/// The records whose instruction falls through to one address.
#[derive(Debug, Clone, Copy)]
struct FallsInto {
    /// How many there are.
    count: usize,
    /// The first decoded, for when it is the only one.
    first: u64,
    /// The last decoded, with its control-flow class.
    last: (u64, FlowControl),
    /// The target of the last decoded near call among them.
    last_call: Option<u64>,
}

impl Recorded {
    /// Enters one record.
    ///
    /// # Arguments
    ///
    /// * `addr` - The instruction's address.
    /// * `rec` - Its record.
    fn push(&mut self, addr: u64, rec: &InstrRec) {
        let call = rec.target.filter(|_| rec.flow == FlowControl::Call);
        self.by_next
            .entry(rec.next)
            .and_modify(|f| {
                f.count += 1;
                f.last = (addr, rec.flow);
                f.last_call = call.or(f.last_call);
            })
            .or_insert(FallsInto {
                count: 1,
                first: addr,
                last: (addr, rec.flow),
                last_call: call,
            });
        if let Some(t) = rec.target
            && matches!(
                rec.flow,
                FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch
            )
        {
            self.last_branch_to.insert(t, addr);
        }
    }

    /// Finds the near call whose return address is `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The address of the instruction after the call.
    ///
    /// # Returns
    ///
    /// The target of the last decoded near call that falls through to `va`.
    fn call_before(&self, va: u64) -> Option<u64> {
        self.by_next.get(&va)?.last_call
    }

    /// Finds the instruction control comes from to reach `va`.
    ///
    /// The one that falls through to it, when the instruction before it in
    /// memory can fall through; otherwise the last one that jumps to it. A
    /// switch's bound check sits in the block before its dispatch, and when
    /// that block ends in a jump elsewhere - the default case, say - the
    /// dispatch is entered only by the conditional jump that tested the bound,
    /// and a chain that only ever steps back in memory never finds it.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// The predecessor's address, or `None` when the walk has none for `va`.
    fn pred_of(&self, va: u64) -> Option<u64> {
        if let Some(f) = self.by_next.get(&va)
            && matches!(
                f.last.1,
                FlowControl::Next
                    | FlowControl::ConditionalBranch
                    | FlowControl::Call
                    | FlowControl::IndirectCall
                    | FlowControl::XbeginXabortXend
            )
        {
            return Some(f.last.0);
        }
        self.last_branch_to.get(&va).copied()
    }

    /// The one instruction that falls through to `va`, when exactly one does.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn only_before(&self, va: u64) -> Option<u64> {
        self.by_next
            .get(&va)
            .filter(|f| f.count == 1)
            .map(|f| f.first)
    }
}

/// Mixes one value into a running FNV-1a hash.
///
/// # Arguments
///
/// * `h` - The hash so far.
/// * `v` - The value to fold in.
pub(super) fn mix(h: u64, v: u64) -> u64 {
    let mut h = h;
    for b in v.to_le_bytes() {
        h = (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Structural fingerprint of one instruction, everything but the addresses
/// it names, paired with its shape, the mnemonic and operand kinds alone.
///
/// The mnemonic, the operand kinds, the registers and the memory shape go
/// in as they are. Anything address-derived is left out, because two copies
/// of one function sit at different addresses and work on different data:
/// a rip-relative displacement, an immediate that lands inside the image,
/// and the branch target (which [`walk_function`] folds in separately, as
/// an offset when it stays inside the function). Copies that differ only in
/// the globals they touch therefore agree.
///
/// # Arguments
///
/// * `mapped` - The image's mapped range, to spot address immediates.
/// * `instr` - The instruction.
///
/// # Returns
///
/// `(fingerprint, shape)`.
fn fingerprint(mapped: &std::ops::Range<u64>, instr: &Instruction) -> (u64, u64) {
    let mut shape = mix(0xcbf2_9ce4_8422_2325, instr.mnemonic() as u64);
    shape = mix(shape, instr.op_count().into());
    let mut h = shape;
    for i in 0..instr.op_count() {
        let kind = instr.op_kind(i);
        shape = mix(shape, kind as u64);
        h = mix(h, kind as u64);
        match kind {
            OpKind::Register => h = mix(h, instr.op_register(i) as u64),
            OpKind::Memory => {
                h = mix(h, instr.memory_base() as u64);
                h = mix(h, instr.memory_index() as u64);
                h = mix(h, instr.memory_index_scale().into());
                if instr.memory_base() != Register::RIP {
                    h = mix(h, instr.memory_displacement64());
                }
            }
            OpKind::Immediate8
            | OpKind::Immediate8_2nd
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64 => {
                let imm = instr.immediate(i);
                if !mapped.contains(&imm) {
                    h = mix(h, imm);
                }
            }
            _ => {}
        }
    }
    (h, shape)
}

/// A data reference one instruction makes.
///
/// The kind is [`RefKind::Call`] or [`RefKind::Jmp`] when the instruction
/// branches through the referenced slot, which is how an import is called
/// on a PE (`call qword [rel <IAT slot>]`), [`RefKind::Index`] for the base
/// of a table an index register scales into, and [`RefKind::Data`] for a
/// plain load or an address-carrying immediate. Without the branch kinds
/// every direct call to an import reads as a data load and no import
/// appears in a caller's callee list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DataRef {
    /// The referenced address.
    target: u64,
    /// The referencing instruction's address.
    va: u64,
    /// How the instruction uses the target.
    kind: RefKind,
}

/// A jump table one indirect jump reads, resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedTable {
    /// The jump's address.
    site: u64,
    /// The case targets in table order.
    targets: Vec<u64>,
}

/// What a jump table read produced.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TableRead {
    /// The case targets in table order.
    targets: Vec<u64>,
    /// The byte index table that picked them, when one did.
    picker: Option<u64>,
}

/// A constant a call site puts in an argument register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ArgConst {
    /// The callee.
    callee: u64,
    /// The parameter's index among the argument registers.
    slot: u8,
    /// The constant passed.
    value: u64,
}

/// A class registered with its four-character code.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Registration {
    /// The class name as the registration spells it.
    class: String,
    /// The code that identifies the class on the wire.
    code: u32,
}

/// Everything one [`walk_function`] produced.
struct Walked {
    /// The function record (callers empty, name unset).
    func: Function,
    /// The decoded instructions in address order, for the cross-reference
    /// fold.
    recs: Vec<(u64, InstrRec)>,
    /// Data references seen.
    data_refs: Vec<DataRef>,
    /// Jump tables resolved.
    tables: Vec<ResolvedTable>,
    /// The sites among `tables` a byte index table expanded.
    indexed: BTreeSet<u64>,
    /// Constants this function's call sites put in argument registers.
    arg_consts: Vec<ArgConst>,
    /// Class names registered with their four-character code.
    registrations: Vec<Registration>,
    /// The `__chkstk` callee, when the `call X; sub rsp, rax` idiom appeared.
    chkstk: Option<u64>,
    /// The frame-building prologue helper (`__SEH_prolog4`, `__EH_prolog3`)
    /// the function calls before touching its stack, when it does.
    frame_helper: Option<u64>,
    /// Unconditional jump targets the walk followed into: should one prove
    /// to be a function start later, the jump was a tail call and the
    /// function is walked again.
    followed: BTreeSet<u64>,
    /// Call targets whose fall-through the walk followed: should one prove
    /// to never return, the function is walked again.
    followed_calls: BTreeSet<u64>,
    /// The walk decoded bytes that are not code: a fall-through or a jump
    /// landed on a byte that does not decode. Real from a real seed too (a
    /// jump table resolved wrong), but from a guessed seed it is the sign the
    /// guess was not a function.
    junk: bool,
    /// The walk reached a way out: a return, a tail jump, an indirect jump
    /// it could not resolve, or a call to something that never returns. A
    /// walk that only ever runs into padding has none, and is not a function.
    terminated: bool,
    /// A fall-through reached another function's start. Code does not run
    /// off the end of one function into the next, so this walk either
    /// decoded bytes that are not code or missed that its last call never
    /// returns; the start is not absorbed either way.
    fell_into_start: bool,
    /// The walk tore a frame down it never set up: a callee-saved `pop`, an
    /// `add rsp, N` or a `leave` came before any `push` or `sub rsp, N`. A
    /// function's epilogue undoes its own prologue, so this is the tail of
    /// a function that began earlier - the unreached rest of the one
    /// before, entered through a padding seed.
    unbalanced: bool,
    /// A guessed walk ran past [`GUESS_WALK_MAX`] instructions: longer than
    /// any function, so the guess decoded its way out of one.
    overlong: bool,
    /// The first instruction is one a function opens with: a callee-saved
    /// push, an argument homed to the stack, the frame taken, a hotpatch
    /// `mov edi, edi`, an `endbr`. The middle of a function opens with none
    /// of these, and the byte after padding is as often the unreached rest
    /// of the function before it - a case block, a landing pad - as a
    /// function; the disassemblers that measure best on padding hits ask
    /// for a prologue, and so does this.
    prologue: bool,
    /// The walk decoded an instruction no compiler emits: `add [rax], al`,
    /// what two zero bytes make, or a port read, a descriptor-table load,
    /// a BCD adjust. Data decodes into those and code does not, so a guess
    /// that reads one is data.
    zero_bytes: bool,
    /// The instruction that set `zero_bytes`, named for the seed trace.
    odd: Option<&'static str>,
    /// One of those is no byte add a compiler also writes: a compiler does
    /// write `add [ecx+2], al` for `*p += c`, but not two zero bytes' `add
    /// [eax], al` or any of the rest. A byte add alone does not outweigh a
    /// pointer or relocation naming a start.
    surely_data: bool,
    /// Call targets found to never return: the call is followed by another
    /// function's start, which no returning call can be.
    found_noreturn: BTreeSet<u64>,
    /// Call targets that may never return: the call is followed by `int3`
    /// padding, by a `ud2` trap, or by bytes that do not decode, which a
    /// returning call in an unreachable path can be as well.
    found_noreturn_weak: BTreeSet<u64>,
    /// `__except` filters and handlers this function's scope table names
    /// that lie beyond [`HANDLER_REACH`]: its code, not walked, and never a
    /// function of their own.
    far_handlers: BTreeSet<u64>,
    /// The `__except` filters and handlers the scope table names near the
    /// entry, walked as the function's own code.
    near_handlers: BTreeSet<u64>,
    /// The entry's own bytes are not code: they do not decode, sit on a
    /// relocation, or decode into an instruction no compiler emits. No
    /// witness outweighs that, a call or an export included.
    bad_entry: bool,
    /// The entry opens by undoing a frame (`pop`, `leave`): a label inside
    /// a function, past its body.
    undoes_frame: bool,
    /// The entry is `jmp [slot]` through a slot in a data section: a thunk
    /// through a pointer, one instruction long and a function.
    slot_thunk: bool,
}

/// One walker's own state: what a walk writes and nothing else reads.
struct Worker<'a> {
    /// Decoders over the sections the walks touch; they hold the image.
    cursors: Cursors<'a>,
    /// Addresses the current walk has decoded; empty between walks.
    visited: AddrSet,
    /// Remaining instruction budget.
    fuel: u64,
}

impl<'a> Worker<'a> {
    /// A walker over the program with a budget of its own.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `bitness` - Decoder bitness.
    /// * `fuel` - The budget.
    fn new(program: &'a Program, bitness: u32, fuel: u64) -> Self {
        Worker {
            cursors: Cursors::new(program, bitness),
            visited: AddrSet::new(program),
            fuel,
        }
    }
}

/// Mutable state of one discovery pass over a work queue of function entries.
struct WalkState<'a> {
    /// The pass's own walker, whose budget is the budget across all
    /// functions.
    worker: Worker<'a>,
    /// Function entries still to walk.
    queue: Vec<u64>,
    /// Function entries already walked.
    done: AddrSet,
    /// Functions found so far, in discovery order.
    functions: Vec<Function>,
    /// Target address to its reference sites.
    xrefs: BTreeMap<u64, Vec<RefSite>>,
    /// Indirect-jump site to resolved targets.
    jump_tables: BTreeMap<u64, Vec<u64>>,
    /// Sites whose table a byte index table expanded.
    indexed_tables: BTreeSet<u64>,
    /// Callee to parameter index to the constants callers pass there.
    param_values: BTreeMap<u64, BTreeMap<u8, BTreeSet<u64>>>,
    /// Class name to the four-character code it registered with.
    class_ids: BTreeMap<String, u32>,
    /// Callees followed by `sub rsp, rax`: the stack-probe helper.
    chkstk: BTreeSet<u64>,
    /// Callees that build their caller's exception frame: the MSVC prologue
    /// helpers, recognized by their first two instructions.
    frame_helpers: BTreeSet<u64>,
    /// Authoritative function starts: the header and symbol seeds plus every
    /// near-call target seen so far. A `jmp` into one is a tail call.
    starts: AddrSet,
    /// Per walked function, the jump targets its walk followed into.
    followed: BTreeMap<u64, BTreeSet<u64>>,
    /// Per walked function, the call targets whose fall-through it followed.
    followed_calls: BTreeMap<u64, BTreeSet<u64>>,
    /// Every call target some walk followed the fall-through of: evidence
    /// that it returns, which no single site can outweigh.
    followed_anywhere: BTreeSet<u64>,
    /// Call targets some walk found padding, a trap or undecodable bytes
    /// right after, with how many sites said so; promoted to
    /// [`Self::noreturn`] between rounds when no walk ever followed one.
    learned_noreturn: BTreeMap<u64, usize>,
    /// Functions that never return: named ones from the symbol table, every
    /// callee some walk found a function start right after, and every
    /// learned callee no walk ever followed, each unless its own code is
    /// seen to return.
    noreturn: Arc<AddrSet>,
    /// Callees some walk found a function start right after, held until
    /// the round ends and checked against their own code: the call site
    /// never returns, and the callee may not either, or may be a dispatcher
    /// that returns everywhere else ([`WalkState::can_return`]).
    claimed_noreturn: BTreeSet<u64>,
    /// `__except` filters and handlers some function's scope table claims:
    /// the function's own code, never a seed.
    handlers: FxHashSet<u64>,
    /// Where the loader patches an absolute address: inside an
    /// instruction's displacement or immediate, never where one starts.
    reloc_sites: Arc<AddrSet>,
    /// Whether the image relocates anything at all.
    relocatable: bool,
    /// Entries accepted from a guessed seed, in any batch so far.
    accepted_guesses: FxHashSet<u64>,
    /// Code a function owns that none of its instructions reaches, by the
    /// function's entry: where the runtime resumes it after a catch or an
    /// `__except` ([`crate::unwind::continuations`], [`catch_continuations`]),
    /// walked with it after its own code.
    extra_roots: Arc<FxHashMap<u64, Vec<u64>>>,
    /// IAT and GOT slots of imports that never return.
    noreturn_slots: Arc<FxHashSet<u64>>,
    /// IAT and GOT slots of every import: `jmp [slot]` through one is the
    /// linker's thunk for calls to that import.
    import_slots: FxHashSet<u64>,
    /// How much the seeds now being walked are trusted.
    seed: Seed,
    /// The entries of the current guess list. What an accepted guess calls
    /// is reached by a call and is a fact, and a split round's re-walk of
    /// an accepted function is a fact too; only the guesses themselves are
    /// held to the guess rules.
    guessed: Arc<FxHashSet<u64>>,
    /// Guesses that were walked and rejected. Kept apart from `done` so a
    /// fact about the same address - a call to it found later - still walks
    /// it; a rejected guess is only a guess not worth making twice.
    rejected: AddrSet,
}

impl<'a> WalkState<'a> {
    /// Walks `seeds` as guesses of the given kind, then goes back to facts.
    ///
    /// # Arguments
    ///
    /// * `seeds` - The entries to try.
    /// * `kind` - What made them candidates.
    ///
    /// # Returns
    ///
    /// `true` when the fuel ran out first.
    fn run_guesses(&mut self, seeds: Vec<u64>, kind: Seed) -> bool {
        if seeds.is_empty() {
            return false;
        }
        self.guessed = Arc::new(seeds.iter().copied().collect());
        self.queue = seeds;
        self.seed = kind;
        let incomplete = self.run();
        self.seed = Seed::Fact;
        Arc::make_mut(&mut self.guessed).clear();
        incomplete
    }

    /// Says why a walk from a guessed seed is not a function, when it is not.
    ///
    /// # Arguments
    ///
    /// * `w` - The walk's result.
    ///
    /// # Returns
    ///
    /// The reason, for the seed trace, or `None` when the walk is accepted.
    fn why_rejected(&self, w: &Walked) -> Option<&'static str> {
        if w.bad_entry {
            return Some("opens with bytes that are not code");
        }
        if self.seed == Seed::Fact || !self.guessed.contains(&w.func.entry) {
            return None;
        }
        if w.overlong {
            return Some("ran longer than any function");
        }
        // INVARIANT: a funclet a data pointer names (a C++ unwind action in
        // `FuncInfo`) runs on its parent's frame and is one; a guess from
        // code or its gaps that does is the rest of a function.
        if self.seed != Seed::Pointer && self.on_callers_frame(w.func.entry) {
            return Some("runs on another function's frame");
        }
        if w.junk {
            return Some("decoded bytes that are not code");
        }
        if w.undoes_frame {
            return Some("opens by undoing a frame");
        }
        // INVARIANT: a byte add alone is outweighed by a pointer or a
        // relocation that names a start opening the way functions open; a
        // case label or a table the same relocations name opens like none.
        let named = matches!(self.seed, Seed::Pointer | Seed::Reloc) && w.prologue;
        if w.zero_bytes && (w.surely_data || !named) {
            return Some(w.odd.unwrap_or("decoded an instruction no compiler emits"));
        }
        // INVARIANT: a pointer in data is a witness on its own, and what it
        // names may loop for ever or end in a call to something unknown that
        // never returns; only reading data disqualifies it. A padding or gap
        // seed has no such witness and must look like a function throughout.
        if matches!(self.seed, Seed::Pointer | Seed::Reloc) {
            return None;
        }
        if !w.terminated {
            return Some("found no way out");
        }
        if w.fell_into_start {
            return Some("fell through into another function");
        }
        let n = w.func.instr_count;
        let thunk = w
            .recs
            .first()
            .is_some_and(|(_, r)| r.flow == FlowControl::UnconditionalBranch && r.target.is_some());
        if thunk || w.slot_thunk || self.import_thunk(w.func.entry) {
            return None;
        }
        match self.seed {
            Seed::Fact | Seed::Pointer | Seed::Reloc => None,
            Seed::Padding if n < 2 => Some("one instruction after padding"),
            Seed::Padding if w.unbalanced => Some("tears down a frame it never set up"),
            Seed::Padding => None,
            Seed::Gap if n < GAP_INSTRS_MIN => Some("too short for a bare gap"),
            Seed::Gap if w.unbalanced => Some("tears down a frame it never set up"),
            Seed::Gap if !w.prologue => Some("opens like no function does"),
            Seed::Gap => None,
        }
    }

    /// Whether the code at `va` opens by addressing memory through the frame
    /// pointer, which on entry still holds the caller's frame.
    ///
    /// A function takes its own frame before it reads one; code that opens
    /// with `mov esi, [ebp-0x1c]` runs on a frame some function already
    /// set up: an `__except` body, a `__finally` block, a cold chunk. A
    /// guess at one, from the scope table's relocated words or the padding
    /// before it, is not a function.
    ///
    /// # Arguments
    ///
    /// * `va` - The guessed entry.
    fn on_callers_frame(&self, va: u64) -> bool {
        opens_on_frame(self.worker.cursors.program, self.worker.cursors.bitness, va)
    }

    /// Whether a guessed entry is worth a walk: not walked, not rejected,
    /// not a handler some function's scope table claims, and plausible as
    /// an entry ([`plausible_entry`]).
    ///
    /// # Arguments
    ///
    /// * `va` - The guessed entry.
    fn fresh(&self, va: u64) -> bool {
        !self.done.contains(va)
            && !self.rejected.contains(va)
            && !self.handlers.contains(&va)
            && plausible_entry(self.worker.cursors.program, self.worker.cursors.bitness, va)
    }

    /// What every walk of the current wave reads besides the starts,
    /// shared rather than borrowed, so the wave's threads read it while the
    /// pass commits their walks; nothing a commit writes is in it.
    fn shared(&self) -> Shared {
        Shared {
            noreturn: Arc::clone(&self.noreturn),
            noreturn_slots: Arc::clone(&self.noreturn_slots),
            extra_roots: Arc::clone(&self.extra_roots),
            reloc_sites: self.relocatable.then(|| Arc::clone(&self.reloc_sites)),
            guessed: Arc::clone(&self.guessed),
        }
    }

    /// Whether `va` is the linker's thunk for an import, `jmp [slot]`
    /// through an import slot (after an optional `endbr`).
    ///
    /// It is one instruction between padding, which a padding guess must
    /// otherwise outgrow, and a thunk nothing in the program calls is still
    /// there: user32 keeps ninety-eight `jmp [__imp_NtUser...]` thunks its
    /// own code never calls.
    ///
    /// # Arguments
    ///
    /// * `va` - The guessed entry.
    fn import_thunk(&self, va: u64) -> bool {
        let program = self.worker.cursors.program;
        let bitness = self.worker.cursors.bitness;
        let Some(mut first) = decode_at(program, bitness, va) else {
            return false;
        };
        if matches!(first.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
            let Some(next) = decode_at(program, bitness, first.next_ip()) else {
                return false;
            };
            first = next;
        }
        slot_jump(&first).is_some_and(|slot| self.import_slots.contains(&slot))
    }

    /// Walks every queued entry, then re-walks functions whose walk followed
    /// a jump into an address that has since proven to be a function start
    /// (the jump was a tail call and the callee was absorbed) or followed the
    /// fall-through of a call whose target has since proven to never return,
    /// until no function needs splitting.
    ///
    /// # Returns
    ///
    /// `true` when the fuel ran out before the queue emptied.
    fn run(&mut self) -> bool {
        let mut incomplete = false;
        for round in 0..SPLIT_ROUNDS_MAX {
            incomplete |= self.drain();
            self.promote_noreturn();
            if round + 1 == SPLIT_ROUNDS_MAX {
                break;
            }
            let split: Vec<u64> = self
                .functions
                .iter()
                .map(|f| f.entry)
                .filter(|e| {
                    self.followed
                        .get(e)
                        .is_some_and(|ts| ts.iter().any(|&t| self.starts.contains(t)))
                        || self
                            .followed_calls
                            .get(e)
                            .is_some_and(|ts| ts.iter().any(|&t| self.noreturn.contains(t)))
                })
                .collect();
            if split.is_empty() {
                break;
            }
            self.forget(&split);
            self.queue = split;
        }
        incomplete
    }

    /// Makes the noreturn candidates known, so later walks end at their
    /// calls: every callee a function start was found right after, and the
    /// weakly learned ones no walk ever followed, each unless its own code
    /// can be seen to return ([`WalkState::can_return`]).
    ///
    /// A function start right after a call proves the call site never
    /// returns, not always the callee: a call through Control Flow Guard's
    /// dispatcher to a function pointer that never returns is followed by
    /// the next function, and taking that as the dispatcher's own nature
    /// ended combase's functions at their first indirect call, thousands of
    /// them. Padding, a trap or undecodable bytes after one call site is
    /// weaker still:
    /// `call memcpy; ud2` closes an unreachable path after a call that
    /// returns everywhere else, and a rule that took it condemned every
    /// caller of `memcpy` to end there, the rest of each such function then
    /// found from padding seeds, one of them inside an instruction. A callee
    /// whose fall-through some walk followed returns; the rest, seen only
    /// ever followed by padding, do not.
    fn promote_noreturn(&mut self) {
        let returning: FxHashSet<u64> = self
            .functions
            .iter()
            .filter(|f| f.blocks.iter().any(|b| b.term == BlockTerm::Ret))
            .map(|f| f.entry)
            .collect();
        let claimed: Vec<u64> = std::mem::take(&mut self.claimed_noreturn)
            .into_iter()
            .filter(|&t| !self.noreturn.contains(t) && !self.can_return(t, &returning))
            .collect();
        Arc::make_mut(&mut self.noreturn).extend(claimed);
        let promoted: Vec<u64> = self
            .learned_noreturn
            .keys()
            .copied()
            .filter(|&t| {
                !self.followed_anywhere.contains(&t)
                    && !self.noreturn.contains(t)
                    && !self.can_return(t, &returning)
            })
            .collect();
        Arc::make_mut(&mut self.noreturn).extend(promoted);
    }

    /// Whether the code a call reaches can be seen to return.
    ///
    /// It returns when the function walked from it, or from the end of the
    /// thunk chain it opens with, has a `ret`, or when the chain ends in an
    /// indirect jump that is not through a no-return import's slot: a
    /// dispatcher (`jmp rax`, a patched slot) returns as whatever it was
    /// handed does. What cannot be seen, a callee not walked or one whose
    /// every way out is another call, is left to the evidence.
    ///
    /// # Arguments
    ///
    /// * `t` - The callee.
    /// * `returning` - Entries of walked functions with a `ret`.
    fn can_return(&self, t: u64, returning: &FxHashSet<u64>) -> bool {
        /// Most jumps followed through a thunk chain.
        const CHAIN_MAX: usize = 4;
        let program = self.worker.cursors.program;
        let bitness = self.worker.cursors.bitness;
        let mut va = t;
        for _ in 0..CHAIN_MAX {
            if returning.contains(&va) {
                return true;
            }
            let Some(i) = decode_at(program, bitness, va) else {
                return false;
            };
            match i.flow_control() {
                FlowControl::UnconditionalBranch if i.op0_kind() != OpKind::Memory => {
                    va = i.near_branch_target();
                    if self.noreturn.contains(va) {
                        return false;
                    }
                }
                FlowControl::IndirectBranch => {
                    return slot_jump(&i).is_none_or(|slot| !self.noreturn_slots.contains(&slot));
                }
                _ => return false,
            }
        }
        false
    }

    /// Walks the executable addresses instructions mention that no block
    /// covers, until a round finds nothing new.
    ///
    /// A callback is stored by an immediate and never called, so the only
    /// evidence of it is the instruction that stores it, and that instruction
    /// may belong to a function found late, by a pointer or by padding: each
    /// round can uncover references the next round seeds from, and the rounds
    /// stop when one adds nothing, or at [`SPLIT_ROUNDS_MAX`] rounds.
    ///
    /// # Returns
    ///
    /// `true` when the fuel ran out before a round's queue emptied.
    fn run_code_seeds(&mut self) -> bool {
        let program = self.worker.cursors.program;
        let mut incomplete = false;
        for _ in 0..SPLIT_ROUNDS_MAX {
            let covered = Covered::new(&self.functions);
            let seeds: Vec<u64> = self
                .xrefs
                .iter()
                .filter(|(_, sites)| sites.iter().any(|s| s.kind != RefKind::Index))
                .map(|(&t, _)| t)
                .filter(|&t| {
                    super::is_executable_va(program, t) && !covered.contains(t) && self.fresh(t)
                })
                .take(SEEDS_MAX)
                .collect();
            if seeds.is_empty() {
                break;
            }
            incomplete |= self.run_guesses(seeds, Seed::Pointer);
        }
        incomplete
    }

    /// Drops functions and everything their walks recorded so they can be walked again.
    ///
    /// # Arguments
    ///
    /// * `entries` - Entries of the functions to drop.
    fn forget(&mut self, entries: &[u64]) {
        let set: FxHashSet<u64> = entries.iter().copied().collect();
        self.functions.retain(|f| !set.contains(&f.entry));
        for e in &set {
            self.done.remove(*e);
            self.followed.remove(e);
            self.followed_calls.remove(e);
            self.accepted_guesses.remove(e);
        }
        for sites in self.xrefs.values_mut() {
            sites.retain(|s| !s.from_entry.is_some_and(|f| set.contains(&f)));
        }
        self.xrefs.retain(|_, sites| !sites.is_empty());
    }

    /// Walks every queued entry once, queueing the callees it finds.
    ///
    /// # Returns
    ///
    /// `true` when the fuel ran out before the queue emptied.
    fn drain(&mut self) -> bool {
        let mut incomplete = false;
        loop {
            let mut wave: Vec<u64> = Vec::new();
            let mut seen: FxHashSet<u64> = FxHashSet::default();
            while let Some(entry) = self.queue.pop() {
                if self.done.contains(entry) {
                    if trace_seeds() && self.guessed.contains(&entry) {
                        eprintln!("seed {entry:#x} already walked");
                    }
                    continue;
                }
                if seen.insert(entry) {
                    wave.push(entry);
                }
            }
            if wave.is_empty() {
                break;
            }
            if self.worker.fuel == 0 {
                incomplete = true;
                break;
            }
            // INVARIANT: every walk of the wave reads the starts as they
            // stood when the wave began, whichever batch it is in; the
            // commits of an earlier batch change the starts, not the walks.
            let starts = self.starts.clone();
            let shared = self.shared();
            let known = shared.known(&starts);
            let program = self.worker.cursors.program;
            let bitness = self.worker.cursors.bitness;
            let threads = if wave.len() < WAVE_MIN {
                1
            } else {
                std::thread::available_parallelism()
                    .map_or(1, std::num::NonZeroUsize::get)
                    .min(WAVE_BATCH)
            };
            std::thread::scope(|scope| {
                let lanes = Lanes::start(scope, threads, program, bitness, &known);
                for batch in wave.chunks(WAVE_BATCH) {
                    let walked = self.walk_batch(batch, &known, &lanes);
                    for (&entry, w) in batch.iter().zip(walked) {
                        self.commit(entry, w);
                    }
                }
                lanes.stop();
            });
        }
        incomplete
    }

    /// Walks one batch of a wave, across the wave's lanes when the batch is
    /// large.
    ///
    /// Each walk reads only the program and the starts and noreturn sets as
    /// they stood when the wave began, with its own decoders and scratch
    /// set; what one walk would have told the next (a callee that is a
    /// start, a noreturn callee) the split rounds of [`WalkState::run`]
    /// reconcile, as they do for the sequential order. Every lane spends
    /// from the budget left when the batch began and the total spent is
    /// charged after; a walk a lane did not return is walked again here.
    ///
    /// # Arguments
    ///
    /// * `batch` - Entries to walk, in commit order: one batch of the wave.
    /// * `known` - What the wave's walks read.
    /// * `lanes` - The wave's walker threads.
    ///
    /// # Returns
    ///
    /// One result per entry, in the batch's order.
    fn walk_batch(&mut self, batch: &[u64], known: &Known<'_>, lanes: &Lanes<'_>) -> Vec<Walked> {
        let threads = lanes.lanes.len().min(batch.len());
        if batch.len() < WAVE_MIN || threads <= 1 {
            return batch
                .iter()
                .map(|&entry| walk_capped(&mut self.worker, entry, known))
                .collect();
        }
        let (slots, spent) = lanes.walk(batch, threads, self.worker.fuel);
        self.worker.fuel = self.worker.fuel.saturating_sub(spent);
        slots
            .into_iter()
            .zip(batch)
            .map(|(w, &entry)| w.unwrap_or_else(|| walk_capped(&mut self.worker, entry, known)))
            .collect()
    }

    /// Records one walked function: its references, tables, callees as new
    /// starts and work, and the function itself.
    ///
    /// A walk the guess rules reject is not a function, so nothing it
    /// appeared to call is a start either; a later fact may still walk the
    /// entry, so it is not done. A guess at one of the function's own
    /// handlers, made before the function was found, is evicted: the
    /// handler is this function's code.
    ///
    /// A conditional branch is a reference when its target is not one of
    /// the function's own instructions: `jne other` is a conditional tail
    /// call, and the function it enters listed no reference from it.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry.
    /// * `walked` - What its walk produced.
    fn commit(&mut self, entry: u64, walked: Walked) {
        if let Some(why) = self.why_rejected(&walked) {
            if trace_seeds() {
                eprintln!("seed {entry:#x} rejected: {why}");
            }
            self.rejected.insert(entry);
            return;
        }
        if self.guessed.contains(&entry) {
            self.accepted_guesses.insert(entry);
        }
        if trace_seeds() {
            let how = if self.guessed.contains(&entry) {
                format!("accepted as {:?}", self.seed)
            } else {
                "walked as a fact".to_owned()
            };
            eprintln!(
                "seed {entry:#x} {how} ({} instructions)",
                walked.func.instr_count
            );
        }
        let Walked {
            func,
            recs,
            data_refs,
            tables,
            indexed,
            arg_consts,
            registrations,
            chkstk,
            frame_helper,
            followed,
            followed_calls,
            junk: _,
            overlong: _,
            terminated: _,
            fell_into_start: _,
            zero_bytes: _,
            odd: _,
            surely_data: _,
            prologue: _,
            unbalanced: _,
            found_noreturn,
            found_noreturn_weak,
            far_handlers,
            near_handlers,
            bad_entry: _,
            undoes_frame: _,
            slot_thunk: _,
        } = walked;
        self.handlers.extend(far_handlers);
        let evict: Vec<u64> = near_handlers
            .iter()
            .copied()
            .filter(|r| *r != entry && self.accepted_guesses.contains(r) && self.done.contains(*r))
            .collect();
        if !evict.is_empty() {
            if trace_seeds() {
                for r in &evict {
                    eprintln!("seed {r:#x} evicted: a handler of {entry:#x}");
                }
            }
            self.forget(&evict);
            for r in &evict {
                self.rejected.insert(*r);
                self.starts.remove(*r);
            }
        }
        self.handlers.extend(near_handlers);
        self.done.insert(entry);
        self.followed.insert(entry, followed);
        self.followed_anywhere
            .extend(followed_calls.iter().copied());
        self.followed_calls.insert(entry, followed_calls);
        self.claimed_noreturn.extend(found_noreturn);
        for t in found_noreturn_weak {
            *self.learned_noreturn.entry(t).or_default() += 1;
        }
        if let Some(c) = chkstk {
            self.chkstk.insert(c);
        }
        if let Some(h) = frame_helper {
            self.frame_helpers.insert(h);
        }

        let from = Some(entry);
        for (va, rec) in &recs {
            let Some(target) = rec.target else { continue };
            let kind = match rec.flow {
                FlowControl::Call => RefKind::Call,
                FlowControl::UnconditionalBranch => RefKind::Jmp,
                FlowControl::ConditionalBranch
                    if recs.binary_search_by_key(&target, |(a, _)| *a).is_err() =>
                {
                    RefKind::Jmp
                }
                FlowControl::ConditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::IndirectCall
                | FlowControl::Next
                | FlowControl::Return
                | FlowControl::Interrupt
                | FlowControl::Exception
                | FlowControl::XbeginXabortXend => continue,
            };
            push_site(&mut self.xrefs, target, *va, kind, from);
        }
        for r in data_refs {
            push_site(&mut self.xrefs, r.target, r.va, r.kind, from);
        }
        for t in tables {
            self.jump_tables.insert(t.site, t.targets);
        }
        self.indexed_tables.extend(indexed);
        self.class_ids
            .extend(registrations.into_iter().map(|r| (r.class, r.code)));
        for c in arg_consts {
            let slots = self.param_values.entry(c.callee).or_default();
            let seen = slots.entry(c.slot).or_default();
            if seen.len() <= PARAM_VALUES_MAX {
                seen.insert(c.value);
            }
        }

        self.starts.extend(func.callees.iter().copied());
        self.queue.extend(func.callees.iter().copied());
        self.functions.push(func);
    }
}

/// Sizes the instruction budget for one analysis pass from the code size.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// [`FUEL_PER_CODE_BYTE`] per executable file byte, clamped to
/// [`FUEL_MIN`]..=[`FUEL_MAX`].
pub(super) fn fuel_for(program: &Program) -> u64 {
    let code: u64 = program
        .sections
        .iter()
        .filter(|s| s.executable)
        .map(|s| s.file_size)
        .sum();
    code.saturating_mul(FUEL_PER_CODE_BYTE)
        .clamp(FUEL_MIN, FUEL_MAX)
}

/// Runs the four discovery phases and assembles the [`Analysis`].
///
/// Phase 1 walks the entry point, the symbols and the declared function
/// ranges. Phase 2 walks data pointers into executable code, skipping
/// anything inside an already-found function (jump-table case labels would
/// pollute the result otherwise). Phase 3 walks the executable addresses
/// instructions take without calling, which is the only evidence a
/// registered callback's thunk leaves. Phase 4
/// walks the byte after every run of two or more `int3` (`0xcc`) padding
/// bytes that lies in executable memory and no block covers, which fills
/// the gaps nothing else reaches; asking whether a block covers it rather
/// than whether some function's range reaches over it finds the thunks the
/// linker dropped between two blocks of another function. Afterwards functions are sorted by
/// entry, callers and names are filled in, `__chkstk` is named from its
/// `call X; sub rsp, rax` idiom, and reference sites are sorted by address.
///
/// Phases 4 and 5 look only at executable bytes no block covers, and both
/// are guesses the walk gate validates. Padding is any run of `int3` or of
/// the `nop` forms a linker aligns with, a single `int3` included, since a
/// function that happens to end one byte short of its alignment has
/// exactly one, and a sixteenth of them do. A gap that opens with code
/// rather than padding is seeded at its first byte: the function before it
/// ended flush against it, or nothing references it at all (a syscall
/// stub, a cold path). Each accepted function shrinks its gap, so the next
/// round finds what follows it, until a round finds nothing; a round that
/// adds almost nothing is not worth what the next would cost, since every
/// round rescans every gap. A file that declares its functions (unwind
/// tables, symbols) has said where they are, and a gap it left is not one:
/// what is there is the unreached tail of a function, a table, or nothing.
/// Only a file that declared little is worth guessing at from its gaps;
/// padding is a witness on its own and is followed either way. Gaps are
/// taken between blocks, not only between functions: the linker drops a
/// thunk between two blocks of another function now and then, and `int3`
/// on both sides of it is how it shows. A lone `int3` inside a function's
/// span is as often the padding before the next function as a trap the
/// code itself has, since a span reaches over its neighbours whenever a
/// jump was followed somewhere far; what follows a trap is the unreached
/// rest of a function, and the gate is what tells that from a function.
/// With no padding to vouch for it, the alignment a compiler gives every
/// function is the only witness a bare gap start has; an unaligned one is
/// far more often the unreached tail of the function before it.
///
/// Under the older C++ runtime a catch funclet returns where its parent
/// goes on (`lea rax, [label]; ret`), code of the parent that no
/// instruction of the parent reaches: each parent is walked again with the
/// labels its funclets return. A walk that decoded no instruction is not a
/// function (a pointer or padding seed that landed on data or on a byte
/// that does not decode, real in a decrypted image, where such seeds are
/// many) and is dropped so the list holds only bodies; a thunk is one
/// instruction, so this keeps thunks.
///
/// # Arguments
///
/// * `program` - The loaded image, x86 or x86-64.
/// * `bitness` - The decoder bitness, `32` or `64`.
///
/// # Returns
///
/// The analysis, indexed ([`Analysis::finish_index`]).
pub(crate) fn discover(program: &Program, bitness: u32) -> Analysis {
    let mut phases = crate::timing::Phases::new();
    let mut analysis = Analysis::default();

    let seeds = super::seeds(program);
    let named_noreturn = |s: &&crate::program::Symbol| {
        s.addr != 0 && is_noreturn_name(super::bare_name(&crate::search::demangled_name(&s.name)))
    };
    let mut noreturn = AddrSet::new(program);
    noreturn.extend(
        program
            .symbols
            .iter()
            .filter(|s| s.kind != crate::program::SymbolKind::Import)
            .filter(named_noreturn)
            .map(|s| s.addr),
    );
    let noreturn_slots: FxHashSet<u64> = program
        .symbols
        .iter()
        .filter(|s| s.kind == crate::program::SymbolKind::Import)
        .filter(named_noreturn)
        .map(|s| s.addr)
        .collect();
    let import_slots: FxHashSet<u64> = program
        .symbols
        .iter()
        .filter(|s| s.kind == crate::program::SymbolKind::Import)
        .map(|s| s.addr)
        .collect();
    let mut starts = AddrSet::new(program);
    starts.extend(seeds.iter().copied());
    // INVARIANT: a relocatable image relocates every pointer it holds, so a
    // word without a relocation is no pointer, and a relocation is never
    // where an instruction starts.
    let relocated = program.relocated_words();
    let relocated_all: FxHashSet<u64> = relocated.iter().copied().collect();
    let mut reloc_sites = AddrSet::new(program);
    for &va in &relocated {
        reloc_sites.insert(va);
    }
    let mut extra_roots: FxHashMap<u64, Vec<u64>> = FxHashMap::default();
    for (parent, at) in crate::unwind::continuations(program) {
        extra_roots.entry(parent).or_default().push(at);
    }
    // INVARIANT: an Itanium landing pad is a label of its function that no
    // instruction of it reaches - only the unwinder jumps there - so each
    // one is walked as the parent's own code, the way an `__except` body is.
    let throw_sites = crate::lsda::throw_sites(program);
    for (parent, sites) in &throw_sites {
        for at in sites.iter().filter_map(|s| s.landing_pad) {
            extra_roots.entry(*parent).or_default().push(at);
        }
    }
    let mut st = WalkState {
        worker: Worker::new(program, bitness, fuel_for(program)),
        starts,
        queue: seeds,
        done: AddrSet::new(program),
        functions: Vec::new(),
        xrefs: BTreeMap::new(),
        jump_tables: BTreeMap::new(),
        indexed_tables: BTreeSet::new(),
        param_values: BTreeMap::new(),
        class_ids: BTreeMap::new(),
        chkstk: BTreeSet::new(),
        frame_helpers: BTreeSet::new(),
        followed: BTreeMap::new(),
        followed_calls: BTreeMap::new(),
        followed_anywhere: BTreeSet::new(),
        learned_noreturn: BTreeMap::new(),
        noreturn: Arc::new(noreturn),
        noreturn_slots: Arc::new(noreturn_slots),
        import_slots,
        claimed_noreturn: BTreeSet::new(),
        handlers: FxHashSet::default(),
        extra_roots: Arc::new(extra_roots),
        reloc_sites: Arc::new(reloc_sites),
        relocatable: !relocated.is_empty(),
        accepted_guesses: FxHashSet::default(),
        seed: Seed::Fact,
        guessed: Arc::default(),
        rejected: AddrSet::new(program),
    };
    let mut incomplete = st.run();
    phases.mark("discover run facts");

    let covered = Covered::new(&st.functions);
    let mut ptr_seeds: Vec<u64> = pointer_seeds(
        program,
        (!relocated_all.is_empty()).then_some(&relocated_all),
    )
    .into_iter()
    .filter(|&p| !covered.contains(p) && st.fresh(p))
    .collect();
    dedup_sorted(&mut ptr_seeds);
    incomplete |= st.run_guesses(ptr_seeds, Seed::Pointer);
    phases.mark("discover pointer seeds");
    // INVARIANT: an `__except` filter or handler is named by its function's
    // scope table, a relocated word too, and belongs to that function.
    let covered = Covered::new(&st.functions);
    let spans = Covered::ranges(&st.functions);
    let mut reloc: Vec<u64> = reloc_seeds(program, &covered)
        .into_iter()
        .filter(|&p| !spans.contains(p) && st.fresh(p))
        .collect();
    dedup_sorted(&mut reloc);
    incomplete |= st.run_guesses(reloc, Seed::Reloc);

    incomplete |= st.run_code_seeds();
    phases.mark("discover reloc+code seeds");

    let declared: u64 = program
        .function_ranges
        .iter()
        .map(|r| r.1.saturating_sub(r.0))
        .sum();
    let code: u64 = program
        .sections
        .iter()
        .filter(|s| s.executable)
        .map(|s| s.file_size)
        .sum();
    let guess_gaps = declared.saturating_mul(4) < code;
    for round in 0..GAP_ROUNDS_MAX {
        let blocks = Covered::new(&st.functions);
        let ranges = Covered::ranges(&st.functions);
        let mut pad_seeds: Vec<u64> = Vec::new();
        let mut gap_seeds: Vec<u64> = Vec::new();
        'sec: for s in &program.sections {
            if !s.executable || s.file_size == 0 {
                continue;
            }
            for gap in blocks.uncovered(s.va.0, s.va.0 + s.file_size) {
                let between_functions = !ranges.contains(gap.start);
                let mut va = gap.start;
                let hi = gap.end;
                let mut gap_open = between_functions;
                while va < hi {
                    let Some(&b) = program.read_va(va, 1).and_then(<[u8]>::first) else {
                        break;
                    };
                    // SPEC: only these bytes open a `nop` form, and a `nop`
                    // inside a function aligns a loop head, not a start.
                    let run_end = match b {
                        0xcc => int3_end(program, va, hi),
                        0x90 | 0x66 | 0x0f | 0x2e | 0x8d if between_functions => {
                            padding_end(program, bitness, va, hi)
                        }
                        _ => va,
                    };
                    if run_end > va {
                        if run_end < hi && st.fresh(run_end) {
                            pad_seeds.push(run_end);
                        }
                        va = run_end;
                    } else {
                        if guess_gaps && gap_open && va % 16 == 0 && st.fresh(va) {
                            gap_seeds.push(va);
                        }
                        // INVARIANT: a gap is swept an instruction at a time, so a
                        // `90` inside a displacement is never read as a `nop`
                        // and a seed never lands inside an instruction.
                        va = decode_at(program, bitness, va)
                            .filter(|i| i.code() != Code::INVALID && i.next_ip() > va)
                            .map_or(va + 1, |i| i.next_ip().min(hi));
                    }
                    gap_open = false;
                    if pad_seeds.len() + gap_seeds.len() >= SEEDS_MAX {
                        break 'sec;
                    }
                }
            }
        }
        dedup_sorted(&mut pad_seeds);
        dedup_sorted(&mut gap_seeds);
        if pad_seeds.is_empty() && gap_seeds.is_empty() {
            break;
        }
        if trace_seeds() {
            for va in &pad_seeds {
                eprintln!("seed {va:#x} queued: padding");
            }
            for va in &gap_seeds {
                eprintln!("seed {va:#x} queued: gap");
            }
        }
        let before = st.functions.len();
        let (pads, gaps) = (pad_seeds.len(), gap_seeds.len());
        incomplete |= st.run_guesses(pad_seeds, Seed::Padding);
        incomplete |= st.run_guesses(gap_seeds, Seed::Gap);
        incomplete |= st.run_code_seeds();
        let added = st.functions.len() - before;
        if trace_seeds() {
            eprintln!(
                "round {round}: {pads} padding seeds, {gaps} gap seeds, {added} functions added"
            );
        }
        if added < ROUND_ADDS_MIN {
            break;
        }
    }
    phases.mark("discover gap rounds");

    let continuations = catch_continuations(program, &st.functions);
    phases.mark("discover catch scan");
    if !continuations.is_empty() {
        let parents: Vec<u64> = continuations
            .keys()
            .copied()
            .filter(|&p| st.functions.iter().any(|f| f.entry == p))
            .collect();
        for (parent, labels) in continuations {
            Arc::make_mut(&mut st.extra_roots)
                .entry(parent)
                .or_default()
                .extend(labels);
        }
        st.forget(&parents);
        st.queue = parents;
        incomplete |= st.run();
    }
    phases.mark("discover catch rerun");

    let case_blocks: FxHashSet<u64> = st.jump_tables.values().flatten().copied().collect();
    st.functions.retain(|f| {
        !case_blocks.contains(&f.entry)
            || st
                .xrefs
                .get(&f.entry)
                .is_some_and(|sites| sites.iter().any(|s| s.kind == RefKind::Call))
    });
    st.functions.retain(|f| f.instr_count > 0);
    st.functions.shrink_to_fit();
    let entries: BTreeSet<u64> = st.functions.iter().map(|f| f.entry).collect();
    record_table_refs(
        program,
        &entries,
        &Covered::new(&st.functions),
        &mut st.xrefs,
    );
    analysis.functions = st.functions;
    analysis.xrefs = st.xrefs;
    analysis.jump_tables = st.jump_tables;
    analysis.indexed_tables = st.indexed_tables;
    analysis.throw_sites = throw_sites;
    analysis.classes.ids = st.class_ids;
    analysis.param_values = st
        .param_values
        .into_iter()
        .map(|(k, slots)| {
            (
                k,
                slots
                    .into_iter()
                    .filter(|(_, v)| v.len() <= PARAM_VALUES_MAX)
                    .collect(),
            )
        })
        .filter(|(_, slots): &(u64, BTreeMap<u8, BTreeSet<u64>>)| !slots.is_empty())
        .collect();
    analysis.incomplete = incomplete;
    phases.mark("discover collect");

    analysis.functions.sort_by_key(|f| f.entry);
    build_callers_and_names(program, &mut analysis.functions);
    phases.mark("discover callers+names");
    /// Fewest callers a function needs before it is read for the assert
    /// banner.
    ///
    /// The assert reporter is called from nearly every function of a
    /// debug-checked build and no symbol names it, so every guarded check
    /// in the program reads as a call to `sub_<va>`. It prints a banner
    /// naming itself, and only a handful of functions are called often
    /// enough to be it, so the scan for that banner is over those few.
    const ASSERT_CALLERS_MIN: usize = 200;
    let assert_reporters: BTreeSet<u64> = analysis
        .functions
        .iter()
        .filter(|f| {
            f.name.is_none()
                && f.callers.len() >= ASSERT_CALLERS_MIN
                && prints_assert_banner(program, bitness, f)
        })
        .map(|f| f.entry)
        .collect();
    /// Longest function read for the reference-counting helper's shape.
    ///
    /// A template writes one release per instantiation, so hundreds of
    /// unnamed functions are the same few instructions; naming them by that
    /// shape turns the noise at the end of most functions into the release
    /// it is.
    const RELEASE_INSTRS_MAX: usize = 40;
    let releases: BTreeMap<u64, &'static str> = analysis
        .functions
        .iter()
        .filter(|f| f.name.is_none() && f.instr_count <= RELEASE_INSTRS_MAX)
        .filter_map(|f| refcount_helper_name(program, bitness, f).map(|n| (f.entry, n)))
        .collect();
    for f in &mut analysis.functions {
        if f.name.is_none() && assert_reporters.contains(&f.entry) {
            f.name = Some("assert_failed".to_owned());
        }
        if f.name.is_none()
            && let Some(n) = releases.get(&f.entry)
        {
            f.name = Some((*n).to_owned());
        }
        if f.name.is_none() && st.chkstk.contains(&f.entry) {
            f.name = Some("__chkstk".to_owned());
        }
        if f.name.is_none() && st.frame_helpers.contains(&f.entry) {
            f.name = frame_helper_name(program, bitness, f.entry).map(str::to_owned);
        }
        // INVARIANT: only the epilogue helper opens by unlinking the
        // caller's registration; a function of that shape is the helper.
        if f.name.is_none() && f.instr_count <= EPILOG_INSTRS_MAX {
            f.name = epilog_helper_name(program, bitness, f.entry).map(str::to_owned);
        }
        if f.name.is_none() && f.instr_count <= COOKIE_CHECK_INSTRS_MAX {
            f.name = cookie_check_name(program, bitness, f.entry).map(str::to_owned);
        }
        if f.name.is_none()
            && f.instr_count <= PANIC_INSTRS_MAX
            && matches!(program.arch.isa(), Some(crate::isa::Isa::X86 { .. }))
        {
            f.name = panic_helper_name(program, bitness, f.entry, f.instr_count).map(str::to_owned);
        }
        if f.name.is_some() && f.name_source == NameSource::None {
            f.name_source = NameSource::Helper;
        }
    }
    analysis.finish_index(program);
    phases.mark("discover index+clones");
    analysis
}

/// Groups the functions by a fingerprint, keeping only the fingerprints
/// more than one function has.
///
/// # Arguments
///
/// * `functions` - The functions, in address order.
/// * `key` - The fingerprint of a function.
///
/// # Returns
///
/// Fingerprint to the entries sharing it, in the functions' order.
pub(super) fn shared_classes(
    functions: &[Function],
    key: impl Fn(&Function) -> u64,
) -> BTreeMap<u64, Vec<u64>> {
    let mut classes: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for f in functions {
        classes.entry(key(f)).or_default().push(f.entry);
    }
    classes.retain(|_, v| v.len() > 1);
    classes
}

/// One section's decoder and the address range it can decode.
struct Cursor<'a> {
    /// First address of the section.
    va: u64,
    /// One past the last file-backed address of the section.
    end: u64,
    /// The decoder over the section's file bytes, positioned at its last
    /// decode.
    decoder: Decoder<'a>,
}

/// Decoders over the executable sections, opened as the walks touch them,
/// so a walk does not build a decoder for every instruction.
///
/// A decode at the address a decoder already stands on (the straight-line
/// case, which is most instructions) costs no setup; any other address is
/// a position change. Results equal [`decode_at`]'s: the decoders see the
/// same file-backed bytes, cut at the same section end.
struct Cursors<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Decoder bitness (32 or 64).
    bitness: u32,
    /// The addresses between the first and the last mapped section; an
    /// operand outside it cannot reference the image.
    mapped: std::ops::Range<u64>,
    /// One decoder per section touched so far.
    open: Vec<Cursor<'a>>,
}

impl<'a> Cursors<'a> {
    /// Starts with no section open.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `bitness` - Decoder bitness.
    fn new(program: &'a Program, bitness: u32) -> Self {
        Self {
            program,
            bitness,
            mapped: mapped_range(program),
            open: Vec::new(),
        }
    }

    /// Decodes the instruction at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Address of the instruction.
    ///
    /// # Returns
    ///
    /// The instruction (possibly with [`Code::INVALID`]), or `None` when
    /// `va` is not in executable, file-backed memory.
    fn decode(&mut self, va: u64) -> Option<Instruction> {
        let idx = match self.open.iter().position(|c| va >= c.va && va < c.end) {
            Some(i) => i,
            None => self.open_section(va)?,
        };
        let c = self.open.get_mut(idx)?;
        if c.decoder.ip() != va {
            c.decoder
                .set_position(usize::try_from(va - c.va).ok()?)
                .ok()?;
            c.decoder.set_ip(va);
        }
        let mut instr = Instruction::default();
        c.decoder.decode_out(&mut instr);
        Some(instr)
    }

    /// The offsets of the displacement and the immediates inside `instr`,
    /// the instruction a decoder of this set decoded last.
    ///
    /// # Arguments
    ///
    /// * `instr` - That instruction.
    ///
    /// # Returns
    ///
    /// The offsets, or `None` when no decoder stands right after it.
    fn constant_offsets(&self, instr: &Instruction) -> Option<crate::isa::x86::ConstantOffsets> {
        let c = self.open.iter().find(|c| {
            c.decoder.ip() == instr.next_ip() && instr.ip() >= c.va && instr.ip() < c.end
        })?;
        Some(c.decoder.get_constant_offsets(instr))
    }

    /// Opens the decoder of the section holding `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - An address no open decoder covers.
    ///
    /// # Returns
    ///
    /// The index of the decoder covering `va`, or `None` when `va` is not
    /// in executable, file-backed memory (a section already open but whose
    /// file bytes end before `va` included).
    fn open_section(&mut self, va: u64) -> Option<usize> {
        let program = self.program;
        let s = program.section_at(va)?;
        if !s.executable || self.open.iter().any(|c| c.va == s.va.0) {
            return None;
        }
        let limit = (s.file_off.0 + s.file_size).min(from_usize(program.bytes.len()));
        let bytes = program
            .bytes
            .get(usize::try_from(s.file_off.0).ok()?..usize::try_from(limit).ok()?)
            .filter(|b| !b.is_empty())?;
        let end = s.va.0 + from_usize(bytes.len());
        self.open.push(Cursor {
            va: s.va.0,
            end,
            decoder: Decoder::with_ip(self.bitness, bytes, s.va.0, DecoderOptions::NONE),
        });
        (va < end).then_some(self.open.len() - 1)
    }
}

/// Most bytes of executable address range an [`AddrSet`] covers with bits;
/// a wider range spills every address into the ordered set instead.
const ADDR_BITS_MAX: u64 = 1 << 28;

/// A set of addresses: a bit per byte of the executable address range plus
/// an ordered spill set for everything else.
///
/// The walks test membership for every decoded instruction, jump and call
/// target and queue entry, so the bits keep those tests to one load; the
/// spill keeps addresses outside the range (or every address, when the
/// range is wider than [`ADDR_BITS_MAX`]) exact.
#[derive(Clone)]
struct AddrSet {
    /// Address of bit 0.
    base: u64,
    /// One bit per byte from `base`.
    bits: Vec<u64>,
    /// Addresses outside the bit range.
    spill: BTreeSet<u64>,
}

impl AddrSet {
    /// Sizes the bits to the executable, file-backed sections.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    fn new(program: &Program) -> Self {
        let (lo, hi) = program
            .sections
            .iter()
            .filter(|s| s.executable && s.file_size > 0)
            .fold((u64::MAX, 0), |(lo, hi), s| {
                (
                    lo.min(s.va.0),
                    hi.max(s.va.0.saturating_add(s.vsize.max(s.file_size))),
                )
            });
        let span = hi.saturating_sub(lo);
        let words = if span > ADDR_BITS_MAX {
            0
        } else {
            usize::try_from(span.div_ceil(64)).unwrap_or(0)
        };
        Self {
            base: lo,
            bits: vec![0; words],
            spill: BTreeSet::new(),
        }
    }

    /// Locates the bit for `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// The word index and mask, or `None` when the bits do not cover `va`.
    fn bit(&self, va: u64) -> Option<(usize, u64)> {
        let off = va.checked_sub(self.base)?;
        let word = usize::try_from(off / 64).ok()?;
        (word < self.bits.len()).then_some((word, 1u64 << (off % 64)))
    }

    /// Tells whether `va` is in the set.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn contains(&self, va: u64) -> bool {
        match self.bit(va) {
            Some((w, m)) => self.bits.get(w).is_some_and(|b| b & m != 0),
            None => self.spill.contains(&va),
        }
    }

    /// Adds `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn insert(&mut self, va: u64) {
        match self.bit(va) {
            Some((w, m)) => {
                if let Some(b) = self.bits.get_mut(w) {
                    *b |= m;
                }
            }
            None => {
                self.spill.insert(va);
            }
        }
    }

    /// Finds the first address in the set after `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// The address, or `None` when nothing in the set lies past `va`.
    fn next_after(&self, va: u64) -> Option<u64> {
        let spilled = self.spill.range(va.saturating_add(1)..).next().copied();
        let Some(first) = va.saturating_add(1).checked_sub(self.base) else {
            // INVARIANT: before the bits, the lowest set bit, if any, is the
            // answer.
            return self
                .bits
                .iter()
                .enumerate()
                .find(|(_, w)| **w != 0)
                .map(|(i, w)| self.base + from_usize(i) * 64 + u64::from(w.trailing_zeros()))
                .into_iter()
                .chain(spilled)
                .min();
        };
        let mut word = usize::try_from(first / 64).unwrap_or(usize::MAX);
        let mut mask = u64::MAX << (first % 64);
        let mut found = None;
        while let Some(w) = self.bits.get(word) {
            let hit = w & mask;
            if hit != 0 {
                found = Some(self.base + from_usize(word) * 64 + u64::from(hit.trailing_zeros()));
                break;
            }
            word += 1;
            mask = u64::MAX;
        }
        found.into_iter().chain(spilled).min()
    }

    /// Adds every address of `iter`.
    ///
    /// # Arguments
    ///
    /// * `iter` - Any addresses.
    fn extend<I: IntoIterator<Item = u64>>(&mut self, iter: I) {
        for va in iter {
            self.insert(va);
        }
    }

    /// Removes `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn remove(&mut self, va: u64) {
        match self.bit(va) {
            Some((w, m)) => {
                if let Some(b) = self.bits.get_mut(w) {
                    *b &= !m;
                }
            }
            None => {
                self.spill.remove(&va);
            }
        }
    }
}

/// Prologue and stack-access facts gathered during the walk, enough to say
/// how many stack-passed arguments the function reads.
#[derive(Default)]
struct FrameFacts {
    /// `(address, immediate)` of the first `sub rsp, imm`.
    sub_rsp: Option<(u64, u64)>,
    /// Addresses of `push` instructions.
    pushes: Vec<u64>,
    /// Addresses of `pop` instructions.
    pops: Vec<u64>,
    /// `(address, bytes)` of every `add rsp, imm`, the caller's cleanup
    /// after a call.
    adds: Vec<(u64, i64)>,
    /// `(address, offset)`: rsp-relative offset held by rbp after `mov rbp, rsp` / `lea rbp, [rsp+K]`.
    rbp_off: Option<(u64, i64)>,
    /// The register holding a copy of the stack pointer and the address of
    /// the `mov` that made it: `mov rax, rsp` stores the callee-saved
    /// registers home through `rax` and sets the frame pointer from it, and
    /// `push ebx; mov ebx, esp; and esp, -16` reads the arguments through
    /// `ebx` once the stack is aligned.
    rax_alias: Option<(Register, u64)>,
    /// `(base register, displacement, address)` of every rsp/rbp-based
    /// memory operand.
    refs: Vec<(Register, i64, u64)>,
    /// `(address, next address)` of every instruction an epilogue is made
    /// of: a pop, an `add rsp, imm`, a `mov rsp, reg` or a `leave`.
    links: Vec<(u64, u64)>,
    /// Addresses of `ret` and of unconditional and indirect jumps: where
    /// an epilogue ends.
    exits: Vec<u64>,
    /// A `sub rsp, <register>` was seen: the frame is sized at runtime
    /// (`__chkstk`, `alloca`), so its size is unknown here.
    dynamic_frame: bool,
    /// The frame pointer was set by a prologue helper to one word below the
    /// entry stack pointer, the place `push ebp; mov ebp, esp` puts it.
    helper_frame: bool,
}

impl FrameFacts {
    /// Records what one instruction tells about the frame.
    ///
    /// # Arguments
    ///
    /// * `instr` - The decoded instruction.
    /// * `addr` - Its address; prologue facts keep the earliest occurrence.
    /// * `bitness` - Decoder bitness, which decides how a displacement's
    ///   sign is read.
    fn observe(&mut self, instr: &Instruction, addr: u64, bitness: u32) {
        let earlier = |seen: Option<(u64, i64)>| seen.is_none_or(|(a, _)| addr < a);
        if matches!(
            instr.flow_control(),
            FlowControl::Return | FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
        ) {
            self.exits.push(addr);
        }
        let restores_rsp = instr.op_count() == 2
            && instr.op0_kind() == OpKind::Register
            && instr.op0_register().full_register() == Register::RSP
            && instr.op1_kind() == OpKind::Register;
        if matches!(instr.mnemonic(), Mnemonic::Pop | Mnemonic::Leave)
            || (instr.mnemonic() == Mnemonic::Mov && restores_rsp)
        {
            self.links.push((addr, instr.next_ip()));
        }
        match instr.mnemonic() {
            Mnemonic::Push => self.pushes.push(addr),
            Mnemonic::Pop => self.pops.push(addr),
            Mnemonic::Add if moves_rsp_by_imm(instr) => {
                self.adds.push((addr, instr.immediate(1).cast_signed()));
                self.links.push((addr, instr.next_ip()));
            }
            Mnemonic::Sub
                if moves_rsp_by_imm(instr) && self.sub_rsp.is_none_or(|(a, _)| addr < a) =>
            {
                self.sub_rsp = Some((addr, instr.immediate(1)));
            }
            Mnemonic::Sub
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RSP
                    && instr.op1_kind() == OpKind::Register =>
            {
                self.dynamic_frame = true;
            }
            Mnemonic::Mov
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.op1_kind() == OpKind::Register
                    && instr.op1_register().full_register() == Register::RSP
                    && earlier(self.rbp_off) =>
            {
                self.rbp_off = Some((addr, 0));
            }
            Mnemonic::Lea
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.memory_base().full_register() == Register::RSP
                    && instr.memory_index() == Register::None
                    && earlier(self.rbp_off) =>
            {
                self.rbp_off = Some((addr, crate::disasm::displacement(instr, bitness)));
            }
            // INVARIANT: `lea rbp, [rax+K]` after `mov rax, rsp` sets the
            // frame pointer K bytes from where the stack pointer stood at
            // the `mov`, which is where a read through `rbp` is placed.
            Mnemonic::Lea
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.memory_index() == Register::None
                    && earlier(self.rbp_off)
                    && let Some((alias, at)) = self.rax_alias
                    && instr.memory_base().full_register() == alias =>
            {
                self.rbp_off = Some((at, crate::disasm::displacement(instr, bitness)));
            }
            _ => {}
        }
        let rax_alias = self.rax_alias;
        for op in 0..instr.op_count() {
            if instr.op_kind(op) == OpKind::Memory {
                let base = instr.memory_base().full_register();
                let disp = crate::disasm::displacement(instr, bitness);
                if base == Register::RSP || base == Register::RBP {
                    self.refs.push((base, disp, addr));
                } else if let Some((alias, at)) = rax_alias
                    && base == alias
                {
                    self.refs.push((Register::RSP, disp, at));
                }
            }
        }
        let written = (instr.op0_kind() == OpKind::Register)
            .then(|| instr.op0_register().full_register())
            .filter(|_| !matches!(instr.mnemonic(), Mnemonic::Cmp | Mnemonic::Test));
        let copies_rsp = instr.mnemonic() == Mnemonic::Mov
            && instr.op1_kind() == OpKind::Register
            && instr.op1_register().full_register() == Register::RSP
            && written.is_some_and(|r| r.is_gpr() && r != Register::RSP && r != Register::RBP);
        if copies_rsp {
            self.rax_alias = written.map(|r| (r, addr));
        } else if written.is_some() && written == self.rax_alias.map(|(r, _)| r) {
            self.rax_alias = None;
        }
    }

    /// Computes how many stack-passed arguments the function reads.
    ///
    /// # Arguments
    ///
    /// * `shadow` - Bytes of callee-owned home space above the return address
    ///   (32 for the Microsoft x64 convention, 0 for SysV and 32-bit code).
    /// * `word` - Stack word size in bytes: what a push moves the stack
    ///   pointer by, the width of the return address, and the distance
    ///   between two arguments.
    ///
    /// # Returns
    ///
    /// The highest argument index read, counting from the first slot above
    /// the return address and shadow space; capped at 32. Zero when the frame
    /// is sized at runtime and its size is unknown, since a local read cannot
    /// then be told from an argument.
    ///
    /// Each read is placed against the stack pointer as it stood at that
    /// instruction: the pushes, pops and cleanups before it, and the frame
    /// allocation once made. A frame-pointer read is placed against where
    /// the pointer was set, so the pushes the body makes for its own calls
    /// move nothing. The pops and cleanups of an epilogue, the run of them
    /// right before a `ret` or a tail jump, tear the frame down on that
    /// path alone and move nothing for the code after them in the image
    /// ([`FrameFacts::epilogues`]).
    fn stack_args(&self, shadow: i64, word: i64) -> u32 {
        if self.dynamic_frame && self.sub_rsp.is_none() {
            return 0;
        }
        let epilogue = self.epilogues();
        let below_at = |addr: u64| -> i64 {
            let pushes = count_i64(self.pushes.iter().filter(|a| **a < addr).count());
            let pops = count_i64(
                self.pops
                    .iter()
                    .filter(|a| **a < addr && !epilogue.contains(a))
                    .count(),
            );
            let sub = self
                .sub_rsp
                .filter(|(a, _)| *a < addr)
                .map_or(0, |(_, imm)| imm.cast_signed());
            let adds: i64 = self
                .adds
                .iter()
                .filter(|(a, _)| *a < addr && !epilogue.contains(a))
                .map(|(_, k)| *k)
                .sum();
            sub + (pushes - pops) * word - adds
        };
        let frame_pointer = if self.helper_frame {
            Some(word)
        } else {
            self.rbp_off.map(|(at, k)| below_at(at) - k)
        };
        self.refs
            .iter()
            .filter_map(|(base, disp, addr)| {
                let below = if *base == Register::RSP {
                    below_at(*addr)
                } else {
                    frame_pointer?
                };
                let entry_rel = disp - below;
                let first = word + shadow;
                (entry_rel >= first)
                    .then(|| ((entry_rel - first) / word + 1).min(32))
                    .and_then(|n| u32::try_from(n).ok())
            })
            .max()
            .unwrap_or(0)
    }
}

/// A count of instructions as a signed stack-slot multiplier.
///
/// # Arguments
///
/// * `n` - The count; a function holds far fewer pushes than `i64::MAX`.
fn count_i64(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

impl FrameFacts {
    /// Collects the addresses of the epilogues' instructions: from each
    /// exit, the pops, cleanups and frame restores that lead into it
    /// without a gap, walking back while each one's next address is the
    /// one reached so far.
    ///
    /// A map from each link's next address to its own, built once with the
    /// first link encountered winning as a scan's first match would, answers
    /// each step of that walk in constant time.
    fn epilogues(&self) -> BTreeSet<u64> {
        let mut leads = FxHashMap::with_capacity_and_hasher(self.links.len(), Default::default());
        for &(addr, next) in &self.links {
            leads.entry(next).or_insert(addr);
        }
        let mut out = BTreeSet::new();
        for &exit in &self.exits {
            let mut at = exit;
            while let Some(&addr) = leads.get(&at) {
                if !out.insert(addr) {
                    break;
                }
                at = addr;
            }
        }
        out
    }
}

/// A half-open address range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Span {
    /// First address.
    start: u64,
    /// One past the last.
    end: u64,
}

impl Span {
    /// The range a block covers.
    ///
    /// # Arguments
    ///
    /// * `b` - The block.
    fn of_block(b: &BasicBlock) -> Span {
        Span {
            start: b.start,
            end: b.end,
        }
    }
}

/// Index of the blocks found so far, by address.
///
/// A function's whole span would over-answer: a thunk the linker dropped
/// in a gap between two of a function's blocks would read as claimed, and
/// a function whose walk followed a jump into a shared block far away
/// would claim everything between. Whether an address is worth walking is
/// the finer question of whether any block covers it at all.
struct Covered(Vec<Span>);

impl Covered {
    /// Builds the index from the functions found so far.
    ///
    /// # Arguments
    ///
    /// * `functions` - Functions in any order.
    fn new(functions: &[Function]) -> Covered {
        Covered::from_spans(
            functions
                .iter()
                .flat_map(|f| f.blocks.iter().map(Span::of_block))
                .collect(),
        )
    }

    /// Builds the index from spans in any order: sorted by start, each end
    /// raised to the farthest end at or before it, so a search over the
    /// starts answers whether anything covers an address.
    ///
    /// # Arguments
    ///
    /// * `spans` - The covered ranges.
    fn from_spans(mut spans: Vec<Span>) -> Covered {
        spans.sort_unstable();
        let mut max_end = 0;
        for s in &mut spans {
            max_end = max_end.max(s.end);
            s.end = max_end;
        }
        Covered(spans)
    }

    /// Builds the index from the functions' ranges rather than their blocks.
    ///
    /// A function's range spans the alignment inside it - the `nop` run
    /// before a loop head, a jump table the compiler left between two
    /// blocks - and a seed placed there would walk part of the function as
    /// a function of its own.
    ///
    /// # Arguments
    ///
    /// * `functions` - Functions in any order.
    fn ranges(functions: &[Function]) -> Covered {
        /// Widest gap between two of a function's blocks that its span
        /// still bridges: the alignment and jump tables inside a function.
        ///
        /// Past that the blocks are chunks apart - a PGO cold chunk, an
        /// `__except` handler moved to the section's end, a followed jump
        /// into a distant shared tail - and bridging them hid every
        /// function between from the seeds below: in 32-bit `KernelBase`, a
        /// quarter of all functions.
        const GAP_MAX: u64 = 0x1000;
        let mut spans: Vec<Span> = Vec::new();
        for f in functions {
            let mut chunk: Option<Span> = None;
            for b in f.blocks.iter().map(Span::of_block) {
                chunk = match chunk {
                    Some(c) if b.start <= c.end.saturating_add(GAP_MAX) => Some(Span {
                        start: c.start,
                        end: c.end.max(b.end),
                    }),
                    Some(done) => {
                        spans.push(done);
                        Some(b)
                    }
                    None => Some(b),
                };
            }
            spans.extend(chunk);
        }
        Covered::from_spans(spans)
    }

    /// Lists the maximal ranges of `lo..hi` no block covers.
    ///
    /// # Arguments
    ///
    /// * `lo` - First address of the span.
    /// * `hi` - One past the last.
    ///
    /// # Returns
    ///
    /// The gaps in address order, each non-empty.
    fn uncovered(&self, lo: u64, hi: u64) -> Vec<Span> {
        let mut gaps = Vec::new();
        let mut at = lo;
        let first = self.0.partition_point(|s| s.end <= lo);
        for s in &self.0[first..] {
            if s.start >= hi {
                break;
            }
            if s.start > at {
                gaps.push(Span {
                    start: at,
                    end: s.start.min(hi),
                });
            }
            at = at.max(s.end);
            if at >= hi {
                break;
            }
        }
        if at < hi {
            gaps.push(Span { start: at, end: hi });
        }
        gaps
    }

    /// Tells whether `p` lies inside some indexed block.
    ///
    /// # Arguments
    ///
    /// * `p` - A virtual address.
    ///
    /// # Returns
    ///
    /// Whether a block starting at or before `p` reaches past it.
    fn contains(&self, p: u64) -> bool {
        self.0
            .partition_point(|s| s.start <= p)
            .checked_sub(1)
            .is_some_and(|i| self.0.get(i).is_some_and(|s| s.end > p))
    }
}

/// What the walks of a wave read besides the starts, held by the pass and
/// shared with the wave's threads ([`WalkState::shared`]).
struct Shared {
    /// Functions known never to return.
    noreturn: Arc<AddrSet>,
    /// Import slots of functions that never return.
    noreturn_slots: Arc<FxHashSet<u64>>,
    /// Code each function owns that its instructions do not reach, by
    /// entry.
    extra_roots: Arc<FxHashMap<u64, Vec<u64>>>,
    /// Where the loader patches an absolute address, or `None` when the
    /// image relocates nothing.
    reloc_sites: Option<Arc<AddrSet>>,
    /// The entries of the current guess list, each held to the guess cap.
    guessed: Arc<FxHashSet<u64>>,
}

impl Shared {
    /// What a wave's walks read: these sets and the starts.
    ///
    /// # Arguments
    ///
    /// * `starts` - The starts as they stood when the wave began.
    fn known<'s>(&'s self, starts: &'s AddrSet) -> Known<'s> {
        Known {
            starts,
            noreturn: &self.noreturn,
            noreturn_slots: &self.noreturn_slots,
            extra_roots: &self.extra_roots,
            reloc_sites: self.reloc_sites.as_deref(),
            guessed: &self.guessed,
        }
    }
}

/// The threads that walk the batches of one wave, each walking its stripe
/// of every batch.
///
/// They start once for the wave rather than once for each batch: a batch is
/// a few walks per core, and a large program's discovery started a thread
/// for every few walks, tens of thousands of threads, each with a fresh
/// stack and scratch set to fault in, which was half of discovery's time.
/// A lane keeps its walker from batch to batch with the budget set afresh,
/// which is the walker a batch made anew: a walk leaves its scratch set
/// empty, and a decoder is placed before each instruction it decodes.
struct Lanes<'scope> {
    /// Per thread, where its stripes go and its walks come back.
    lanes: Vec<Lane>,
    /// The threads, joined when the wave ends.
    handles: Vec<ScopedJoinHandle<'scope, ()>>,
}

/// One walker thread's channels.
struct Lane {
    /// The entries of its stripe of a batch and the budget to walk them on.
    stripe: Sender<(Vec<u64>, u64)>,
    /// Its walks of that stripe, in order, and the budget they spent.
    walked: Receiver<(Vec<Walked>, u64)>,
}

impl<'scope> Lanes<'scope> {
    /// Starts `threads` walker threads in `scope`, or none when there is
    /// one: a single core walks on the pass's own walker.
    ///
    /// # Arguments
    ///
    /// * `scope` - The wave's thread scope.
    /// * `threads` - How many lanes.
    /// * `program` - The loaded image.
    /// * `bitness` - Decoder bitness.
    /// * `known` - What the wave's walks read.
    fn start<'env>(
        scope: &'scope Scope<'scope, 'env>,
        threads: usize,
        program: &'env Program,
        bitness: u32,
        known: &'env Known<'env>,
    ) -> Self {
        let mut lanes = Lanes {
            lanes: Vec::new(),
            handles: Vec::new(),
        };
        if threads <= 1 {
            return lanes;
        }
        for _ in 0..threads {
            let (stripe, stripes) = channel::<(Vec<u64>, u64)>();
            let (done, walked) = channel();
            lanes.handles.push(scope.spawn(move || {
                let mut worker = Worker::new(program, bitness, 0);
                for (entries, budget) in stripes {
                    worker.fuel = budget;
                    let out: Vec<Walked> = entries
                        .iter()
                        .map(|&entry| walk_capped(&mut worker, entry, known))
                        .collect();
                    if done.send((out, budget - worker.fuel)).is_err() {
                        break;
                    }
                }
            }));
            lanes.lanes.push(Lane { stripe, walked });
        }
        lanes
    }

    /// Walks a batch across the first `threads` lanes, lane `t` taking the
    /// entries at `t`, `t + threads`, and so on, each from `budget`.
    ///
    /// # Arguments
    ///
    /// * `batch` - The entries.
    /// * `threads` - How many lanes walk it; at most the lanes there are.
    /// * `budget` - What each lane may spend.
    ///
    /// # Returns
    ///
    /// One walk per entry, `None` where a lane failed, and the budget the
    /// lanes spent.
    fn walk(&self, batch: &[u64], threads: usize, budget: u64) -> (Vec<Option<Walked>>, u64) {
        let sent: Vec<bool> = self
            .lanes
            .iter()
            .take(threads)
            .enumerate()
            .map(|(t, lane)| {
                let entries = batch.iter().copied().skip(t).step_by(threads).collect();
                lane.stripe.send((entries, budget)).is_ok()
            })
            .collect();
        let mut slots: Vec<Option<Walked>> = (0..batch.len()).map(|_| None).collect();
        let mut spent = 0u64;
        for ((t, lane), sent) in self.lanes.iter().enumerate().zip(sent) {
            let Some(Ok((walked, used))) = sent.then(|| lane.walked.recv()) else {
                continue;
            };
            spent = spent.saturating_add(used);
            for (slot, w) in slots.iter_mut().skip(t).step_by(threads).zip(walked) {
                *slot = Some(w);
            }
        }
        (slots, spent)
    }

    /// Ends the threads and waits for them. A thread that failed is not an
    /// error here: the pass walked what it left.
    fn stop(self) {
        drop(self.lanes);
        for handle in self.handles {
            drop(handle.join());
        }
    }
}

/// What every walk of a wave reads and none writes.
#[derive(Clone, Copy)]
struct Known<'a> {
    /// Known function starts.
    starts: &'a AddrSet,
    /// Functions known never to return.
    noreturn: &'a AddrSet,
    /// Import slots of functions that never return.
    noreturn_slots: &'a FxHashSet<u64>,
    /// Code each function owns that its instructions do not reach, by
    /// entry.
    extra_roots: &'a FxHashMap<u64, Vec<u64>>,
    /// Where the loader patches an absolute address, or `None` when the
    /// image relocates nothing.
    reloc_sites: Option<&'a AddrSet>,
    /// The entries of the current guess list, each held to the guess cap.
    guessed: &'a FxHashSet<u64>,
}

/// [`walk_function`] with a guessed entry held to [`GUESS_WALK_MAX`]
/// instructions: a walk that reaches it is marked [`Walked::overlong`], and
/// only what it decoded is charged to the worker's budget.
///
/// # Arguments
///
/// * `worker` - The walker's decoders, scratch set and budget.
/// * `entry` - The entry to walk.
/// * `known` - What every walk reads; an entry among its guesses is held
///   to the cap.
fn walk_capped(worker: &mut Worker<'_>, entry: u64, known: &Known<'_>) -> Walked {
    let extra = known.extra_roots.get(&entry).map_or(&[][..], Vec::as_slice);
    if !known.guessed.contains(&entry) {
        return walk_function(worker, entry, known, extra);
    }
    let budget = worker.fuel;
    let allowed = budget.min(GUESS_WALK_MAX);
    worker.fuel = allowed;
    let mut w = walk_function(worker, entry, known, extra);
    let left = worker.fuel;
    worker.fuel = budget - (allowed - left);
    w.overlong = left == 0 && allowed == GUESS_WALK_MAX;
    w
}

/// How a pending address was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Via {
    /// A fall-through: landing on bytes that do not decode means the walk
    /// was reading data.
    Fall,
    /// A branch: landing on bytes that do not decode is only a branch not
    /// taken.
    Branch,
}

/// Walks one function by decoding from its entry.
///
/// Every reachable instruction is decoded once; near branches are followed,
/// near call targets become callees, an unconditional jump into another
/// known function start is a tail call (a callee, not followed), a call to a
/// function that never returns (by name, through an import slot or a thunk
/// to one, or because another function's start, `int3` padding, a `ud2`
/// trap or undecodable bytes follow the call) ends the path, and indirect jumps are
/// resolved through [`resolve_jump_table`]
/// using the walk's own decode chain (the last decoded instruction whose
/// next address is the one asked for). The `call X; sub rsp, rax` idiom
/// identifies the stack-probe helper `__chkstk`. The function's range is
/// the lowest decoded address to the end of the highest one.
///
/// The addresses right after an epilogue instruction (`pop ebp`, `leave`,
/// `add esp, N`) are kept: a jump there has torn the frame down first, and
/// no jump within a function does that, so it is a tail call. An `add esp,
/// N` right after a call is the caller's argument cleanup, not the frame's
/// release, so the addresses after calls are kept apart. Where a `mov
/// dword [ebp-4], -2` (the trylevel restored) ends is kept too: the call
/// right after it enters a `__finally` on the normal path. The `nop`s
/// after calls that do not return are each the function's last byte when
/// no path reaches them otherwise. The `__except` filters and handlers a
/// scope table names are walked after the function's own code: PGO moves
/// them to the section's cold end, where a handler's last call may never
/// return and the bytes after it are another function's or data, so what
/// they lead into is kept as the function's blocks but tells nothing about
/// whether the entry is one.
///
/// # Arguments
///
/// * `worker` - The walk's decoders (they hold the image and its bitness),
///   its decoded-address set (empty on entry and on return) and its
///   instruction budget, decremented per decoded instruction.
/// * `entry` - Address to start at.
/// * `known` - What every walk reads: the starts (a jump into one other
///   than `entry` is a tail call, and one right after a call marks the
///   callee noreturn), the functions and import slots that never return,
///   and the relocation sites.
/// * `extra_roots` - Code this function owns that its instructions do not
///   reach.
fn walk_function(
    worker: &mut Worker<'_>,
    entry: u64,
    known: &Known<'_>,
    extra_roots: &[u64],
) -> Walked {
    let Known {
        starts,
        noreturn,
        noreturn_slots,
        reloc_sites,
        ..
    } = *known;
    let Worker {
        cursors,
        visited,
        fuel,
    } = worker;
    let program = cursors.program;
    let bitness = cursors.bitness;
    let pe = program.format == crate::program::BinaryFormat::Pe;
    let mapped = cursors.mapped.clone();
    let mut recs: Vec<(u64, InstrRec)> = Vec::new();
    let mut recorded = Recorded::default();
    let mut data_refs: Vec<DataRef> = Vec::new();
    let mut tables: Vec<ResolvedTable> = Vec::new();
    let mut indexed: BTreeSet<u64> = BTreeSet::new();
    let mut arg_consts: Vec<ArgConst> = Vec::new();
    let mut registrations: Vec<Registration> = Vec::new();
    let mut callees: BTreeSet<u64> = BTreeSet::new();
    let mut followed: BTreeSet<u64> = BTreeSet::new();
    let mut followed_calls: BTreeSet<u64> = BTreeSet::new();
    let mut found_noreturn: BTreeSet<u64> = BTreeSet::new();
    let mut found_noreturn_weak: BTreeSet<u64> = BTreeSet::new();
    let mut far_handlers: BTreeSet<u64> = BTreeSet::new();
    let mut near_handlers: BTreeSet<u64> = BTreeSet::new();
    let mut pending: Vec<(u64, Via)> = vec![(entry, Via::Fall)];
    let mut after_epilogue: BTreeSet<u64> = BTreeSet::new();
    let mut after_call: BTreeSet<u64> = BTreeSet::new();
    let mut chkstk: Option<u64> = None;
    let mut frame_helper: Option<u64> = None;
    let mut stack_pop: u32 = 0;
    let mut frame = FrameFacts::default();
    let mut junk = false;
    let mut bad_entry = false;
    let mut undoes_frame = false;
    let mut slot_thunk = false;
    let mut trylevel_at: Option<u64> = None;
    let mut terminated = false;
    let mut fell_into_start = false;
    let mut zero_bytes = false;
    let mut surely_data = false;
    let mut after_noreturn: Vec<u64> = Vec::new();
    let mut odd: Option<&'static str> = None;
    let mut prologue = false;
    let mut frame_opened = false;
    let mut unbalanced = false;
    let mut handler_roots: Vec<u64> = extra_roots.to_vec();
    let mut in_handlers = false;

    loop {
        while let Some((addr, via)) = pending.pop() {
            if visited.contains(addr) || *fuel == 0 {
                continue;
            }
            *fuel -= 1;
            let linear = via == Via::Fall;
            let Some(instr) = cursors.decode(addr) else {
                junk |= linear && !in_handlers;
                bad_entry |= recs.is_empty() && !in_handlers;
                continue;
            };
            if instr.code() == Code::INVALID {
                junk |= linear && !in_handlers;
                bad_entry |= recs.is_empty() && !in_handlers;
                continue;
            }
            // INVARIANT: a relocation site is where the loader patches an
            // address into an instruction's displacement or immediate: never
            // where an instruction starts, and inside one nowhere else. A
            // decode that puts an instruction against a site otherwise is
            // reading a table in the section as code.
            if reloc_sites.is_some_and(|s| s.contains(addr) || misplaced_site(cursors, s, &instr)) {
                junk |= linear && !in_handlers;
                bad_entry |= recs.is_empty() && !in_handlers;
                continue;
            }
            let next = instr.next_ip();
            // SPEC: Linux's `int 0x80` system call returns to the next
            // instruction, as `syscall` does; every other `int` but `int3`
            // ends its path.
            let flow = match instr.flow_control() {
                FlowControl::Interrupt
                    if instr.mnemonic() == Mnemonic::Int
                        && instr.try_immediate(0).ok() == Some(0x80) =>
                {
                    FlowControl::Next
                }
                other => other,
            };
            let target = near_target(&instr);
            if odd_instruction(&instr, bitness, pe) && !in_handlers {
                zero_bytes = true;
                surely_data |= !byte_add(&instr);
                bad_entry |= recs.is_empty();
                if odd.is_none() {
                    odd = Some(mnemonic_name(instr.mnemonic()));
                }
            }
            if recs.is_empty() {
                prologue = prologue_like(&instr);
                undoes_frame = matches!(instr.mnemonic(), Mnemonic::Pop | Mnemonic::Leave);
                slot_thunk = slot_jump(&instr)
                    .is_some_and(|slot| program.section_at(slot).is_some_and(|s| !s.executable));
            }
            match frame_step(&instr) {
                Some(FrameStep::Opens) => frame_opened = true,
                Some(FrameStep::Closes) if !frame_opened && !in_handlers => unbalanced = true,
                Some(FrameStep::Closes) | None => {}
            }
            if matches!(flow, FlowControl::Call | FlowControl::IndirectCall) {
                after_call.insert(next);
            }
            // SPEC: 32-bit code pops the arguments of several calls with one
            // `add esp, N`, not always right after the last call; only the
            // size the prologue took (`sub esp, N`) is the frame's release,
            // and `add esp, eax` releases a dynamic frame: no immediate,
            // never the size the prologue took.
            let arg_cleanup = instr.mnemonic() == Mnemonic::Add
                && (after_call.contains(&addr)
                    || (bitness == 32
                        && frame.sub_rsp.is_none_or(|(_, taken)| {
                            instr.try_immediate(1).unwrap_or(0) != taken
                        })));
            if tears_frame_down(&instr) && !arg_cleanup {
                after_epilogue.insert(next);
            }
            // SPEC: the callee-saved registers restored after the frame's
            // release are the epilogue too: `add rsp, 0x20; pop rbx; jmp f`.
            if instr.mnemonic() == Mnemonic::Pop && after_epilogue.contains(&addr) {
                after_epilogue.insert(next);
            }
            let patched = reloc_sites.and_then(|s| Some((s, cursors.constant_offsets(&instr)?)));
            record_data_refs(program, &mapped, &instr, addr, &mut data_refs, patched);
            // SPEC: a 32-bit SEH frame names its `__except` filters and
            // handlers only in the scope table it pushes; they are this
            // function's code.
            if bitness == 32
                && instr.mnemonic() == Mnemonic::Push
                && matches!(
                    instr.op0_kind(),
                    OpKind::Immediate32 | OpKind::Immediate8to32
                )
            {
                let table = instr.immediate(0) & 0xffff_ffff;
                let roots = seh_scope_roots(program, table, entry);
                if trace_seeds() && !roots.is_empty() {
                    eprintln!("scope table {table:#x} of {entry:#x}: {roots:x?}");
                }
                for root in roots {
                    if root.abs_diff(entry) <= HANDLER_REACH {
                        handler_roots.push(root);
                        near_handlers.insert(root);
                    } else {
                        far_handlers.insert(root);
                        if let Some(t) = handler_lands_near(cursors, root, entry) {
                            handler_roots.push(t);
                            near_handlers.insert(t);
                        }
                    }
                }
            }
            if bitness == 32
                && instr.mnemonic() == Mnemonic::Mov
                && instr.op0_kind() == OpKind::Memory
                && instr.memory_base().full_register() == Register::RBP
                && instr.memory_index() == Register::None
                && crate::disasm::displacement(&instr, bitness) == -4
                && (instr.op1_kind() == OpKind::Register
                    || (matches!(
                        instr.op1_kind(),
                        OpKind::Immediate32 | OpKind::Immediate8to32
                    ) && matches!(instr.immediate(1) & 0xffff_ffff, 0xffff_fffe | 0..=0x3f)))
            {
                trylevel_at = Some(next);
            }
            frame.observe(&instr, addr, cursors.bitness);
            if instr.mnemonic() == Mnemonic::Sub
                && instr.op0_kind() == OpKind::Register
                && instr.op0_register().full_register() == Register::RSP
                && instr.op1_kind() == OpKind::Register
                && instr.op1_register().full_register() == Register::RAX
                && let Some(callee) = recorded.call_before(addr)
            {
                chkstk = Some(callee);
            }
            // INVARIANT: the 32-bit probe moves the stack pointer itself, so no
            // `sub esp, eax` follows the call; its body is the same in every
            // MSVC runtime and is known by its first three instructions.
            if flow == FlowControl::Call
                && let Some(callee) = target
                && program.read_va(callee, CHKSTK_X86.len()) == Some(&CHKSTK_X86[..])
            {
                chkstk = Some(callee);
            }
            visited.insert(addr);
            let (print, shape) = fingerprint(&mapped, &instr);
            let rec = InstrRec {
                next,
                flow,
                target,
                print,
                shape,
            };
            recorded.push(addr, &rec);
            recs.push((addr, rec));

            match flow {
                FlowControl::Next => {
                    if next != entry && starts.contains(next) {
                        fell_into_start |= !in_handlers;
                    } else {
                        pending.push((next, Via::Fall));
                    }
                }
                FlowControl::ConditionalBranch => {
                    // INVARIANT: a conditional branch into a known function
                    // start is a conditional tail call (`if (c) return f();`),
                    // the same as the unconditional case below: record the
                    // callee and do not walk into it, so the callee's blocks
                    // are not absorbed. A target not yet a start is followed
                    // and remembered, so a later split round re-walks this
                    // function once it proves one.
                    match target {
                        Some(t) if t == entry => pending.push((t, Via::Branch)),
                        Some(t) if starts.contains(t) || after_padding(program, bitness, t) => {
                            callees.insert(t);
                        }
                        Some(t) => {
                            followed.insert(t);
                            pending.push((t, Via::Branch));
                        }
                        None => {}
                    }
                    pending.push((next, Via::Fall));
                }
                FlowControl::UnconditionalBranch | FlowControl::IndirectBranch => match target {
                    Some(t) if t == entry => pending.push((t, Via::Branch)),
                    // SPEC: a function that is only `jmp $+2` is a hot-patch
                    // stub (`__CIcos: jmp short $+2`, then `__CIcos_default`):
                    // what follows is the function it stands for.
                    Some(t) if addr == entry && t == next && instr.len() == 2 => {
                        callees.insert(t);
                        terminated = true;
                    }
                    // INVARIANT: a jump into a known function, one made after the
                    // frame was torn down, or one to an address that opens the
                    // way a function opens, is a tail call: the target is a
                    // callee and, uncovered, a seed of its own. The third is what
                    // finds a function that is only ever tail-jumped to: nothing
                    // calls it, so nothing else would ever make it a start, and
                    // the walk would absorb it whole. A short jump to the next
                    // instruction goes nowhere (the delay-load thunk's `jmp
                    // $+2`): a jump to another function is a `jmp rel32` the
                    // linker fills in, and 32-bit code packs a tail callee right
                    // after its caller that way.
                    Some(t)
                        if starts.contains(t)
                            || (!(declared_interior(program, t)
                                || t == next && instr.len() == 2)
                                && (after_padding(program, bitness, t)
                                    || after_epilogue.contains(&addr)
                                    || opens_a_function(cursors, t))) =>
                    {
                        callees.insert(t);
                        terminated = true;
                    }
                    Some(t) => {
                        followed.insert(t);
                        pending.push((t, Via::Branch));
                    }
                    None => {
                        if let Some(table) =
                            resolve_jump_table(program, bitness, addr, &recorded, &|t| {
                                t >= entry && known.starts.next_after(addr).is_none_or(|s| t < s)
                            })
                        {
                            pending.extend(table.targets.iter().map(|&t| (t, Via::Branch)));
                            if table.picker.is_some() {
                                indexed.insert(addr);
                            }
                            tables.push(ResolvedTable {
                                site: addr,
                                targets: table.targets,
                            });
                        } else {
                            terminated = true;
                        }
                    }
                },
                FlowControl::Call => {
                    let Some(t) = target else {
                        pending.push((next, Via::Fall));
                        continue;
                    };
                    // INVARIANT: a near-call target outside executable,
                    // file-backed memory is not a function: an obfuscated
                    // operand, or a byte of decrypted data read as code, can
                    // encode a call to anywhere in the address space, and
                    // recording it seeds a phantom empty function that nothing
                    // can walk. The call still falls through, so the walk goes
                    // on after it, as phases 2 and 3 gate their seeds.
                    if !super::is_executable_va(program, t) {
                        pending.push((next, Via::Fall));
                        continue;
                    }
                    // SPEC: 32-bit MSVC calls a `__finally` block on the
                    // normal path as the unwinder does on the other: a call a
                    // few bytes forward to code on this function's frame, a
                    // call to a block the scope table names, or a call right
                    // after the trylevel is restored (`mov dword [ebp-4], -2`)
                    // in a function with a scope table; the block is this
                    // function's and returns to the call.
                    let has_seh = !near_handlers.is_empty() || !far_handlers.is_empty();
                    let finally_call = bitness == 32
                        && epilog_helper_name(program, bitness, t).is_none()
                        && (near_handlers.contains(&t)
                            || far_handlers.contains(&t)
                            || (t > addr
                                && t - addr <= FINALLY_REACH
                                && opens_on_frame(program, bitness, t))
                            || (t > addr
                                && t - addr <= FINALLY_CALL_REACH
                                && has_seh
                                && trylevel_at == Some(addr)
                                && !starts.contains(t)
                                && !opens_a_function(cursors, t)));
                    if finally_call {
                        pending.push((t, Via::Branch));
                        pending.push((next, Via::Fall));
                        continue;
                    }
                    callees.insert(t);
                    // INVARIANT: the helper's own arguments, the frame size
                    // and the scope table `push N; push table` hands it, are
                    // no pushes of the frame.
                    let helper_args = frame.pushes.iter().all(|&a| {
                        decode_at(program, bitness, a).is_some_and(|i| is_imm(i.op0_kind()))
                    });
                    if recs.len() <= 2 + frame.pushes.len()
                        && helper_args
                        && frame_helper_name(program, cursors.bitness, t).is_some()
                    {
                        frame.helper_frame = true;
                        frame_helper = Some(t);
                    }
                    arg_consts.extend(call_arg_consts(program, bitness, addr, t, &recorded));
                    registrations.extend(class_registration(program, bitness, addr, &recorded));
                    let start_after = next != entry && starts.contains(next);
                    // INVARIANT: what follows the call is padding or a table (a
                    // relocated word starts one): nothing returns there.
                    let ends_here = start_after
                        || (next != entry
                            && (is_padding(cursors, next)
                                || reloc_sites.is_some_and(|s| s.contains(next))));
                    if start_after {
                        found_noreturn.insert(t);
                    } else if ends_here {
                        found_noreturn_weak.insert(t);
                    }
                    let known = noreturn.contains(t)
                        || thunk_slot(cursors, t).is_some_and(|s| noreturn_slots.contains(&s));
                    if ends_here || known {
                        terminated = true;
                        if !ends_here && unwind_nop(cursors, next) {
                            after_noreturn.push(next);
                        }
                    } else {
                        followed_calls.insert(t);
                        pending.push((next, Via::Fall));
                    }
                }
                FlowControl::IndirectCall => {
                    let slot = (instr.op0_kind() == OpKind::Memory
                        && matches!(instr.memory_base(), Register::None | Register::RIP)
                        && instr.memory_index() == Register::None)
                        .then(|| instr.memory_displacement64());
                    if slot.is_some_and(|s| noreturn_slots.contains(&s)) {
                        terminated = true;
                        if unwind_nop(cursors, next) {
                            after_noreturn.push(next);
                        }
                    } else if reloc_sites.is_some_and(|s| s.contains(next)) {
                        terminated = true;
                    } else {
                        pending.push((next, Via::Fall));
                    }
                }
                FlowControl::Return => {
                    terminated = true;
                    if instr.mnemonic() == Mnemonic::Ret && instr.op_count() == 1 {
                        stack_pop = stack_pop.max(u32::from(instr.immediate16()));
                    }
                }
                FlowControl::Exception => terminated = true,
                // SPEC: `int3` is padding as often as it is a trap and says
                // nothing; any other interrupt is a deliberate end, `int 29h`
                // above all.
                FlowControl::Interrupt => {
                    if instr.mnemonic() != Mnemonic::Int3 {
                        terminated = true;
                    }
                }
                FlowControl::XbeginXabortXend => {
                    if let Some(t) = target {
                        pending.push((t, Via::Branch));
                    }
                    pending.push((next, Via::Fall));
                }
            }
        }
        if in_handlers || handler_roots.is_empty() {
            break;
        }
        in_handlers = true;
        pending.extend(handler_roots.drain(..).map(|r| (r, Via::Branch)));
    }

    // INVARIANT: a `nop` a path reaches was walked with it: MSVC also puts
    // one after calls that return, where a jump joins.
    dedup_sorted(&mut after_noreturn);
    let mut tail_nops = Vec::new();
    for va in after_noreturn {
        if visited.contains(va) || starts.contains(va) {
            continue;
        }
        let Some(nop) = cursors.decode(va) else {
            continue;
        };
        let (print, shape) = fingerprint(&mapped, &nop);
        visited.insert(va);
        recs.push((
            va,
            InstrRec {
                next: nop.next_ip(),
                flow: FlowControl::Next,
                target: None,
                print,
                shape,
            },
        ));
        tail_nops.push(va);
    }
    for (addr, _) in &recs {
        visited.remove(*addr);
    }
    recs.sort_unstable_by_key(|(addr, _)| *addr);
    let blocks = build_blocks(entry, &recs, &tables, &tail_nops);
    let start = recs.first().map_or(entry, |(addr, _)| *addr);
    let end = recs.iter().map(|(_, r)| r.next).max().unwrap_or(entry);
    let body_hash = recs.iter().fold(0xcbf2_9ce4_8422_2325, |h, (addr, r)| {
        let h = mix(h, r.print);
        match r.target {
            Some(t) if (start..end).contains(&t) => mix(h, t.wrapping_sub(*addr)),
            Some(t) => mix(h, t),
            None => h,
        }
    });
    // INVARIANT: a function that is one jump through a slot is that slot,
    // so the slot stays in its fingerprint: left out, every such thunk ran
    // the same code, and `memcpy`'s was called a clone of 24 thunks to
    // other imports.
    let body_hash = match recs.as_slice() {
        [(addr, r)] if r.flow == FlowControl::IndirectBranch => cursors
            .decode(*addr)
            .filter(|i| i.op0_kind() == OpKind::Memory && i.memory_base() == Register::RIP)
            .map_or(body_hash, |i| mix(body_hash, i.memory_displacement64())),
        _ => body_hash,
    };
    let shape_hash = recs
        .iter()
        .fold(0xcbf2_9ce4_8422_2325, |h, (_, r)| mix(h, r.shape));
    let conv = crate::analysis::decompile::lift::conv(program, bitness);
    let func = Function {
        entry,
        start,
        end,
        instr_count: recs.len(),
        blocks,
        callees: callees.into_iter().collect(),
        callers: Vec::new(),
        name: None,
        name_inferred: false,
        name_source: NameSource::None,
        thunk: None,
        funclet: None,
        signature: None,
        body_hash,
        shape_hash,
        returns_value: None,
        ret_width: None,
        ret_partial: None,
        ret_float: None,
        preserves_rax: false,
        hands_back_rdx: false,
        param_hints: BTreeMap::new(),
        ret_hint: None,
        stack_args: frame
            .stack_args(conv.shadow, conv.word)
            .max(stack_pop / u32::try_from(conv.word).unwrap_or(8)),
        stack_pop,
    };
    Walked {
        func,
        recs,
        data_refs,
        tables,
        indexed,
        arg_consts,
        registrations,
        chkstk,
        frame_helper,
        followed,
        followed_calls,
        junk,
        overlong: false,
        terminated,
        fell_into_start,
        unbalanced,
        prologue,
        zero_bytes,
        odd,
        surely_data,
        found_noreturn,
        found_noreturn_weak,
        far_handlers,
        near_handlers,
        bad_entry,
        undoes_frame,
        slot_thunk,
    }
}

/// Names the reference-counting helper a function is, when it is one.
///
/// An intrusive smart pointer's release is the same handful of instructions
/// in every instantiation: load the object, atomically take one off its
/// reference count, destroy it through its vtable when that count reaches
/// zero, and clear the pointer. A template writes one copy per type, so a C++
/// program carries hundreds of them, all unnamed.
///
/// The assignment operator opens with that same release and then stores the
/// new object and adds a reference to it, so the two are told apart by the
/// atomic increment: a release only ever takes one away.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `f` - The candidate function.
///
/// # Returns
///
/// `refcounted_release`, `refcounted_assign`, or `None` when the shape is
/// neither: an exchange-add paired with an indirect call is what marks them.
fn refcount_helper_name(program: &Program, bitness: u32, f: &Function) -> Option<&'static str> {
    let mut takes_one = false;
    let mut adds_one = false;
    let mut destroys = false;
    for b in &f.blocks {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = decode_at(program, bitness, va) else {
                break;
            };
            if i.has_lock_prefix() {
                match i.mnemonic() {
                    Mnemonic::Xadd => takes_one = true,
                    Mnemonic::Inc => adds_one = true,
                    Mnemonic::Add if i.try_immediate(1).is_ok_and(|v| v == 1) => adds_one = true,
                    _ => {}
                }
            }
            destroys |= i.flow_control() == FlowControl::IndirectCall;
            va = i.next_ip();
        }
    }
    if !(takes_one && destroys) {
        return None;
    }
    Some(if adds_one {
        "refcounted_assign"
    } else {
        "refcounted_release"
    })
}

/// Whether a function prints an assertion banner of its own.
///
/// The reporter behind `assert` names itself in the text it prints: Nebula's
/// says `*** NEBULA ASSERTION ***`, the CRT's `Assertion failed`. Reading the
/// literals a function references is what tells it from the thousands of
/// functions that merely call it.
///
/// # Arguments
///
/// * `program` - The loaded image, read for the literals.
/// * `bitness` - Decoder bitness.
/// * `f` - The candidate function.
fn prints_assert_banner(program: &Program, bitness: u32, f: &Function) -> bool {
    /// Longest banner read.
    const CAP: usize = 64;
    /// Shortest run accepted, so a stray byte pair is not a banner.
    const MIN: usize = 6;
    for b in &f.blocks {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = decode_at(program, bitness, va) else {
                break;
            };
            let refs = [i.memory_displacement64(), i.immediate64()];
            if refs.iter().any(|addr| {
                *addr != 0
                    && crate::strings::cstr_at(program, *addr, MIN, CAP)
                        .is_some_and(|(_, t)| t.to_ascii_lowercase().contains("assert"))
            }) {
                return true;
            }
            va = i.next_ip();
        }
    }
    false
}

/// The `__except` filters and handlers of the 32-bit SEH scope table at
/// `table`, when one is there.
///
/// A frame pushes its table's address, to `__SEH_prolog4` or into its own
/// registration. An `EH4` table opens with four cookie offsets, each a
/// small negative frame offset (`-2` for no cookie) or a small XOR
/// adjustment, then records `{enclosing level, filter, handler}`: the
/// first outermost (`-2`), each later one enclosed by an earlier, and a
/// `__finally` with no filter. The blocks they name are reached from no
/// instruction, so without the table a walk never decodes them and a
/// guess later takes each for a function of its own. The header is held
/// to that shape so that some other table is not read as one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - The pushed address.
/// * `entry` - The pushing function's entry, whose section its handlers
///   share.
///
/// # Returns
///
/// The filters and handlers in record order, empty when `table` does not
/// hold a scope table.
fn seh_scope_roots(program: &Program, table: u64, entry: u64) -> Vec<u64> {
    /// Most records read from one table.
    const RECORDS_MAX: u64 = 64;
    /// Largest frame offset or XOR adjustment a cookie field holds.
    const FRAME_MAX: i32 = 0x1_0000;
    /// The outermost enclosing level, and the no-cookie offset.
    const TOPMOST: u32 = 0xffff_fffe;
    let Some(home) = program.section_at(entry).map(|s| s.va.0) else {
        return Vec::new();
    };
    let word = |va: u64| read_u32(program, va);
    let Some(header) = (0..4)
        .map(|k| word(table + 4 * k).map(u32::cast_signed))
        .collect::<Option<Vec<i32>>>()
    else {
        return Vec::new();
    };
    let offset = |v: i32| v == TOPMOST.cast_signed() || (-FRAME_MAX..0).contains(&v);
    let adjust = |v: i32| (-FRAME_MAX..FRAME_MAX).contains(&v);
    if !(offset(header[0]) && adjust(header[1]) && offset(header[2]) && adjust(header[3])) {
        return Vec::new();
    }
    let code = |va: u32| {
        let va = u64::from(va);
        super::is_executable_va(program, va)
            && program.section_at(va).is_some_and(|s| s.va.0 == home)
            && plausible_entry(program, 32, va)
    };
    let mut roots = Vec::new();
    for k in 0..RECORDS_MAX {
        let at = table + 16 + 12 * k;
        let (Some(level), Some(filter), Some(handler)) = (word(at), word(at + 4), word(at + 8))
        else {
            break;
        };
        let enclosed = if k == 0 {
            level == TOPMOST
        } else {
            level == TOPMOST || u64::from(level) < k
        };
        if !enclosed || !code(handler) || (filter != 0 && !code(filter)) {
            break;
        }
        if filter != 0 {
            roots.push(u64::from(filter));
        }
        roots.push(u64::from(handler));
    }
    roots
}

/// Names the MSVC prologue helper at `va` by its first two instructions.
///
/// `__SEH_prolog4` opens with `push -1; push eax`, or, as later CRTs build
/// it, with `push __except_handler4; push dword [fs:0]`, and `__EH_prolog3`
/// with `push eax; push dword [fs:0]`: each pushes the caller's exception
/// registration, points `ebp` one word below the entry stack pointer and
/// returns with the stack lower than it found it, which is why a caller's
/// `[ebp+8]` is its first argument only when the helper's effect is known.
/// The names are the CRT's own; the `_GS` and `_catch` variants share the
/// opening and the frame effect and are not told apart.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The callee's entry.
///
/// # Returns
///
/// The helper's name, or `None` when the code at `va` does not open like one.
pub(crate) fn frame_helper_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let pushes_reg = |i: &Instruction, r: Register| {
        i.mnemonic() == Mnemonic::Push
            && i.op0_kind() == OpKind::Register
            && i.op0_register().full_register() == r
    };
    let pushes_minus_one = first.mnemonic() == Mnemonic::Push
        && matches!(
            first.op0_kind(),
            OpKind::Immediate8to32 | OpKind::Immediate32
        )
        && first.immediate(0) & 0xffff_ffff == 0xffff_ffff;
    let pushes_fs0 = second.mnemonic() == Mnemonic::Push
        && second.op0_kind() == OpKind::Memory
        && second.segment_prefix() == Register::FS
        && second.memory_base() == Register::None
        && second.memory_displacement64() == 0;
    let pushes_handler =
        first.mnemonic() == Mnemonic::Push && first.op0_kind() == OpKind::Immediate32;
    if (pushes_minus_one && pushes_reg(&second, Register::RAX)) || (pushes_handler && pushes_fs0) {
        Some("__SEH_prolog4")
    } else if pushes_reg(&first, Register::RAX) && pushes_fs0 {
        Some("__EH_prolog3")
    } else {
        None
    }
}

/// Names the MSVC epilogue helper at `va` by its first two instructions.
///
/// `__SEH_epilog4` opens with `mov ecx, [ebp-0x10]; mov fs:[0], ecx` and
/// `__EH_epilog3` with `mov ecx, [ebp-0xc]; mov fs:[0], ecx`: each unlinks
/// the caller's exception registration, restores the registers the
/// prologue helper saved, tears the frame down and returns to the
/// caller's return address, which it pops and pushes back around the
/// work. The names are the CRT's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The callee's entry.
///
/// # Returns
///
/// The helper's name, or `None` when the code at `va` does not open like one.
pub(crate) fn epilog_helper_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let loads_link = first.mnemonic() == Mnemonic::Mov
        && first.op0_kind() == OpKind::Register
        && first.op0_register().full_register() == Register::RCX
        && first.op1_kind() == OpKind::Memory
        && first.memory_base().full_register() == Register::RBP
        && first.memory_index() == Register::None;
    let unlinks = second.mnemonic() == Mnemonic::Mov
        && second.op0_kind() == OpKind::Memory
        && second.segment_prefix() == Register::FS
        && second.memory_base() == Register::None
        && second.memory_displacement64() == 0
        && second.op1_kind() == OpKind::Register
        && second.op1_register().full_register() == Register::RCX;
    if !(loads_link && unlinks) {
        return None;
    }
    match crate::disasm::displacement(&first, bitness) {
        -0x10 => Some("__SEH_epilog4"),
        -0xc => Some("__EH_epilog3"),
        _ => None,
    }
}

/// Names the `/GS` cookie check at `va` by its first three instructions.
///
/// `__security_check_cookie` compares its argument with the cookie
/// global and jumps to the failure report when they differ: on x64 `cmp
/// rcx, [cookie]; jne fail; rol rcx, 16` (its second test checks the top
/// word is clear), on x86 `cmp ecx, [cookie]; jne fail; ret`. A function of
/// that shape returns its argument register and every other one as it
/// found them, which the decompiler reads it by. The name is the CRT's
/// own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The function's entry.
///
/// # Returns
///
/// The checker's name, or `None` when the code at `va` does not open like
/// one.
pub(crate) fn cookie_check_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let third = decode_at(program, bitness, second.next_ip())?;
    let arg = if bitness == 64 {
        Register::RCX
    } else {
        Register::ECX
    };
    let compares = first.mnemonic() == Mnemonic::Cmp
        && first.op0_kind() == OpKind::Register
        && first.op0_register() == arg
        && first.op1_kind() == OpKind::Memory
        && matches!(
            first.memory_base(),
            Register::None | Register::RIP | Register::EIP
        )
        && first.memory_index() == Register::None
        && first.segment_prefix() == Register::None;
    let differs = second.flow_control() == FlowControl::ConditionalBranch
        && second.condition_code() == ConditionCode::ne;
    let then = if bitness == 64 {
        third.mnemonic() == Mnemonic::Rol
            && third.op0_kind() == OpKind::Register
            && third.op0_register() == Register::RCX
    } else {
        third.flow_control() == FlowControl::Return
    };
    (compares && differs && then).then_some("__security_check_cookie")
}

/// Names a Rust panic entry at `va` by the message it formats.
///
/// A panic entry (`core::panicking::panic_bounds_check`, the
/// `panic_const_*` family, `core::option::unwrap_failed`, the slice
/// index failures) is a few instructions that load the address of its
/// message, or of a format template whose first byte is the literal's
/// length, and call on into the panic machinery without returning. A
/// small function of that shape whose one message is one of
/// [`PANIC_MESSAGES`] is that entry; the names are the standard
/// library's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The function's entry.
/// * `count` - Its instruction count.
///
/// # Returns
///
/// The entry's name, or `None` when the function returns, loads no
/// message, or more than one.
pub(crate) fn panic_helper_name(
    program: &Program,
    bitness: u32,
    va: u64,
    count: usize,
) -> Option<&'static str> {
    /// Bytes read at a loaded address, enough for the longest message.
    const READ: usize = 72;
    let mut at = va;
    let mut found = None;
    for _ in 0..count {
        let i = decode_at(program, bitness, at)?;
        if i.flow_control() == FlowControl::Return {
            return None;
        }
        if i.mnemonic() == Mnemonic::Lea
            && i.op1_kind() == OpKind::Memory
            && i.memory_base() == Register::RIP
            && let Some(bytes) = program.read_va_upto(i.memory_displacement64(), READ)
        {
            let says = |m: &str| {
                bytes.starts_with(m.as_bytes())
                    || bytes.get(1..).is_some_and(|b| b.starts_with(m.as_bytes()))
            };
            if let Some((_, name)) = PANIC_MESSAGES.iter().find(|(m, _)| says(m)) {
                if found.is_some_and(|f| f != *name) {
                    return None;
                }
                found = Some(*name);
            }
        }
        at = i.next_ip();
    }
    found
}

/// Most distinct values kept for one parameter.
///
/// A parameter every caller sets to a different number is not an enumeration
/// and listing its values says nothing; one set from a handful of constants
/// is a set of cases a reader can act on.
const PARAM_VALUES_MAX: usize = 12;

/// Longest run of instructions searched back from a call for its arguments.
const ARG_SETUP_MAX: usize = 32;

/// The straight-line instructions leading into `call_va`, in address order.
///
/// At most [`ARG_SETUP_MAX`] of them, walked back through the records as
/// long as each has exactly one predecessor that falls through.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
fn straight_line_before(
    program: &Program,
    bitness: u32,
    call_va: u64,
    recorded: &Recorded,
) -> Vec<Instruction> {
    let mut window: Vec<Instruction> = Vec::new();
    let mut cur = call_va;
    while window.len() < ARG_SETUP_MAX {
        let Some(prev) = recorded.only_before(cur) else {
            break;
        };
        let Some(i) = decode_at(program, bitness, prev) else {
            break;
        };
        if i.flow_control() != FlowControl::Next {
            break;
        }
        window.push(i);
        cur = prev;
    }
    window.reverse();
    window
}

/// Reads the constants a call site puts in the argument registers.
///
/// Walks back from the call over at most [`ARG_SETUP_MAX`] instructions,
/// keeping for each argument register the last constant written to it and
/// forgetting the register when anything else writes it. `xor r, r` counts
/// as zero, which is how a compiler writes it.
///
/// # Arguments
///
/// * `program` - The loaded image, for the calling convention.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `callee` - The call's target.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
///
/// # Returns
///
/// One constant per argument register holding one the call did not
/// overwrite.
fn call_arg_consts(
    program: &Program,
    bitness: u32,
    call_va: u64,
    callee: u64,
    recorded: &Recorded,
) -> Vec<ArgConst> {
    let args = crate::analysis::decompile::lift::conv(program, bitness).args;
    let window = straight_line_before(program, bitness, call_va, recorded);
    let mut held: BTreeMap<Register, Option<u64>> = BTreeMap::new();
    for i in &window {
        if i.op0_kind() != OpKind::Register {
            continue;
        }
        let r = i.op0_register().full_register();
        if !args.contains(&r) {
            continue;
        }
        let value = match i.mnemonic() {
            Mnemonic::Mov if i.op1_kind() != OpKind::Register && i.op1_kind() != OpKind::Memory => {
                Some(i.immediate(1))
            }
            Mnemonic::Xor
                if i.op1_kind() == OpKind::Register && i.op1_register().full_register() == r =>
            {
                Some(0)
            }
            _ => None,
        };
        held.insert(r, value);
    }
    held.into_iter()
        .filter_map(|(r, v)| {
            let slot = u8::try_from(args.iter().position(|a| *a == r)?).ok()?;
            Some(ArgConst {
                callee,
                slot,
                value: v?,
            })
        })
        .collect()
}

/// Reads a class registration from a call site.
///
/// A registrar is handed the class's name and the four-character code that
/// identifies it on the wire, and the code is what a message's format is
/// useless without: with it, `Commands::ActivateGodModeCommand` is `GMTg`
/// and its encoder's `1 bit, 32 bits` is a packet a reader can find. The
/// second argument must be a readable name and the third a constant whose
/// four bytes are all printable.
///
/// # Arguments
///
/// * `program` - The loaded image, for reading the name.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
///
/// # Returns
///
/// The class name and its code.
fn class_registration(
    program: &Program,
    bitness: u32,
    call_va: u64,
    recorded: &Recorded,
) -> Option<Registration> {
    let args = crate::analysis::decompile::lift::conv(program, bitness).args;
    let (name_reg, code_reg) = (*args.get(1)?, *args.get(2)?);
    let window = straight_line_before(program, bitness, call_va, recorded);
    let (mut name_at, mut code) = (None, None);
    for i in &window {
        if i.op0_kind() != OpKind::Register {
            continue;
        }
        let r = i.op0_register().full_register();
        if r == name_reg && i.mnemonic() == Mnemonic::Lea && i.memory_base() == Register::RIP {
            name_at = Some(i.memory_displacement64());
        } else if r == code_reg
            && i.mnemonic() == Mnemonic::Mov
            && i.op_count() > 1
            && !matches!(i.op1_kind(), OpKind::Register | OpKind::Memory)
        {
            code = u32::try_from(i.immediate(1)).ok();
        }
    }
    let code = code.filter(|c| c.to_be_bytes().iter().all(|b| (0x20..0x7f).contains(b)))?;
    let (_, name) = crate::strings::cstr_at(program, name_at?, 3, CLASS_NAME_MAX)?;
    name.chars()
        .all(|c| c.is_ascii_alphanumeric() || "_:<>, ".contains(c))
        .then_some(Registration { class: name, code })
}

/// Longest class name read from a registration.
const CLASS_NAME_MAX: usize = 96;

/// Tells whether the code at `va` is padding a call never returns into.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - The address after a call.
///
/// # Returns
///
/// `true` when `va` does not decode, or decodes as `int3` or `ud2`.
fn is_padding(cursors: &mut Cursors<'_>, va: u64) -> bool {
    cursors.decode(va).is_none_or(|i| {
        i.code() == Code::INVALID || matches!(i.mnemonic(), Mnemonic::Int3 | Mnemonic::Ud2)
    })
}

/// Where a far `__except` handler lands when it restores a few registers
/// and jumps near its function.
///
/// PGO keeps the handler's few instructions cold and the block they jump
/// to, a `__finally` the normal path also calls, with the function.
///
/// # Arguments
///
/// * `cursors` - Decode cursors over the image.
/// * `root` - The handler.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The jump's target when the handler's first instructions reach one
/// within [`HANDLER_REACH`] of `entry`.
fn handler_lands_near(cursors: &mut Cursors<'_>, root: u64, entry: u64) -> Option<u64> {
    /// Most instructions a handler restores registers with before it jumps.
    const LEAD_MAX: usize = 6;
    let mut at = root;
    for _ in 0..LEAD_MAX {
        let i = cursors.decode(at)?;
        match i.flow_control() {
            FlowControl::Next if i.mnemonic() == Mnemonic::Mov => at = i.next_ip(),
            FlowControl::UnconditionalBranch => {
                let t = near_target(&i)?;
                return (t.abs_diff(entry) <= HANDLER_REACH).then_some(t);
            }
            _ => return None,
        }
    }
    None
}

/// Tells whether `va`, after a call that does not return, holds an x64 `nop`.
///
/// MSVC puts one there when the call would end the function: the return
/// address the unwinder looks up then still lies inside the function, and
/// the byte is the function's.
///
/// # Arguments
///
/// * `cursors` - Decode cursors over the image.
/// * `va` - The address after the call.
fn unwind_nop(cursors: &mut Cursors<'_>, va: u64) -> bool {
    cursors.bitness == 64
        && cursors
            .decode(va)
            .is_some_and(|i| i.mnemonic() == Mnemonic::Nop && i.len() == 1)
}

/// Whether `instr` is `lea r, [r]`, the multi-byte nop an assembler pads
/// with (`lea esp, [esp+0]`, `lea ecx, [ecx+0]`).
///
/// # Arguments
///
/// * `instr` - The instruction.
fn lea_nop(instr: &Instruction) -> bool {
    instr.mnemonic() == Mnemonic::Lea
        && instr.op0_kind() == OpKind::Register
        && instr.memory_base() == instr.op0_register()
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
}

/// Returns where the run of padding starting at `va` ends.
///
/// Padding is what a linker aligns with: `int3` bytes, or any of the `nop`
/// forms (`90`, `66 90`, `0f 1f ..`, with `66` and `2e` prefixes). A byte
/// that opens neither ends the run at once.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - Where the run may start.
/// * `hi` - One past the last byte to consider.
///
/// # Returns
///
/// The first address past the run; `va` itself when nothing pads there.
fn padding_end(program: &Program, bitness: u32, va: u64, hi: u64) -> u64 {
    let mut cur = va;
    while cur < hi {
        let Some(i) = decode_at(program, bitness, cur) else {
            break;
        };
        if i.code() == Code::INVALID
            || !(matches!(i.mnemonic(), Mnemonic::Int3 | Mnemonic::Nop) || lea_nop(&i))
        {
            break;
        }
        cur = i.next_ip().min(hi);
    }
    cur
}

/// Tells whether the seed trace is on.
///
/// `BORER_TRACE_SEEDS` set in the environment prints every guessed seed
/// and what became of it to stderr, which is how the guess rules are tuned
/// against a binary with a known answer.
fn trace_seeds() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("BORER_TRACE_SEEDS").is_some())
}

/// What an instruction does to a function's frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FrameStep {
    /// A callee-saved `push` or `sub rsp, N`: the frame is being set up.
    Opens,
    /// The matching `pop`, `add rsp, N` or `leave`: the frame is torn down.
    Closes,
}

/// Tells whether `instr` adds an immediate to the stack pointer or takes
/// one from it: `sub rsp, N` and `add rsp, N` in any width.
///
/// Every reader of the frame goes through here, so they agree on the
/// widths: the decoder gives `sub esp, 8` an [`OpKind::Immediate8to32`],
/// and that is as much a frame as the [`OpKind::Immediate8to64`] it gives
/// `sub rsp, 8`.
///
/// # Arguments
///
/// * `instr` - The decoded instruction, a `sub` or an `add`.
fn moves_rsp_by_imm(instr: &Instruction) -> bool {
    instr.op0_kind() == OpKind::Register
        && instr.op0_register().full_register() == Register::RSP
        && is_imm(instr.op1_kind())
}

/// Tells whether `instr` opens or closes a frame.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
///
/// # Returns
///
/// [`FrameStep::Opens`] for a callee-saved push or `sub rsp, N`;
/// [`FrameStep::Closes`] for the matching pop, `add rsp, N` or `leave`;
/// `None` for anything else. An `add rsp` right after a call cleans
/// arguments in 32-bit code, but by then the frame has long been opened,
/// so it cannot be told apart from teardown here and need not be.
fn frame_step(instr: &Instruction) -> Option<FrameStep> {
    let saved = |r: Register| {
        matches!(
            r.full_register(),
            Register::RBX
                | Register::RBP
                | Register::RSI
                | Register::RDI
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        )
    };
    let on_rsp = moves_rsp_by_imm(instr);
    match instr.mnemonic() {
        Mnemonic::Push if instr.op0_kind() == OpKind::Register && saved(instr.op0_register()) => {
            Some(FrameStep::Opens)
        }
        Mnemonic::Sub if on_rsp => Some(FrameStep::Opens),
        Mnemonic::Pop if instr.op0_kind() == OpKind::Register && saved(instr.op0_register()) => {
            Some(FrameStep::Closes)
        }
        Mnemonic::Add if on_rsp => Some(FrameStep::Closes),
        Mnemonic::Leave => Some(FrameStep::Closes),
        _ => None,
    }
}

/// Tells whether `va` opens the way a function opens.
///
/// A jump to such an address is a tail call. On x64 the frame is taken
/// once, at the entry: an argument homed to its slot, a callee-saved push,
/// a `sub rsp, N` never appear in the middle of a function, so any of them
/// at a jump target says the target is another function. 32-bit code pushes
/// in its middle to pass arguments, so only the shapes no argument push
/// makes are believed there: `push ebp; mov ebp, esp`, the hotpatch
/// `mov edi, edi`, `sub esp, N` then a register saved or the cookie
/// loaded, an `endbr32`, or a thunk's `jmp [slot]`.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - The jump target.
fn opens_a_function(cursors: &mut Cursors<'_>, va: u64) -> bool {
    let Some(first) = cursors.decode(va) else {
        return false;
    };
    if first.code() == Code::INVALID {
        return false;
    }
    if cursors.bitness == 64 {
        return prologue_like(&first);
    }
    let is = |i: &Instruction, r: Register| {
        i.op0_kind() == OpKind::Register && i.op0_register().full_register() == r
    };
    match first.mnemonic() {
        Mnemonic::Push if is(&first, Register::RBP) => {
            cursors.decode(first.next_ip()).is_some_and(|second| {
                second.mnemonic() == Mnemonic::Mov
                    && is(&second, Register::RBP)
                    && second.op1_kind() == OpKind::Register
                    && second.op1_register().full_register() == Register::RSP
            })
        }
        // SPEC: an SEH frame opens `push N; push offset scopetable; call
        // __SEH_prolog4`.
        Mnemonic::Push
            if matches!(
                first.op0_kind(),
                OpKind::Immediate8to32 | OpKind::Immediate32
            ) =>
        {
            let program = cursors.program;
            let bitness = cursors.bitness;
            let Some(second) = cursors.decode(first.next_ip()) else {
                return false;
            };
            if second.mnemonic() != Mnemonic::Push
                || second.op0_kind() != OpKind::Immediate32
                || seh_scope_roots(program, u64::from(second.immediate32()), va).is_empty()
            {
                return false;
            }
            cursors.decode(second.next_ip()).is_some_and(|third| {
                third.flow_control() == FlowControl::Call
                    && near_target(&third)
                        .is_some_and(|t| frame_helper_name(program, bitness, t).is_some())
            })
        }
        Mnemonic::Mov => {
            first.op0_kind() == OpKind::Register
                && first.op1_kind() == OpKind::Register
                && first.op0_register() == first.op1_register()
        }
        // SPEC: a frame without `ebp` opens `sub esp, N` and then saves a
        // register or loads the stack cookie; `sub esp, 8` in the middle
        // makes room for a `double` argument and is followed by its store.
        Mnemonic::Sub => {
            is(&first, Register::RSP)
                && first.op1_kind() != OpKind::Register
                && cursors.decode(first.next_ip()).is_some_and(|second| {
                    let saves = second.mnemonic() == Mnemonic::Push
                        && second.op0_kind() == OpKind::Register
                        && matches!(
                            second.op0_register().full_register(),
                            Register::RBX | Register::RSI | Register::RDI | Register::RBP
                        );
                    let cookie = second.mnemonic() == Mnemonic::Mov
                        && second.op1_kind() == OpKind::Memory
                        && second.memory_base() == Register::None
                        && second.memory_index() == Register::None;
                    saves || cookie
                })
        }
        Mnemonic::Endbr32 => true,
        Mnemonic::Jmp => first.op0_kind() == OpKind::Memory,
        _ => false,
    }
}

/// Tells whether `instr` is one a function opens with.
///
/// A callee-saved register pushed, an argument register homed to its stack
/// slot, the frame taken with `sub rsp, N`, `mov rax, rsp` before a big
/// frame, the hotpatch `mov edi, edi`, an `endbr`, or the `jmp` of a
/// thunk. A leaf that opens with its work (`xor eax, eax; ret`) is not
/// recognized here, and is found by the call or the pointer that names it.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
fn prologue_like(instr: &Instruction) -> bool {
    let op0_reg = instr.op0_kind() == OpKind::Register;
    let op1_reg = instr.op1_kind() == OpKind::Register;
    match instr.mnemonic() {
        Mnemonic::Push => {
            op0_reg
                && matches!(
                    instr.op0_register().full_register(),
                    Register::RBX
                        | Register::RBP
                        | Register::RSI
                        | Register::RDI
                        | Register::RCX
                        | Register::R12
                        | Register::R13
                        | Register::R14
                        | Register::R15
                )
        }
        Mnemonic::Mov => {
            // SPEC: the x64 prologue homes an argument register or parks a
            // nonvolatile one in the four home slots, [rsp+8] to [rsp+20h].
            // A store of a volatile register, or to any other slot, is the
            // middle of a function spilling a local.
            let homing = instr.op0_kind() == OpKind::Memory
                && instr.memory_base().full_register() == Register::RSP
                && instr.memory_index() == Register::None
                && matches!(instr.memory_displacement64(), 0x8 | 0x10 | 0x18 | 0x20)
                && op1_reg
                && matches!(
                    instr.op1_register().full_register(),
                    Register::RCX
                        | Register::RDX
                        | Register::R8
                        | Register::R9
                        | Register::RBX
                        | Register::RBP
                        | Register::RSI
                        | Register::RDI
                        | Register::R12
                        | Register::R13
                        | Register::R14
                        | Register::R15
                );
            let frame_copy =
                op0_reg && op1_reg && instr.op1_register().full_register() == Register::RSP;
            let hotpatch = op0_reg && op1_reg && instr.op0_register() == instr.op1_register();
            homing || frame_copy || hotpatch
        }
        Mnemonic::Sub => moves_rsp_by_imm(instr),
        Mnemonic::Endbr64 | Mnemonic::Endbr32 | Mnemonic::Jmp => true,
        _ => false,
    }
}

/// Names a mnemonic for the seed trace, as `decoded <mnemonic>`.
///
/// A handful of names cover what the trace has ever shown; the rest share
/// one line rather than allocate for a diagnostic.
///
/// # Arguments
///
/// * `m` - The mnemonic.
fn mnemonic_name(m: Mnemonic) -> &'static str {
    match m {
        Mnemonic::In => "decoded in",
        Mnemonic::Out => "decoded out",
        Mnemonic::Hlt => "decoded hlt",
        Mnemonic::Cli | Mnemonic::Sti => "decoded cli/sti",
        Mnemonic::Int => "decoded int N",
        Mnemonic::Xlatb => "decoded xlatb",
        Mnemonic::Ud0 | Mnemonic::Ud1 => "decoded ud0/ud1",
        Mnemonic::Add => "decoded add [..], r8 (zero bytes)",
        Mnemonic::Jmp | Mnemonic::Call => "decoded a far transfer",
        _ => {
            "decoded an instruction no compiler emits (a segment override, a BCD adjust, a descriptor load)"
        }
    }
}

/// Tells whether a relocation site lies inside `instr` anywhere but at its
/// displacement or an immediate, where the address the loader patches sits.
///
/// # Arguments
///
/// * `cursors` - The decoders, one of which decoded `instr` last.
/// * `sites` - The relocation sites.
/// * `instr` - The instruction.
fn misplaced_site(cursors: &Cursors<'_>, sites: &AddrSet, instr: &Instruction) -> bool {
    let start = instr.ip();
    let inside = || (start + 1..instr.next_ip()).filter(|va| sites.contains(*va));
    if inside().next().is_none() {
        return false;
    }
    let Some(offsets) = cursors.constant_offsets(instr) else {
        return true;
    };
    let patched = |va: u64| {
        let off = usize::try_from(va - start).unwrap_or(usize::MAX);
        (offsets.has_displacement()
            && off == offsets.displacement_offset()
            && offsets.displacement_size() >= 4)
            || (offsets.has_immediate()
                && off == offsets.immediate_offset()
                && offsets.immediate_size() >= 4)
            || (offsets.has_immediate2()
                && off == offsets.immediate_offset2()
                && offsets.immediate_size2() >= 4)
    };
    inside().any(|va| !patched(va))
}

/// Tells whether `instr` adds a byte register into memory other than the
/// way two zero bytes do, `add [eax], al`: rare in code, but written.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
fn byte_add(instr: &Instruction) -> bool {
    instr.code() == Code::Add_rm8_r8
        && !(instr.op0_kind() == OpKind::Memory
            && instr.memory_base().full_register() == Register::RAX
            && instr.memory_index() == Register::None
            && instr.memory_displacement64() == 0
            && instr.op1_register() == Register::AL)
}

/// Tells whether `instr` is one no compiler emits into a program.
///
/// Data read as code decodes into these: `add [..], r8`, the opcode zero
/// that a run of zero bytes makes, port and descriptor-table instructions,
/// the BCD adjusts, far transfers, and interrupts other than the ones
/// Windows and Linux use. One of them in a walk from a guessed seed is the
/// clearest sign the seed was data; the same rule is what the disassemblers
/// with the best measured precision apply to their pattern hits.
///
/// A `nop` is left out even with a `cs` prefix, because that is exactly how
/// an aligning `nop` inside a function is written.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
/// * `bitness` - Decoder bitness; segment overrides mean nothing in 64-bit
///   code and no compiler writes them there.
/// * `pe` - The program is a PE, whose interrupts are Windows' and not
///   Linux's.
fn odd_instruction(instr: &Instruction, bitness: u32, pe: bool) -> bool {
    use crate::isa::x86::Mnemonic as M;
    if instr.code() == Code::Add_rm8_r8 {
        return true;
    }
    if matches!(
        instr.mnemonic(),
        M::In
            | M::Out
            | M::Insb
            | M::Insw
            | M::Insd
            | M::Outsb
            | M::Outsw
            | M::Outsd
            | M::Hlt
            | M::Cli
            | M::Sti
            | M::Clts
            | M::Lgdt
            | M::Lidt
            | M::Lldt
            | M::Ltr
            | M::Sgdt
            | M::Sidt
            | M::Aaa
            | M::Aad
            | M::Aam
            | M::Aas
            | M::Daa
            | M::Das
            | M::Arpl
            | M::Bound
            | M::Lds
            | M::Les
            | M::Into
            | M::Iret
            | M::Iretd
            | M::Iretq
            | M::Retf
            | M::Lss
            | M::Lfs
            | M::Lgs
            | M::Lar
            | M::Lsl
            | M::Rsm
            | M::Int1
            | M::Xlatb
            | M::Rdmsr
            | M::Wrmsr
            | M::Ud0
            | M::Ud1
    ) {
        return true;
    }
    // SPEC: `push es`, `pop ds` touch the segment registers no compiled
    // code touches.
    if matches!(instr.mnemonic(), M::Push | M::Pop)
        && instr.op0_kind() == OpKind::Register
        && matches!(
            instr.op0_register(),
            Register::ES | Register::CS | Register::SS | Register::DS
        )
    {
        return true;
    }
    if instr.mnemonic() == M::Int {
        // SPEC: `int 3` is a trap, `int 29h` is Windows' `__fastfail`,
        // `int 2ch`/`2dh` its assertion and debug services, `int 2eh` its
        // system call when `syscall` is not used, `int 80h` the Linux
        // system call; anything else is a byte that decodes.
        let n = instr.immediate8();
        return if pe {
            !matches!(n, 3 | 0x29 | 0x2c | 0x2d | 0x2e)
        } else {
            !matches!(n, 3 | 0x80)
        };
    }
    // SPEC: `ret N` pops arguments: a multiple of four, and never pages of
    // them.
    if instr.mnemonic() == M::Ret && instr.op_count() == 1 {
        let n = instr.immediate16();
        if !n.is_multiple_of(4) || n > 0x1000 {
            return true;
        }
    }
    if matches!(
        instr.code(),
        Code::Jmp_ptr1616 | Code::Jmp_ptr1632 | Code::Call_ptr1616 | Code::Call_ptr1632
    ) {
        return true;
    }
    bitness == 64
        && instr.mnemonic() != M::Nop
        && matches!(
            instr.segment_prefix(),
            Register::CS | Register::DS | Register::ES | Register::SS
        )
}

/// Returns where the run of `int3` bytes starting at `va` ends.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Where the run may start.
/// * `hi` - One past the last byte to consider.
///
/// # Returns
///
/// The first address past the run; `va` itself when no `int3` is there.
fn int3_end(program: &Program, va: u64, hi: u64) -> u64 {
    let mut cur = va;
    while cur < hi && program.read_va(cur, 1) == Some(&[0xcc][..]) {
        cur += 1;
    }
    cur
}

/// Returns the import slot a thunk at `va` jumps through.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - A call target.
///
/// # Returns
///
/// The slot address when the first instruction (after an optional `endbr64`)
/// is `jmp [slot]` with a rip-relative or absolute operand, else `None`.
fn thunk_slot(cursors: &mut Cursors<'_>, va: u64) -> Option<u64> {
    let mut instr = cursors.decode(va)?;
    if matches!(instr.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
        instr = cursors.decode(instr.next_ip())?;
    }
    slot_jump(&instr)
}

/// The slot `instr` jumps through when it is `jmp [slot]` with a
/// rip-relative or absolute operand.
///
/// # Arguments
///
/// * `instr` - The instruction.
fn slot_jump(instr: &Instruction) -> Option<u64> {
    if instr.mnemonic() != Mnemonic::Jmp || instr.op0_kind() != OpKind::Memory {
        return None;
    }
    if !matches!(instr.memory_base(), Register::None | Register::RIP)
        || instr.memory_index() != Register::None
    {
        return None;
    }
    Some(instr.memory_displacement64())
}

/// Decodes the instruction at `va`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - Address of the instruction.
///
/// # Returns
///
/// The instruction (possibly with [`Code::INVALID`]), or `None` when `va` is
/// not in executable, file-backed memory.
pub(crate) fn decode_at(program: &Program, bitness: u32, va: u64) -> Option<Instruction> {
    if !super::is_executable_va(program, va) {
        return None;
    }
    let bytes = program.read_va_upto(va, 15)?;
    let mut decoder = Decoder::with_ip(bitness, bytes, va, DecoderOptions::NONE);
    let mut instr = Instruction::default();
    decoder.decode_out(&mut instr);
    Some(instr)
}

/// Decodes one block with one decoder over its bytes, stopping at the
/// first instruction that does not decode.
///
/// # Arguments
///
/// * `program` - The image.
/// * `bitness` - 32 or 64.
/// * `blk` - The block.
///
/// # Returns
///
/// The instructions in address order; empty when the block's bytes are not
/// file-backed.
pub(crate) fn decode_block(program: &Program, bitness: u32, blk: &BasicBlock) -> Vec<Instruction> {
    let len = usize::try_from(blk.end.saturating_sub(blk.start)).unwrap_or(0);
    let Some(bytes) = program.read_va_upto(blk.start, len) else {
        return Vec::new();
    };
    let mut decoder = Decoder::with_ip(bitness, bytes, blk.start, DecoderOptions::NONE);
    let mut instrs = Vec::new();
    while decoder.can_decode() {
        let i = decoder.decode();
        if i.is_invalid() {
            break;
        }
        instrs.push(i);
    }
    instrs
}

/// Tells whether the call that ends a block never returns, though the block
/// still names the address after it, outside its function, as where it
/// goes on.
///
/// The walk ends a function at a call it knows never returns, and keeps
/// the address after the call as the block's successor; a text that then
/// writes the jump there, `goto *0x140001527;`, sends the reader into the
/// `int3` padding after `_CxxThrowException`. The call ends the path when
/// what follows it is padding (`int3`, `ud2`, bytes that do not decode,
/// Rust's `call; ud2` after a panic), another function's entry, or when the
/// callee, or the import it jumps or calls through, is a function that never
/// returns by name ([`is_noreturn_name`]).
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the next entry and the callee's name.
/// * `b` - The block, whose successors the caller found outside its
///   function.
///
/// # Returns
///
/// `true` for a call block whose call does not return; `false` for any
/// other block.
pub(crate) fn call_ends_path(program: &Program, analysis: &Analysis, b: &BasicBlock) -> bool {
    if b.term != BlockTerm::Call {
        return false;
    }
    let Some(bitness) = program.arch.bitness() else {
        return false;
    };
    let after = b.end;
    let padding = decode_at(program, bitness, after).is_none_or(|i| {
        i.code() == Code::INVALID || matches!(i.mnemonic(), Mnemonic::Int3 | Mnemonic::Ud2)
    });
    let entry = analysis.function(after).is_some_and(|g| g.entry == after);
    padding || entry || calls_noreturn(program, analysis, bitness, b)
}

/// Tells whether the last instruction of a block calls a function that
/// never returns by name: a direct callee, the import a thunk it reaches
/// jumps through, or the import slot it calls through.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the callee's name.
/// * `bitness` - 32 or 64.
/// * `b` - The block.
fn calls_noreturn(program: &Program, analysis: &Analysis, bitness: u32, b: &BasicBlock) -> bool {
    let Some(call) = decode_block(program, bitness, b).pop() else {
        return false;
    };
    let named =
        |name: &str| is_noreturn_name(super::bare_name(&crate::search::demangled_name(name)));
    let import = |slot: u64| {
        program.symbols.iter().any(|s| {
            s.kind == crate::program::SymbolKind::Import && s.addr == slot && named(&s.name)
        })
    };
    match call.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            let t = call.near_branch_target();
            analysis
                .function(t)
                .filter(|g| g.entry == t)
                .and_then(|g| g.name.as_deref())
                .is_some_and(named)
                || decode_at(program, bitness, t)
                    .and_then(|i| slot_jump(&i))
                    .is_some_and(import)
        }
        OpKind::Memory
            if matches!(call.memory_base(), Register::None | Register::RIP)
                && call.memory_index() == Register::None =>
        {
            import(call.memory_displacement64())
        }
        _ => false,
    }
}

/// Tells whether an instruction tears the frame down: `pop ebp`, `leave`,
/// or `add esp, N`, the last things a function does before it returns or
/// tail-jumps.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
fn tears_frame_down(instr: &Instruction) -> bool {
    let op0_is = |r: Register| {
        instr.op0_kind() == OpKind::Register && instr.op0_register().full_register() == r
    };
    match instr.mnemonic() {
        Mnemonic::Leave => true,
        Mnemonic::Pop => op0_is(Register::RBP),
        Mnemonic::Add => moves_rsp_by_imm(instr),
        _ => false,
    }
}

/// Returns the near-branch target when operand 0 is a near branch.
///
/// # Arguments
///
/// * `instr` - Any decoded instruction.
fn near_target(instr: &Instruction) -> Option<u64> {
    match instr.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            Some(instr.near_branch_target())
        }
        _ => None,
    }
}

/// Recovers the instructions immediately before `va`.
///
/// x86 has no reliable backward decode, so every start within 64 bytes is
/// tried and the longest chain that ends exactly on `va` wins.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The address the chain must end at.
/// * `want` - Chain length that stops the search early.
///
/// # Returns
///
/// The chain in address order, or `None` when no start decodes onto `va`.
fn prev_instructions(
    program: &Program,
    bitness: u32,
    va: u64,
    want: usize,
) -> Option<Vec<Instruction>> {
    /// How far back a chain may start, in bytes.
    const MAX_BACK: u64 = 64;
    let mut best: Option<Vec<Instruction>> = None;
    for back in 1..=MAX_BACK.min(va) {
        let start = va - back;
        if !super::is_executable_va(program, start) {
            continue;
        }
        let mut chain = Vec::new();
        let mut cur = start;
        while cur < va {
            let Some(instr) = decode_at(program, bitness, cur) else {
                break;
            };
            if instr.code() == Code::INVALID {
                break;
            }
            cur = instr.next_ip();
            chain.push(instr);
        }
        if cur == va && !chain.is_empty() {
            if chain.len() >= want {
                return Some(chain);
            }
            if chain.len() > best.as_ref().map_or(0, Vec::len) {
                best = Some(chain);
            }
        }
    }
    best
}

/// Resolves the bounded jump table feeding the indirect jump at `jmp_va`.
///
/// The preceding instructions come from the walk's own decode chain, falling
/// back to [`prev_instructions`] when the chain is shorter than three. The
/// bound is the range check of the table's index ([`index_bound`]) or, when
/// no load names an index, the nearest check before the jump
/// ([`check_bound`]); a table sized loosely ends at its first case farther
/// than [`LOOSE_REACH`] from the jump, or at the first that `within` refuses
/// (the walk passes the function's entry and the next known function start:
/// an index that came from a byte reads up to 256 entries, and the entries
/// past a six-case table's end are the next table's, which land in the next
/// function). The table base is the nearest `lea
/// reg, [rip+X]` or `mov reg, imm` after that compare that lands in a
/// section. Every target must decode as an instruction inside the jump's
/// own section.
///
/// Three shapes are tried before that. The jump's own memory operand may
/// name the table (`jmp qword [rax * 8 + T]`, what GCC emits). A load
/// through a `lea`-filled register may name it (`lea rdx, [rip + B]; mov
/// ecx, [rdx + rax * 4 + D]`, what MSVC emits, where the entries are
/// offsets from `B`), and a byte table read the same way
/// (`movzx eax, byte [rdx + rcx + D2]`) selects among those targets when
/// several cases share one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `recorded` - What the walk's records so far say.
/// * `within` - Whether a target of a loosely sized table may be this
///   function's.
///
/// # Returns
///
/// The case targets in table order, with the byte index table that picked
/// them when one did, or `None` when no bound, no base, or an implausible
/// table was found.
fn resolve_jump_table(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    recorded: &Recorded,
    within: &dyn Fn(u64) -> bool,
) -> Option<TableRead> {
    /// Longest backward chain examined for the range check and table base.
    const CHAIN_MAX: usize = 40;
    let mut window: Vec<Instruction> = Vec::new();
    let mut cur = jmp_va;
    while window.len() < CHAIN_MAX {
        let Some(prev) = recorded.pred_of(cur) else {
            break;
        };
        let Some(i) = decode_at(program, bitness, prev) else {
            break;
        };
        window.push(i);
        cur = prev;
    }
    window.reverse();
    if window.len() < 3 {
        window = prev_instructions(program, bitness, jmp_va, 6)?;
    }

    let bound = match table_index(&window, decode_at(program, bitness, jmp_va).as_ref()) {
        Some((at, index)) => index_bound(&window, jmp_va, at, index),
        None => window.iter().enumerate().rev().find_map(|(k, i)| {
            check_bound(i, window.get(k + 1)).map(|entries| TableBound {
                check_at: k,
                entries,
                loose: false,
            })
        }),
    };
    let TableBound {
        check_at,
        entries,
        loose,
    } = bound?;
    let mut table = read_jump_table(program, bitness, jmp_va, &window, check_at, entries)?;
    if !loose {
        return Some(table);
    }
    let near = table
        .targets
        .iter()
        .take_while(|t| t.abs_diff(jmp_va) <= LOOSE_REACH && within(**t))
        .count();
    table.targets.truncate(near);
    (near > 0).then_some(table)
}

/// Reads the jump table a bounded index selects from, in whichever form
/// the instructions before the jump name it (see [`resolve_jump_table`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `window` - The instructions before the jump, in order.
/// * `cmp_at` - Position of the range check in `window`.
/// * `entries` - How many entries it allows.
///
/// # Returns
///
/// The case targets in table order and the byte table that picked them,
/// or `None` when no table reads as plausible.
fn read_jump_table(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    window: &[Instruction],
    cmp_at: usize,
    entries: u64,
) -> Option<TableRead> {
    let entries = usize::try_from(entries).ok()?;

    if let Some(jmp) = decode_at(program, bitness, jmp_va)
        && jmp.op0_kind() == OpKind::Memory
        && jmp.memory_index() != Register::None
        && matches!(jmp.memory_base(), Register::None)
    {
        let table = jmp.memory_displacement64();
        let picker = window
            .iter()
            .skip(cmp_at)
            .rev()
            .find_map(|i| byte_index_load(program, i, jmp.memory_index()));
        let found = match picker.and_then(|n| index_bytes(program, n, entries).map(|b| (n, b))) {
            Some((picker, indices)) => {
                let count = usize::from(*indices.iter().max().unwrap_or(&0)) + 1;
                table_targets(program, table, count)
                    .map(|t| {
                        indices
                            .iter()
                            .filter_map(|i| t.get(usize::from(*i)).copied())
                            .collect::<Vec<u64>>()
                    })
                    .filter(|t| t.len() == entries)
                    .map(|targets| TableRead {
                        targets,
                        picker: Some(picker),
                    })
            }
            None => table_targets(program, table, entries).map(|targets| TableRead {
                targets,
                picker: None,
            }),
        };
        if found.is_some() {
            return found;
        }
    }

    let mut bases: BTreeMap<Register, u64> = BTreeMap::new();
    for i in window {
        if i.mnemonic() == Mnemonic::Lea && i.memory_base() == Register::RIP {
            bases.insert(i.op0_register(), i.memory_displacement64());
        }
    }
    // SPEC: MSVC's x64 switch tables hang off the image base, which a long
    // function loads once at its top (`lea r15, [__ImageBase]`), before the
    // window: a base register nothing in the window set is taken for it. A
    // struct offset from some other pointer lands in the headers, not a
    // section, and the targets are checked either way.
    if program.is_64 && program.format == crate::program::BinaryFormat::Pe {
        for i in window {
            let base = i.memory_base();
            if i.memory_index() != Register::None
                && base.is_gpr()
                && !matches!(base.full_register(), Register::RSP | Register::RBP)
            {
                bases.entry(base).or_insert(program.image_base);
            }
        }
    }
    let mut wide: Option<(u64, u64)> = None;
    let mut narrow: Option<u64> = None;
    for i in window.iter().skip(cmp_at) {
        match table_load(program, &bases, i) {
            Some((table, base, 4)) => wide = Some((table, base)),
            Some((table, _, 1)) => narrow = Some(table),
            _ => {}
        }
    }
    if let Some((table, base)) = wide {
        let expanded = match narrow.and_then(|n| index_bytes(program, n, entries)) {
            Some(indices) => {
                let count = usize::from(*indices.iter().max().unwrap_or(&0)) + 1;
                offset_targets(program, table, count, base).map(|t| {
                    indices
                        .iter()
                        .filter_map(|i| t.get(usize::from(*i)).copied())
                        .collect::<Vec<u64>>()
                })
            }
            None => offset_targets(program, table, entries, base),
        };
        if let Some(targets) = expanded.filter(|t| t.len() == entries) {
            return Some(TableRead {
                targets,
                picker: narrow,
            });
        }
    }

    let mut table: Option<u64> = None;
    for i in window.iter().skip(cmp_at).rev() {
        match i.mnemonic() {
            Mnemonic::Lea if i.memory_base() == Register::RIP => {
                let t = i.memory_displacement64();
                if program.section_at(t).is_some() {
                    table = Some(t);
                }
            }
            Mnemonic::Mov => {
                for op in 0..i.op_count() {
                    if matches!(
                        i.op_kind(op),
                        OpKind::Immediate64 | OpKind::Immediate32 | OpKind::Immediate32to64
                    ) {
                        let v = i.immediate(op);
                        if program.section_at(v).is_some() {
                            table = Some(v);
                        }
                    }
                }
            }
            _ => {}
        }
        if table.is_some() {
            break;
        }
    }
    let table = table?;

    let targets = table_targets(program, table, entries)?;
    let jmp_section = program.section_at(jmp_va)?.va.0;
    let plausible = targets.iter().all(|&t| {
        program.section_at(t).is_some_and(|s| s.va.0 == jmp_section)
            && decode_at(program, bitness, t).is_some_and(|i| i.code() != Code::INVALID)
    });
    plausible.then_some(TableRead {
        targets,
        picker: None,
    })
}

/// Reads a table of signed 32-bit offsets added to `base`, the form a
/// compiler uses when the targets are near a register it already holds.
///
/// The entries are sign-extended, as the `movsxd` that reads them does:
/// a rel32 table's targets sit on both sides of its base, and a hand-built
/// interpreter's handlers (reached through `lea r11, [table]; movsxd rcx,
/// [r11+rcx*4]; add rcx, r11; jmp rcx`) are always below the read-only
/// data its program lives in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first entry.
/// * `entries` - Number of entries.
/// * `base` - What each entry is relative to.
///
/// # Returns
///
/// The targets in table order, or `None` when an entry is unreadable or the
/// table does not pass [`accept_table`].
fn offset_targets(program: &Program, table: u64, entries: usize, base: u64) -> Option<Vec<u64>> {
    let targets: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            let slot = table.checked_add(from_usize(i).checked_mul(4)?)?;
            let bytes: [u8; 4] = program.read_va(slot, 4)?.try_into().ok()?;
            Some(base.wrapping_add_signed(i64::from(u32::from_le_bytes(bytes).cast_signed())))
        })
        .collect();
    targets.filter(|t| accept_table(program, t))
}

/// Returns the byte table a load picks the jump table's slot from, when
/// `instr` is that load: `movzx eax, byte [eax + I]` (or `[I + eax]`)
/// feeding `jmp dword [eax*4 + T]`.
///
/// With the byte table in front, the bound counts cases and not slots, so
/// reading that many slots of `T` runs past its end into whatever follows,
/// the byte table included, and its bytes read as addresses.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `instr` - A candidate load.
/// * `index` - The register the jump indexes its table with.
///
/// # Returns
///
/// The byte table's address, or `None` when `instr` is not such a load.
fn byte_index_load(program: &Program, instr: &Instruction, index: Register) -> Option<u64> {
    let fills_index = instr.mnemonic() == Mnemonic::Movzx
        && instr.op0_kind() == OpKind::Register
        && instr.op0_register().full_register() == index.full_register()
        && instr.op1_kind() == OpKind::Memory
        && instr.memory_size().size() == 1;
    let one_register = match (instr.memory_base(), instr.memory_index()) {
        (Register::None, Register::None) => false,
        (_, Register::None) => true,
        (Register::None, _) => instr.memory_index_scale() == 1,
        _ => false,
    };
    let table = instr.memory_displacement64();
    (fills_index && one_register && program.section_at(table).is_some()).then_some(table)
}

/// Reads the byte index table a compiler emits when several cases share a
/// target: entry `i` selects the target-table slot for case `i`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first byte.
/// * `entries` - Number of cases.
///
/// # Returns
///
/// The indices, or `None` when the table is unreadable or selects more
/// targets than a jump table may have.
fn index_bytes(program: &Program, table: u64, entries: usize) -> Option<Vec<u8>> {
    let bytes = program.read_va(table, entries)?.to_vec();
    let max = u64::from(*bytes.iter().max()?);
    (max < TABLE_ENTRIES_MAX).then_some(bytes)
}

/// The address a table load names, given the `lea`-loaded bases in scope.
///
/// A load of the form `mov r, [base + idx * scale + disp]` reads a table at
/// `base + disp` when `base` is a register a `lea reg, [rip + X]` filled;
/// the scale says how wide an entry is.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bases` - Registers holding an address, from `lea`.
/// * `instr` - The candidate load.
///
/// # Returns
///
/// `(table address, base value, entry scale)`, or `None`.
fn table_load(
    program: &Program,
    bases: &BTreeMap<Register, u64>,
    instr: &Instruction,
) -> Option<(u64, u64, u32)> {
    if !matches!(
        instr.mnemonic(),
        Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsxd | Mnemonic::Movsx
    ) {
        return None;
    }
    let base = *bases.get(&instr.memory_base())?;
    if instr.memory_index() == Register::None {
        return None;
    }
    let table = base.checked_add(instr.memory_displacement64())?;
    program.section_at(table)?;
    Some((table, base, instr.memory_index_scale()))
}

/// Reads a jump table's targets, trying each encoding compilers emit.
///
/// In order: absolute qword entries; dword entries relative to the table
/// base (`table + (i32)entry`, LLVM and MSVC); dword entries relative to
/// their own slot (`slot + (i32)entry`); and, for PE images, dword RVAs
/// (`image_base + entry`). The first encoding whose targets pass
/// [`accept_table`] wins.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first entry.
/// * `entries` - Number of entries from the range check.
///
/// # Returns
///
/// The targets in table order, or `None` when no encoding reads and validates.
fn table_targets(program: &Program, table: u64, entries: usize) -> Option<Vec<u64>> {
    // INVARIANT: a 32-bit program's absolute table holds four-byte
    // addresses, `jmp dword [eax*4+table]`; reading it eight bytes at a
    // time pairs every two cases into one impossible target.
    if !program.is_64 {
        let abs32: Option<Vec<u64>> = (0..entries)
            .map(|i| read_u32(program, table + from_usize(i) * 4).map(u64::from))
            .collect();
        if let Some(t) = abs32
            && accept_table(program, &t)
        {
            return Some(t);
        }
    }
    let abs: Option<Vec<u64>> = (0..entries)
        .map(|i| read_u64(program, table + from_usize(i) * 8))
        .collect();
    if let Some(t) = abs
        && accept_table(program, &t)
    {
        return Some(t);
    }

    let base_rel: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            read_u32(program, table + from_usize(i) * 4)
                .map(|e| table.wrapping_add_signed(i64::from(e.cast_signed())))
        })
        .collect();
    if let Some(t) = base_rel
        && accept_table(program, &t)
    {
        return Some(t);
    }

    let rel: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            let slot = table + from_usize(i) * 4;
            read_u32(program, slot).map(|e| slot.wrapping_add_signed(i64::from(e.cast_signed())))
        })
        .collect();
    if let Some(t) = rel
        && accept_table(program, &t)
    {
        return Some(t);
    }

    if program.image_base != 0 {
        let rva: Option<Vec<u64>> = (0..entries)
            .map(|i| {
                read_u32(program, table + from_usize(i) * 4)
                    .map(|e| program.image_base + u64::from(e))
            })
            .collect();
        if let Some(t) = rva
            && accept_table(program, &t)
        {
            return Some(t);
        }
    }
    None
}

/// Judges whether decoded table targets look like code addresses.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `targets` - Candidate targets; only the first 16 are sampled.
///
/// # Returns
///
/// `true` when at least three quarters of the sample lie in executable memory.
pub(super) fn accept_table(program: &Program, targets: &[u64]) -> bool {
    let sample = targets.len().min(16);
    if sample == 0 {
        return false;
    }
    let hits = targets
        .iter()
        .take(sample)
        .filter(|&&t| super::is_executable_va(program, t))
        .count();
    hits * 4 >= sample * 3
}

/// Tells whether a heuristic seed can start a function.
///
/// Pointer and padding seeds are guesses; one that lands on an `int3`, on
/// bytes that do not decode, inside a procedure linkage table (the GOT's
/// lazy-binding pointers aim at the `push` after each stub's jump), or
/// inside a function an x64 exception table declares ([`declared_interior`]:
/// a catch funclet returns its continuation there, `lea rax, [label]`) is
/// not a function.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The candidate entry.
fn plausible_entry(program: &Program, bitness: u32, va: u64) -> bool {
    if program
        .section_at(va)
        .is_none_or(|s| s.name.starts_with(".plt"))
        || string_at(program, va)
        || declared_interior(program, va)
    {
        return false;
    }
    decode_at(program, bitness, va)
        .is_some_and(|i| i.code() != Code::INVALID && i.mnemonic() != Mnemonic::Int3)
}

/// The catch continuations the catch funclets found return, by the entry
/// of the function each lies in.
///
/// Under `__CxxFrameHandler3` a catch funclet returns the address its
/// parent resumes at: it ends `lea rax, [label]` and `ret`, the label
/// inside the parent, past everything the parent's own code reaches, since
/// only the runtime jumps there. The parent is the function the exception
/// table declares around the label; a label already inside the parent's
/// blocks is left out. (`__CxxFrameHandler4` names them in its records,
/// [`crate::unwind::continuations`].)
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `functions` - The functions found so far.
///
/// # Returns
///
/// The labels by parent entry, empty without an x64 exception table.
fn catch_continuations(program: &Program, functions: &[Function]) -> FxHashMap<u64, Vec<u64>> {
    let mut out: FxHashMap<u64, Vec<u64>> = FxHashMap::default();
    let ranges = &program.function_ranges;
    if !(program.is_64 && program.format == crate::program::BinaryFormat::Pe) || ranges.is_empty() {
        return out;
    }
    let catches: FxHashSet<u64> = crate::unwind::funclets(program)
        .iter()
        .filter(|f| matches!(f.role, crate::analysis::FuncletRole::Catch(..)))
        .map(|f| f.entry)
        .collect();
    let covered = Covered::new(functions);
    for f in functions.iter().filter(|f| catches.contains(&f.entry)) {
        for b in f.blocks.iter().filter(|b| b.term == BlockTerm::Ret) {
            let Some(bytes) = usize::try_from(b.end - b.start)
                .ok()
                .and_then(|n| program.read_va(b.start, n))
            else {
                continue;
            };
            let mut decoder = Decoder::with_ip(64, bytes, b.start, DecoderOptions::NONE);
            let mut label = None;
            for i in &mut decoder {
                if i.mnemonic() == Mnemonic::Lea
                    && i.op0_kind() == OpKind::Register
                    && i.op0_register().full_register() == Register::RAX
                    && i.memory_base() == Register::RIP
                {
                    label = Some(i.memory_displacement64());
                } else if i.op0_kind() == OpKind::Register
                    && i.op0_register().full_register() == Register::RAX
                    && !matches!(
                        i.mnemonic(),
                        Mnemonic::Push | Mnemonic::Cmp | Mnemonic::Test
                    )
                {
                    label = None;
                }
            }
            let Some(label) = label else { continue };
            let k = ranges.partition_point(|r| r.0 <= label);
            let Some(&(parent, end)) = k.checked_sub(1).and_then(|k| ranges.get(k)) else {
                continue;
            };
            if label > parent
                && label < end
                && !(f.start..f.end).contains(&label)
                && !covered.contains(label)
            {
                out.entry(parent).or_default().push(label);
            }
        }
    }
    for labels in out.values_mut() {
        dedup_sorted(labels);
    }
    out
}

/// Whether `va` follows `int3` padding, so a jump there is a tail call.
///
/// MSVC pads with `int3` only between functions; inside one, an aligned
/// loop head follows `nop`s. On x64 the exception table has the last word:
/// a target inside a function it declares is the function's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The jump target.
fn after_padding(program: &Program, bitness: u32, va: u64) -> bool {
    if program.format != crate::program::BinaryFormat::Pe
        || va < 2
        || program.read_va(va - 2, 2) != Some(&[0xcc, 0xcc][..])
    {
        return false;
    }
    if bitness == 64 {
        !program.function_ranges.is_empty() && !declared_interior(program, va)
    } else {
        true
    }
}

/// Whether an x64 exception table puts `va` inside a function it declares,
/// past its start, or in one of a function's separated chunks.
///
/// No function starts there, so a jump there is the function's own: the
/// shapes that otherwise read as a tail call - a jump after the frame's
/// release, to code that opens like a function, over padding - are only
/// guesses the table overrules. MSVC threads jumps through shared `jmp`
/// blocks and stores to stack slots (`mov [rsp+0x30], eax`), and both read
/// as a function's opening.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The jump target.
fn declared_interior(program: &Program, va: u64) -> bool {
    /// Whether `va` lies in one of `ranges` (sorted by start), past its start
    /// unless `at_start`.
    fn inside(ranges: &[(u64, u64)], va: u64, at_start: bool) -> bool {
        let k = ranges.partition_point(|r| r.0 <= va);
        k > 0 && {
            let (lo, hi) = ranges[k - 1];
            va < hi && (at_start || va > lo)
        }
    }
    program.format == crate::program::BinaryFormat::Pe
        && program.is_64
        && (inside(&program.function_ranges, va, false)
            || inside(&program.headers.chained_chunks, va, true))
}

/// Whether the instruction at `va` addresses memory through the frame
/// pointer, which on a function's entry still holds its caller's frame.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The address.
fn opens_on_frame(program: &Program, bitness: u32, va: u64) -> bool {
    decode_at(program, bitness, va).is_some_and(|i| {
        (0..i.op_count()).any(|k| i.op_kind(k) == OpKind::Memory)
            && i.memory_base().full_register() == Register::RBP
    })
}

/// Whether a terminated string begins at `va`: five or more printable
/// ASCII bytes and a NUL, or four or more printable UTF-16 units and a
/// NUL unit.
///
/// A linker without a separate read-only section puts the strings in
/// `.text`, and an instruction that pushes one's address reads as a
/// reference to code. Text decodes as instructions (`Buffer` is `inc edx;
/// jne ...`), but code does not open with a run of printable bytes and a
/// terminator. Text is letters, digits and the punctuation prose has; code
/// whose bytes happen to print (`push 4B287C40h; push 0` is `h@|(Kj`) is
/// not.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The candidate entry.
pub(crate) fn string_at(program: &Program, va: u64) -> bool {
    let Some(bytes) = program.read_va_upto(va, 256) else {
        return false;
    };
    let printable = |b: u8| (0x20..0x7f).contains(&b) || matches!(b, b'\t' | b'\n' | b'\r');
    let wordy = |run: &[u8]| {
        let odd = run
            .iter()
            .filter(|&&b| {
                !(b.is_ascii_alphanumeric()
                    || b.is_ascii_whitespace()
                    || b".,_-:/\\%()'\"*?!=<>[]".contains(&b))
            })
            .count();
        odd <= 1 || run.len() >= 12
    };
    let ascii = bytes.iter().take_while(|&&b| printable(b)).count();
    if ascii >= 5 && bytes.get(ascii) == Some(&0) && wordy(&bytes[..ascii]) {
        return true;
    }
    let wide = bytes
        .chunks_exact(2)
        .take_while(|c| printable(c[0]) && c[1] == 0)
        .count();
    wide >= 4 && bytes.get(2 * wide..2 * wide + 2) == Some(&[0, 0][..])
}

/// Returns the addresses between the first and the last mapped section.
///
/// A value outside it cannot reference the image, and most words in data
/// and most immediates in code are outside it, so the range rejects them
/// before any section lookup.
///
/// # Arguments
///
/// * `program` - The loaded image.
fn mapped_range(program: &Program) -> std::ops::Range<u64> {
    let (lo, hi) =
        program
            .sections
            .iter()
            .filter(|s| s.file_size > 0)
            .fold((u64::MAX, 0), |(lo, hi), s| {
                (
                    lo.min(s.va.0),
                    hi.max(s.va.0.saturating_add(s.vsize.max(s.file_size))),
                )
            });
    lo..hi.max(lo)
}

/// Tells whether a section describes addresses rather than uses them.
///
/// An exception table names the function it covers, a relocation names
/// the word it patches, and a symbol table names everything; a word in
/// any of them is a description of the address, not a reference to it.
///
/// # Arguments
///
/// * `name` - The section name.
fn describes_addresses(name: &str) -> bool {
    matches!(
        name,
        ".pdata" | ".reloc" | ".eh_frame" | ".eh_frame_hdr" | ".dynamic" | ".dynsym" | ".symtab"
    ) || name.starts_with(".rel")
}

/// Tells whether a section holds resources rather than the program's data.
///
/// A PE's `.rsrc` holds icons, version blocks, manifests and string
/// tables: bytes that are what they are, not pointers, and a word there
/// that happens to spell a code address names no function.
///
/// # Arguments
///
/// * `name` - The section's name.
fn holds_resources(name: &str) -> bool {
    name == ".rsrc" || name.starts_with(".rsrc$")
}

/// The bytes of a section pointers are read from, as the image holds them.
///
/// That is a non-executable section that neither describes addresses
/// ([`describes_addresses`]) nor holds resources ([`holds_resources`]), at
/// least one word long. Its words are the relocated ones
/// ([`Program::section_bytes`]): a PIE lld linked keeps its vtables and
/// callback tables as zeros in the file.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `s` - The section.
/// * `word` - The pointer width in bytes.
///
/// # Returns
///
/// The section's bytes, or `None` when no pointer is read from it.
fn pointer_section_bytes<'a>(program: &'a Program, s: &Section, word: usize) -> Option<&'a [u8]> {
    if s.executable
        || describes_addresses(&s.name)
        || holds_resources(&s.name)
        || saturating_usize(s.file_size) < word
    {
        return None;
    }
    program.section_bytes(s)
}

/// Records a reference from every data pointer that names a function or
/// another data address.
///
/// A virtual method is reached through its class's table, a callback
/// through the table it was registered in, and neither leaves an
/// instruction that names the function; on this client that is 29,487
/// functions with no reference at all until the tables are read. A word
/// that lands in a data section is a `ptr` site the same way: the locator
/// naming a type descriptor, a table of string pointers, a static holding
/// the address of another. So is a word that lands in an executable
/// section where no block covers it, the data a linker merged into `.text`
/// (32-bit system binaries keep their strings and tables there). Every
/// non-executable section is scanned a word at a time, skipping those that
/// describe addresses rather than use them ([`describes_addresses`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entries` - Function entry addresses; most words in a data section
///   are not addresses at all, so a range check comes before the lookup.
/// * `covered` - The functions' blocks, which tell code from data in an
///   executable section.
/// * `xrefs` - Reference sites, extended in place.
fn record_table_refs(
    program: &Program,
    entries: &BTreeSet<u64>,
    covered: &Covered,
    xrefs: &mut BTreeMap<u64, Vec<RefSite>>,
) {
    let word = saturating_usize(pointer_size(program));
    let sorted: Vec<u64> = entries.iter().copied().collect();
    let mapped = mapped_range(program);
    for s in &program.sections {
        let Some(data) = pointer_section_bytes(program, s, word) else {
            continue;
        };
        for (i, chunk) in data.chunks_exact(word).enumerate() {
            let v = le_word(program, chunk);
            if !mapped.contains(&v) {
                continue;
            }
            let slot = s.va.0 + from_usize(i * word);
            if sorted.binary_search(&v).is_ok() {
                push_site(xrefs, v, slot, RefKind::Table, None);
            } else if program
                .section_at(v)
                .is_some_and(|t| !t.executable || !covered.contains(v))
            {
                push_site(xrefs, v, slot, RefKind::Ptr, None);
            }
        }
    }
}

/// The code addresses that relocated words inside executable sections hold.
///
/// Only words no decoded instruction covers count: a table of callbacks a
/// linker without `.rdata` keeps in `.text`, which [`pointer_seeds`] never
/// reads.
///
/// A jump table is such a run of words too, and its entries are case
/// labels, not functions: a run whose every target lies just below it (a
/// function's cases precede its table) is left out, as is a word whose
/// target a block already covers.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `covered` - The blocks found so far.
///
/// # Returns
///
/// The targets, at most [`SEEDS_MAX`].
fn reloc_seeds(program: &Program, covered: &Covered) -> Vec<u64> {
    /// Farthest below its table a case label lies.
    const CASES_REACH: u64 = 0x1_0000;
    let word = pointer_size(program);
    let mut sites: Vec<u64> = program
        .relocated_words()
        .into_iter()
        .filter(|&va| super::is_executable_va(program, va) && !covered.contains(va))
        .collect();
    sites.sort_unstable();
    let mut out = Vec::new();
    let mut run: Vec<(u64, u64)> = Vec::new();
    let flush = |run: &mut Vec<(u64, u64)>, out: &mut Vec<u64>| {
        let Some(&(first, _)) = run.first() else {
            return;
        };
        let cases = run
            .iter()
            .all(|&(_, t)| t < first && first - t <= CASES_REACH);
        if !cases {
            out.extend(
                run.iter()
                    .map(|&(_, t)| t)
                    .filter(|&t| super::is_executable_va(program, t) && !covered.contains(t)),
            );
        }
        run.clear();
    };
    for va in sites {
        let Some(target) = read_word(program, va) else {
            continue;
        };
        if run.last().is_some_and(|&(prev, _)| prev + word != va) {
            flush(&mut run, &mut out);
        }
        run.push((va, target));
        if out.len() >= SEEDS_MAX {
            break;
        }
    }
    flush(&mut run, &mut out);
    out.truncate(SEEDS_MAX);
    out
}

/// Whether the `len` bytes at `at` lie inside text: a run of six or more
/// printable ASCII bytes, or three or more printable UTF-16 units.
///
/// A 32-bit image loads at `0x400000`, and a UTF-16 pair of letters from
/// `@` to `Q` is an address in its `.text` (`E\0C\0` is `0x00430045`), as
/// are the last bytes of a type name (`d@@\0`). A pointer table never
/// runs printable for that long: `0x00404064` next to `0x00404080` reads
/// `d@@\0\x80@@\0`.
///
/// The ASCII run is the printable bytes through the word's first printable
/// byte; the UTF-16 run is the printable units on even offsets through the
/// word.
///
/// # Arguments
///
/// * `data` - The section's bytes.
/// * `at` - Offset of the word.
/// * `len` - The word's width.
fn inside_text(data: &[u8], at: usize, len: usize) -> bool {
    let printable = |b: u8| (0x20..0x7f).contains(&b);
    let end = (at + len).min(data.len());
    if let Some(first) = (at..end).find(|&i| printable(data[i])) {
        let mut lo = first;
        while lo > 0 && printable(data[lo - 1]) {
            lo -= 1;
        }
        let mut hi = first;
        while hi < data.len() && printable(data[hi]) {
            hi += 1;
        }
        if hi - lo >= 6 {
            return true;
        }
    }
    let unit = |i: usize| i + 1 < data.len() && printable(data[i]) && data[i + 1] == 0;
    let base = at & !1;
    if (base..end).step_by(2).any(unit) {
        let first = (base..end).step_by(2).find(|&i| unit(i)).unwrap_or(base);
        let mut lo = first;
        while lo >= 2 && unit(lo - 2) {
            lo -= 2;
        }
        let mut hi = first;
        while unit(hi) {
            hi += 2;
        }
        if (hi - lo) / 2 >= 3 {
            return true;
        }
    }
    false
}

/// Collects data pointers (vtables, callbacks) that point into executable sections.
///
/// # Arguments
///
/// * `program` - The loaded image; every non-executable section is scanned
///   in word-sized steps.
/// * `sites` - The relocation sites, when the image has any: only a word
///   the loader relocates is a pointer then.
///
/// # Returns
///
/// The pointed-to addresses in scan order, at most [`SEEDS_MAX`].
fn pointer_seeds(program: &Program, sites: Option<&FxHashSet<u64>>) -> Vec<u64> {
    let word = saturating_usize(pointer_size(program));
    let mut out = Vec::new();
    'sec: for s in &program.sections {
        // INVARIANT: a section that describes addresses or holds resources
        // has words that look like code addresses and are not pointers.
        let Some(data) = pointer_section_bytes(program, s, word) else {
            continue;
        };
        for (k, chunk) in data.chunks_exact(word).enumerate() {
            // INVARIANT: a relocatable image relocates every pointer it
            // holds; a word the loader leaves alone is a number, or text.
            if sites.is_some_and(|set| !set.contains(&(s.va.0 + from_usize(k * word)))) {
                continue;
            }
            let v = le_word(program, chunk);
            if v != 0 && super::is_executable_va(program, v) && !inside_text(data, k * word, word) {
                out.push(v);
                if out.len() >= SEEDS_MAX {
                    break 'sec;
                }
            }
        }
    }
    out
}

/// Records the immediate and memory operands of `instr` that land in mapped
/// sections or in a PE's mapped headers.
///
/// The headers count because `lea rcx, [__ImageBase]` is how x64 code finds
/// its own image (the base of every RVA table it reads), and that
/// reference was dropped for want of a section. A memory operand counts
/// when it has no effective base: a bare
/// displacement (iced pre-computes rip-relative ones into absolute targets,
/// so the raw displacement is the address in both cases), or a scaled index
/// on a displacement, `[esi*4 + table]`, which is how 32-bit code reads a
/// table and the only reference a lookup table ever gets. A base register
/// makes the displacement a field offset, not an address. Most immediates
/// are small constants, so the range check rejects them before the section
/// lookup.
///
/// # Arguments
///
/// * `program` - The loaded image, for the section check.
/// * `mapped` - The addresses between the first and the last mapped section.
/// * `instr` - The decoded instruction.
/// * `va` - Its address, recorded as the referencing site.
/// * `out` - Receives `(target, va)` pairs.
/// * `patched` - The relocation sites and the operands' offsets inside
///   `instr`, in an image that relocates: an absolute operand the loader
///   does not patch is then a constant, whatever it looks like.
fn record_data_refs(
    program: &Program,
    mapped: &std::ops::Range<u64>,
    instr: &Instruction,
    va: u64,
    out: &mut Vec<DataRef>,
    patched: Option<(&AddrSet, crate::isa::x86::ConstantOffsets)>,
) {
    let in_image =
        |v: u64| (mapped.contains(&v) && program.section_at(v).is_some()) || program.in_headers(v);
    let relocated = |offset: usize, size: usize| {
        patched.is_none_or(|(sites, _)| size >= 4 && sites.contains(va + from_usize(offset)))
    };
    for op in 0..instr.op_count() {
        match instr.op_kind(op) {
            OpKind::Memory => {
                let has_effective_base =
                    instr.memory_base() != Register::None && instr.memory_base() != Register::RIP;
                if has_effective_base {
                    continue;
                }
                if !instr.is_ip_rel_memory_operand()
                    && let Some((_, offsets)) = &patched
                    && !(offsets.has_displacement()
                        && relocated(offsets.displacement_offset(), offsets.displacement_size()))
                {
                    continue;
                }
                let target = instr.memory_displacement64();
                if in_image(target) {
                    // INVARIANT: an operand scaled by an index register names
                    // a table's base, and a table is what it is wherever it
                    // lies, in `.text` after the switch that reads it as
                    // often as not; its base is no instruction to walk.
                    let kind = if instr.memory_index() == Register::None {
                        match instr.flow_control() {
                            FlowControl::IndirectCall => RefKind::Call,
                            FlowControl::IndirectBranch => RefKind::Jmp,
                            FlowControl::Next
                            | FlowControl::UnconditionalBranch
                            | FlowControl::ConditionalBranch
                            | FlowControl::Return
                            | FlowControl::Call
                            | FlowControl::Interrupt
                            | FlowControl::Exception
                            | FlowControl::XbeginXabortXend => RefKind::Data,
                        }
                    } else {
                        RefKind::Index
                    };
                    out.push(DataRef { target, va, kind });
                }
            }
            OpKind::Immediate64
            | OpKind::Immediate32
            | OpKind::Immediate32to64
            | OpKind::Immediate8to64
            | OpKind::Immediate8to32 => {
                if let Some((_, offsets)) = &patched
                    && !(offsets.has_immediate()
                        && relocated(offsets.immediate_offset(), offsets.immediate_size()))
                {
                    continue;
                }
                let v = instr.immediate(op);
                if in_image(v) {
                    out.push(DataRef {
                        target: v,
                        va,
                        kind: RefKind::Data,
                    });
                }
            }
            _ => {}
        }
    }
}

/// Cuts the decoded instructions into basic blocks.
///
/// Leaders are the entry, every branch target, every jump-table case target,
/// the instruction after every conditional branch or call, and every
/// instruction nothing falls into: code the runtime enters, an `__except`
/// body or a catch continuation, follows a `ret` with no jump naming it. A
/// block whose last instruction simply continues into the next leader is a
/// [`BlockTerm::Fall`] block with that leader as its successor. The `nop`
/// after a call that does not return ends the call's block, which has no
/// successor: what follows the `nop` may be another path's code.
///
/// The blocks and their successor lists hold no spare room: a list grown a
/// push at a time keeps room for four successors where a block has one or
/// two, and over a large program's million blocks that room was tens of
/// megabytes kept for as long as the program stays loaded. Freed here, on
/// the walker's thread, the room goes straight to the next walk.
///
/// # Arguments
///
/// * `entry` - The function's entry address.
/// * `recs` - The decoded instructions in address order.
/// * `tables` - Resolved jump tables.
/// * `tail_nops` - The `nop`s that end the function after such a call.
///
/// # Returns
///
/// The blocks in address order.
fn build_blocks(
    entry: u64,
    recs: &[(u64, InstrRec)],
    tables: &[ResolvedTable],
    tail_nops: &[u64],
) -> Vec<BasicBlock> {
    let mut leaders: Vec<u64> = vec![entry];
    for t in tables {
        leaders.extend(t.targets.iter().copied());
    }
    for (_, rec) in recs {
        match rec.flow {
            FlowControl::Next => {}
            FlowControl::ConditionalBranch => {
                leaders.extend(rec.target);
                leaders.push(rec.next);
            }
            FlowControl::UnconditionalBranch | FlowControl::IndirectBranch => {
                leaders.extend(rec.target);
            }
            FlowControl::Call | FlowControl::IndirectCall => {
                if !tail_nops.contains(&rec.next) {
                    leaders.push(rec.next);
                }
            }
            FlowControl::XbeginXabortXend => {
                leaders.extend(rec.target);
                leaders.push(rec.next);
            }
            FlowControl::Return | FlowControl::Interrupt | FlowControl::Exception => {}
        }
    }
    dedup_sorted(&mut leaders);

    let mut blocks = Vec::new();
    let mut current: Option<BasicBlock> = None;
    let mut next_leader = 0;
    for &(addr, ref rec) in recs {
        while leaders.get(next_leader).is_some_and(|&l| l < addr) {
            next_leader += 1;
        }
        let falls_in = current.as_ref().is_some_and(|b| {
            b.end == addr && (b.term == BlockTerm::Fall || tail_nops.contains(&addr))
        });
        if leaders.get(next_leader) == Some(&addr) || !falls_in {
            if let Some(mut b) = current.take() {
                if b.term == BlockTerm::Fall && b.end == addr {
                    b.successors.push(addr);
                }
                blocks.push(b);
            }
            current = Some(BasicBlock {
                start: addr,
                end: rec.next,
                term: BlockTerm::Fall,
                successors: Vec::new(),
            });
        }
        let Some(block) = current.as_mut() else {
            continue;
        };
        block.end = rec.next;
        match rec.flow {
            FlowControl::Next if tail_nops.contains(&addr) => {
                block.successors.retain(|&s| s != addr);
            }
            FlowControl::Next => {}
            FlowControl::ConditionalBranch => {
                block.term = BlockTerm::Cond;
                if let Some(t) = rec.target {
                    block.successors.push(t);
                }
                block.successors.push(rec.next);
            }
            FlowControl::UnconditionalBranch => {
                block.term = BlockTerm::Jmp;
                match rec.target {
                    Some(t) => block.successors.push(t),
                    None => {
                        if let Some(t) = tables.iter().find(|t| t.site == addr) {
                            block.term = BlockTerm::Indirect;
                            block.successors.extend(t.targets.iter().copied());
                        }
                    }
                }
            }
            FlowControl::IndirectBranch => {
                block.term = BlockTerm::Indirect;
                if let Some(t) = tables.iter().find(|t| t.site == addr) {
                    block.successors.extend(t.targets.iter().copied());
                }
            }
            FlowControl::Call | FlowControl::IndirectCall => {
                block.term = BlockTerm::Call;
                block.successors.push(rec.next);
            }
            FlowControl::Return => block.term = BlockTerm::Ret,
            FlowControl::Interrupt | FlowControl::Exception => block.term = BlockTerm::Invalid,
            FlowControl::XbeginXabortXend => {
                block.term = BlockTerm::Cond;
                if let Some(t) = rec.target {
                    block.successors.push(t);
                }
                block.successors.push(rec.next);
            }
        }
    }
    if let Some(b) = current {
        blocks.push(b);
    }
    for b in &mut blocks {
        b.successors.shrink_to_fit();
    }
    blocks.shrink_to_fit();
    blocks
}

/// Fills in callers and names for the discovered functions.
///
/// Callers are inverted from the callee lists. Names come from non-import
/// symbols at the entry (demangled to the bare qualified name); a
/// `jmp [rip+slot]` thunk, optionally behind an `endbr64`, takes the name of
/// the import whose IAT or GOT slot it jumps through.
///
/// # Arguments
///
/// * `program` - The loaded image, for symbols and thunk decoding.
/// * `functions` - The functions, updated in place.
pub(super) fn build_callers_and_names(program: &Program, functions: &mut [Function]) {
    let mut callers: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for f in functions.iter() {
        for c in &f.callees {
            callers.entry(*c).or_default().push(f.entry);
        }
    }
    for f in functions.iter_mut() {
        let mut cs = callers.remove(&f.entry).unwrap_or_default();
        dedup_sorted(&mut cs);
        f.callers = cs;
    }
    // PERF: the lookups below are by address, and a linear scan per function
    // over every symbol was the slowest single pass of a big PDB-carrying
    // binary; one pass here makes each a hash lookup. `or_insert` keeps the
    // first symbol of an address in file order, exactly what `find` returned.
    let mut named: FxHashMap<u64, usize> = FxHashMap::default();
    let mut import_slots: FxHashMap<u64, usize> = FxHashMap::default();
    for (i, s) in program.symbols.iter().enumerate() {
        if s.kind == crate::program::SymbolKind::Import {
            import_slots.entry(s.addr).or_insert(i);
        } else {
            named.entry(s.addr).or_insert(i);
        }
    }
    for f in functions.iter_mut() {
        f.name = named
            .get(&f.entry)
            .map(|&i| crate::search::demangled_name(&program.symbols[i].name));
        f.name_source = if f.name.is_some() {
            NameSource::Symbol
        } else {
            NameSource::None
        };
    }
    let Some(bitness) = program.arch.bitness() else {
        return;
    };
    for f in functions.iter_mut() {
        if f.name.is_some() || f.instr_count > 2 {
            continue;
        }
        let Some(mut instr) = decode_at(program, bitness, f.entry) else {
            continue;
        };
        if matches!(instr.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
            let Some(next) = decode_at(program, bitness, instr.next_ip()) else {
                continue;
            };
            instr = next;
        } else if f.instr_count != 1 {
            continue;
        }
        if instr.mnemonic() != Mnemonic::Jmp || instr.op0_kind() != OpKind::Memory {
            continue;
        }
        let base = instr.memory_base();
        if base != Register::None && base != Register::RIP {
            continue;
        }
        let slot = instr.memory_displacement64();
        f.name = (slot != 0)
            .then(|| import_slots.get(&slot))
            .flatten()
            .map(|&i| crate::search::demangled_name(&program.symbols[i].name));
        f.name_source = if f.name.is_some() {
            NameSource::Symbol
        } else {
            NameSource::None
        };
        if f.name.is_some() {
            f.thunk = Some(slot);
        }
    }
}

/// Appends one reference site to the cross-reference index.
///
/// A target's list starts with room for the one site most targets ever
/// have; grown from nothing it would hold room for four, which over a large
/// program's half million targets was tens of megabytes never used.
///
/// # Arguments
///
/// * `map` - Target address to its sites.
/// * `target` - The referenced address.
/// * `va` - Address of the referencing instruction.
/// * `kind` - How the site uses the target.
/// * `from_entry` - Entry of the function containing `va`.
pub(super) fn push_site(
    map: &mut BTreeMap<u64, Vec<RefSite>>,
    target: u64,
    va: u64,
    kind: RefKind,
    from_entry: Option<u64>,
) {
    let sites = map.entry(target).or_insert_with(|| Vec::with_capacity(1));
    if sites.len() < XREF_SITES_PER_TARGET {
        sites.push(RefSite {
            va,
            kind,
            from_entry,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::{prints_assert_banner, seh_scope_roots, string_at};
    use crate::analysis::Analysis;
    use crate::headers::ExceptionHandler;
    use crate::program::{Arch, Program, Section, Symbol, SymbolKind};

    /// A one-function x64 image: `code` at `0x1000` in a `.text` page and
    /// `data` at `0x2000` in a read-only `.rdata` page.
    ///
    /// # Arguments
    ///
    /// * `code` - The entry function's bytes.
    /// * `data` - What the read-only page holds.
    fn fixture(code: &[u8], data: &[u8]) -> Program {
        let mut bytes = vec![0u8; 0x3000];
        bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
        bytes[0x2000..0x2000 + data.len()].copy_from_slice(data);
        Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
                Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
            ],
        )
    }

    /// Builds a one-function image whose code points at `banner`.
    fn image(banner: &[u8]) -> Program {
        fixture(
            &[0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, 0xc3], // ASM: lea rax,[rip+0xff9] (= 0x2000); ret
            banner,
        )
    }

    /// Builds a one-function image whose body is `code`.
    fn code_image(code: &[u8]) -> Program {
        fixture(code, &[])
    }

    /// A reference-counting helper is named by its shape, and the assignment
    /// operator is told from the release by the reference it adds.
    ///
    /// # Panics
    ///
    /// When a shape is named wrongly.
    #[test]
    fn a_refcount_helper_is_named_by_its_shape() {
        let named = |code: &[u8]| {
            let p = code_image(code);
            let a = Analysis::compute(&p);
            let f = a.function(0x1000).expect("the function is discovered");
            super::refcount_helper_name(&p, 64, f)
        };
        let release: &[u8] = &[
            0x48, 0x8b, 0x09, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xf0, 0x0f, 0xc1, 0x41, 0x08, 0xff,
            0x10,
            0xc3, // ASM: mov rcx,[rcx]; mov eax,-1; lock xadd [rcx+8],eax; call [rax]; ret
        ];
        assert_eq!(named(release), Some("refcounted_release"));
        let assign: &[u8] = &[
            0x48, 0x8b, 0x09, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xf0, 0x0f, 0xc1, 0x41, 0x08, 0xff,
            0x10, 0xf0, 0xff, 0x42, 0x08, 0xc3, // ASM: the release, then lock inc [rdx+8]
        ];
        assert_eq!(
            named(assign),
            Some("refcounted_assign"),
            "a reference added is an assignment"
        );
        assert_eq!(
            named(&[0x48, 0x31, 0xc0, 0xc3]), // ASM: xor rax,rax; ret
            None,
            "neither"
        );
    }

    /// The reporter behind `assert` names itself in the text it prints.
    ///
    /// Thousands of functions call it and look alike from the outside; the
    /// banner is what tells the reporter from its callers. A function that
    /// points at any other literal is not one.
    ///
    /// # Panics
    ///
    /// When the banner does not decide it.
    #[test]
    fn an_assert_banner_marks_the_reporter() {
        let yes = image(b"*** NEBULA ASSERTION ***\0");
        let a = Analysis::compute(&yes);
        let f = a.function(0x1000).expect("the function is discovered");
        assert!(prints_assert_banner(&yes, 64, f));

        let no = image(b"loading world chunk\0");
        let a = Analysis::compute(&no);
        let f = a.function(0x1000).expect("the function is discovered");
        assert!(!prints_assert_banner(&no, 64, f));
    }

    /// A string in `.text` is not an entry; code is, even when its bytes
    /// are printable, so long as no terminator follows them.
    ///
    /// # Panics
    ///
    /// When a string passes for code or code for a string.
    #[test]
    fn strings_are_not_entries() {
        let p = image(b"Buffer too small\0");
        assert!(string_at(&p, 0x2000), "an ASCII string");
        let p = image(b"H\0e\0l\0l\0o\0\0\0");
        assert!(string_at(&p, 0x2000), "a UTF-16 string");
        let p = image(b"SVWU\x8b\xec");
        assert!(
            !string_at(&p, 0x2000),
            "push ebx; push esi; push edi; push ebp; mov ebp, esp"
        );
        assert!(!string_at(&p, 0x1000), "lea rax, [rip+...]");
    }

    /// An `EH4` scope table names its filters and handlers; a table whose
    /// cookie offsets are not frame offsets names nothing.
    ///
    /// # Panics
    ///
    /// When the handlers are not read, or the lookalike is.
    #[test]
    fn scope_tables_name_their_handlers() {
        let words = |w: &[u32]| w.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<u8>>();
        // SPEC: the header says no GS cookie and an EH cookie at [ebp-0x38];
        // then one outermost record with a filter at 0x1010 and a handler at
        // 0x1020, then a second enclosed by the first with a handler only
        // (`__finally`).
        let table = words(&[
            0xffff_fffe,
            0,
            0xffff_ffc8,
            0,
            0xffff_fffe,
            0x1010,
            0x1020,
            0,
            0,
            0x1030,
        ]);
        let mut p = image(&table);
        p.is_64 = false;
        p.arch = Arch::X86;
        for va in [0x1010usize, 0x1020, 0x1030] {
            p.bytes[va] = 0x90; // nop: something that decodes
        }
        assert_eq!(
            seh_scope_roots(&p, 0x2000, 0x1000),
            vec![0x1010, 0x1020, 0x1030]
        );
        let lookalike = words(&[0x1234_5678, 0, 0xffff_ffc8, 0, 0xffff_fffe, 0x1010, 0x1020]);
        let mut p = image(&lookalike);
        p.is_64 = false;
        assert!(seh_scope_roots(&p, 0x2000, 0x1000).is_empty());
    }

    /// An x64 `__except` body inside its function's declared range is the
    /// function's own code: the runtime resumes the function there, nothing
    /// else reaches it, and it is no function of its own.
    ///
    /// # Panics
    ///
    /// When the body is left out of its function or made one of its own.
    #[test]
    fn an_except_body_is_its_functions_code() {
        let code = [
            0x48, 0x83, 0xec, 0x28, // sub rsp, 0x28
            0x31, 0xc0, // xor eax, eax
            0x90, 0x90, // the guarded code
            0x48, 0x83, 0xc4, 0x28, // add rsp, 0x28
            0xc3, // ret
            0xcc, 0xcc, 0xcc, // padding
            0xb8, 0x01, 0x00, 0x00, 0x00, // 0x1010, the __except body: mov eax, 1
            0x48, 0x83, 0xc4, 0x28, // add rsp, 0x28
            0xc3, // ret
        ];
        let mut p = code_image(&code);
        // SPEC: the handler, named, and its scope table: one `__try` over
        // 0x1004..0x1008 with no filter (`EXCEPTION_EXECUTE_HANDLER`).
        p.bytes[0x1800] = 0xc3;
        p.symbols.push(Symbol {
            name: "__C_specific_handler".to_owned(),
            addr: 0x1800,
            kind: SymbolKind::Export,
        });
        for (i, v) in [1u32, 0x1004, 0x1008, 1, 0x1010].iter().enumerate() {
            p.bytes[0x2000 + 4 * i..0x2004 + 4 * i].copy_from_slice(&v.to_le_bytes());
        }
        p.headers.exception_handlers = vec![ExceptionHandler {
            function: 0x1000,
            handler: 0x1800,
            data: 0x2000,
        }];
        p.function_ranges = vec![(0x1000, 0x101a), (0x1800, 0x1801)];
        let a = Analysis::compute(&p);
        let f = a.function(0x1000).expect("the function is found");
        assert!(f.blocks.iter().any(|b| b.start == 0x1010));
        assert!(a.function(0x1010).is_none());
    }

    /// A wave of several batches finds every function a single walker
    /// finds.
    ///
    /// One function calling two hundred leaves makes a second wave of three
    /// full batches and a short one, the full ones walked across the wave's
    /// threads, each thread walking a stripe of every batch.
    ///
    /// # Panics
    ///
    /// When a leaf is missed or walked wrongly.
    #[test]
    fn a_wave_of_many_batches_finds_every_function() {
        /// Leaves the entry calls.
        const LEAVES: u32 = 200;
        /// Where the first leaf starts; each takes eight bytes.
        const LEAF_BASE: u32 = 0x1400;
        let mut code = Vec::new();
        for i in 0..LEAVES {
            let next = 0x1000 + 5 * (i + 1);
            let rel = (LEAF_BASE + 8 * i).wrapping_sub(next);
            code.push(0xe8); // ASM: call leaf
            code.extend_from_slice(&rel.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        code.resize(usize::try_from(LEAF_BASE - 0x1000).expect("fits"), 0xcc);
        for i in 0..LEAVES {
            code.push(0xb8); // ASM: mov eax, i
            code.extend_from_slice(&i.to_le_bytes());
            code.extend_from_slice(&[0xc3, 0xcc, 0xcc]); // ASM: ret; int3; int3
        }
        let a = Analysis::compute(&code_image(&code));
        let entry = a.function(0x1000).expect("the entry is found");
        assert_eq!(entry.callees.len(), 200);
        for i in 0..LEAVES {
            let at = u64::from(LEAF_BASE + 8 * i);
            let leaf = a.function(at).expect("every leaf is found");
            assert_eq!(
                (leaf.end, leaf.instr_count, leaf.blocks.len()),
                (at + 6, 2, 1)
            );
            assert_eq!(leaf.callers, [0x1000]);
        }
    }

    /// Discovery's lists hold what they hold and no spare room.
    ///
    /// A list grown a push at a time keeps room for four: a call's block
    /// has one successor and a function called once one reference site, so
    /// each list took four times its contents.
    ///
    /// # Panics
    ///
    /// When a list keeps room it does not use.
    #[test]
    fn discovered_lists_hold_no_spare_room() {
        let code = [
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0x85, 0xc0, // ASM: test eax, eax
            0x74, 0x01, // ASM: je 0x100a
            0x90, // ASM: nop
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // padding
            0x31, 0xc0, // ASM: 0x1010: xor eax, eax
            0xc3, // ASM: ret
        ];
        let a = Analysis::compute(&code_image(&code));
        assert_eq!(a.functions.capacity(), a.functions.len());
        let entry = a.function(0x1000).expect("the entry is found");
        assert_eq!(entry.blocks.len(), 4, "{:?}", entry.blocks);
        assert_eq!(entry.blocks.capacity(), entry.blocks.len());
        for b in &entry.blocks {
            assert_eq!(b.successors.capacity(), b.successors.len(), "{b:?}");
        }
        let sites = a.xrefs.get(&0x1010).expect("the callee is referenced");
        assert_eq!((sites.len(), sites.capacity()), (1, 1));
    }
}
