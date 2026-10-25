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

use super::{
    Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, RefSite, dedup_sorted, read_u32,
};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::isa::x86::{
    Code, Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind, Register,
};
use crate::num::from_usize;
use crate::program::Program;

mod frame;
mod guess;
pub(super) mod helpers;
pub(super) mod seeds;
mod sets;
pub(super) mod tables;
mod walk;

use frame::moves_rsp_by_imm;
use guess::{int3_end, plausible_entry};
use helpers::{
    COOKIE_CHECK_INSTRS_MAX, EPILOG_INSTRS_MAX, PANIC_INSTRS_MAX, cookie_check_name,
    epilog_helper_name, exits_on_status_name, frame_helper_name, is_noreturn_name,
    panic_helper_name, prints_assert_banner, refcount_helper_name,
};
use seeds::{got_base, mapped_range, pointer_seeds, record_table_refs, reloc_seeds};
use sets::{AddrSet, Covered};
use tables::ResolvedTable;
use walk::{Known, WalkState, Walked, Worker, walk_capped};

/// Smallest instruction budget for one full analysis pass.
const FUEL_MIN: u64 = 2_000_000;
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
pub(crate) const XREF_SITES_PER_TARGET: usize = 65_536;
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
    /// Calls ended for the status they pass glibc's `error`, each with the
    /// address after it and the addresses between the status and the call,
    /// held until the walk has all the function's branches
    /// ([`helpers::exits_with_status`]).
    status_ends: Vec<(u64, u64, Vec<u64>)>,
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
/// and the branch target (which [`walk_function`](walk::walk_function) folds in separately, as
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
        .filter(|s| s.kind == crate::program::SymbolKind::Import && named_noreturn(s))
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
        status_exits: Arc::new(helpers::status_exits(program)),
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
        #[expect(
            clippy::iter_over_hash_type,
            reason = "each parent's labels go to its own entry"
        )]
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
    analysis.noreturn = entries
        .iter()
        .copied()
        .filter(|&e| st.noreturn.contains(e))
        .collect();
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

/// What the walks of a wave read besides the starts, held by the pass and
/// shared with the wave's threads ([`WalkState::shared`]).
struct Shared {
    /// Functions known never to return.
    noreturn: Arc<AddrSet>,
    /// Import slots of functions that never return.
    noreturn_slots: Arc<FxHashSet<u64>>,
    /// Where calls reach glibc's `error` ([`helpers::status_exits`]).
    status_exits: Arc<FxHashSet<u64>>,
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
            status_exits: &self.status_exits,
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

/// The `__except` filters and handlers of the 32-bit SEH scope table at
/// `table`, when one is there ([`seh_scope_records`]).
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
    seh_scope_records(program, table, entry, true)
        .into_iter()
        .flat_map(|r| {
            (r.filter != 0)
                .then_some(u64::from(r.filter))
                .into_iter()
                .chain([u64::from(r.handler)])
        })
        .collect()
}

/// One record of a 32-bit SEH scope table: one `__try`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ScopeRecord {
    /// The index of the record whose `__try` encloses this one, or the
    /// outermost level.
    pub(crate) enclosing: u32,
    /// The `__except` filter, or `0` for a `__finally`.
    pub(crate) filter: u32,
    /// The `__except` body, or the `__finally` block.
    pub(crate) handler: u32,
}

/// Reads the records of the 32-bit SEH scope table at `table`, when one is
/// there.
///
/// A frame pushes its table's address, to `__SEH_prolog4` or into its own
/// registration. An `EH4` table opens with four cookie offsets, each a
/// small negative frame offset (`-2` for no cookie) or a small XOR
/// adjustment, then records `{enclosing level, filter, handler}`: the
/// first outermost (`-2`), each later one enclosed by an earlier, and a
/// `__finally` with no filter. An `EH3` table is the records alone, its
/// outermost level `-1`. The blocks they name are reached from no
/// instruction, so without the table a walk never decodes them and a
/// guess later takes each for a function of its own. The header is held
/// to that shape so that some other table is not read as one, and the
/// records end at the first that does not hold together.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - The pushed address.
/// * `entry` - The pushing function's entry, whose section its handlers
///   share.
/// * `eh4` - Whether the table is `_except_handler4`'s, with the cookie
///   header, rather than `_except_handler3`'s.
///
/// # Returns
///
/// The records in table order, empty when `table` does not hold a scope
/// table.
pub(crate) fn seh_scope_records(
    program: &Program,
    table: u64,
    entry: u64,
    eh4: bool,
) -> Vec<ScopeRecord> {
    /// Most records read from one table.
    const RECORDS_MAX: u64 = 64;
    /// Largest frame offset or XOR adjustment a cookie field holds.
    const FRAME_MAX: i32 = 0x1_0000;
    /// The outermost enclosing level of `EH4`, and the no-cookie offset.
    const TOPMOST: u32 = 0xffff_fffe;
    let Some(home) = program.section_at(entry).map(|s| s.va.0) else {
        return Vec::new();
    };
    let word = |va: u64| read_u32(program, va);
    let outermost = if eh4 { TOPMOST } else { u32::MAX };
    if eh4 {
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
    }
    let code = |va: u32| {
        let va = u64::from(va);
        super::is_executable_va(program, va)
            && program.section_at(va).is_some_and(|s| s.va.0 == home)
            && plausible_entry(program, 32, va)
    };
    let first = table + if eh4 { 16 } else { 0 };
    let mut out = Vec::new();
    for k in 0..RECORDS_MAX {
        let at = first + 12 * k;
        let (Some(level), Some(filter), Some(handler)) = (word(at), word(at + 4), word(at + 8))
        else {
            break;
        };
        let enclosed = level == outermost || (k > 0 && u64::from(level) < k);
        if !enclosed || !code(handler) || (filter != 0 && !code(filter)) {
            break;
        }
        out.push(ScopeRecord {
            enclosing: level,
            filter,
            handler,
        });
    }
    out
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
    let args = crate::analysis::decompile::abi::conv(program, bitness).args;
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
/// useless without: with it, `Type::Move` is `MOVE`
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
    let args = crate::analysis::decompile::abi::conv(program, bitness).args;
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
pub(crate) fn padding_end(program: &Program, bitness: u32, va: u64, hi: u64) -> u64 {
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
/// returns by name ([`is_noreturn_name`]), one discovery found never
/// returns ([`Analysis::noreturn`]), or glibc's `error` called with a
/// nonzero status ([`calls_noreturn`]).
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
/// never returns.
///
/// That is one discovery found never returns, one named so
/// ([`is_noreturn_name`]), or glibc's imported `error` or `error_at_line`
/// when the block sets the status to a nonzero constant before the call
/// ([`helpers::sets_nonzero_status`]).
///
/// The callee is a direct one, the import a thunk it reaches jumps
/// through, or the import slot it calls through ([`helpers::calls_named`]);
/// glibc's `error` is only ever an import ([`helpers::calls_import`]).
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the callee's name.
/// * `bitness` - 32 or 64.
/// * `b` - The block.
fn calls_noreturn(program: &Program, analysis: &Analysis, bitness: u32, b: &BasicBlock) -> bool {
    let mut instrs = decode_block(program, bitness, b);
    let Some(call) = instrs.pop() else {
        return false;
    };
    near_target(&call).is_some_and(|t| analysis.noreturn.contains(&t))
        || helpers::calls_named(program, analysis, bitness, &call, is_noreturn_name)
        || (program.format == crate::program::BinaryFormat::Elf
            && helpers::calls_import(program, bitness, &call, exits_on_status_name)
            && helpers::sets_nonzero_status(program, bitness, &instrs, |_| false))
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
        for label in returned_labels(program, f) {
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
    #[expect(clippy::iter_over_hash_type, reason = "each list is sorted on its own")]
    for labels in out.values_mut() {
        dedup_sorted(labels);
    }
    out
}

/// Lists the labels a catch funclet hands back to the runtime: the `lea
/// rax, [label]` (x64) or `mov eax, label` (x86) that last sets the result
/// register before each of its `ret`s.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The catch funclet.
///
/// # Returns
///
/// One label per returning block that loads one, in block order.
pub(crate) fn returned_labels(program: &Program, f: &Function) -> Vec<u64> {
    let mut out = Vec::new();
    for b in f.blocks.iter().filter(|b| b.term == BlockTerm::Ret) {
        let Some(bytes) = usize::try_from(b.end - b.start)
            .ok()
            .and_then(|n| program.read_va(b.start, n))
        else {
            continue;
        };
        let mut label = None;
        let bits = if program.is_64 { 64 } else { 32 };
        for i in Decoder::with_ip(bits, bytes, b.start, DecoderOptions::NONE) {
            if i.mnemonic() == Mnemonic::Lea
                && i.op0_kind() == OpKind::Register
                && i.op0_register().full_register() == Register::RAX
                && i.memory_base() == Register::RIP
            {
                label = Some(i.memory_displacement64());
            } else if bits == 32
                && i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op0_register() == Register::EAX
                && i.op1_kind() == OpKind::Immediate32
            {
                label = Some(u64::from(i.immediate32()));
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
        out.extend(label);
    }
    out
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
/// * `ended` - The calls the walk found never return, sorted: each ends
///   its block with no successor, though the instruction after it may
///   start a block other paths reach.
///
/// # Returns
///
/// The blocks in address order.
fn build_blocks(
    entry: u64,
    recs: &[(u64, InstrRec)],
    tables: &[ResolvedTable],
    tail_nops: &[u64],
    ended: &[u64],
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
                if ended.binary_search(&addr).is_err() {
                    block.successors.push(rec.next);
                }
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
        if instr.mnemonic() != Mnemonic::Jmp
            || instr.op0_kind() != OpKind::Memory
            || instr.memory_index() != Register::None
        {
            continue;
        }
        let slot = match instr.memory_base() {
            Register::None | Register::RIP => instr.memory_displacement64(),
            Register::EBX if bitness == 32 => {
                let Some(got) = got_base(program) else {
                    continue;
                };
                u64::from(crate::num::lo32(got).wrapping_add(instr.memory_displacement32()))
            }
            _ => continue,
        };
        f.name = (slot != 0)
            .then(|| import_slots.get(&slot))
            .flatten()
            .map(|&i| crate::search::demangled_name(&program.symbols[i].name));
        if f.name.is_some() {
            f.thunk = Some(slot);
        } else if let Some((target, &i)) = crate::analysis::decompile::abi::bound(program, slot)
            .and_then(|target| Some((target, named.get(&target)?)))
        {
            f.name = Some(crate::search::demangled_name(&program.symbols[i].name));
            f.bound = Some(target);
        }
        f.name_source = if f.name.is_some() {
            NameSource::Symbol
        } else {
            NameSource::None
        };
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
        let yes = image(b"*** ASSERTION FAILED ***\0");
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
            p.bytes[va] = 0x90;
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
            0x48, 0x83, 0xec, 0x28, 0x31, 0xc0, 0x90, 0x90, 0x48, 0x83, 0xc4, 0x28, 0xc3, 0xcc,
            0xcc, 0xcc, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
        ];
        let mut p = code_image(&code);
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
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0x31, 0xc0, // ASM: 0x1010: xor eax, eax
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
