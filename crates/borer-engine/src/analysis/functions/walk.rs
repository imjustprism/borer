//! The recursive-descent walk of one function: its worker, its state and
//! the walk itself.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::frame::{FrameFacts, FrameStep, frame_step};
use super::guess::{
    after_padding, byte_add, declared_interior, is_padding, misplaced_site, mnemonic_name,
    odd_instruction, opens_a_function, opens_on_frame, plausible_entry, prologue_like, slot_jump,
    thunk_slot,
};
use super::helpers::{CHKSTK_X86, epilog_helper_name, frame_helper_name};
use super::seeds::{DataRef, record_data_refs};
use super::sets::{AddrSet, Covered};
use super::tables::{ResolvedTable, resolve_jump_table};
use super::{
    ArgConst, Cursors, FINALLY_CALL_REACH, FINALLY_REACH, GAP_INSTRS_MIN, GUESS_WALK_MAX,
    HANDLER_REACH, InstrRec, Lanes, PARAM_VALUES_MAX, Recorded, Registration, SEEDS_MAX,
    SPLIT_ROUNDS_MAX, Seed, Shared, WAVE_BATCH, WAVE_MIN, build_blocks, call_arg_consts,
    class_registration, decode_at, fingerprint, handler_lands_near, mix, near_target, push_site,
    seh_scope_roots, tears_frame_down, trace_seeds, unwind_nop,
};
use crate::analysis::{BlockTerm, Function, NameSource, RefKind, RefSite, dedup_sorted, is_imm};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::isa::x86::{Code, FlowControl, Mnemonic, OpKind, Register};
use crate::program::Program;

/// Everything one [`walk_function`] produced.
pub(super) struct Walked {
    /// The function record (callers empty, name unset).
    pub(super) func: Function,
    /// The decoded instructions in address order, for the cross-reference
    /// fold.
    pub(super) recs: Vec<(u64, InstrRec)>,
    /// Data references seen.
    pub(super) data_refs: Vec<DataRef>,
    /// Jump tables resolved.
    pub(super) tables: Vec<ResolvedTable>,
    /// The sites among `tables` a byte index table expanded.
    pub(super) indexed: BTreeSet<u64>,
    /// Constants this function's call sites put in argument registers.
    pub(super) arg_consts: Vec<ArgConst>,
    /// Class names registered with their four-character code.
    pub(super) registrations: Vec<Registration>,
    /// The `__chkstk` callee, when the `call X; sub rsp, rax` idiom appeared.
    pub(super) chkstk: Option<u64>,
    /// The frame-building prologue helper (`__SEH_prolog4`, `__EH_prolog3`)
    /// the function calls before touching its stack, when it does.
    pub(super) frame_helper: Option<u64>,
    /// Unconditional jump targets the walk followed into: should one prove
    /// to be a function start later, the jump was a tail call and the
    /// function is walked again.
    pub(super) followed: BTreeSet<u64>,
    /// Call targets whose fall-through the walk followed: should one prove
    /// to never return, the function is walked again.
    pub(super) followed_calls: BTreeSet<u64>,
    /// The walk decoded bytes that are not code: a fall-through or a jump
    /// landed on a byte that does not decode. Real from a real seed too (a
    /// jump table resolved wrong), but from a guessed seed it is the sign the
    /// guess was not a function.
    pub(super) junk: bool,
    /// The walk reached a way out: a return, a tail jump, an indirect jump
    /// it could not resolve, or a call to something that never returns. A
    /// walk that only ever runs into padding has none, and is not a function.
    pub(super) terminated: bool,
    /// A fall-through reached another function's start. Code does not run
    /// off the end of one function into the next, so this walk either
    /// decoded bytes that are not code or missed that its last call never
    /// returns; the start is not absorbed either way.
    pub(super) fell_into_start: bool,
    /// The walk tore a frame down it never set up: a callee-saved `pop`, an
    /// `add rsp, N` or a `leave` came before any `push` or `sub rsp, N`. A
    /// function's epilogue undoes its own prologue, so this is the tail of
    /// a function that began earlier - the unreached rest of the one
    /// before, entered through a padding seed.
    pub(super) unbalanced: bool,
    /// A guessed walk ran past [`GUESS_WALK_MAX`] instructions: longer than
    /// any function, so the guess decoded its way out of one.
    pub(super) overlong: bool,
    /// The first instruction is one a function opens with: a callee-saved
    /// push, an argument homed to the stack, the frame taken, a hotpatch
    /// `mov edi, edi`, an `endbr`. The middle of a function opens with none
    /// of these, and the byte after padding is as often the unreached rest
    /// of the function before it - a case block, a landing pad - as a
    /// function; the disassemblers that measure best on padding hits ask
    /// for a prologue, and so does this.
    pub(super) prologue: bool,
    /// The walk decoded an instruction no compiler emits: `add [rax], al`,
    /// what two zero bytes make, or a port read, a descriptor-table load,
    /// a BCD adjust. Data decodes into those and code does not, so a guess
    /// that reads one is data.
    pub(super) zero_bytes: bool,
    /// The instruction that set `zero_bytes`, named for the seed trace.
    pub(super) odd: Option<&'static str>,
    /// One of those is no byte add a compiler also writes: a compiler does
    /// write `add [ecx+2], al` for `*p += c`, but not two zero bytes' `add
    /// [eax], al` or any of the rest. A byte add alone does not outweigh a
    /// pointer or relocation naming a start.
    pub(super) surely_data: bool,
    /// Call targets found to never return: the call is followed by another
    /// function's start, which no returning call can be.
    pub(super) found_noreturn: BTreeSet<u64>,
    /// Call targets that may never return: the call is followed by `int3`
    /// padding, by a `ud2` trap, or by bytes that do not decode, which a
    /// returning call in an unreachable path can be as well.
    pub(super) found_noreturn_weak: BTreeSet<u64>,
    /// `__except` filters and handlers this function's scope table names
    /// that lie beyond [`HANDLER_REACH`]: its code, not walked, and never a
    /// function of their own.
    pub(super) far_handlers: BTreeSet<u64>,
    /// The `__except` filters and handlers the scope table names near the
    /// entry, walked as the function's own code.
    pub(super) near_handlers: BTreeSet<u64>,
    /// The entry's own bytes are not code: they do not decode, sit on a
    /// relocation, or decode into an instruction no compiler emits. No
    /// witness outweighs that, a call or an export included.
    pub(super) bad_entry: bool,
    /// The entry opens by undoing a frame (`pop`, `leave`): a label inside
    /// a function, past its body.
    pub(super) undoes_frame: bool,
    /// The entry is `jmp [slot]` through a slot in a data section: a thunk
    /// through a pointer, one instruction long and a function.
    pub(super) slot_thunk: bool,
}

/// One walker's own state: what a walk writes and nothing else reads.
pub(super) struct Worker<'a> {
    /// Decoders over the sections the walks touch; they hold the image.
    pub(super) cursors: Cursors<'a>,
    /// Addresses the current walk has decoded; empty between walks.
    pub(super) visited: AddrSet,
    /// Remaining instruction budget.
    pub(super) fuel: u64,
}

impl<'a> Worker<'a> {
    /// A walker over the program with a budget of its own.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `bitness` - Decoder bitness.
    /// * `fuel` - The budget.
    pub(super) fn new(program: &'a Program, bitness: u32, fuel: u64) -> Self {
        Worker {
            cursors: Cursors::new(program, bitness),
            visited: AddrSet::new(program),
            fuel,
        }
    }
}

/// Mutable state of one discovery pass over a work queue of function entries.
pub(super) struct WalkState<'a> {
    /// The pass's own walker, whose budget is the budget across all
    /// functions.
    pub(super) worker: Worker<'a>,
    /// Function entries still to walk.
    pub(super) queue: Vec<u64>,
    /// Function entries already walked.
    pub(super) done: AddrSet,
    /// Functions found so far, in discovery order.
    pub(super) functions: Vec<Function>,
    /// Target address to its reference sites.
    pub(super) xrefs: BTreeMap<u64, Vec<RefSite>>,
    /// Indirect-jump site to resolved targets.
    pub(super) jump_tables: BTreeMap<u64, Vec<u64>>,
    /// Sites whose table a byte index table expanded.
    pub(super) indexed_tables: BTreeSet<u64>,
    /// Callee to parameter index to the constants callers pass there.
    pub(super) param_values: BTreeMap<u64, BTreeMap<u8, BTreeSet<u64>>>,
    /// Class name to the four-character code it registered with.
    pub(super) class_ids: BTreeMap<String, u32>,
    /// Callees followed by `sub rsp, rax`: the stack-probe helper.
    pub(super) chkstk: BTreeSet<u64>,
    /// Callees that build their caller's exception frame: the MSVC prologue
    /// helpers, recognized by their first two instructions.
    pub(super) frame_helpers: BTreeSet<u64>,
    /// Authoritative function starts: the header and symbol seeds plus every
    /// near-call target seen so far. A `jmp` into one is a tail call.
    pub(super) starts: AddrSet,
    /// Per walked function, the jump targets its walk followed into.
    pub(super) followed: BTreeMap<u64, BTreeSet<u64>>,
    /// Per walked function, the call targets whose fall-through it followed.
    pub(super) followed_calls: BTreeMap<u64, BTreeSet<u64>>,
    /// Every call target some walk followed the fall-through of: evidence
    /// that it returns, which no single site can outweigh.
    pub(super) followed_anywhere: BTreeSet<u64>,
    /// Call targets some walk found padding, a trap or undecodable bytes
    /// right after, with how many sites said so; promoted to
    /// [`Self::noreturn`] between rounds when no walk ever followed one.
    pub(super) learned_noreturn: BTreeMap<u64, usize>,
    /// Functions that never return: named ones from the symbol table, every
    /// callee some walk found a function start right after, and every
    /// learned callee no walk ever followed, each unless its own code is
    /// seen to return, and every function whose own code never returns.
    pub(super) noreturn: Arc<AddrSet>,
    /// Callees some walk found a function start right after, held until
    /// the round ends and checked against their own code: the call site
    /// never returns, and the callee may not either, or may be a dispatcher
    /// that returns everywhere else ([`WalkState::can_return`]).
    pub(super) claimed_noreturn: BTreeSet<u64>,
    /// `__except` filters and handlers some function's scope table claims:
    /// the function's own code, never a seed.
    pub(super) handlers: FxHashSet<u64>,
    /// Where the loader patches an absolute address: inside an
    /// instruction's displacement or immediate, never where one starts.
    pub(super) reloc_sites: Arc<AddrSet>,
    /// Whether the image relocates anything at all.
    pub(super) relocatable: bool,
    /// Entries accepted from a guessed seed, in any batch so far.
    pub(super) accepted_guesses: FxHashSet<u64>,
    /// Code a function owns that none of its instructions reaches, by the
    /// function's entry: where the runtime resumes it after a catch or an
    /// `__except` ([`crate::unwind::continuations`], [`catch_continuations`](super::catch_continuations)),
    /// walked with it after its own code.
    pub(super) extra_roots: Arc<FxHashMap<u64, Vec<u64>>>,
    /// IAT and GOT slots of imports that never return.
    pub(super) noreturn_slots: Arc<FxHashSet<u64>>,
    /// IAT and GOT slots of every import: `jmp [slot]` through one is the
    /// linker's thunk for calls to that import.
    pub(super) import_slots: FxHashSet<u64>,
    /// How much the seeds now being walked are trusted.
    pub(super) seed: Seed,
    /// The entries of the current guess list. What an accepted guess calls
    /// is reached by a call and is a fact, and a split round's re-walk of
    /// an accepted function is a fact too; only the guesses themselves are
    /// held to the guess rules.
    pub(super) guessed: Arc<FxHashSet<u64>>,
    /// Guesses that were walked and rejected. Kept apart from `done` so a
    /// fact about the same address - a call to it found later - still walks
    /// it; a rejected guess is only a guess not worth making twice.
    pub(super) rejected: AddrSet,
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
    pub(super) fn run_guesses(&mut self, seeds: Vec<u64>, kind: Seed) -> bool {
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
        if self.seed != Seed::Pointer && self.on_callers_frame(w.func.entry) {
            return Some("runs on another function's frame");
        }
        if w.junk {
            return Some("decoded bytes that are not code");
        }
        if w.undoes_frame {
            return Some("opens by undoing a frame");
        }
        let named = matches!(self.seed, Seed::Pointer | Seed::Reloc)
            && (w.prologue || self.taken_by_code(w.func.entry));
        if w.zero_bytes && (w.surely_data || !named) {
            return Some(w.odd.unwrap_or("decoded an instruction no compiler emits"));
        }
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

    /// Whether a walked function's code takes the address `va`, as a `lea`
    /// passing a callback does.
    ///
    /// That names an entry as surely as a prologue: sqlite's
    /// `incrAggDepth`, a walker callback whose `add [rdx+2], al` is a byte
    /// add, opens with a `cmp` and is reached only through the `lea`.
    ///
    /// # Arguments
    ///
    /// * `va` - The guessed entry.
    fn taken_by_code(&self, va: u64) -> bool {
        self.xrefs.get(&va).is_some_and(|sites| {
            sites
                .iter()
                .any(|s| s.kind == RefKind::Data && s.from_entry.is_some())
        })
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
    pub(super) fn fresh(&self, va: u64) -> bool {
        !self.done.contains(va)
            && !self.rejected.contains(va)
            && !self.handlers.contains(&va)
            && plausible_entry(self.worker.cursors.program, self.worker.cursors.bitness, va)
    }

    /// What every walk of the current wave reads besides the starts,
    /// shared rather than borrowed, so the wave's threads read it while the
    /// pass commits their walks; nothing a commit writes is in it.
    pub(super) fn shared(&self) -> Shared {
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
    pub(super) fn run(&mut self) -> bool {
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
    /// can be seen to return ([`WalkState::can_return`]), and every walked
    /// function whose own code never returns ([`WalkState::ends_every_path`]).
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
    pub(super) fn promote_noreturn(&mut self) {
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
        let ending: Vec<u64> = self
            .functions
            .iter()
            .filter(|f| !self.noreturn.contains(f.entry) && self.ends_every_path(f))
            .map(|f| f.entry)
            .collect();
        Arc::make_mut(&mut self.noreturn).extend(ending);
    }

    /// Tells whether a walked function's own code never returns: no block
    /// returns or leaves the function by a jump, and the paths that end
    /// end at a trap or at a call to a function known never to return.
    ///
    /// A compiler's clone of a function that never returns (GCC's
    /// `.constprop`, `.isra` and `.part` copies) carries no name the
    /// symbol table's no-return list knows, and its callers may lay out
    /// live code right after the call, so only its body says it never
    /// returns.
    ///
    /// # Arguments
    ///
    /// * `f` - The walked function.
    fn ends_every_path(&self, f: &Function) -> bool {
        let inside: FxHashSet<u64> = f.blocks.iter().map(|b| b.start).collect();
        let mut ends = false;
        for b in &f.blocks {
            let stays = b.successors.iter().all(|s| inside.contains(s));
            match b.term {
                BlockTerm::Ret => return false,
                BlockTerm::Jmp | BlockTerm::Cond | BlockTerm::Fall | BlockTerm::Indirect => {
                    if !stays || b.successors.is_empty() {
                        return false;
                    }
                }
                BlockTerm::Invalid => ends = true,
                BlockTerm::Call if stays && !b.successors.is_empty() => {}
                BlockTerm::Call => {
                    if !self.calls_noreturn(b.start, b.end) {
                        return false;
                    }
                    ends = true;
                }
            }
        }
        ends
    }

    /// Tells whether the call ending a block reaches a function known never
    /// to return, directly, through a linker's thunk, or through an import's
    /// slot.
    ///
    /// # Arguments
    ///
    /// * `start` - The block's first instruction.
    /// * `end` - The end of the block's last instruction, the call.
    fn calls_noreturn(&self, start: u64, end: u64) -> bool {
        let program = self.worker.cursors.program;
        let bitness = self.worker.cursors.bitness;
        let mut va = start;
        let call = loop {
            let Some(i) = decode_at(program, bitness, va) else {
                return false;
            };
            if i.is_invalid() || i.next_ip() > end || i.next_ip() <= va {
                return false;
            }
            if i.next_ip() == end {
                break i;
            }
            va = i.next_ip();
        };
        if call.flow_control() != FlowControl::Call {
            return false;
        }
        if call.op0_kind() == OpKind::Memory {
            return call.memory_index() == Register::None
                && matches!(call.memory_base(), Register::None | Register::RIP)
                && self.noreturn_slots.contains(&call.memory_displacement64());
        }
        let t = call.near_branch_target();
        if self.noreturn.contains(t) {
            return true;
        }
        let Some(mut first) = decode_at(program, bitness, t) else {
            return false;
        };
        if matches!(first.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
            let Some(next) = decode_at(program, bitness, first.next_ip()) else {
                return false;
            };
            first = next;
        }
        slot_jump(&first).is_some_and(|slot| self.noreturn_slots.contains(&slot))
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
    pub(super) fn can_return(&self, t: u64, returning: &FxHashSet<u64>) -> bool {
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
    pub(super) fn run_code_seeds(&mut self) -> bool {
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
                    crate::analysis::is_executable_va(program, t)
                        && !covered.contains(t)
                        && self.fresh(t)
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
    pub(super) fn forget(&mut self, entries: &[u64]) {
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
    pub(super) fn drain(&mut self) -> bool {
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
    pub(super) fn commit(&mut self, entry: u64, walked: Walked) {
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

/// What every walk of a wave reads and none writes.
#[derive(Clone, Copy)]
pub(super) struct Known<'a> {
    /// Known function starts.
    pub(super) starts: &'a AddrSet,
    /// Functions known never to return.
    pub(super) noreturn: &'a AddrSet,
    /// Import slots of functions that never return.
    pub(super) noreturn_slots: &'a FxHashSet<u64>,
    /// Code each function owns that its instructions do not reach, by
    /// entry.
    pub(super) extra_roots: &'a FxHashMap<u64, Vec<u64>>,
    /// Where the loader patches an absolute address, or `None` when the
    /// image relocates nothing.
    pub(super) reloc_sites: Option<&'a AddrSet>,
    /// The entries of the current guess list, each held to the guess cap.
    pub(super) guessed: &'a FxHashSet<u64>,
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
pub(super) fn walk_capped(worker: &mut Worker<'_>, entry: u64, known: &Known<'_>) -> Walked {
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
pub(super) enum Via {
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
/// A call to the very next instruction is 32-bit position-independent
/// code reading its own address (`call $+5; pop ebx`), not a call: it falls
/// through and names no callee, where it made the rest of the function a
/// second function.
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
pub(super) fn walk_function(
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
            if reloc_sites.is_some_and(|s| s.contains(addr) || misplaced_site(cursors, s, &instr)) {
                junk |= linear && !in_handlers;
                bad_entry |= recs.is_empty() && !in_handlers;
                continue;
            }
            let next = instr.next_ip();
            let flow = match instr.flow_control() {
                FlowControl::Interrupt
                    if instr.mnemonic() == Mnemonic::Int
                        && instr.try_immediate(0).ok() == Some(0x80) =>
                {
                    FlowControl::Next
                }
                FlowControl::Call if near_target(&instr) == Some(next) => FlowControl::Next,
                other => other,
            };
            let target = near_target(&instr).filter(|&t| t != next || flow != FlowControl::Next);
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
            let arg_cleanup = instr.mnemonic() == Mnemonic::Add
                && (after_call.contains(&addr)
                    || (bitness == 32
                        && frame.sub_rsp.is_none_or(|(_, taken)| {
                            instr.try_immediate(1).unwrap_or(0) != taken
                        })));
            if tears_frame_down(&instr) && !arg_cleanup {
                after_epilogue.insert(next);
            }
            if instr.mnemonic() == Mnemonic::Pop && after_epilogue.contains(&addr) {
                after_epilogue.insert(next);
            }
            let patched = reloc_sites.and_then(|s| Some((s, cursors.constant_offsets(&instr)?)));
            record_data_refs(program, &mapped, &instr, addr, &mut data_refs, patched);
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
                    Some(t) if addr == entry && t == next && instr.len() == 2 => {
                        callees.insert(t);
                        terminated = true;
                    }
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
                            resolve_jump_table(program, bitness, addr, &recorded, &recs, &|t| {
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
                    if !crate::analysis::is_executable_va(program, t) {
                        pending.push((next, Via::Fall));
                        continue;
                    }
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
    let conv = crate::analysis::decompile::abi::conv(program, bitness);
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
        bound: None,
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
