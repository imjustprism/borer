//! Analysis results derived from a [`Program`] (pure, derived, immutable).
//!
//! [`Analysis::compute`] walks executable code recursively from the entry point
//! and exported symbols, recovers functions and their basic blocks, and builds
//! a code/data cross-reference index. Everything here is a deterministic
//! function of the program bytes: same input, same output, byte-identical.

mod a32;
pub use a32::{entry_or_gap, in_blocks};
mod a64;
pub mod about;
pub mod anchors;
pub mod apihash;
pub mod apply;
pub mod attributes;
pub mod cdecl;
mod cell;
pub mod classes;
pub mod decompile;
mod descriptors;
pub mod eh;
pub mod encode;
pub mod fieldrefs;
pub mod functions;
pub(crate) mod guards;
pub mod libnames;
pub mod map;
pub mod messages;
pub mod modsdk;
mod naming;
pub mod objc;
pub mod opcodes;
pub mod ports;
pub mod protocol;
pub mod protos;
pub mod prototypes;
pub mod qt;
pub mod reads;
pub mod recognize;
pub mod render;
mod returns;
pub(crate) mod rtti;
pub mod runtime;
pub mod schema;
pub mod sdk;
mod seh32;
pub mod senders;
pub mod sigs;
pub mod snapshot;
mod switch_index;
pub mod syscalls;
pub mod typelib;
pub mod utypes;
pub mod vtables;
mod x87;

use std::any::{Any, TypeId};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use cell::{Cell, Publish};

use crate::isa::Isa;
use crate::isa::x86::OpKind;

use crate::fxmap::FxHashMap;

use crate::program::{Program, Symbol, SymbolKind};

/// How a basic block ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockTerm {
    /// A return instruction.
    Ret,
    /// An unconditional near jump.
    Jmp,
    /// A conditional jump: two successors, target and fall-through.
    Cond,
    /// A call; the block continues at the return address.
    Call,
    /// An indirect jump (register or memory operand), a jump table when resolved.
    Indirect,
    /// No terminator: the next instruction starts a block another edge targets.
    Fall,
    /// An undecodable or trapping instruction (`ud2`, `int3`, ...).
    Invalid,
}

impl BlockTerm {
    /// Returns the lowercase name used in block tables and graphs.
    pub fn name(self) -> &'static str {
        match self {
            BlockTerm::Ret => "ret",
            BlockTerm::Jmp => "jmp",
            BlockTerm::Cond => "cond",
            BlockTerm::Call => "call",
            BlockTerm::Indirect => "indirect",
            BlockTerm::Fall => "fall",
            BlockTerm::Invalid => "invalid",
        }
    }
}

/// A maximal straight-line run of instructions with one entry and one exit.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Address of the first instruction.
    pub start: u64,
    /// End of the block's last instruction (exclusive).
    pub end: u64,
    /// How the block ends.
    pub term: BlockTerm,
    /// Start addresses of successor blocks, held in the block for up to
    /// two: all but a switch's have at most two, and a heap list each cost
    /// more than the block on a binary of millions of blocks.
    pub successors: smallvec::SmallVec<[u64; 2]>,
}

/// Where a function's name came from.
///
/// A name read out of the binary and one worked out from the code are not
/// the same kind of fact, and every listing says which it is, so an agent can
/// treat `Ns::Type::Method` (a signature literal the
/// function itself carries) differently from `class_141212308::vfunc_5_47`
/// (a slot of a table whose class is itself a guess).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum NameSource {
    /// No name: the function is `sub_<entry>`.
    #[default]
    None,
    /// The program's symbol table, or an import's name for its thunk.
    Symbol,
    /// A compiler or runtime helper recognized by its shape (`__chkstk`, a
    /// refcount release, the assert reporter).
    Helper,
    /// A `__FUNCSIG__`-style signature string only this function references.
    Signature,
    /// A dispatcher's wrong-type message naming the type this handles.
    Handler,
    /// A vtable slot of a recovered class, numbered by position.
    Slot,
    /// Qt moc metadata mapping a signal, slot or method to the function.
    Qt,
    /// An exception funclet named after the function it belongs to.
    Funclet,
    /// A pack's `[names]` line, matched by the function's first bytes.
    Pack,
    /// A library signature (a pack's `lib` line): the function's bytes as
    /// the library's object has them, and what they reference.
    Library,
    /// Objective-C runtime metadata naming a method's implementation or a
    /// message-send stub ([`objc`]).
    ObjC,
    /// The known constants of one algorithm the function uses
    /// ([`recognize`]): a table it reads or immediates it carries.
    Constants,
}

impl NameSource {
    /// The short tag listings print: `-`, `sym`, `hlp`, `sig`, `hnd`,
    /// `slot`, `qt`, `fnl`, `pack`, `lib`, `objc`, `const`.
    #[must_use]
    pub fn code(self) -> &'static str {
        match self {
            NameSource::None => "-",
            NameSource::Symbol => "sym",
            NameSource::Helper => "hlp",
            NameSource::Signature => "sig",
            NameSource::Handler => "hnd",
            NameSource::Slot => "slot",
            NameSource::Qt => "qt",
            NameSource::Funclet => "fnl",
            NameSource::Pack => "pack",
            NameSource::Library => "lib",
            NameSource::ObjC => "objc",
            NameSource::Constants => "const",
        }
    }

    /// The source spelled out, for a summary.
    #[must_use]
    pub fn describe(self) -> &'static str {
        match self {
            NameSource::None => "no name in the binary or the code",
            NameSource::Symbol => "declared in the binary's symbol table",
            NameSource::Helper => "a helper recognized by its shape",
            NameSource::Signature => "a signature string the function itself carries",
            NameSource::Handler => "the wrong-type message of a command handler",
            NameSource::Slot => "a vtable slot of a recovered class, numbered by position",
            NameSource::Qt => "Qt moc metadata",
            NameSource::Funclet => "the function the funclet belongs to",
            NameSource::Pack => "a pack's [names] line, by the function's first bytes",
            NameSource::Library => {
                "a library signature: the function's bytes and what they reference, as the library's object has them"
            }
            NameSource::ObjC => "Objective-C runtime metadata",
            NameSource::Constants => "inferred from the known constants of an algorithm it uses",
        }
    }
}

/// One discovered function.
#[derive(Debug, Clone)]
pub struct Function {
    /// Address discovery entered the function at.
    pub entry: u64,
    /// Lowest decoded address (entry or below via backward branches).
    pub start: u64,
    /// End of the highest decoded instruction (exclusive).
    pub end: u64,
    /// Number of decoded instructions.
    pub instr_count: usize,
    /// Basic blocks sorted by start address.
    pub blocks: Vec<BasicBlock>,
    /// Near call targets (sorted, deduplicated).
    pub callees: Vec<u64>,
    /// Entries of functions that call this one (sorted, deduplicated).
    pub callers: Vec<u64>,
    /// From the program's symbol table when the entry matches one, else
    /// inferred from a signature string only this function references (an
    /// assert's `__FUNCSIG__`); see [`Function::name_inferred`].
    pub name: Option<String>,
    /// The name was inferred from a signature string, not read from a symbol.
    pub name_inferred: bool,
    /// Where the name came from, so a reader can weigh it.
    pub name_source: NameSource,
    /// The slot this function jumps through when it is an import thunk,
    /// `jmp [slot]` and nothing else: the import under an address of the
    /// program's own, not code of the program's own.
    pub thunk: Option<u64>,
    /// The entry of the function this one is a linkage stub for: a PLT
    /// entry whose slot the loader binds to a function the program defines
    /// itself, so a call to the stub is a call to that function
    /// ([`decompile::abi::bound`]).
    pub bound: Option<u64>,
    /// The funclet this function is: code the C++ exception runtime runs
    /// on another function's frame, found from that function's exception
    /// metadata ([`eh`]) and named after it.
    pub funclet: Option<Funclet>,
    /// Return type and parameter types parsed from the signature string the
    /// name came from, when it had one.
    pub signature: Option<Signature>,
    /// Fingerprint of the instructions, with the addresses they name left
    /// out, so two copies of one function agree ([`Analysis::clones_of`]);
    /// the slot a function that is one jump through it jumps through stays
    /// in, since that slot is all such a thunk is.
    pub body_hash: u64,
    /// Fingerprint of the instruction shape alone, mnemonics and operand
    /// kinds, so functions differing only in registers, constants or
    /// offsets agree ([`Analysis::shapes_of`]).
    pub shape_hash: u64,
    /// Whether the function hands a value back: `Some(true)` when some
    /// caller reads the return register after calling it, `Some(false)`
    /// when its body returns nothing or every caller discards what is only
    /// a callee's leftover, `None` when no call site is known or the
    /// callers discard a value the body computes itself. `Some(false)` lets
    /// the decompiler drop a stale `return rax;` and type the function
    /// `void` when no signature declares a result.
    pub returns_value: Option<bool>,
    /// Width in bits of the value returned through rax when it is narrower
    /// than the register: the lane of the function's own last rax writes
    /// before every `ret` (`sete al` returns a byte), or the widest read any
    /// caller makes of the result, whichever is narrower. `None` when the
    /// whole register is returned or nothing narrower is known. Lets the
    /// decompiler read such a result without a mask.
    pub ret_width: Option<u8>,
    /// Width in bits every path to a `ret` WRITES of rax, when that is at
    /// most a byte or a word (`sete al`, `mov al, dl`): the machine's bits
    /// above it are the caller's, left as its own `rax` had them, so a
    /// caller reading the whole register reads its own value merged with
    /// the lane. `None` when some path writes rax fully (`mov eax, 0x50`
    /// zeroes the upper half) or hands it back from a call.
    pub ret_partial: Option<u8>,
    /// Width in bits, 32 or 64, of the `float` or `double` the function
    /// hands back in `xmm0` on a 64-bit target, where its declaration
    /// states one or every exit leaves one and some caller reads it, or in
    /// `st0` on a 32-bit one, where every exit leaves the x87 stack one
    /// value deeper ([`returns`]). `None` for a result in rax or none.
    pub ret_float: Option<u8>,
    /// The function hands `rax` back untouched: on every path to a `ret`
    /// nothing writes it and nothing is called (a stack-cookie check), so a
    /// call to it is not a result and the caller's `rax` survives it. Only
    /// functions of at most 32 instructions are checked ([`returns`]).
    pub preserves_rax: bool,
    /// The function hands a second value back in `rdx`: some caller reads
    /// `rdx` before writing it after the call ([`returns`]). The calling
    /// convention leaves `rdx` to the callee to clobber, so such a read
    /// wants the value the callee left there, a second result alongside
    /// the one in `rax`.
    pub hands_back_rdx: bool,
    /// Class of the object a parameter points at, by argument position,
    /// inferred from callers that pass their own `this`, or the type of the
    /// object it points at when callers pass the address of a field whose
    /// embedded type is known (`Core::Ptr<T>`, an embedded object)
    /// ([`vtables`]); only set on functions without a declared signature.
    pub param_hints: BTreeMap<u8, String>,
    /// Class of the object the result points at, inferred from callers that
    /// pass the result as a method's `this` ([`vtables`]); only set on
    /// functions without a declared signature.
    pub ret_hint: Option<String>,
    /// Stack-passed arguments this function reads (slots above the shadow
    /// space and return address), from `[rsp+X]`/`[rbp+X]` accesses after the
    /// prologue. Callers need only materialize that many outgoing slots.
    pub stack_args: u32,
    /// Bytes of arguments the function pops on return (`ret imm16`), which
    /// a `stdcall` or `thiscall` function states exactly; zero when the
    /// caller cleans up.
    pub stack_pop: u32,
}

/// A piece of code the C++ exception runtime runs on another function's
/// frame: the handler thunk a function registers, an unwind action or a
/// catch clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Funclet {
    /// Entry of the function whose frame the funclet runs on; `ebp` is that
    /// frame's pointer while it runs.
    pub parent: u64,
    /// What the runtime runs it for.
    pub role: FuncletRole,
}

/// What the exception runtime runs a funclet for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FuncletRole {
    /// The handler thunk itself, `mov eax, FuncInfo; jmp __CxxFrameHandler3`.
    Handler,
    /// The unwind action of a state: the destructors run on leaving it.
    Unwind(u32),
    /// The body of a `catch` clause, by try block and clause index.
    Catch(u32, u32),
    /// The filter of an `__except`, by `__try` scope: run to decide whether
    /// the body handles the exception.
    Filter(u32),
    /// The body of a `__finally`, by `__try` scope.
    Finally(u32),
    /// The body of an `__except`, by `__try` scope: a label the runtime jumps
    /// to, that nothing else reaches. A body inside the parent's declared
    /// range is walked as the parent's own code; only one moved away is a
    /// funclet.
    Except(u32),
}

impl FuncletRole {
    /// Describes the role in a phrase, for a listing or a note.
    ///
    /// # Returns
    ///
    /// `the exception handler thunk`, `the unwind action of state N`,
    /// `catch clause K of try block T`, or the `__try` scope a filter, a
    /// `__finally` or an `__except` body belongs to.
    #[must_use]
    pub fn describe(self) -> String {
        match self {
            FuncletRole::Handler => "the exception handler thunk".to_owned(),
            FuncletRole::Unwind(state) => format!("the unwind action of state {state}"),
            FuncletRole::Catch(block, clause) => {
                format!("catch clause {clause} of try block {block}")
            }
            FuncletRole::Filter(scope) => format!("the __except filter of __try scope {scope}"),
            FuncletRole::Finally(scope) => format!("the __finally of __try scope {scope}"),
            FuncletRole::Except(scope) => format!("the __except body of __try scope {scope}"),
        }
    }
}

/// One call-site record of a function's Itanium LSDA: a range of its code a
/// call may throw through, where the unwinder resumes when one does, and
/// what the landing pad catches ([`crate::lsda`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThrowSite {
    /// Start of the guarded range.
    pub start: u64,
    /// End of the guarded range (exclusive).
    pub end: u64,
    /// Where the unwinder resumes: the function's own code, reached by none
    /// of its instructions. `None` when the range does not handle what it
    /// catches.
    pub landing_pad: Option<u64>,
    /// The demangled types the landing pad's action chain catches, in the
    /// order its clauses run.
    pub catches: Vec<String>,
    /// The type filter of each catch in [`ThrowSite::catches`], in the same
    /// order: the selector the landing pad compares to tell which clause
    /// matched.
    pub filters: Vec<i64>,
    /// The action chain holds a cleanup entry, which runs for whatever
    /// passes through, caught or not.
    pub cleanup: bool,
}

impl Function {
    /// Returns the bytes of code the function owns: its blocks' extents summed.
    ///
    /// Below the `start..end` span whenever the blocks are not contiguous,
    /// which a tail jump into a distant thunk makes common. Absorbing that
    /// block puts the span hundreds of kilobytes past the entry while the
    /// function still holds two instructions, so the span cannot be a size.
    pub fn size(&self) -> u64 {
        self.blocks
            .iter()
            .map(|b| b.end.saturating_sub(b.start))
            .sum()
    }
}

/// A function signature as its source declared it, from a `__FUNCSIG__` or
/// `__PRETTY_FUNCTION__` string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// Return type text, `void` when none.
    pub ret: String,
    /// Qualified function name.
    pub name: String,
    /// Parameter type texts, in order; `(void)` is empty.
    pub params: Vec<String>,
    /// A `const` member function.
    pub is_const: bool,
    /// The value is returned through a hidden pointer argument that precedes
    /// the declared parameters: a class returned by value, which MSVC's
    /// `__FUNCSIG__` elaborates as `class`/`struct`/`union`.
    pub by_pointer: bool,
}

/// One reference site pointing at a target address.
#[derive(Debug, Clone)]
pub struct RefSite {
    /// Address of the referencing instruction.
    pub va: u64,
    /// What the site does with its target; [`RefKind::word`] spells it.
    pub kind: RefKind,
    /// Entry of the containing function, when known.
    pub from_entry: Option<u64>,
}

/// What a reference site does with its target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefKind {
    /// A near or indirect call.
    Call,
    /// A near or indirect jump.
    Jmp,
    /// A data reference from code: a load, a store or an address-carrying
    /// immediate.
    Data,
    /// The base of a table an index register scales into (a switch's jump
    /// table, a lookup table).
    Index,
    /// A pointer to the function stored in data, which is how a virtual
    /// method and a registered callback are reached.
    Table,
    /// A pointer to data stored in data (a locator naming its descriptor).
    Ptr,
}

impl RefKind {
    /// Returns the word a listing prints for the kind: `call`, `jmp`,
    /// `imm/mem`, `index`, `table` or `ptr`.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            RefKind::Call => "call",
            RefKind::Jmp => "jmp",
            RefKind::Data => "imm/mem",
            RefKind::Index => "index",
            RefKind::Table => "table",
            RefKind::Ptr => "ptr",
        }
    }
}

impl RefSite {
    /// Tells whether the site transfers control to its target, by a call
    /// or a jump, rather than referencing it as data.
    #[must_use]
    pub fn is_branch(&self) -> bool {
        matches!(self.kind, RefKind::Call | RefKind::Jmp)
    }
}

/// Iterates the entries of the functions referencing a target as data:
/// every site that is not a call or a jump, with a known function.
///
/// # Arguments
///
/// * `sites` - The target's reference sites.
pub(crate) fn data_referrers(sites: &[RefSite]) -> impl Iterator<Item = u64> + '_ {
    sites
        .iter()
        .filter(|s| !s.is_branch())
        .filter_map(|s| s.from_entry)
}

/// Fewest functions worth spreading over the cores in a sweep.
const STRIPE_MIN: usize = 256;

/// Maps `f` over `items` across the cores, results in the items' order.
///
/// Workers take every `threads`-th item, so the work spreads without a
/// queue; a worker that fails leaves `None` in its places. With one core,
/// or fewer than 256 items, the map runs inline.
///
/// # Arguments
///
/// * `items` - The inputs.
/// * `f` - The per-item function; it sees only shared references.
///
/// # Returns
///
/// One result per item, in order.
pub(crate) fn striped<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<Option<R>> {
    striped_with(items, STRIPE_MIN, || (), |(), x| f(x))
}

/// Maps `f` over `items` across the cores with a state per worker (a
/// context carrying memos), results in the items' order.
///
/// Workers take every `threads`-th item; each makes its own state with
/// `init` first, so a memo need not be shared. A worker that fails leaves
/// `None` in its places. With one core, or fewer than `min` items, the map
/// runs inline over one state.
///
/// # Arguments
///
/// * `items` - The inputs.
/// * `min` - Fewest items worth a thread each.
/// * `init` - Makes one worker's state.
/// * `f` - The per-item function over the worker's state.
///
/// # Returns
///
/// One result per item, in order.
pub(crate) fn striped_with<T: Sync, S, R: Send>(
    items: &[T],
    min: usize,
    init: impl Fn() -> S + Sync,
    f: impl Fn(&S, &T) -> R + Sync,
) -> Vec<Option<R>> {
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(items.len().max(1));
    if threads <= 1 || items.len() < min {
        let state = init();
        return items.iter().map(|x| Some(f(&state, x))).collect();
    }
    let init = &init;
    let f = &f;
    let here = reads::Handle::here();
    let stripes: Vec<Vec<(usize, R)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let here = here.clone();
                scope.spawn(move || {
                    here.enter(|| {
                        let state = init();
                        items
                            .iter()
                            .enumerate()
                            .skip(t)
                            .step_by(threads)
                            .map(|(i, x)| (i, f(&state, x)))
                            .collect::<Vec<_>>()
                    })
                })
            })
            .collect();
        handles.into_iter().filter_map(|h| h.join().ok()).collect()
    });
    let mut out: Vec<Option<R>> = (0..items.len()).map(|_| None).collect();
    for (i, r) in stripes.into_iter().flatten() {
        if let Some(slot) = out.get_mut(i) {
            *slot = Some(r);
        }
    }
    out
}

/// Runs `side` on a thread of its own while `main` runs on this one.
///
/// For two passes that read nothing of each other: the analysis scans the
/// image for crypto tables, which reads the program alone, while discovery
/// walks the code. With one core both run here, `main` first.
///
/// # Arguments
///
/// * `main` - The pass this thread runs.
/// * `side` - The pass the other thread runs.
///
/// # Returns
///
/// What `main` returned, and what `side` returned or `None` when its
/// thread failed.
pub(crate) fn beside<M, S: Send>(
    main: impl FnOnce() -> M,
    side: impl FnOnce() -> S + Send,
) -> (M, Option<S>) {
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    if cores <= 1 {
        let m = main();
        return (m, Some(side()));
    }
    let here = reads::Handle::here();
    std::thread::scope(|scope| {
        let handle = scope.spawn(|| here.enter(side));
        let m = main();
        (m, handle.join().ok())
    })
}

/// The crypto and hash tables the image holds
/// ([`crate::crypto::find_crypto_constants`]), with the slicing tables
/// derived from each CRC-32 table, by address.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// Each table's address and the algorithm's name.
fn crypto_tables(program: &Program) -> BTreeMap<u64, &'static str> {
    let mut crypto: BTreeMap<u64, &'static str> = crate::crypto::find_crypto_constants(program)
        .into_iter()
        .filter_map(|hit| Some((hit.va?, hit.name)))
        .collect();
    let crc_tables: Vec<u64> = crypto
        .iter()
        .filter(|(_, name)| name.starts_with("CRC-32 (IEEE"))
        .map(|(&va, _)| va)
        .collect();
    for table in crc_tables {
        crypto.extend(crate::crypto::crc32_slices(program, table));
    }
    crypto
}

/// Most bytes the item results of one [`Derived`] hold before the least
/// recently asked for are let go.
///
/// An item result is one function's text, name table or call shape, one
/// method's assertion votes, one function's summary. Sized on a
/// 100,000-function C++ client, where a decompile of a class method reads
/// its class's other methods back and one function asked for keeps about
/// 8 KB of them: 3,000 decompiles hold about 23 MB and a session's catalogs
/// under a rename about 20 MB, so an ordinary session never reaches the
/// budget, while decompiling every function would hold 130 MB and stops
/// here.
pub const ITEMS_BUDGET: usize = 64 << 20;

/// The share of the budget the item results are cut back to once they pass
/// it, as a fraction: far enough under it that the builds right after one
/// sweep do not each start another.
const ITEMS_KEPT: (usize, usize) = (3, 4);

/// The one memo store of an [`Analysis`]: every result derived after
/// [`Analysis::compute`], each built once and shared by every later query.
///
/// A result is found by its kind, a fixed name, and a key saying what else
/// it depends on, and how it was asked for says how long it is kept:
///
/// * a result of the program alone ([`Derived::get_or_build`]) is kept as
///   long as the analysis;
/// * a whole-program result read under names, those of the overlay with a
///   fingerprint ([`Derived::get_or_build_named`]), is kept while those names
///   are in force ([`Derived::forget_names_but`]);
/// * one item's result read under names ([`Derived::get_or_build_item`]) is
///   kept while those names are in force and the items' results fit the
///   budget ([`ITEMS_BUDGET`]), the least recently asked for let go first.
///
/// Every result is a function of the program, the names and its key alone,
/// so one let go is built again, byte for byte, when it is asked for again:
/// letting go costs time, never a different answer, and no caller compares
/// two results by address. How recently a result was asked for is a count
/// of the asks, not a clock.
///
/// Each result keeps what it read of the overlay ([`reads::Reads`]), so an
/// edit ([`Derived::moved`]) carries every result that read none of the
/// facts it changed over to the new names, and lets go of only the rest.
///
/// Each result has one cell, so a thread asking for a result while another
/// builds it waits for that build instead of repeating it. No lock is held
/// while a result is built, so a build may ask for other results, never for
/// its own: that would wait on itself.
pub struct Derived {
    /// Each kind's cells.
    kinds: Mutex<Kinds>,
    /// Asks for item results so far: an ask stamps its cell with the count,
    /// so the lowest stamps are the least recently asked for.
    asks: AtomicU64,
    /// Bytes the built item results hold, as their weights say.
    item_bytes: AtomicUsize,
    /// Most bytes the item results may hold, [`ITEMS_BUDGET`] unless set.
    budget: AtomicUsize,
    /// Results built so far, of every kind and scope.
    builds: AtomicU64,
}

impl Default for Derived {
    fn default() -> Self {
        Self {
            kinds: Mutex::default(),
            asks: AtomicU64::new(0),
            item_bytes: AtomicUsize::new(0),
            budget: AtomicUsize::new(ITEMS_BUDGET),
            builds: AtomicU64::new(0),
        }
    }
}

/// What a result in [`Derived`] was read under, which says how long it is
/// kept.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Scope {
    /// The program alone.
    Program,
    /// The whole program, under the names of the overlay with this
    /// fingerprint.
    Names(u64),
    /// One item, under the names of the overlay with this fingerprint.
    Item(u64),
}

/// What becomes of one result in [`Derived`] when results are let go.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fate {
    /// Kept where it is.
    Keep,
    /// Let go.
    Drop,
    /// Filed under another scope, unless a result is already there.
    Move(Scope),
}

/// Each kind's cells in [`Derived`], by the kind's name and its cells' type.
type Kinds = FxHashMap<(&'static str, TypeId), Arc<dyn Kind>>;

/// The cells of one kind of result in [`Derived`], by what each was read
/// under and its key.
type Cells<K, T> = Mutex<FxHashMap<(Scope, K), Arc<Cell<T>>>>;

/// What [`Derived`] reads of one kind's cells without naming their types.
trait Kind: Any + Send + Sync {
    /// How many results the kind holds, built or being built.
    fn held(&self) -> usize;

    /// Adds when each built item result was last asked for, and its weight.
    ///
    /// # Arguments
    ///
    /// * `out` - Collects `(stamp, bytes)` pairs.
    fn asked(&self, out: &mut Vec<(u64, usize)>);

    /// Decides the fate of every built result by `pick`; one being built
    /// stays where it is.
    ///
    /// A result moved onto a scope and key that already hold one is let
    /// go, so the one there, maybe still being built, stays.
    ///
    /// # Arguments
    ///
    /// * `pick` - Decides a result's fate by what it was read under, when
    ///   it was last asked for, and what it read.
    ///
    /// # Returns
    ///
    /// The bytes the item results let go of held.
    fn sweep(&self, pick: &dyn Fn(Scope, u64, &reads::Reads) -> Fate) -> usize;

    /// The cells as [`Any`], to be downcast to their [`Cells`] type.
    fn into_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync>;
}

impl<K: Hash + Eq + Send + 'static, T: Send + Sync + 'static> Kind for Cells<K, T> {
    fn held(&self) -> usize {
        self.lock().map_or(0, |cells| cells.len())
    }

    fn asked(&self, out: &mut Vec<(u64, usize)>) {
        if let Ok(cells) = self.lock() {
            out.extend(
                cells
                    .iter()
                    .filter(|((scope, _), cell)| {
                        matches!(scope, Scope::Item(_)) && matches!(cell.value.get(), Some(Some(_)))
                    })
                    .map(|(_, cell)| {
                        (
                            cell.asked.load(Ordering::Relaxed),
                            cell.weight.load(Ordering::Relaxed),
                        )
                    }),
            );
        }
    }

    fn sweep(&self, pick: &dyn Fn(Scope, u64, &reads::Reads) -> Fate) -> usize {
        let Ok(mut cells) = self.lock() else {
            return 0;
        };
        let freed_by = |scope: Scope, cell: &Cell<T>| match scope {
            Scope::Item(_) => cell.weight.load(Ordering::Relaxed),
            Scope::Program | Scope::Names(_) => 0,
        };
        let mut freed = 0;
        let mut moved = Vec::new();
        let mut kept = FxHashMap::default();
        #[expect(
            clippy::iter_over_hash_type,
            reason = "each cell's fate is its own and the kept map is keyed"
        )]
        for ((scope, key), cell) in cells.drain() {
            let fate = match cell.value.get() {
                None => Fate::Keep,
                Some(None) => Fate::Drop,
                Some(Some((_, read))) => pick(scope, cell.asked.load(Ordering::Relaxed), read),
            };
            match fate {
                Fate::Keep => {
                    kept.insert((scope, key), cell);
                }
                Fate::Drop => freed += freed_by(scope, &cell),
                Fate::Move(to) => moved.push(((to, key), cell)),
            }
        }
        for (at, cell) in moved {
            match kept.entry(at) {
                std::collections::hash_map::Entry::Occupied(there) => {
                    freed += freed_by(there.key().0, &cell);
                }
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert(cell);
                }
            }
        }
        *cells = kept;
        freed
    }

    fn into_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync> {
        self
    }
}

impl Clone for Derived {
    /// Returns an empty store with the same item budget: every result is
    /// built again, byte for byte, when it is asked for.
    fn clone(&self) -> Self {
        let fresh = Self::default();
        fresh
            .budget
            .store(self.budget.load(Ordering::Relaxed), Ordering::Relaxed);
        fresh
    }
}

impl std::fmt::Debug for Derived {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let held: usize = self
            .kinds
            .lock()
            .map_or(0, |kinds| kinds.values().map(|k| k.held()).sum());
        write!(f, "Derived({held} results)")
    }
}

impl Derived {
    /// Returns the result of `kind` for `key`, a result of the program
    /// alone, built by `make` the first time anyone asks for it and kept as
    /// long as the analysis.
    ///
    /// The kind's name and the key and result types together pick the
    /// cells, so two sites naming one kind share results only when they
    /// agree on both types.
    ///
    /// # Arguments
    ///
    /// * `kind` - What the result is, as a fixed name.
    /// * `key` - What it depends on beyond the analysis.
    /// * `make` - Builds the result.
    ///
    /// # Returns
    ///
    /// The shared result; built afresh and not kept only when a lock was
    /// poisoned by a build that panicked.
    pub fn get_or_build<K, T>(&self, kind: &'static str, key: K, make: impl FnOnce() -> T) -> Arc<T>
    where
        K: Hash + Eq + Send + 'static,
        T: Send + Sync + 'static,
    {
        self.fetch(kind, Scope::Program, key, make, |_| 0)
    }

    /// Returns the result of `kind` for `key` read over the whole program
    /// under the names `names`, built by `make` the first time anyone asks
    /// for it and kept while those names are in force.
    ///
    /// # Arguments
    ///
    /// * `kind` - What the result is, as a fixed name.
    /// * `names` - [`Overlay::fingerprint`] of the overlay `make` reads.
    /// * `key` - What else it depends on.
    /// * `make` - Builds the result.
    ///
    /// # Returns
    ///
    /// The shared result, as for [`Derived::get_or_build`].
    pub fn get_or_build_named<K, T>(
        &self,
        kind: &'static str,
        names: u64,
        key: K,
        make: impl FnOnce() -> T,
    ) -> Arc<T>
    where
        K: Hash + Eq + Send + 'static,
        T: Send + Sync + 'static,
    {
        self.fetch(kind, Scope::Names(names), key, make, |_| 0)
    }

    /// Returns the result of `kind` for one item, `key`, read under the
    /// names `names`, built by `make` the first time anyone asks for it and
    /// kept while those names are in force and the item results fit the
    /// budget.
    ///
    /// # Arguments
    ///
    /// * `kind` - What the result is, as a fixed name.
    /// * `names` - [`Overlay::fingerprint`] of the overlay `make` reads.
    /// * `key` - The item: a function's entry, a class and an offset.
    /// * `make` - Builds the result.
    /// * `weigh` - The bytes the result holds beyond its own size: the
    ///   capacity of its strings and collections.
    ///
    /// # Returns
    ///
    /// The shared result, as for [`Derived::get_or_build`].
    pub fn get_or_build_item<K, T>(
        &self,
        kind: &'static str,
        names: u64,
        key: K,
        make: impl FnOnce() -> T,
        weigh: impl FnOnce(&T) -> usize,
    ) -> Arc<T>
    where
        K: Hash + Eq + Send + 'static,
        T: Send + Sync + 'static,
    {
        self.fetch(kind, Scope::Item(names), key, make, weigh)
    }

    /// Lets go of every result read under names other than those in force
    /// for a caller holding `overlay`: an overlay the session has moved
    /// past is asked for again only if the same names come back, and then
    /// its results are built again, the same.
    ///
    /// In force are `overlay` under either source of name tables, the same
    /// names without tables ([`Overlay::without_tables`], which the
    /// binary's own tables are read under), and the empty overlay without
    /// tables, which the program-wide sweeps (the index) read under. A
    /// request still running under the old names when this is called
    /// rebuilds what it asks for again; what it leaves goes at the next
    /// call or, for items, under the budget.
    ///
    /// # Arguments
    ///
    /// * `overlay` - The names and comments now in force.
    pub fn forget_names_but(&self, overlay: &Overlay) {
        let live = in_force(overlay);
        self.forget(&|scope, _| match scope {
            Scope::Program => false,
            Scope::Names(names) | Scope::Item(names) => !live.contains(&names),
        });
    }

    /// Carries every result read under `before` that read none of the facts
    /// an edit changed over to `after`, and lets go of every other result
    /// read under names not in force for `after`, as
    /// [`Derived::forget_names_but`] does.
    ///
    /// A result read under one of the overlays [`Derived::forget_names_but`]
    /// keeps for `before` moves to the same overlay for `after`. A result
    /// is a function of the overlay facts it read ([`reads::Reads`]), so
    /// one whose reads miss the edit ([`reads::Edit::touches`]) is the
    /// result the new names would build, byte for byte; it is filed under
    /// the new names instead of being built again. When the two overlays
    /// differ in where name tables come from, which no read-set notes,
    /// nothing is carried.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The analysis these results derive from, for the names
    ///   its functions go by without the overlay's.
    /// * `before` - The names and comments results were read under.
    /// * `after` - The names and comments now in force.
    pub fn moved(&self, analysis: &Analysis, before: &Overlay, after: &Overlay) {
        let Some(edit) = reads::Edit::between(analysis, before, after) else {
            self.forget_names_but(after);
            return;
        };
        let (old, live) = (in_force(before), in_force(after));
        let carry = |names: u64| {
            old.iter()
                .zip(live)
                .find_map(|(&was, now)| (was == names && was != now).then_some(now))
        };
        self.sweep(&|scope, _, read| {
            let (Scope::Names(names) | Scope::Item(names)) = scope else {
                return Fate::Keep;
            };
            if live.contains(&names) {
                return Fate::Keep;
            }
            match carry(names) {
                Some(now) if !edit.touches(read) => Fate::Move(match scope {
                    Scope::Item(_) => Scope::Item(now),
                    Scope::Program | Scope::Names(_) => Scope::Names(now),
                }),
                Some(_) | None => Fate::Drop,
            }
        });
    }

    /// Returns what the built results read of the overlay, summed over
    /// every result read under names.
    #[must_use]
    pub fn read_stats(&self) -> reads::ReadStats {
        let stats = std::cell::Cell::new(reads::ReadStats::default());
        self.sweep(&|scope, _, read| {
            if !matches!(scope, Scope::Program) {
                stats.set(stats.get().with(read));
            }
            Fate::Keep
        });
        stats.get()
    }

    /// Returns how many results have been built, of every kind and scope:
    /// each a cell filled, so a result built again after being let go
    /// counts again.
    #[must_use]
    pub fn builds(&self) -> u64 {
        self.builds.load(Ordering::Relaxed)
    }

    /// Sets the most bytes the item results may hold, letting go of the
    /// least recently asked for at once when they hold more.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The budget; [`ITEMS_BUDGET`] until set.
    pub fn set_budget(&self, bytes: usize) {
        self.budget.store(bytes, Ordering::Relaxed);
        self.shrink();
    }

    /// Returns the bytes the built item results hold, as their weights say.
    #[must_use]
    pub fn item_bytes(&self) -> usize {
        self.item_bytes.load(Ordering::Relaxed)
    }

    /// Returns how many results of `kind` are held, built or being built.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind's name.
    #[must_use]
    pub fn held(&self, kind: &str) -> usize {
        self.kinds.lock().map_or(0, |kinds| {
            kinds
                .iter()
                .filter(|((name, _), _)| *name == kind)
                .map(|(_, cells)| cells.held())
                .sum()
        })
    }

    /// Returns the result of `kind` read under `scope` for `key`, building
    /// it the first time; an item's result is weighed as it is built, and
    /// the item results shrunk to the budget after.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind's name.
    /// * `scope` - What the result is read under.
    /// * `key` - The key within the kind.
    /// * `make` - Builds the result.
    /// * `weigh` - The bytes an item's result holds beyond its own size.
    ///
    /// # Returns
    ///
    /// The shared result, as for [`Derived::get_or_build`]; built afresh
    /// and not kept when the caller's cancel flag is raised, and let go
    /// again when it was raised while this call built it. A thread that
    /// waited for a build left with nothing to share builds its own, not
    /// kept: the cancel flag is the builder's, never the waiter's.
    fn fetch<K, T>(
        &self,
        kind: &'static str,
        scope: Scope,
        key: K,
        make: impl FnOnce() -> T,
        weigh: impl FnOnce(&T) -> usize,
    ) -> Arc<T>
    where
        K: Hash + Eq + Send + 'static,
        T: Send + Sync + 'static,
    {
        if crate::cancel::Cancel::raised() {
            return Arc::new(make());
        }
        let Some(cell) = self.cell(kind, scope, key) else {
            return Arc::new(make());
        };
        let item = matches!(scope, Scope::Item(_));
        if item {
            cell.asked
                .store(self.asks.fetch_add(1, Ordering::Relaxed), Ordering::Relaxed);
        }
        if cell.claimed.swap(true, Ordering::AcqRel) {
            let Some((value, read)) = cell.value.wait() else {
                return Arc::new(make());
            };
            reads::absorb(read);
            return Arc::clone(value);
        }
        let sweep = || self.sweep(&|_, _, _| Fate::Keep);
        let mut publish = Publish(&cell.value, None, &sweep);
        let (value, read) = reads::recording(make);
        self.builds.fetch_add(1, Ordering::Relaxed);
        reads::absorb(&read);
        let (value, cut) = (Arc::new(value), crate::cancel::Cancel::raised());
        if item && !cut {
            let weight = size_of::<(Scope, K, Cell<T>, T)>() + weigh(&value) + read.bytes();
            cell.weight.store(weight, Ordering::Relaxed);
            self.item_bytes.fetch_add(weight, Ordering::Relaxed);
        }
        publish.1 = (!cut).then(|| (Arc::clone(&value), read));
        drop(publish);
        if !cut && item && self.item_bytes() > self.budget.load(Ordering::Relaxed) {
            self.shrink();
        }
        value
    }

    /// The cell of `kind` read under `scope` for `key`, made empty when there
    /// is none yet.
    ///
    /// Each lock is held only to find or insert, never while a result is
    /// built.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind's name.
    /// * `scope` - What the result is read under.
    /// * `key` - The key within the kind.
    ///
    /// # Returns
    ///
    /// The cell, or `None` when a lock is poisoned.
    fn cell<K, T>(&self, kind: &'static str, scope: Scope, key: K) -> Option<Arc<Cell<T>>>
    where
        K: Hash + Eq + Send + 'static,
        T: Send + Sync + 'static,
    {
        let cells = {
            let mut kinds = self.kinds.lock().ok()?;
            let cells = kinds
                .entry((kind, TypeId::of::<Cells<K, T>>()))
                .or_insert_with(|| Arc::new(Cells::<K, T>::default()));
            Arc::clone(cells)
        };
        let cells = cells.into_any().downcast::<Cells<K, T>>().ok()?;
        let mut cells = cells.lock().ok()?;
        Some(Arc::clone(cells.entry((scope, key)).or_default()))
    }

    /// Lets go of the least recently asked for item results when they hold
    /// more than the budget, down to [`ITEMS_KEPT`] of it.
    ///
    /// Cutting below the budget, not to it, makes one sweep pay for the
    /// builds of many asks.
    fn shrink(&self) {
        let budget = self.budget.load(Ordering::Relaxed);
        if self.item_bytes() <= budget {
            return;
        }
        let mut asked = Vec::new();
        if let Ok(kinds) = self.kinds.lock() {
            #[expect(
                clippy::iter_over_hash_type,
                reason = "the list is sorted by stamp after"
            )]
            for cells in kinds.values() {
                cells.asked(&mut asked);
            }
        }
        asked.sort_unstable_by_key(|&(stamp, _)| std::cmp::Reverse(stamp));
        let keep = budget / ITEMS_KEPT.1 * ITEMS_KEPT.0;
        let mut held = 0;
        let Some(&(last, _)) = asked.iter().find(|&&(_, weight)| {
            held += weight;
            held > keep
        }) else {
            return;
        };
        self.forget(&|scope, asked| matches!(scope, Scope::Item(_)) && asked <= last);
    }

    /// Lets go of every built result, for when the analysis they were read
    /// from changed under them.
    pub(crate) fn forget_all(&self) {
        self.forget(&|_, _| true);
    }

    /// Lets go of every built result `drop` picks, and of the bytes the
    /// item results among them held.
    ///
    /// # Arguments
    ///
    /// * `drop` - Picks a result by what it was read under and when it was
    ///   last asked for.
    fn forget(&self, drop: &dyn Fn(Scope, u64) -> bool) {
        self.sweep(&|scope, asked, _| {
            if drop(scope, asked) {
                Fate::Drop
            } else {
                Fate::Keep
            }
        });
    }

    /// Decides the fate of every built result by `pick`, and lets go of the
    /// bytes the item results let go of held.
    ///
    /// # Arguments
    ///
    /// * `pick` - Decides a result's fate by what it was read under, when
    ///   it was last asked for, and what it read.
    fn sweep(&self, pick: &dyn Fn(Scope, u64, &reads::Reads) -> Fate) {
        let freed: usize = self.kinds.lock().map_or(0, |kinds| {
            kinds.values().map(|cells| cells.sweep(pick)).sum()
        });
        self.item_bytes.fetch_sub(freed, Ordering::Relaxed);
    }
}

/// Returns the fingerprints of the overlays a caller holding `overlay`
/// reads results under.
///
/// They are `overlay` under either source of name tables, the same names
/// without tables, and the empty overlay without tables.
///
/// # Arguments
///
/// * `overlay` - The names and comments in force.
///
/// # Returns
///
/// The four fingerprints, in that order.
fn in_force(overlay: &Overlay) -> [u64; 4] {
    let under = |enum_source| {
        Overlay {
            enum_source,
            ..overlay.clone()
        }
        .fingerprint()
    };
    [
        under(EnumSource::Given),
        under(EnumSource::Binary),
        overlay.without_tables().fingerprint(),
        Overlay::default().fingerprint(),
    ]
}

/// Derived analysis results: computed once per [`Program`] and shared.
///
/// A clone holds the same facts and an empty [`Derived`], which builds each
/// result again when asked: a copy to change, such as one a recovered
/// function is added to ([`Analysis::start_gap_function`]).
#[derive(Debug, Default, Clone)]
pub struct Analysis {
    /// Functions sorted by entry address.
    pub functions: Vec<Function>,
    /// Target address to its reference sites (sorted by site address).
    pub xrefs: BTreeMap<u64, Vec<RefSite>>,
    /// Indirect-jump site to its resolved case targets (bounded jump tables).
    pub jump_tables: BTreeMap<u64, Vec<u64>>,
    /// The sites in [`Analysis::jump_tables`] whose targets a byte index
    /// table expanded, so the case labels are the values the source
    /// switched on and not the byte the compiler looked up.
    pub indexed_tables: BTreeSet<u64>,
    /// The Itanium LSDA call sites of each function that carries one, by its
    /// entry: the code ranges a call may throw through, and where the
    /// unwinder resumes inside the function ([`crate::lsda`]). Empty without
    /// `.eh_frame` FDEs carrying an `L`-augmented LSDA pointer, as on MSVC
    /// binaries and plain C.
    pub throw_sites: BTreeMap<u64, Vec<ThrowSite>>,
    /// Function to parameter index to the constants its callers put in that
    /// argument register: the values a parameter is actually called with,
    /// kept only while there are few enough of them to be a set of cases.
    pub param_values: BTreeMap<u64, BTreeMap<u8, BTreeSet<u64>>>,
    /// The packs the analysis ran with ([`crate::pack`]), in load order.
    pub packs: Arc<crate::pack::Packs>,
    /// What the packs' `[names]` lines found: the functions they named, and
    /// the names whose signature matched no entry or several.
    pub pack_names: sigs::PackNames,
    /// What the packs' `[names]` `lib` lines found: the library functions
    /// the program links, by name.
    pub library_names: libnames::LibraryNames,
    /// What each pack script ran to and named ([`crate::script`]).
    pub pack_scripts: Vec<crate::script::PackScript>,
    /// The instruction fuel ran out before the walk finished.
    pub incomplete: bool,
    /// Entries of the functions discovery found never return: by name, by
    /// what follows their calls, or by their own code
    /// ([`functions::call_ends_path`] reads it).
    pub noreturn: BTreeSet<u64>,
    /// The `QObject` subclasses `moc` described, with their signals, slots
    /// and properties and the functions its dispatchers map them to.
    pub qt: Vec<qt::QtClass>,
    /// What a Mach-O image's Objective-C metadata says: its classes,
    /// categories and protocols, and the messages its code sends.
    pub objc: objc::ObjcFacts,
    /// The constant tables and magic numbers of known algorithms found in
    /// the image ([`crate::crypto::find_crypto_constants`]), by address,
    /// each with the algorithm's name, so a read through one renders by
    /// name.
    pub crypto: BTreeMap<u64, &'static str>,
    /// What each function that uses a known algorithm's constants uses, by
    /// entry ([`recognize`]): the tables it reads and the immediates it
    /// carries, settled and ordered by algorithm.
    pub recognized: BTreeMap<u64, Vec<recognize::Evidence>>,
    /// Every reference a function makes, by its entry: pairs of the target
    /// and the index into the target's list in [`Analysis::xrefs`], in
    /// address order, so [`Analysis::refs_from`] is a lookup rather than a
    /// scan of every reference in the binary.
    pub refs_by_function: BTreeMap<u64, Vec<(u64, usize)>>,
    /// Entries of the functions sharing one body fingerprint
    /// ([`Function::body_hash`]), by fingerprint, in address order; only
    /// the fingerprints more than one function has. Template
    /// instantiations, the per-object copies of one destructor and inlined
    /// helpers land here, so an agent reading a binary can skip what it has
    /// already read.
    pub clones: BTreeMap<u64, Vec<u64>>,
    /// Entries of the functions sharing one shape fingerprint
    /// ([`Function::shape_hash`]), by fingerprint, in address order; only
    /// the shapes more than one function has. A shape class wider than the
    /// clone class holds near-clones: the same instruction sequence over
    /// other registers, constants or field offsets.
    pub shapes: BTreeMap<u64, Vec<u64>>,
    /// What the program's classes are: their constructors and vtables,
    /// where their instances live, and what they registered as
    /// ([`ClassFacts`]).
    pub classes: ClassFacts,
    /// Every result derived after discovery, built once and shared: the
    /// plain decompilations the passes that read pseudo-C back work from
    /// (field names from setters, schemas), each class's field names, the
    /// whole-program catalogs (the attribute registry, the message routes,
    /// the message catalog), so a second query reads the first one's work.
    pub derived: Derived,
    /// Entry address to index into [`Analysis::functions`].
    entry_index: BTreeMap<u64, usize>,
    /// Address to index into the program's symbols: an export, forwarder,
    /// local or data symbol first, an import's slot where none is there
    /// (the first symbol of the winning kind at an address wins, and the
    /// functions are inserted before the data, so a function name beats a
    /// data name at one address).
    symbol_index: BTreeMap<u64, usize>,
}

/// What the analysis found about the program's classes.
///
/// [`Analysis`]'s own fields are facts every binary has: functions,
/// references, jump tables. These come from the class model a C++
/// program carries (constructors, vtables, RTTI) and the registrations an
/// engine's conventions add on top of it, which packs name ([`crate::pack`]).
#[derive(Debug, Default, Clone)]
pub struct ClassFacts {
    /// Classes whose constructors were found, by qualified name
    /// ([`vtables`]).
    pub by_name: BTreeMap<String, vtables::ClassInfo>,
    /// Primary vtable address to the class it belongs to.
    pub vtables: BTreeMap<u64, String>,
    /// A further base's vtable under multiple inheritance, by address, named
    /// `Class::vftable_Base` after the class and the base its locator places
    /// at the subobject's offset, or `Class::vftable_<offset>` when no base
    /// states that offset; the class's own table is in [`ClassFacts::vtables`].
    pub secondary_vtables: BTreeMap<u64, String>,
    /// The vtable slots that hold a deleting destructor: the indexes at
    /// which many classes' functions are destructors. A call through one
    /// with `1` alone is a `delete`.
    pub dtor_slots: BTreeSet<usize>,
    /// `(class, offset)` to the class the pointer field there points at,
    /// inferred from methods passing the field as another method's `this`.
    pub field_hints: BTreeMap<(String, u64), String>,
    /// `(class, offset)` to the type of the object embedded there, inferred
    /// from methods passing the field's address to a declared parameter or
    /// as a method's `this` ([`vtables`]).
    pub field_types: BTreeMap<(String, u64), String>,
    /// TLS block offset to the class whose constructor stores `this` there
    /// (a thread-local singleton), ([`vtables`]).
    pub tls_slots: BTreeMap<u64, String>,
    /// Data address to the class whose constructor stores `this` there (a
    /// global singleton), ([`vtables`]).
    pub global_hints: BTreeMap<u64, String>,
    /// Setter signature strings by class: each `(string address, member
    /// name)` for a `Class::SetMember` signature the binary carries, read by
    /// [`classes::field_names`] to name the field the inlined setter writes.
    pub setters: BTreeMap<String, Vec<(u64, String)>>,
    /// Class name to the four-character code it registered with, which is
    /// what identifies the class on the wire.
    pub ids: BTreeMap<String, u32>,
    /// A bare class name a registration spelled to the qualified name the
    /// rest of the program knows the class by (`Actor` to
    /// `Cmd::Actor`), for the names [`ClassFacts::ids`]
    /// was rewritten with.
    pub registered_as: BTreeMap<String, String>,
    /// Each class's type descriptor, by address: the static object its
    /// registration names and its type accessor hands out (`Class::RTTI`).
    pub descriptors: BTreeMap<u64, String>,
}

impl Analysis {
    /// Discovers functions, blocks, cross-references and jump tables.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image; only its file-derived facts are read.
    ///
    /// # Returns
    ///
    /// The complete analysis. Same program, same result, byte for byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use borer_engine::analysis::Analysis;
    /// use borer_engine::program::Program;
    ///
    /// let program = Program::load(&std::env::current_exe()?)?;
    /// let analysis = Analysis::compute(&program);
    /// let entry = program.entry.expect("an executable has an entry point");
    /// assert!(analysis.function_at(entry).is_some());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn compute(program: &Program) -> Analysis {
        Analysis::compute_with(program, Arc::default())
    }

    /// Runs the analysis with packs: the conventions of the family the
    /// program belongs to, which the generic rules read where a program's
    /// own strings and tables leave a choice open (what a class's static
    /// instance is called, which types are serializer streams).
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded binary.
    /// * `packs` - The packs, in load order; empty for the generic rules
    ///   alone.
    ///
    /// # Returns
    ///
    /// The complete analysis, carrying the packs for the passes that read
    /// them later (rendering, the catalogs).
    #[must_use]
    pub fn compute_with(program: &Program, packs: Arc<crate::pack::Packs>) -> Analysis {
        let mut phases = crate::timing::Phases::new();
        let discover = || match program.arch.isa() {
            Some(Isa::X86 { bits }) => functions::discover(program, bits),
            Some(Isa::A64) => a64::discover(program),
            Some(Isa::A32) => a32::discover(program),
            None => {
                let mut empty = Analysis::default();
                empty.finish_index(program);
                empty
            }
        };
        let (mut analysis, crypto) = beside(discover, || crypto_tables(program));
        let crypto = crypto.unwrap_or_else(|| crypto_tables(program));
        phases.mark("analysis discover");
        analysis.packs = packs;
        naming::infer(program, &mut analysis);
        phases.mark("analysis naming");
        naming::infer_handlers(program, &mut analysis);
        phases.mark("analysis naming handlers");
        descriptors::qualify_registrations(&mut analysis);
        phases.mark("analysis descriptors");
        match program.arch.isa() {
            Some(Isa::A64) => a64::infer_returns(program, &mut analysis),
            Some(Isa::A32) => a32::infer_returns(program, &mut analysis),
            Some(Isa::X86 { .. }) | None => returns::infer(program, &mut analysis),
        }
        phases.mark("analysis returns");
        vtables::infer(program, &mut analysis);
        phases.mark("analysis vtables");
        messages::name_id_accessors(program, &mut analysis);
        phases.mark("analysis messages");
        qt::infer(program, &mut analysis);
        phases.mark("analysis qt");
        objc::infer(program, &mut analysis);
        phases.mark("analysis objc");
        eh::infer(program, &mut analysis);
        phases.mark("analysis eh");
        analysis.crypto = crypto;
        phases.mark("analysis crypto");
        analysis.index_refs();
        phases.mark("analysis refs_by_function");
        let mut pack_names = sigs::find_pack_names(program, &analysis);
        sigs::apply_pack_names(&mut analysis, &mut pack_names);
        analysis.pack_names = pack_names;
        phases.mark("analysis sigs");
        let mut library_names = libnames::find_library_names(program, &analysis);
        libnames::apply_library_names(&mut analysis, &mut library_names);
        analysis.library_names = library_names;
        phases.mark("analysis libnames");
        recognize::infer(program, &mut analysis);
        phases.mark("analysis recognize");
        let analysis = crate::script::run_pack_scripts(program, analysis);
        phases.mark("analysis scripts");
        analysis
    }

    /// Builds the lookups over what discovery found: the entry index, the
    /// clone and shape classes, the symbol index, and every reference
    /// list sorted by site.
    ///
    /// The last step of discovery for every instruction set, run once the
    /// functions are final and sorted by entry; an instruction set with no
    /// discovery runs it over no functions, which still indexes the
    /// program's symbols.
    ///
    /// # Arguments
    ///
    /// * `program` - The program whose symbols are indexed.
    pub(crate) fn finish_index(&mut self, program: &Program) {
        for (i, f) in self.functions.iter().enumerate() {
            self.entry_index.insert(f.entry, i);
        }
        self.clones = functions::shared_classes(&self.functions, |f| f.body_hash);
        self.shapes = functions::shared_classes(&self.functions, |f| f.shape_hash);
        for imports in [false, true] {
            for (i, s) in program.symbols.iter().enumerate() {
                if (s.kind == SymbolKind::Import) == imports && s.addr != 0 {
                    self.symbol_index.entry(s.addr).or_insert(i);
                }
            }
        }
        for sites in self.xrefs.values_mut() {
            sites.sort_by_key(|s| s.va);
        }
    }

    /// Looks up the function whose entry is exactly `entry`.
    ///
    /// # Arguments
    ///
    /// * `entry` - A function entry address.
    ///
    /// # Returns
    ///
    /// The function, or `None` when no discovered function starts there.
    pub fn function(&self, entry: u64) -> Option<&Function> {
        self.entry_index.get(&entry).map(|&i| &self.functions[i])
    }

    /// The function whose entry is exactly `entry`, to change in place.
    ///
    /// # Arguments
    ///
    /// * `entry` - A function entry address.
    pub(crate) fn function_mut(&mut self, entry: u64) -> Option<&mut Function> {
        let i = *self.entry_index.get(&entry)?;
        self.functions.get_mut(i)
    }

    /// Finds the function whose decoded range contains `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address inside a function.
    ///
    /// # Returns
    ///
    /// The function with the highest entry at or below `va` whose range
    /// covers it, or `None`.
    pub fn function_at(&self, va: u64) -> Option<&Function> {
        let idx = self.entry_index.range(..=va).next_back().map(|(_, &i)| i)?;
        let f = &self.functions[idx];
        if va >= f.start && va < f.end {
            Some(f)
        } else {
            None
        }
    }

    /// Adds a function at `va` when no discovered function contains it.
    ///
    /// Discovery's own gap walk leaves some code unclaimed: a straight
    /// Thumb run nothing calls, a handler whose literal pool sits in a
    /// hole of a later function's span, or a body a later thunk entered
    /// by jumping backward. A decompile that names that address starts a
    /// function there, records the jump tables and the call and jump
    /// sites the walk resolved, and infers what that function returns,
    /// the same pass discovery runs. Those sites are recorded first, so
    /// a callee whose result this call reads is not left as returning
    /// nothing. A float left in `s0` or `d0` is then the result.
    /// Functions already found are not walked again.
    ///
    /// # Arguments
    ///
    /// * `program` - The image the analysis was computed from.
    /// * `va` - The address asked for.
    ///
    /// # Returns
    ///
    /// The new function's entry, or `None` when the address is not a clean
    /// gap on ARM32.
    pub fn start_gap_function(&mut self, program: &Program, va: u64) -> Option<u64> {
        a32::start_gap_function(program, self, va)
    }

    /// Rebuilds [`Analysis::refs_by_function`] from [`Analysis::xrefs`].
    ///
    /// Each function's list is the targets it references, in site order,
    /// with the index of that site in the target's list.
    pub(crate) fn index_refs(&mut self) {
        let mut all: Vec<(u64, u64, u64, usize)> = self
            .xrefs
            .iter()
            .flat_map(|(&target, sites)| {
                let from = move |(i, s): (usize, &RefSite)| Some((s.from_entry?, s.va, target, i));
                sites.iter().enumerate().filter_map(from)
            })
            .collect();
        all.sort_unstable();
        self.refs_by_function = all
            .chunk_by(|a, b| a.0 == b.0)
            .filter_map(|run| Some((run.first()?.0, run.iter().map(|r| (r.2, r.3)).collect())))
            .collect();
    }

    /// Returns the symbol at `va`: the export, forwarder, local or data
    /// symbol there, else the import whose IAT or GOT slot it is.
    ///
    /// # Arguments
    ///
    /// * `program` - The program this analysis was computed from.
    /// * `va` - A virtual address (function entry, data or import slot).
    ///
    /// # Returns
    ///
    /// The symbol, or `None` when nothing the symbol tables state is at `va`.
    pub fn symbol_at<'p>(&self, program: &'p Program, va: u64) -> Option<&'p Symbol> {
        self.symbol_index
            .get(&va)
            .and_then(|i| program.symbols.get(*i))
    }

    /// Returns the entries of every function whose body matches the one at
    /// `entry`, that one included and in address order.
    ///
    /// # Arguments
    ///
    /// * `entry` - A function's entry address.
    ///
    /// # Returns
    ///
    /// The class, or an empty slice when the function is unique or unknown.
    pub fn clones_of(&self, entry: u64) -> &[u64] {
        self.function(entry)
            .and_then(|f| self.clones.get(&f.body_hash))
            .map_or(&[], Vec::as_slice)
    }

    /// Returns the entries of every function whose instruction shape matches
    /// the one at `entry`, that one included and in address order.
    ///
    /// # Arguments
    ///
    /// * `entry` - A function entry address.
    ///
    /// # Returns
    ///
    /// The shape class, or an empty slice when the shape is unique or the
    /// function unknown.
    pub fn shapes_of(&self, entry: u64) -> &[u64] {
        self.function(entry)
            .and_then(|f| self.shapes.get(&f.shape_hash))
            .map_or(&[], Vec::as_slice)
    }

    /// Keeps one function per clone class, in the order given.
    ///
    /// The first entry of each class stands for the class; the later
    /// members are listed after it so a caller can name what it skipped.
    /// Unique functions and unknown entries pass through with an empty
    /// list.
    ///
    /// # Arguments
    ///
    /// * `entries` - Function entries, in the order to keep.
    ///
    /// # Returns
    ///
    /// `(kept entry, skipped clones of it)` pairs.
    pub fn dedupe_clones(&self, entries: &[u64]) -> Vec<(u64, Vec<u64>)> {
        let mut seen: BTreeMap<u64, usize> = BTreeMap::new();
        let mut out: Vec<(u64, Vec<u64>)> = Vec::new();
        for &e in entries {
            let hash = self.function(e).map(|f| f.body_hash);
            match hash.and_then(|h| seen.get(&h).copied()) {
                Some(i) if self.clones_of(e).len() > 1 => {
                    if let Some((_, skipped)) = out.get_mut(i) {
                        skipped.push(e);
                    }
                }
                _ => {
                    if let Some(h) = hash {
                        seen.insert(h, out.len());
                    }
                    out.push((e, Vec::new()));
                }
            }
        }
        out
    }

    /// Returns every reference site pointing at `va` (empty when there is none).
    ///
    /// # Arguments
    ///
    /// * `va` - The referenced address (code or data).
    pub fn xrefs_to(&self, va: u64) -> &[RefSite] {
        self.xrefs.get(&va).map_or(&[], Vec::as_slice)
    }
}

/// User annotations overlaid on the derived analysis.
///
/// Never mutate [`Program`] or [`Analysis`]; lookups consult the
/// overlay first. Serialized as the JSON project file.
#[derive(Debug, Default, Clone, serde::Serialize, serde::Deserialize)]
pub struct Overlay {
    /// Address to user-chosen name (functions and data globals).
    pub names: reads::Tracked<u64, String, reads::NamesTag>,
    /// Address to user comment.
    pub comments: reads::Tracked<u64, String, reads::CommentsTag>,
    /// User-defined types by name: the structs, enums and typedefs an agent
    /// stated ([`utypes::UserType`]), applied to globals through
    /// [`Overlay::applied`]. Serialized with the project, validated on
    /// load, and part of [`Overlay::fingerprint`], so a decompilation read
    /// under them names the fields of what they type.
    pub types: reads::Tracked<String, utypes::UserType, reads::TypesTag>,
    /// Address to the type applied there: the declared type of the global
    /// the decompiler renders for that address, so a `Player *` applied at
    /// a global's address makes every field read through it render by
    /// name. Structs reach the rendering as pointers; the types
    /// themselves live in [`Overlay::types`].
    pub applied: reads::Tracked<u64, utypes::TypeExpr, reads::AppliedTag>,
    /// Function entry to the prototype an agent stated for it: the
    /// function's signature, its parameters' names and types, and the
    /// arity and the result every call to it shows, ahead of what debug
    /// information states. Part of [`Overlay::fingerprint`]; saved with a
    /// project, which spells each one ([`protos::Proto::spell`]).
    #[serde(default, skip)]
    pub prototypes: reads::Tracked<u64, protos::Proto, reads::PrototypesTag>,
    /// Function entry to the variables an agent named or typed in it: a
    /// parameter renders by the name and the type everywhere, a stack slot
    /// by the name, declared of the type where it is as wide. Part of
    /// [`Overlay::fingerprint`]; saved with a project like the prototypes.
    #[serde(default, skip)]
    pub vars: reads::Tracked<u64, BTreeMap<protos::VarKey, protos::Var>, reads::VarsTag>,
    /// Name tables by the display name of the function encoding each
    /// ([`decompile::enum_tables`]); a caller comparing that function's
    /// result, or passing a constant to it, renders the constant by its
    /// member name. Read when [`Overlay::enum_source`] is
    /// [`EnumSource::Given`]. Derived from the binary, so never saved with a
    /// project.
    #[serde(default, skip)]
    pub enums: reads::Tracked<String, decompile::EnumTable, reads::EnumsTag>,
    /// Where a decompilation finds the name tables it renders constants by.
    /// Never saved with a project.
    #[serde(default, skip)]
    pub enum_source: EnumSource,
    /// The text passes a decompilation leaves out, none by default: a
    /// bisection's way to read a function's text without some of them
    /// ([`decompile::Passes`]). Part of [`Overlay::fingerprint`] when not
    /// empty. Never saved with a project.
    #[serde(default, skip)]
    pub passes: decompile::Passes,
    /// The choice points a decompilation renders at their literal rung,
    /// none by default: the repair search's way to read a function's text
    /// with some guesses undone ([`decompile::Choices`]). Part of
    /// [`Overlay::fingerprint`] when not empty. Never saved with a project.
    #[serde(default, skip)]
    pub choices: decompile::Choices,
}

/// Where a decompilation finds the name tables it renders constants by
/// ([`decompile::apply_enums`]).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EnumSource {
    /// The tables in [`Overlay::enums`], none by default.
    #[default]
    Given,
    /// The binary's own, every table [`decompile::enum_tables`] lists: each
    /// body reads only the tables of the functions it names, once per
    /// function, so no decompilation waits for the whole binary's.
    Binary,
}

/// Decompiles `entry` plainly, once per overlay, through [`Analysis::derived`].
///
/// The memo is keyed by the overlay's fingerprint as well, so a rename does
/// not hand back text that still carries the old name. The cell holds the
/// whole [`decompile::Decompiled`], so a summary that wants the virtual
/// callees and the text pays for one decompile, not two. It is an item
/// result, weighed by its text and what is kept beside it, so the least
/// recently read texts go once they pass the budget
/// ([`Derived::get_or_build_item`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `overlay_key` - [`Overlay::fingerprint`] of `overlay`, computed once by the caller.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The shared decompilation, `None` inside when the function does not
/// decompile.
pub(crate) fn decompiled_cached(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    overlay_key: u64,
    entry: u64,
) -> Arc<Option<decompile::Decompiled>> {
    analysis.derived.get_or_build_item(
        "plain_text",
        overlay_key,
        entry,
        || decompile::decompile_plain_full(program, analysis, overlay, entry),
        |d| d.as_ref().map_or(0, decompile::Decompiled::bytes),
    )
}

/// [`decompiled_cached`], built, when nothing memoized it yet, with the
/// lifter's witness kept beside the text for the answer's check to take
/// ([`decompile::replay`]).
///
/// The text is the same either way; only who builds the cell first decides
/// whether it holds a witness.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `overlay_key` - [`Overlay::fingerprint`] of `overlay`, computed once by the caller.
/// * `entry` - The function's entry.
pub(crate) fn decompiled_witnessed(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    overlay_key: u64,
    entry: u64,
) -> Arc<Option<decompile::Decompiled>> {
    analysis.derived.get_or_build_item(
        "plain_text",
        overlay_key,
        entry,
        || decompile::decompile_witnessed(program, analysis, overlay, entry),
        |d| d.as_ref().map_or(0, decompile::Decompiled::bytes),
    )
}

/// Decompiles `entry` plainly, once per overlay, through [`Analysis::derived`].
///
/// The text of [`decompiled_cached`], cloned out of the shared cell.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `overlay_key` - [`Overlay::fingerprint`] of `overlay`, computed once by the caller.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The pseudo-C, or `None` when the function does not decompile.
#[must_use]
pub fn plain_text_cached(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    overlay_key: u64,
    entry: u64,
) -> Option<String> {
    decompiled_cached(program, analysis, overlay, overlay_key, entry)
        .as_ref()
        .as_ref()
        .map(|d| d.text.clone())
}

impl Overlay {
    /// A fingerprint of everything that changes a decompilation's text: the
    /// names and the comments, folded in address order, the user types,
    /// their applications, the stated prototypes and variables, then the name
    /// tables, folded by the function each is keyed under, then where the
    /// tables come from.
    ///
    /// The tables are in it because a decompilation renders constants by
    /// their member names ([`decompile::apply_enums`]): the memo keyed by
    /// this fingerprint must not hand text rendered with the tables to a
    /// caller whose overlay has none, or the other way round. The binary's
    /// own tables ([`EnumSource::Binary`]) follow from the names and the
    /// binary, so their source alone tells them apart.
    ///
    /// Each name and comment starts with its field's own byte and its
    /// length, so the two maps fold different bytes: a name and a comment
    /// of one text at one address fingerprinted alike, and each was handed
    /// the other's text.
    #[must_use]
    pub fn fingerprint(&self) -> u64 {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        let mut fold = |bytes: &[u8]| {
            for b in bytes {
                h = (h ^ u64::from(*b)).wrapping_mul(0x0000_0100_0000_01b3);
            }
        };
        for (field, map) in [(7, self.names.raw()), (8, self.comments.raw())] {
            for (addr, text) in map {
                fold(&[field]);
                fold(&addr.to_le_bytes());
                fold(&crate::num::from_usize(text.len()).to_le_bytes());
                fold(text.as_bytes());
            }
        }
        for (name, ty) in self.types.raw() {
            fold(name.as_bytes());
            fold(&[0]);
            match ty {
                utypes::UserType::Struct(s) => {
                    fold(&s.size.to_le_bytes());
                    for (off, f) in &s.fields {
                        fold(&off.to_le_bytes());
                        fold(f.name.as_bytes());
                        fold(&[0]);
                        fold(f.ty.spell().as_bytes());
                        fold(&[0]);
                    }
                }
                utypes::UserType::Alias(inner) => {
                    fold(&[1]);
                    fold(inner.spell().as_bytes());
                }
                utypes::UserType::Enum(e) => {
                    fold(&[2]);
                    fold(&e.size.to_le_bytes());
                    for (value, value_name) in &e.values {
                        fold(&value.to_le_bytes());
                        fold(value_name.as_bytes());
                        fold(&[0]);
                    }
                }
            }
            fold(&[0]);
        }
        for (addr, ty) in self.applied.raw() {
            fold(&addr.to_le_bytes());
            fold(ty.spell().as_bytes());
            fold(&[0]);
        }
        for (addr, proto) in self.prototypes.raw() {
            fold(&[3]);
            fold(&addr.to_le_bytes());
            fold(proto.spell().as_bytes());
            fold(&[0]);
        }
        for (addr, vars) in self.vars.raw() {
            for (key, var) in vars {
                fold(&[4]);
                fold(&addr.to_le_bytes());
                match key {
                    protos::VarKey::Param(i) => fold(&[0, *i]),
                    protos::VarKey::Slot(off) => {
                        fold(&[1]);
                        fold(&off.to_le_bytes());
                    }
                }
                fold(var.spell().as_bytes());
                fold(&[0]);
            }
        }
        for (function, table) in self.enums.raw() {
            fold(function.as_bytes());
            fold(&[0]);
            fold(table.name.as_bytes());
            fold(&[0]);
            fold(&table.param.map_or(0, |p| p + 1).to_le_bytes());
            for (value, member) in &table.members {
                fold(&value.to_le_bytes());
                fold(member.as_bytes());
                fold(&[0]);
            }
        }
        fold(&[match self.enum_source {
            EnumSource::Given => 0,
            EnumSource::Binary => 1,
        }]);
        if !self.passes.is_empty() {
            fold(&[5]);
            fold(&self.passes.bits().to_le_bytes());
        }
        for site in self.choices.sites() {
            fold(&[6]);
            match site {
                decompile::Site::Pass(p) => fold(p.name().as_bytes()),
                decompile::Site::Slot(k) => fold(&k.to_le_bytes()),
                decompile::Site::Return => fold(&[1]),
            }
        }
        h
    }

    /// Returns the [`Overlay::fingerprint`] of these names without the
    /// passes left out and the choice points moved: the key of a table read
    /// over the whole program under the names, which the renderings a
    /// repair search tries then share instead of each building its own.
    ///
    /// # Returns
    ///
    /// The fingerprint itself when nothing is left out or moved, the common
    /// case, which costs no copy.
    #[must_use]
    pub(crate) fn names_key(&self) -> u64 {
        if self.passes.is_empty() && self.choices.is_empty() {
            return self.fingerprint();
        }
        Self {
            passes: decompile::Passes::NONE,
            choices: decompile::Choices::default(),
            ..self.clone()
        }
        .fingerprint()
    }

    /// Returns the names, comments, types, applications, prototypes and
    /// variables alone, without name tables: the overlay the binary's own
    /// tables are read under, so reading one table never needs another.
    #[must_use]
    pub(crate) fn without_tables(&self) -> Self {
        Self {
            names: self.names.clone(),
            comments: self.comments.clone(),
            types: self.types.clone(),
            applied: self.applied.clone(),
            prototypes: self.prototypes.clone(),
            vars: self.vars.clone(),
            ..Self::default()
        }
    }
}

/// Resolves the display name of a function entry.
///
/// # Arguments
///
/// * `analysis` - Supplies symbol-table names.
/// * `overlay` - User names, which win over everything else.
/// * `entry` - The function entry address.
///
/// # Returns
///
/// The overlay name, else the symbol name, else `sub_<hex>`.
pub fn name_of(analysis: &Analysis, overlay: &Overlay, entry: u64) -> String {
    if let Some(n) = overlay.names.get(&entry) {
        return n.clone();
    }
    if let Some(f) = analysis.function(entry)
        && let Some(n) = &f.name
    {
        return n.clone();
    }
    format!("sub_{entry:x}")
}

/// Names one vtable slot for a listing: the function its word holds, or
/// `data` for the `0` that marks a word the table's slots skipped
/// ([`crate::analysis::vtables`] keeps the datum's index).
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names, which win over everything else.
/// * `slot` - The slot's word.
///
/// # Returns
///
/// The slot's listing text; `data` is never a function's name.
pub fn slot_name_of(analysis: &Analysis, overlay: &Overlay, slot: u64) -> String {
    if slot == 0 {
        return "data".to_owned();
    }
    name_of(analysis, overlay, slot)
}

/// Collects the seed addresses for function discovery.
///
/// A funclet is entered by the runtime and named by no instruction: an
/// `__except` body in particular has no unwind entry of its own, and only
/// the scope table says where it is, so the funclets are seeds too.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The entry point, every non-import symbol that marks code, every declared
/// function range start and every funclet that lies in executable memory,
/// sorted and deduplicated. A data symbol never seeds: what it names sits
/// in a data section, which no function lives in. Nor does a PE export
/// whose first instructions are two zero bytes' `add [eax], al`
/// ([`opens_as_data`]): a PE export does not say whether it is code, and a
/// DLL that merges its read-only data into `.text` exports variables there.
pub(crate) fn seeds(program: &Program) -> Vec<u64> {
    let mut s: Vec<u64> = Vec::new();
    if let Some(e) = program.entry
        && is_executable_va(program, e)
    {
        s.push(e);
    }
    for sym in &program.symbols {
        if matches!(
            sym.kind,
            SymbolKind::Import | SymbolKind::Forwarder | SymbolKind::Data
        ) || sym.addr == 0
        {
            continue;
        }
        let data_export = sym.kind == SymbolKind::Export
            && program.format == crate::program::BinaryFormat::Pe
            && opens_as_data(program, sym.addr);
        if is_executable_va(program, sym.addr) && !data_export {
            s.push(sym.addr);
        }
    }
    s.extend(
        program
            .function_ranges
            .iter()
            .map(|r| r.0)
            .filter(|va| is_executable_va(program, *va)),
    );
    s.extend(
        crate::unwind::funclets(program)
            .iter()
            .map(|f| f.entry)
            .filter(|va| is_executable_va(program, *va)),
    );
    dedup_sorted(&mut s);
    s
}

/// Tells whether the bytes at `va` read as data rather than as code: one of
/// the first instructions is `add [eax], al`, the two zero bytes of an
/// integer's high half.
///
/// msvcrt exports `_sys_nerr` (the int 43, `2b 00 00 00`) from `.text`;
/// seeded as a function it walked 7,500 bytes of the error-string table as
/// code, read as 109 `in` instructions and an anti-analysis verdict.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Where the symbol points.
fn opens_as_data(program: &Program, va: u64) -> bool {
    /// Instructions read from the symbol's address.
    const LOOK: usize = 4;
    let (Some(Isa::X86 { bits }), Some(code)) = (program.arch.isa(), program.read_va_upto(va, 32))
    else {
        return false;
    };
    let mut d =
        crate::isa::x86::Decoder::with_ip(bits, code, va, crate::isa::x86::DecoderOptions::NONE);
    d.iter().take(LOOK).any(|i| {
        i.code() == crate::isa::x86::Code::Add_rm8_r8
            && program.read_va_upto(i.ip(), 2) == Some(&[0, 0][..])
    })
}

/// Tells whether `va` lies inside an executable, file-backed section.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - A virtual address.
pub(crate) fn is_executable_va(program: &Program, va: u64) -> bool {
    program.section_at(va).is_some_and(|s| {
        s.executable && va >= s.va.0 && va < s.va.0.saturating_add(s.vsize.max(s.file_size))
    })
}

/// Parses an address as typed by an agent.
///
/// Bare digits are decimal: `140001064` is `0x8583f28`, and hex takes its
/// `0x`. Text with a hex letter and no `0x` (`14000106a`) can only be hex,
/// so it reads as hex. A name that spells a number (`cafe`, `1234`) is
/// [`resolve`]'s to find before this reading applies.
///
/// # Arguments
///
/// * `s` - `0x`-prefixed hex, plain decimal, or bare hex; surrounding whitespace is ignored.
///
/// # Returns
///
/// The address, or `None` when `s` is not a number in any of those forms.
pub fn parse_addr(s: &str) -> Option<u64> {
    let t = s.trim();
    if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return u64::from_str_radix(h, 16).ok();
    }
    t.parse::<u64>()
        .ok()
        .or_else(|| u64::from_str_radix(t, 16).ok())
}

/// Tells whether address text carries a `0x` prefix, the one spelling that
/// is an address whatever names exist.
///
/// # Arguments
///
/// * `s` - The text as typed; surrounding whitespace is ignored.
#[must_use]
pub fn hex_prefixed(s: &str) -> bool {
    let t = s.trim();
    t.starts_with("0x") || t.starts_with("0X")
}

/// Parses a file offset as typed by an agent: `off:` or `off=` before a
/// number.
///
/// Bytes no section maps (an overlay, the headers, a file with no
/// sections) have no virtual address, so a read names them by where they
/// sit in the file. `off=` is how `strings` and `search` print such a
/// place, so a row can be read back as it was printed.
///
/// # Arguments
///
/// * `s` - The text; the number after the prefix takes any form
///   [`parse_addr`] accepts.
///
/// # Returns
///
/// The offset, or `None` when `s` is not an offset in that form.
pub fn parse_off(s: &str) -> Option<u64> {
    let t = s.trim();
    parse_addr(t.strip_prefix("off:").or_else(|| t.strip_prefix("off="))?)
}

/// Returns the entry of the discovered function containing an address.
///
/// An import's slot holds a pointer to code in another module, so asking
/// for the function there (`decompile GetLastError` where no thunk wraps
/// it) is answered with what the slot is, not as a function not found.
/// The start of a .NET method's IL body is refused the same way: it is not
/// x86 code, and a function a sweep made of its bytes would be noise.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies the functions.
/// * `va` - The address.
///
/// # Returns
///
/// The function's entry.
///
/// # Errors
///
/// Says the address is an import's slot or an IL body, or that no
/// discovered function contains it ([`no_function_at`]).
pub fn function_entry(program: &Program, analysis: &Analysis, va: u64) -> Result<u64, String> {
    if let Some(m) = program
        .clr()
        .and_then(|c| c.method_at(program.image_base, va))
        .filter(|m| m.body == crate::clr::Body::Il)
    {
        return Err(format!(
            "{va:#x} is the IL body of .NET method {:#010x} {}: borer does not decompile IL; disassemble_function, function, function_strings and xrefs on it read its CIL; borer://clr lists the methods",
            m.token, m.name
        ));
    }
    if let Some(f) = analysis.function_at(va) {
        return Ok(f.entry);
    }
    match program
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::Import && s.addr == va && va != 0)
    {
        Some(s) => Err(format!(
            "{va:#x} is the import slot of {}: its code is in another module, so no function here; xrefs {va:#x} lists its callers",
            s.name
        )),
        None => Err(no_function_at(program, analysis, va)),
    }
}

/// Says that no discovered function contains `va`, and what to try.
///
/// An address outside every section names the image's span and, when
/// the image base plus it is mapped, that address, since an RVA passed
/// for a virtual address is the usual slip; one inside names the nearest
/// function before it.
///
/// # Arguments
///
/// * `program` - Supplies the sections and the image base.
/// * `analysis` - Supplies the functions.
/// * `va` - The address no function contains.
///
/// # Returns
///
/// The sentence a tool answers with.
#[must_use]
pub fn no_function_at(program: &Program, analysis: &Analysis, va: u64) -> String {
    let span = program
        .sections
        .iter()
        .map(|s| (s.va.0, s.va.0.saturating_add(s.vsize.max(s.file_size))))
        .reduce(|(lo, hi), (a, b)| (lo.min(a), hi.max(b)));
    match span {
        Some((lo, hi)) if program.section_at(va).is_none() => {
            let rva = program
                .image_base
                .checked_add(va)
                .filter(|&at| at != va && program.section_at(at).is_some())
                .map_or_else(String::new, |at| {
                    format!("; as an RVA it is {at:#x}, which is mapped")
                });
            format!(
                "no discovered function contains {va:#x}: it is outside the image ({lo:#x}..{hi:#x}){rva}"
            )
        }
        Some(_) | None => {
            let before = analysis
                .functions
                .iter()
                .take_while(|f| f.entry <= va)
                .last()
                .map_or_else(String::new, |f| {
                    format!(
                        "; the nearest function before it is {} at {:#x}",
                        f.name
                            .as_deref()
                            .map_or_else(|| format!("sub_{:x}", f.entry), str::to_owned),
                        f.entry
                    )
                });
            format!("no discovered function contains {va:#x}{before}")
        }
    }
}

/// Resolves an address or a name to a virtual address.
///
/// Names match case-insensitively against overlay names, discovered function
/// names, `sub_<hex>`, and symbols (imports and exports, with or without
/// their `dll!` prefix, mangled or demangled). The names the decompiler
/// writes for a class's singleton global (`Class::instance`) and its vtable
/// (`Class::vftable`) resolve too, so a live read can start from either. An
/// import named by both its IAT slot and a thunk function resolves to the
/// function, the thing tools decompile, graph and cross-reference.
///
/// `0x`-prefixed text is always an address. Any other text is looked up as
/// a name first and read as a number ([`parse_addr`]) only when no name
/// matches: a function named `add`, `cafe` or `1234` was unreachable by
/// name while the number reading came first.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address in any form [`parse_addr`] accepts, or a name.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// Returns a message when nothing matches (with the tools to try next) or
/// when several addresses match (listing up to six candidates).
pub fn resolve(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Result<u64, String> {
    resolve_noting(program, analysis, overlay, text, String::new)
}

/// Resolves an address or a name as [`resolve`] does, and a name nothing
/// matches is answered with the names nearest it ([`nearest_names`]).
///
/// For an agent's argument, where the right name one edit away saves a
/// listing; [`resolve`] stays without the search for callers that try
/// many names and use only the hits.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address in any form [`parse_addr`] accepts, or a name.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// As [`resolve`], a miss naming up to [`NEAREST_NAMES`] names.
pub fn resolve_suggesting(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Result<u64, String> {
    resolve_noting(program, analysis, overlay, text, || {
        let near = nearest_names(program, analysis, overlay, text);
        if near.is_empty() {
            String::new()
        } else {
            format!("; nearest: {}", near.join(", "))
        }
    })
}

/// What a name nothing matches ends with: the tools that list the names,
/// in the MCP tools' syntax. A caller speaking another syntax (the CLI)
/// replaces it with its own.
pub const LIST_HINT: &str = "; try functions(filter=...) or symbols(filter=...)";

/// Most names a miss suggests ([`resolve_suggesting`]).
pub const NEAREST_NAMES: usize = 3;

/// Returns the names nearest one that names nothing.
///
/// The candidates are the overlay's names, and the functions' and mapped
/// symbols' names without their `dll!` prefix, as [`resolve`] matches
/// them, ranked by [`crate::text::nearest`].
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names.
/// * `overlay` - Supplies user names.
/// * `text` - The name that matched nothing.
///
/// # Returns
///
/// At most [`NEAREST_NAMES`] names, nearest first, each escaped to one line.
#[must_use]
pub fn nearest_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Vec<String> {
    let names = overlay
        .names
        .values()
        .map(String::as_str)
        .chain(
            analysis
                .functions
                .iter()
                .filter_map(|f| f.name.as_deref().map(bare_name)),
        )
        .chain(
            program
                .symbols
                .iter()
                .filter(|s| s.addr != 0)
                .map(|s| bare_name(&s.name)),
        );
    crate::text::nearest(text, names, NEAREST_NAMES)
        .into_iter()
        .map(crate::text::one_line)
        .collect()
}

/// What [`resolve`] finds a name by besides the overlay: a function, by its
/// entry, or a mapped symbol, by its place in [`Program::symbols`].
#[derive(Debug, Clone, Copy)]
enum Named {
    /// The function with this entry.
    Function(u64),
    /// The symbol at this index.
    Symbol(usize),
}

/// Returns every function and mapped symbol by each lowercased name
/// [`resolve`] matches it by, built once per analysis.
///
/// A function goes under its name and bare name, a symbol under its name,
/// bare name and demangled form. A lookup walked every function and
/// symbol, demangling each, per name: most of a millisecond on a DLL of a
/// few thousand functions, in every tool given a name.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries, and holds the index.
fn name_index(program: &Program, analysis: &Analysis) -> Arc<FxHashMap<String, Vec<Named>>> {
    analysis.derived.get_or_build("name_index", (), || {
        let mut ix: FxHashMap<String, Vec<Named>> = FxHashMap::default();
        for f in &analysis.functions {
            if let Some(n) = &f.name {
                for key in [n.to_lowercase(), bare_name(n).to_lowercase()] {
                    ix.entry(key).or_default().push(Named::Function(f.entry));
                }
            }
        }
        for (i, s) in program
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, s)| s.addr != 0)
        {
            let demangled = crate::search::demangled_or_raw(&s.name).to_lowercase();
            for key in [
                s.name.to_lowercase(),
                bare_name(&s.name).to_lowercase(),
                demangled,
            ] {
                ix.entry(key).or_default().push(Named::Symbol(i));
            }
        }
        ix
    })
}

/// [`resolve`], with `miss` saying more about a name nothing matches.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address or a name.
/// * `miss` - Builds what a miss says after its first clause; called only
///   on a miss.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// As [`resolve`].
fn resolve_noting(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
    miss: impl FnOnce() -> String,
) -> Result<u64, String> {
    if hex_prefixed(text)
        && let Some(va) = parse_addr(text)
    {
        return Ok(va);
    }
    let want = text.trim().to_lowercase();
    if let Some(hex) = want.strip_prefix("sub_")
        && let Ok(va) = u64::from_str_radix(hex, 16)
    {
        return Ok(va);
    }
    let mut hits: Vec<(u64, String)> = Vec::new();
    for (va, n) in &overlay.names {
        if n.to_lowercase() == want {
            hits.push((*va, n.clone()));
        }
    }
    let index = name_index(program, analysis);
    let named = index.get(&want).map_or(&[][..], Vec::as_slice);
    let symbols = || {
        named.iter().filter_map(|n| match *n {
            Named::Symbol(i) => program.symbols.get(i),
            Named::Function(_) => None,
        })
    };
    hits.extend(named.iter().filter_map(|n| match *n {
        Named::Function(entry) => analysis.function(entry)?.name.clone().map(|n| (entry, n)),
        Named::Symbol(_) => None,
    }));
    if let Some(class) = want.strip_suffix("::instance") {
        for (addr, c) in &analysis.classes.global_hints {
            if c.to_lowercase() == class {
                hits.push((*addr, format!("{c}::instance")));
            }
        }
    }
    if let Some(class) = want.strip_suffix("::vftable") {
        for (va, c) in &analysis.classes.vtables {
            if c.to_lowercase() == class {
                hits.push((*va, format!("{c}::vftable")));
            }
        }
    }
    hits.extend(symbols().map(|s| (s.addr, format!("{} {}", s.kind.name(), s.name))));
    hits.sort();
    hits.dedup_by_key(|h| h.0);
    if hits.iter().any(|(va, _)| analysis.function(*va).is_some()) {
        hits.retain(|(va, _)| analysis.function(*va).is_some());
    }
    let own: BTreeSet<u64> = symbols()
        .filter(|s| s.kind != SymbolKind::Import)
        .filter(|s| s.name.to_lowercase() == want || bare_name(&s.name).to_lowercase() == want)
        .map(|s| s.addr)
        .collect();
    if hits.len() > 1 && hits.iter().any(|(va, _)| own.contains(va)) {
        hits.retain(|(va, _)| own.contains(va));
    }
    match hits.len() {
        0 => parse_addr(text).ok_or_else(|| {
            format!(
                "{} is neither an address nor a known name{}{LIST_HINT}",
                crate::text::quoted(text),
                miss()
            )
        }),
        1 => Ok(hits[0].0),
        _ => Err(format!(
            "{} is ambiguous: {}",
            crate::text::quoted(text),
            hits.iter()
                .take(6)
                .map(|(va, n)| format!("{va:#x} ({n})"))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// Strips the `dll!` prefix from an import name.
///
/// The prefix ends at the first `!`, and only when what precedes it is a
/// module name: a demangled `QString::operator!=` carries a `!` of its
/// own, and splitting at the last one left `=`.
///
/// # Arguments
///
/// * `name` - A symbol name, possibly `DLL!name`.
///
/// # Returns
///
/// The part after the module prefix, or the whole name when there is none.
pub fn bare_name(name: &str) -> &str {
    match name.split_once('!') {
        Some((module, rest))
            if !module.is_empty()
                && !module.contains("::")
                && !module.contains(['(', ' ', '<']) =>
        {
            rest
        }
        _ => name,
    }
}

impl Analysis {
    /// Lists the reference sites inside a function, code and data alike.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry address.
    ///
    /// # Returns
    ///
    /// `(target, site)` pairs sorted by site address.
    pub fn refs_from(&self, entry: u64) -> Vec<(u64, &RefSite)> {
        self.refs_by_function
            .get(&entry)
            .map_or_else(Vec::new, |list| {
                list.iter()
                    .filter_map(|&(t, i)| self.xrefs.get(&t).and_then(|v| v.get(i)).map(|s| (t, s)))
                    .collect()
            })
    }
}

/// Tells whether an operand kind is an immediate of any width.
///
/// The second immediate of `enter` and `extrq` is not one: the passes
/// asking read the one value an instruction carries.
///
/// # Arguments
///
/// * `kind` - The operand kind.
pub(crate) fn is_imm(kind: OpKind) -> bool {
    matches!(
        kind,
        OpKind::Immediate8
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64
    )
}

/// Sorts a list and drops its repeats.
///
/// # Arguments
///
/// * `items` - The list, in any order.
pub(crate) fn dedup_sorted<T: Ord>(items: &mut Vec<T>) {
    items.sort_unstable();
    items.dedup();
}

/// The only item of a sequence.
///
/// # Arguments
///
/// * `items` - The sequence.
///
/// # Returns
///
/// The item, or `None` when there are none or several.
pub(crate) fn single<I: IntoIterator>(items: I) -> Option<I::Item> {
    let mut items = items.into_iter();
    let first = items.next()?;
    items.next().is_none().then_some(first)
}

/// The image's pointer width in bytes: 8 on a 64-bit image, 4 otherwise.
///
/// # Arguments
///
/// * `program` - The loaded image.
pub(crate) fn pointer_size(program: &Program) -> u64 {
    if program.is_64 { 8 } else { 4 }
}

/// Reads a little-endian `u32`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The value's address.
///
/// # Returns
///
/// The value, or `None` when the four bytes are not file-backed.
pub(crate) fn read_u32(program: &Program, at: u64) -> Option<u32> {
    let bytes = program.read_va(at, 4)?;
    Some(u32::from_le_bytes(bytes.try_into().ok()?))
}

/// Reads a little-endian `u64`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The value's address.
///
/// # Returns
///
/// The value, or `None` when the eight bytes are not file-backed.
pub(crate) fn read_u64(program: &Program, at: u64) -> Option<u64> {
    let bytes = program.read_va(at, 8)?;
    Some(u64::from_le_bytes(bytes.try_into().ok()?))
}

/// Reads a little-endian pointer of the image's width ([`pointer_size`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The value's address.
///
/// # Returns
///
/// The value, widened on a 32-bit image, or `None` when the bytes are not
/// file-backed.
pub(crate) fn read_word(program: &Program, at: u64) -> Option<u64> {
    if program.is_64 {
        read_u64(program, at)
    } else {
        read_u32(program, at).map(u64::from)
    }
}

/// The little-endian value of one pointer-sized word of bytes
/// ([`pointer_size`]), widened on a 32-bit image.
///
/// # Arguments
///
/// * `program` - The loaded image, for its width.
/// * `bytes` - The word's bytes; a word of another length reads as zero.
pub(crate) fn le_word(program: &Program, bytes: &[u8]) -> u64 {
    if program.is_64 {
        u64::from_le_bytes(bytes.try_into().unwrap_or([0; 8]))
    } else {
        u64::from(u32::from_le_bytes(bytes.try_into().unwrap_or([0; 4])))
    }
}

/// A name not yet in `taken`: `base`, else `base_2`, `base_3` and so on;
/// the name chosen is added to `taken`.
///
/// # Arguments
///
/// * `taken` - The names in use.
/// * `base` - The name wanted.
pub(crate) fn unique_name(taken: &mut BTreeSet<String>, base: &str) -> String {
    let mut name = base.to_owned();
    let mut n = 1u32;
    while !taken.insert(name.clone()) {
        n += 1;
        name = format!("{base}_{n}");
    }
    name
}
