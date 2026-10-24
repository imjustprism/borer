//! Decompiler: symbolic lift, phi placement, structuring, pseudo-C emission.
//!
//! The lifter ([`lift`]) turns x86/x64 into symbolic expressions that stay
//! symbolic until the text needs them; assignments are placed at join points
//! where a value is lost (phi placement); the obvious shapes (if / if-else /
//! while / for / switch) are structured; the rest is emitted as pseudo-C.
//!
//! The lifter maps iced-x86 instructions to borer's own semantics (x86/x64
//! only). Modeled
//! instructions become C statements; unmodeled ones appear as `/* asm: ... */`
//! comments and forget what they may have changed. Shapes the structurer
//! cannot prove fall back to labels and gotos, never to a wrong structure.
//!
//! In pipeline order: [`lift`] executes blocks over [`expr`] values,
//! [`verify`] checks that lifting against the emulator, [`params`] finds
//! the arguments, [`liveness`] places the phis, [`structure`] and [`emit`]
//! recover and write the control flow, then [`rewrite`], [`asserts`],
//! [`fields`], [`types`], [`enums`], [`wire`], [`stores`], [`tidy`] and
//! [`finish`] rework the text, and [`tables`] writes out the read-only tables it
//! indexes. [`outline`] and [`scenario`] are other views of the
//! same function; [`opaque`] spots conditions that always go one way;
//! [`traces`] checks the text's control flow against the binary's.
//! [`lift_a64`] lifts arm64 blocks into the same expressions,
//! [`verify_a64`] checks it against the arm64 machine and [`replay_a64`]
//! checks an arm64 text there. The pipeline itself is written against
//! [`arch::Lifter`], what it asks of an instruction set, which x86 and
//! arm64 both answer.

pub(crate) mod abi;
mod arch;
mod asserts;
mod canary;
pub mod choice;
mod cir;
mod ctext;
mod declared;
mod defs;
mod emit;
mod enums;
mod evidence;
pub mod export;
mod expr;
mod expr_render;
mod fcmp;
mod fields;
mod finish;
mod floats;
mod format;
mod frame;
mod globals;
mod guarded;
mod helper;
pub(crate) mod interp;
mod ladder;
mod lanes;
mod lexer;
pub(crate) mod lift;
mod lift_a32;
mod lift_a64;
mod line;
mod literal;
mod liveness;
mod loops;
mod masks;
mod mir;
mod opaque;
mod outline;
mod panics;
mod params;
mod passes;
pub mod replay;
mod replay_a32;
mod replay_a64;
mod rewrite;
mod scenario;
pub(crate) mod signature;
mod sites;
mod stack;
mod stores;
mod strlen;
mod structure;
mod tables;
mod tidy;
pub mod traces;
mod types;
mod unit;
mod vars;
mod vector;
pub mod verify;
pub mod verify_a32;
pub mod verify_a64;
mod verify_lanes;
mod warn;
mod wire;

pub use crate::timing::step_times;
use arch::Lifter;
pub use asserts::*;
pub use choice::{Choices, Site};
use emit::*;
pub use enums::*;
use fields::*;
pub use finish::*;
use line::*;
use literal::literal_at;
pub(in crate::analysis) use liveness::*;
use masks::*;
pub use outline::*;
use params::*;
pub use passes::{Pass, Passes};
use rewrite::*;
pub use scenario::*;
pub(crate) use sites::{CallArg, CallSite, call_sites};
use stores::*;
use strlen::*;
use structure::*;
pub use tidy::*;
use types::*;
use wire::*;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::isa::x86::{
    ConditionCode, Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory,
    Mnemonic, OpAccess, OpKind, Register,
};

use abi::Conv;
use expr::{Cc, Expr, Flags, Key, Names, Ty};
use lift::{BlockFacts, BlockOut, Branch, Env, Rebase, SlotUse, exec_block};

use super::{
    Analysis, BasicBlock, BlockTerm, EnumSource, Funclet, Function, Overlay, classes,
    decompiled_cached, name_of, plain_text_cached,
};
use crate::fxmap::FxHashMap;
use crate::program::Program;
use crate::strings::cstr_at;

/// Structuring recursion guard: deeper than this, fall back to gotos.
///
/// A compiled string ladder nests one level per compare (the client's
/// key-name parser has 134), and each level costs well under 4 KB of
/// stack, so 256 fits a 1 MB main thread with room to spare.
const MAX_DEPTH: usize = 256;
/// Dataflow fixpoint budget (cyclic folding can oscillate; capped values are
/// weaker but sound).
const MAX_PASSES: usize = 64;

/// Top level: continue the text at the target of an unconditional jump when
/// that block is still unwritten (flow order), instead of address order.
const FOLLOW_JUMPS: bool = true;

/// Returns the block an emitted piece of text jumps to at its end.
///
/// # Arguments
///
/// * `text` - The text just emitted for one block or structure.
///
/// # Returns
///
/// The target address when the last line is a plain `goto L_x;`.
fn trailing_goto(text: &str) -> Option<u64> {
    let last = text.lines().last()?.trim();
    is_goto(last).then(|| goto_address(last)).flatten()
}

/// Per-function decompilation state shared by the lifter and the emitter.
#[derive(Clone)]
struct Ctx<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Discovery results (functions, jump tables, names).
    analysis: &'a Analysis,
    /// User names and comments.
    overlay: &'a Overlay,
    /// [`Overlay::fingerprint`] of `overlay`: what a result derived under
    /// these names is memoized by ([`callee_shape`]).
    overlay_key: u64,
    /// Decoder bitness (32 or 64).
    bitness: u32,
    /// Calling convention of the program.
    conv: &'static Conv,
    /// Registers a scenario fixes to constants at the function's entry.
    assume: Vec<(Register, u64)>,
    /// Never write a value out: every register's value stays an expression
    /// over the block's entry state, for [`verify`] to evaluate.
    symbolic_only: bool,
    /// What the lifter did beyond its environment, recorded only while
    /// [`verify`] checks it.
    probe: Option<verify::Probe>,
    /// Start addresses of the function's blocks (a jump elsewhere leaves the function).
    block_starts: BTreeSet<u64>,
    /// The function registers a structured exception handler: its prologue
    /// is a frame helper or stores `esp` to `fs:[0]`. The handler's
    /// bookkeeping, the try-level stores at `[ebp-4]` and the unlink that
    /// restores `fs:[0]` before every return, is the compiler's and renders
    /// as nothing ([`lift::Exec::store`]).
    seh_frame: bool,
    /// Blocks only the exception runtime enters (a landing pad, an
    /// `__except` body, a catch's continuation), each with the protected
    /// blocks whose frame it starts from ([`guarded::Plan::roots`]).
    eh_roots: Vec<(usize, Vec<usize>)>,
    /// A Go function's stack-growth check ([`go_stack_check`]): the address
    /// of its `jbe` to the `runtime.morestack` call, which the lifter takes
    /// as never taken, and the header's note of what was folded.
    go_check: Option<(u64, String)>,
    /// Parameters detected from calling-convention registers read first.
    params: Vec<Register>,
    /// Text variables assigned somewhere in the body, with their type.
    declared: BTreeMap<Key, Ty>,
    /// The stack slots among `declared`, shared with the renderer
    /// ([`Names::slot_types`]).
    slot_types: std::sync::Arc<BTreeMap<i64, Ty>>,
    /// The type each of `globals` is declared with, shared with the
    /// renderer ([`Names::global_types`]).
    global_types: std::sync::Arc<BTreeMap<u64, Ty>>,
    /// Absolute data accesses hoisted to named globals.
    globals: BTreeSet<(u64, Ty)>,
    /// Lowest stack offset whose address reached a callee or memory: slots
    /// from there up may be read or written by any call.
    escape_floor: Option<i64>,
    /// Some instruction (not a call) writes rax: `ret` returns it.
    rax_written: bool,
    /// The function returns nothing: its signature says `void`, or it has
    /// none and no caller reads the return register after calling it, so a
    /// stale `rax` at `ret` is not a result.
    unused_result: bool,
    /// The function is variadic: it homed its argument registers for
    /// `va_start`, and the parameters past the fixed ones are `...`.
    variadic: bool,
    /// The first parameter is `this` (a member function per its signature).
    this_param: bool,
    /// Index of the hidden return-pointer parameter of a function returning a
    /// class by value, right after `this` when there is one.
    result_param: Option<u8>,
    /// Widest value returned so far (8/16 from partial writes, 32 when every
    /// exit writes `eax`, 64 otherwise).
    ret_bits: u8,
    /// Lane of rax a `ret` hands back: 8, 16, 32 or 64 ([`lift::ret_lane`]).
    ret_lane: u8,
    /// The declared return type is floating point, so the value comes
    /// back in `xmm0` and reading `rax` at the return would kill it.
    ret_float: bool,
    /// A 32-bit function hands its float back in `xmm0`, not `st0`: every
    /// exit leaves one there and a caller reads it
    /// ([`lift::sse_callee`]). Implies [`Ctx::ret_float`].
    ret_sse: bool,
    /// Widest float a 32-bit function hands back in `st0` so far, as its
    /// own expression types it: 32 when every one is a single, 64 when any
    /// is wider or untyped, 0 before the first.
    x87_ret: u8,
    /// The 64-bit function hands a second result back in `rdx`
    /// ([`Function::hands_back_rdx`]): a `return` shows it too.
    ret_rdx: bool,
    /// Parameter index to the class it points at, from the declared
    /// signature (`this`, `Foo *`, `const Foo &`), for virtual calls.
    param_class: BTreeMap<u8, String>,
    /// Bare name of the function, so its own `__FUNCSIG__` literal renders
    /// as the macro.
    own_name: std::sync::Arc<str>,
    /// The prototype an agent stated for the function
    /// ([`Overlay::prototypes`]), which the signature, the parameters and
    /// the return shape follow ahead of debug information and inference.
    stated: Option<&'a crate::analysis::protos::Proto>,
    /// The return type the stated prototype gives, else the one the debug
    /// information recorded; `None` for `void` or when nothing states one.
    debug_ret: Option<String>,
    /// Parameters the stated prototype lists, else the ones the debug
    /// information recorded, in order, each stated variable's name and
    /// type over its position ([`declared::params`]).
    ///
    /// The compiler wrote these down, so they beat `a1`, `a2`, `a3` and
    /// `uint64_t` in both the signature and the body: a condition on
    /// `dwReason` says what it tests, where one on `a2` says only where the
    /// value came from.
    debug_params: std::sync::Arc<[crate::dwarf::Parameter]>,
    /// The source file and line the debug information states the function
    /// was written in - the PDB's rows, or a Go function's `pclntab`
    /// record ([`pdb_sources`], [`go_source`]) - for the header's
    /// `// source:` line; `None` when nothing was recorded, which leaves
    /// the line to what the body's own assertions cite. The PDB's rows
    /// are read lazily, so the first header that states one pays their
    /// walk once.
    debug_source: Option<(String, u32)>,
    /// The frame-relative locals the debug information states, as slot
    /// offset to name, each stated variable's name over its slot
    /// ([`declared::locals`]); the names render where the synthesized
    /// `local_N` would. The offsets are facts the file or the agent states,
    /// so they name slots without touching their widths, which the
    /// lifting's own declarations keep stating.
    debug_locals: std::sync::Arc<BTreeMap<i64, String>>,
    /// Entries the function's virtual calls resolved to (emission pass).
    vcalls: BTreeSet<u64>,
    /// Callees whose whole body is `ret`, whose calls are left out of the
    /// text (emission pass); the header names them.
    empty_calls: BTreeSet<u64>,
    /// Callees that only load registers and return or jump on, lifted in
    /// place of their calls (emission pass); the header names them.
    read_in_place: BTreeSet<u64>,
    /// Callees that only jump through a register (the CFG dispatcher),
    /// with that register: each call to one is lifted as the call through
    /// the register (emission pass); the header names them.
    dispatches: BTreeMap<u64, Register>,
    /// The same thunks where a call reaches one through a read-only pointer
    /// (`call [__guard_dispatch_icall_fptr]`), which the header leaves
    /// unnamed: what [`replay`] follows a call through.
    pointer_dispatches: BTreeMap<u64, Register>,
    /// Per block: reads flags it did not set itself (a `jcc` at its start).
    flag_readers: Vec<bool>,
    /// Per block, how its out flags are re-expressed because a successor
    /// join's other predecessors compare the same value.
    rebase_flags: Vec<Option<Rebase>>,
    /// Temporaries created in the emission pass (`tmp_N` numbering).
    tmp_count: u32,
    /// What each block's statements do, as its first emission recorded
    /// them, packed ([`lift::pack`]), by the block's start.
    effects: BTreeMap<u64, Vec<u8>>,
    /// Declaration type of each vector register that held a scalar float
    /// (`float`/`double`); registers absent here declare as `uint128_t`.
    reg_ty: BTreeMap<Key, Ty>,
    /// The word-wide type each declared callee whose result the text binds
    /// returns, by the callee's text (emission pass): what a variable that
    /// holds only such results is declared as ([`typed_results`]).
    result_types: BTreeMap<String, String>,
    /// The constant group each library callee whose result the text binds
    /// compares its result with, and the result's width in bits, by the
    /// callee's text (emission pass): what [`apply_results`] names the
    /// constants a comparison with the result holds by.
    result_groups: BTreeMap<String, (&'static str, u8)>,
    /// Register-argument count of each callee looked at so far (see
    /// [`lift::Exec::callee_reg_params`]).
    callee_arity: BTreeMap<u64, (usize, u8, bool)>,
    /// Stack-passed arguments this function reads, which continue the
    /// numbering the register arguments start.
    stack_params: u32,
    /// The funclet this function is, when the exception runtime runs it on
    /// another function's frame ([`Function::funclet`](super::Function::funclet)).
    funclet: Option<Funclet>,
    /// Index of the block the function is entered at. Blocks are in address
    /// order, and code a function jumps back to (a shared tail, a chunk the
    /// compiler placed first) can lie below its entry.
    entry_block: usize,
    /// Positions the signature lists ([`Shape::count`]), which the arm64
    /// lifter's entry state places in their registers.
    arg_count: usize,
    /// A bit per position passed in a vector register ([`Shape::floats`]).
    arg_floats: u8,
    /// The vector registers nothing in the function reads above a single,
    /// and those that only ever hold one ([`lanes::solve`]).
    lanes: lanes::Lanes,
    /// The frame's slots and the types solved for them ([`frame::Frame`]).
    frame: frame::Frame,
    /// The choice points the lift met besides the passes ([`choice::Site`]).
    sites: BTreeSet<Site>,
    /// Whether the function hands a value back, as its callers say
    /// ([`Function::returns_value`](super::Function::returns_value)).
    returns_value: Option<bool>,
    /// The program's import name tables, taken from the memo the first time
    /// the lift reads them ([`lift::ImportNames`]).
    imports: std::sync::OnceLock<std::sync::Arc<lift::ImportNames>>,
}

impl<'a> Ctx<'a> {
    /// Decodes the instruction at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Address inside executable, file-backed memory.
    ///
    /// # Returns
    ///
    /// The instruction, or `None` when the address is unmapped, not
    /// executable, or does not decode.
    fn decode(&self, va: u64) -> Option<Instruction> {
        if !super::is_executable_va(self.program, va) {
            return None;
        }
        let bytes = self.program.read_va_upto(va, 15)?;
        let mut d = Decoder::with_ip(self.bitness, bytes, va, DecoderOptions::NONE);
        let mut i = Instruction::default();
        d.decode_out(&mut i);
        if i.code() == crate::isa::x86::Code::INVALID {
            return None;
        }
        Some(i)
    }

    /// Returns the name resolver for rendering.
    ///
    /// An x86 function's stack arguments sit above its return address and
    /// shadow space and continue the numbering its convention's registers
    /// start; an arm64 function's sit at the stack pointer it is entered
    /// with, past the eight registers the standard passes in.
    fn names(&self) -> Names<'a> {
        let (first_stack, reg_params) = match self.program.arch.isa() {
            Some(crate::isa::Isa::A64) => (0, u32::from(lift_a64::INT_ARGS)),
            Some(crate::isa::Isa::A32) => (0, 4),
            Some(crate::isa::Isa::X86 { .. }) | None => (
                self.conv.word + self.conv.shadow,
                u32::try_from(self.conv.args.len()).unwrap_or(0),
            ),
        };
        Names {
            program: self.program,
            analysis: self.analysis,
            overlay: self.overlay,
            this_param: self.this_param,
            result_param: self.result_param,
            own_name: self.own_name.clone(),
            debug_params: self.debug_params.clone(),
            debug_locals: self.debug_locals.clone(),
            first_stack,
            stack_params: self.stack_params,
            reg_params,
            word: self.conv.word,
            slot_types: self.slot_types.clone(),
            global_types: self.global_types.clone(),
        }
    }
}

/// Decompiles many functions at once, one stripe of them per core.
///
/// Each function comes out exactly as [`decompile`] renders it alone: the
/// workers share nothing but the read-only program, analysis and overlay,
/// and the results come back in the order of `entries`. A worker that
/// fails leaves its entries `None`.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
/// * `entries` - Function entries, in any order.
///
/// # Returns
///
/// One result per entry, `None` where [`decompile`] returns `None`.
pub fn decompile_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
) -> Vec<Option<String>> {
    render_all(program, analysis, overlay, entries, decompile_afresh)
}

/// [`decompile_all`], each text with how its cleanup passes ended.
///
/// A sweep reads the [`Settle`] to find a function whose passes spent
/// their budget without settling, which no rendering shows.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
/// * `entries` - Function entries, in any order.
///
/// # Returns
///
/// One result per entry, `None` where [`decompile`] returns `None`.
pub fn decompile_all_settled(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
) -> Vec<Option<(String, Settle)>> {
    render_all(program, analysis, overlay, entries, |p, a, o, e| {
        decompile_plain_full(p, a, o, e).map(|d| (finished(&d.text, p, a, o, e), d.settle))
    })
}

/// Decompiles many functions at once as [`decompile_named`] renders each,
/// one stripe of them per core: the text the `decompile` tool shows, with
/// fields named through their class.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
/// * `entries` - Function entries, in any order.
///
/// # Returns
///
/// One result per entry, in the order of `entries`.
pub fn decompile_named_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
) -> Vec<Option<String>> {
    render_all(program, analysis, overlay, entries, decompile_named_afresh)
}

/// Renders many functions with `render` across the cores, the results in
/// the order of `entries`.
///
/// The workers take the functions from one queue, largest first. A
/// binary's few largest functions take seconds each where the rest take
/// milliseconds, so a sweep lasts as long as its largest function from the
/// moment a worker starts it; striped by position, one could start last in
/// its stripe, and the sweep waited the whole stripe longer.
///
/// Each worker has a decompile's stack and runs its decompiles in place
/// ([`stack::worker`]).
///
/// The renderers a batch takes build their text afresh instead of through
/// the memo of [`Analysis::derived`]: a sweep over a binary would fill it
/// with every function's text, which the caller holds already, and a
/// sweep's overlay (the plain one, before the name tables) is not the one
/// the tools decompile under.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
/// * `entries` - Function entries, in any order.
/// * `render` - The entry point that renders one function.
fn render_all<T: Send + Clone>(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
    render: fn(&Program, &Analysis, &Overlay, u64) -> Option<T>,
) -> Vec<Option<T>> {
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(entries.len().max(1));
    let mut out: Vec<Option<T>> = vec![None; entries.len()];
    if threads <= 1 {
        for (slot, &entry) in out.iter_mut().zip(entries) {
            *slot = render(program, analysis, overlay, entry);
        }
        return out;
    }
    let mut order: Vec<usize> = (0..entries.len()).collect();
    order.sort_by_key(|&i| {
        std::cmp::Reverse(analysis.function(entries[i]).map_or(0, Function::size))
    });
    let next = std::sync::atomic::AtomicUsize::new(0);
    let (order, next) = (&order, &next);
    let here = super::reads::Handle::here();
    let stripes: Vec<Vec<(usize, Option<T>)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .filter_map(|_| {
                let here = here.clone();
                stack::worker(scope, move || {
                    here.enter(|| {
                        let mut done = Vec::new();
                        while let Some(&i) =
                            order.get(next.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
                        {
                            done.push((i, render(program, analysis, overlay, entries[i])));
                        }
                        done
                    })
                })
            })
            .collect();
        handles.into_iter().filter_map(|h| h.join().ok()).collect()
    });
    for (i, text) in stripes.into_iter().flatten() {
        if let Some(slot) = out.get_mut(i) {
            *slot = text;
        }
    }
    out
}

/// Decompiles the function whose entry is `entry` into pseudo-C.
///
/// The text starts with a header comment (name, entry, counts), a
/// `// signature:` line, an `// enum` line when the body is a name table
/// ([`enum_table`]), an `// effects:` line naming what the body writes
/// ([`effects_line`]), a `// clones:` line when other functions run the
/// same code ([`Analysis::clones_of`]), a `// shape:` line when others run
/// the same instruction sequence over other operands
/// ([`Analysis::shapes_of`]), optional `// note:` lines (escaping
/// locals, omitted unreachable blocks), the declarations of every variable
/// the body names (grouped per type), then the body.
///
/// The text is memoized per function under the names through
/// [`Analysis::derived`], and [`decompile_named`] hands out the same text
/// where naming the fields changes no line: a `decompile` answer reads
/// both, and finishing the one text twice cost a quarter of the answer.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments, applied to the output.
/// * `entry` - The function's entry address (use
///   [`Analysis::function_at`] first for an address inside it).
///
/// # Returns
///
/// The pseudo-C, or `None` when no discovered function starts at `entry` or
/// the architecture has no lifter.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::{Analysis, Overlay, decompile::decompile};
/// use borer_engine::program::Program;
///
/// let program = Program::load(&std::env::current_exe()?)?;
/// let analysis = Analysis::compute(&program);
/// let entry = program.entry.expect("an executable has an entry point");
/// let entry = analysis.function_at(entry).expect("the entry is a function").entry;
/// let text = decompile(&program, &analysis, &Overlay::default(), entry).expect("decompiles");
/// assert!(text.contains("// signature:"));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn decompile(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let names = overlay.fingerprint();
    let memo = analysis.derived.get_or_build_item(
        "layout_text",
        names,
        entry,
        || {
            decompiled_cached(program, analysis, overlay, names, entry)
                .as_ref()
                .as_ref()
                .map(|d| finished(&d.text, program, analysis, overlay, entry))
        },
        |text| text.as_ref().map_or(0, String::capacity),
    );
    memo.as_ref().clone()
}

/// [`decompile`] built afresh, for a batch ([`decompile_all`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments, applied to the output.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or `None` as for [`decompile`].
fn decompile_afresh(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    decompile_plain_full(program, analysis, overlay, entry)
        .map(|d| finished(&d.text, program, analysis, overlay, entry))
}

/// The source file and line each PDB-named function starts at, read once
/// for the analysis's life.
///
/// The line programs a PDB states cost seconds to parse, and no load
/// answers from them, so the load leaves them out and this re-opens the
/// recorded companion through [`crate::pdb::sources`] at the first
/// function whose header states a source - the memo keeping the answer
/// and the seconds paid once - rather than the program holding the
/// companion's bytes or every load paying for lines no one asked for.
///
/// # Arguments
///
/// * `program` - The loaded image, holding the applied PDB's path and
///   record.
/// * `analysis` - Discovery results, holding the memo.
///
/// # Returns
///
/// The shared rows, empty when no PDB applied: function entry to the
/// `(file, line)` its first row states.
fn pdb_sources(
    program: &Program,
    analysis: &Analysis,
) -> std::sync::Arc<BTreeMap<u64, (String, u32)>> {
    let Some((path, record)) = &program.pdb_source else {
        return std::sync::Arc::default();
    };
    let word = i64::from(program.arch.bitness().unwrap_or(64) / 8);
    analysis.derived.get_or_build("pdb_sources", (), || {
        crate::pdb::sources(path, record, None, program.image_base, word).unwrap_or_default()
    })
}

/// The source file and line a Go function's own table states it starts
/// at, where the debug information said nothing.
///
/// Go's `pclntab` names the file and line runs beside the function names
/// it already gave, read straight from the section the load found the
/// table in. One function's lookup is two short varint runs, so unlike
/// [`pdb_sources`] no walk is worth memoizing.
///
/// # Arguments
///
/// * `program` - The loaded image, holding the table.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The `(file, line)` the table states, or `None` when no table was
/// kept, it does not list `entry`, or it predates the file tables.
fn go_source(program: &Program, entry: u64) -> Option<(String, u32)> {
    let go = program.go.as_ref()?;
    let bytes = program.section_bytes(program.section_at(go.at)?)?;
    go.source_of(bytes, entry)
}

/// The per-function state the lifter runs with, before the parameters and
/// the calling convention are read from the code.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names and comments.
/// * `f` - The function.
/// * `bitness` - Decoder bitness.
/// * `block_starts` - Its blocks' start addresses.
/// * `assume` - Parameter slots a scenario fixes, and their values.
fn new_ctx<'a>(
    program: &'a Program,
    analysis: &'a Analysis,
    overlay: &'a Overlay,
    f: &Function,
    bitness: u32,
    block_starts: BTreeSet<u64>,
    assume: &[(u8, u64)],
) -> Ctx<'a> {
    let debug = program.debug_functions.iter().find(|d| d.low_pc == f.entry);
    let stated = overlay.prototypes.get(&f.entry);
    let vars = overlay.vars.get(&f.entry);
    let conv = abi::conv_at(program, f.entry, bitness);
    Ctx {
        program,
        analysis,
        overlay,
        overlay_key: overlay.fingerprint(),
        bitness,
        conv,
        assume: assume
            .iter()
            .filter_map(|&(slot, v)| Some((*conv.args.get(usize::from(slot))?, v)))
            .collect(),
        block_starts,
        symbolic_only: false,
        probe: None,
        seh_frame: false,
        eh_roots: Vec::new(),
        go_check: None,
        params: Vec::new(),
        declared: BTreeMap::new(),
        slot_types: std::sync::Arc::default(),
        global_types: std::sync::Arc::default(),
        globals: BTreeSet::new(),
        escape_floor: None,
        rax_written: false,
        unused_result: false,
        variadic: false,
        this_param: false,
        result_param: None,
        ret_bits: 0,
        ret_lane: 64,
        ret_float: false,
        ret_sse: false,
        x87_ret: 0,
        ret_rdx: false,
        param_class: BTreeMap::new(),
        own_name: std::sync::Arc::from(expr::bare(&name_of(analysis, overlay, f.entry))),
        stated,
        debug_ret: match stated {
            Some(p) => p.ret.as_ref().map(crate::analysis::protos::CType::spell),
            None => debug.and_then(|d| d.return_type.clone()),
        },
        debug_params: std::sync::Arc::from(declared::params(stated, debug, vars)),
        debug_source: pdb_sources(program, analysis)
            .get(&f.entry)
            .cloned()
            .or_else(|| go_source(program, f.entry)),
        debug_locals: std::sync::Arc::new(declared::locals(debug, vars)),
        vcalls: BTreeSet::new(),
        empty_calls: BTreeSet::new(),
        read_in_place: BTreeSet::new(),
        dispatches: BTreeMap::new(),
        pointer_dispatches: BTreeMap::new(),
        flag_readers: Vec::new(),
        rebase_flags: Vec::new(),
        tmp_count: 0,
        effects: BTreeMap::new(),
        reg_ty: BTreeMap::new(),
        result_types: BTreeMap::new(),
        result_groups: BTreeMap::new(),
        callee_arity: BTreeMap::new(),
        stack_params: f.stack_args,
        funclet: f.funclet,
        entry_block: f
            .blocks
            .iter()
            .position(|b| b.start == f.entry)
            .unwrap_or(0),
        arg_count: 0,
        arg_floats: 0,
        lanes: lanes::Lanes::default(),
        frame: frame::Frame::default(),
        sites: BTreeSet::new(),
        returns_value: f.returns_value,
        imports: std::sync::OnceLock::new(),
    }
}

/// Decompiles like [`decompile`] without the layout pass.
///
/// For consumers that read `*(T*)(base + off)` accesses back out of the
/// text, such as class layouts.
///
/// PERF: under the tools' overlay (the binary's own name tables) the text
/// comes through the memo [`decompile`] fills: a decompile names the
/// fields of its own class by reading every method of the class, itself
/// among them, and built afresh the largest function of a binary was
/// decompiled twice. A sweep's plain overlay builds afresh, since nothing
/// reads its texts back.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or `None` as for [`decompile`].
pub fn decompile_plain(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    match overlay.enum_source {
        EnumSource::Binary => {
            plain_text_cached(program, analysis, overlay, overlay.fingerprint(), entry)
        }
        EnumSource::Given => {
            decompile_plain_full(program, analysis, overlay, entry).map(|d| d.text)
        }
    }
}

/// Decompiles like [`decompile_plain`] and keeps what the lifter learned
/// beside the text: what [`decompiled_cached`] memoizes.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The decompilation, or `None` as for [`decompile`].
pub(crate) fn decompile_plain_full(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Decompiled> {
    decompile_with(program, analysis, overlay, entry, true, &[], false)
}

/// [`decompile_plain_full`] with the lifter's witness kept, for the check
/// of an answer ([`crate::analysis::decompiled_witnessed`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
pub(crate) fn decompile_witnessed(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Decompiled> {
    decompile_with(program, analysis, overlay, entry, true, &[], true)
}

/// Decompiles like [`decompile`] and renders the fields of class-typed
/// objects by the names their class's asserts give them.
///
/// The objects are `this` (the class part of the name when the header
/// declares `this`), `result` (the class returned by value), each parameter
/// declared `Foo *`/`Foo &` and each parameter a caller hinted, up to
/// [`NAMED_OBJECTS_MAX`] of them; a class's field names come from
/// [`classes::field_names`] (one pass over its methods), and every
/// `*(T*)(var + off)` with a named offset becomes `var->name`, every bare
/// `var + off` `&var->name`. Offsets no class names still get the layout
/// treatment of [`decompile`]. The answer is memoized per overlay through
/// [`Analysis::derived`]: naming and polishing a function of ten thousand
/// instructions took a second on every call.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or `None` as for [`decompile`].
pub fn decompile_named(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let names = overlay.fingerprint();
    let memo = analysis.derived.get_or_build_item(
        "named_text",
        names,
        entry,
        || {
            let text = plain_text_cached(program, analysis, overlay, names, entry)?;
            let out = name_fields(program, analysis, overlay, entry, &text)?;
            if out == text {
                return decompile(program, analysis, overlay, entry);
            }
            Some(finished(&out, program, analysis, overlay, entry))
        },
        |text| text.as_ref().map_or(0, String::capacity),
    );
    memo.as_ref().clone()
}

/// What the check of a function's answer found ([`replay::TextCheck`]),
/// once per overlay, through [`Analysis::derived`] beside the text.
///
/// The statements the lifter emitted for the function under `overlay` are
/// replayed against the emulator from fixed states within a fixed block
/// budget, so the result is a function of the binary, the names and the
/// entry alone. It is an item result, let go with the names it was read
/// under, like the text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The check, `None` inside when the function does not decompile or the
/// image has no emulator.
pub fn text_check(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> std::sync::Arc<Option<replay::TextCheck>> {
    analysis.derived.get_or_build_item(
        "text_check",
        overlay.fingerprint(),
        entry,
        || {
            crate::timing::timed(crate::timing::Step::Replay, || {
                replay::check_answer(program, analysis, overlay, entry)
            })
        },
        |c| c.as_ref().map_or(0, replay::TextCheck::bytes),
    )
}

/// Returns the choice points the lift met in a function besides the text
/// passes ([`Site`]): the frame slots it solved as floats and a 64-bit
/// integer return.
///
/// They are read from the memoized decompilation, so asking costs what
/// the text cost, once.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The sites in order, none when the function does not decompile.
#[must_use]
pub fn choice_points(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Vec<Site> {
    decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry)
        .as_ref()
        .as_ref()
        .map_or_else(Vec::new, |d| d.sites.clone())
}

/// The header line a `decompile` answer prints under its first line: what
/// of the text was checked against the binary ([`text_check`]).
///
/// Only the tools' rendering carries it; the text every other reader
/// parses ([`decompile_named`], [`decompile_plain`] and the memo) does not.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The line, without its newline; `None` when nothing could be checked.
pub fn checked_header(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    text_check(program, analysis, overlay, entry)
        .as_ref()
        .as_ref()
        .map(replay::TextCheck::header)
}

/// Puts the header line of [`checked_header`] under a text's first line.
///
/// # Arguments
///
/// * `text` - The answer's text.
/// * `header` - The line, or `None` to leave the text as it is.
#[must_use]
pub fn with_header(text: &str, header: Option<&str>) -> String {
    let Some(header) = header else {
        return text.to_owned();
    };
    match text.split_once('\n') {
        Some((first, rest)) => format!("{first}\n{header}\n{rest}"),
        None => format!("{text}\n{header}\n"),
    }
}

/// Returns the `// warn:` line a `decompile` answer prints under its check
/// line: what keeps the text from being the C it claims.
///
/// Each item says what it means in a few words: a computed `goto`, a
/// callee of the binary with no prototype, a helper with no definition, a
/// name nothing declares, an operator C refuses on a float, a pointer or
/// an integer, a missing label, an instruction left as asm.
///
/// Only the tools' rendering carries it, like [`checked_header`]. Each
/// warning is a fact of the text, never a guess, so it flags no right
/// text; a text with no line may still be wrong in ways no fact of the
/// text shows. The input a run of the text still differs on after the
/// repair search ([`crate::analysis::render::Repair::note`]) is the last
/// item.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, which say what the function calls.
/// * `overlay` - The names the text was written under.
/// * `entry` - The function's entry.
/// * `text` - Its text as [`decompile_named`] wrote it.
/// * `differs` - The repair search's note, when the text still differs.
///
/// # Returns
///
/// The line without its newline, `None` when nothing is known wrong.
#[must_use]
pub fn warnings(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
    differs: Option<&str>,
) -> Option<String> {
    let word = program
        .arch
        .bitness()
        .and_then(|b| u8::try_from(b).ok())
        .unwrap_or(64);
    let in_binary: BTreeSet<String> = analysis
        .function(entry)
        .map(|f| f.callees.as_slice())
        .unwrap_or_default()
        .iter()
        .filter_map(|&c| {
            let g = analysis.function(c)?;
            let target = g.bound.unwrap_or(c);
            (g.thunk.is_none() && target != entry).then(|| name_of(analysis, overlay, target))
        })
        .collect();
    match (warn::line(text, &in_binary, word), differs) {
        (Some(line), Some(d)) => Some(format!("{line}; {d}")),
        (None, Some(d)) => Some(format!("{} {d}", warn::WARN)),
        (line, None) => line,
    }
}

/// The closure check of a function's text: each line that reads a
/// variable no line of the text sets before it on any path
/// ([`interp::Script::unset_reads`]).
///
/// A register variable no line sets holds only what the register held
/// when the function was entered; unless it is a parameter, that is a
/// value the text lost on the way (a `mov` dropped, a call taken to
/// clobber what it keeps). The per-block replay of [`text_check`] cannot
/// see it: it rebuilds every block's inputs from the machine.
///
/// It is a sweep's measure, not a mark on the answer: a value read unset
/// that is stored and never used again, or merged under bits a later line
/// keeps, leaves the text right, and the hard benchmark found such reads
/// in as many right texts as wrong ones.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - The names the text was written under.
/// * `entry` - The function's entry.
/// * `text` - Its text as [`decompile_named`] wrote it.
///
/// # Returns
///
/// Each flagged 1-based line with the names it reads so, in line order.
///
/// # Errors
///
/// When the text does not read as the program it claims to be (no
/// signature, a body that does not nest, a target that is not emulated),
/// so nothing was checked.
pub fn unset_reads(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
) -> Result<Vec<(usize, Vec<String>)>, String> {
    interp::Script::read(program, analysis, overlay, entry, text).map(|s| s.unset_reads())
}

/// [`decompile_named`] built afresh, for a batch ([`decompile_named_all`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or `None` as for [`decompile`].
fn decompile_named_afresh(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let text = decompile_plain_full(program, analysis, overlay, entry)?.text;
    name_fields(program, analysis, overlay, entry, &text)
        .map(|out| finished(&out, program, analysis, overlay, entry))
}

/// Renders the fields of class-typed objects in a plain decompilation by
/// name: the work of [`decompile_named`] after the plain text and before
/// [`finished`].
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
/// * `text` - Its plain decompilation ([`decompile_plain`]).
///
/// # Returns
///
/// The text with the fields named, or `None` when no function starts at
/// `entry`.
fn name_fields(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
) -> Option<String> {
    let mut lap = crate::timing::Lap::new();
    let f = analysis.function(entry)?;
    let name = name_of(analysis, overlay, entry);
    let own = classes::class_of(crate::analysis::bare_name(&name))
        .or_else(|| f.param_hints.get(&0).map(String::as_str));
    let has_this = own.is_some_and(|c| text.contains(&format!("{c} *this")));
    let mut objects: Vec<(String, String)> = Vec::new();
    if let (true, Some(c)) = (has_this, own) {
        objects.push(("this".to_owned(), c.to_owned()));
    }
    if let Some(sig) = &f.signature {
        if sig.by_pointer {
            objects.push(("result".to_owned(), sig.ret.clone()));
        }
        let lead = usize::from(has_this) + usize::from(sig.by_pointer);
        for (j, ty) in sig.params.iter().enumerate() {
            if let Some(c) = pointee_class(ty) {
                objects.push((format!("a{}", lead + j + 1), c.to_owned()));
            }
        }
    }
    for (i, c) in &f.param_hints {
        let var = format!("a{}", u32::from(*i) + 1);
        if !objects.iter().any(|(v, _)| *v == var) {
            objects.push((var, c.clone()));
        }
    }
    objects.truncate(NAMED_OBJECTS_MAX);
    let mut cache: BTreeMap<String, BTreeMap<u64, String>> = BTreeMap::new();
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    for (var, class) in &objects {
        let names = cache
            .entry(class.clone())
            .or_insert_with(|| classes::field_names(program, analysis, overlay, class));
        if names.is_empty() {
            continue;
        }
        for line in &mut lines {
            *line = rename_fields(line, var, names);
        }
    }
    let singleton = format!("::{}", analysis.packs.name_for("singleton"));
    let singletons = singleton_classes(&lines, &singleton);
    for class in singletons.iter().take(SINGLETONS_MAX) {
        let names = cache
            .entry(class.clone())
            .or_insert_with(|| classes::field_names(program, analysis, overlay, class));
        if names.is_empty() {
            continue;
        }
        let var = format!("{class}{singleton}");
        for line in &mut lines {
            *line = rename_fields(line, &var, names);
        }
    }
    let returns = result_classes(analysis, overlay, f);
    if !returns.is_empty() || !singletons.is_empty() {
        let bindings = result_bindings(&lines, |rhs| {
            callee_of(rhs)
                .and_then(|c| returns.get(c))
                .cloned()
                .or_else(|| {
                    rhs.strip_suffix(singleton.as_str())
                        .filter(|c| singletons.iter().any(|s| s == c))
                        .map(str::to_owned)
                })
        });
        let mut wanted: Vec<&str> = Vec::new();
        for b in &bindings {
            if !wanted.contains(&b.class.as_str()) && wanted.len() < RESULT_CLASSES_MAX {
                wanted.push(&b.class);
            }
        }
        for b in bindings
            .iter()
            .filter(|b| wanted.contains(&b.class.as_str()))
        {
            let names = cache
                .entry(b.class.clone())
                .or_insert_with(|| classes::field_names(program, analysis, overlay, &b.class));
            if names.is_empty() {
                continue;
            }
            for line in lines.iter_mut().take(b.to).skip(b.from) {
                *line = rename_fields(line, &b.var, names);
            }
            if b.rewritten
                && let Some(line) = lines.get_mut(b.to)
                && let Some(eq) = line.find(" = ")
            {
                let rhs = rename_fields(&line[eq..], &b.var, names);
                line.replace_range(eq.., &rhs);
            }
        }
    }
    if !overlay.passes.runs(Pass::NameFields) {
        lines = text.lines().map(str::to_owned).collect();
    }
    for Rename { var, name } in assert_names(&lines) {
        for line in &mut lines {
            *line = rename_word(line, &var, &name);
        }
    }
    let mut out = lines.join("\n");
    out.push('\n');
    lap.end(crate::timing::Step::NameFields);
    Some(out)
}

/// Returns the entries a function's virtual calls resolve to.
///
/// A call through the vtable of `this`, of a class-typed parameter or of a
/// typed call result resolves to a slot function (the lifter's virtual-target rule);
/// these are the callees the cross-reference index cannot see.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The resolved entries, sorted and deduplicated; empty when the function
/// does not decompile or makes no resolvable virtual call.
pub fn virtual_callees(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Vec<u64> {
    decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry)
        .as_ref()
        .as_ref()
        .map_or_else(Vec::new, |d| d.virtual_callees.clone())
}

/// What one decompilation produced.
#[derive(Debug)]
pub(crate) struct Decompiled {
    /// The pseudo-C text.
    pub(crate) text: String,
    /// Entries the function's virtual calls resolved to, sorted.
    pub(crate) virtual_callees: Vec<u64>,
    /// Basic blocks in the function.
    blocks: usize,
    /// Blocks no path from the entry reaches once constant branches and
    /// switches are folded.
    cut: usize,
    /// The graph the structurer was handed, which [`traces`] checks the
    /// text against.
    pub(crate) live: traces::LiveCfg,
    /// What each block's statements do, by block index, as the emission
    /// wrote them before the text passes ran; none for a block the text
    /// leaves out.
    effects: lift::Packed,
    /// What the lifter knew when it wrote them, kept only when asked for
    /// ([`replay`] checks the text with it) and until the check takes it.
    witness: std::sync::Mutex<Option<Box<replay::Witness>>>,
    /// How the cleanup passes ended, the default when they did not run.
    settle: Settle,
    /// The choice points the lift met besides the passes, in order.
    pub(crate) sites: Vec<Site>,
}

impl Decompiled {
    /// Takes the lifter's witness out, leaving none: the check that reads it
    /// is the only reader, so a memoized decompilation does not keep it.
    fn take_witness(&self) -> Option<Box<replay::Witness>> {
        self.witness.lock().ok().and_then(|mut w| w.take())
    }

    /// The bytes the decompilation holds, which the memo keeping it counts.
    ///
    /// The witness is not counted: the check it is kept for takes it as
    /// soon as the decompilation is built.
    pub(crate) fn bytes(&self) -> usize {
        self.text.capacity()
            + self.virtual_callees.capacity() * size_of::<u64>()
            + self.live.bytes()
            + self.effects.bytes()
    }
}

/// Decompiles like [`decompile`] but skips the text cleanup pass.
///
/// The goto/label cancellation and dead-text removal are left out, so the
/// output is the structurer's raw text, for debugging it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The raw pseudo-C, or `None` as for [`decompile`].
#[doc(hidden)]
pub fn decompile_raw(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    decompile_with(program, analysis, overlay, entry, false, &[], false).map(|d| d.text)
}

/// Runs the decompiler pipeline for one function.
///
/// Every block is decoded once and all passes read that cache. Dataflow
/// round 1 treats every slot as live and records slot uses and definitions;
/// round 2 reruns with real slot liveness so dead spills need no phi
/// assignment. Edges of branches whose condition folded to a constant are
/// removed before structuring (the dataflow stayed conservative), blocks
/// nothing reaches afterwards (a folded condition's other side, an unwinding
/// landing pad) are omitted along with their edges, and the body is emitted:
/// every block and structure ends with an explicit transfer, so the text may
/// be laid out in any order and the driver follows an unconditional jump to
/// a block not yet written (the goto/label pair then cancels), else takes
/// the lowest unwritten block. Only variables the body names are declared.
///
/// The work runs with a decompile's stack ([`stack::roomy`]): structuring
/// nests [`MAX_DEPTH`] emitter frames deep, and one inlined monolith (a
/// Zig `main` holding the whole program, 3,890 blocks) fills each frame
/// with kilobytes of its own, where the cap was sized for a megabyte in
/// total. The answer is only deep, so it gets room for it; wasm builds
/// have no threads and keep the caller's stack.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
/// * `cleanup` - Run [`cleanup_text`] on the body.
/// * `assume` - Parameter slots a scenario fixes, and their values.
/// * `witness` - Keep what the lifter knew about each block beside the
///   text, for [`replay`].
///
/// # Returns
///
/// The decompilation, or `None` when there is no such function or no lifter.
fn decompile_with(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    cleanup: bool,
    assume: &[(u8, u64)],
    witness: bool,
) -> Option<Decompiled> {
    let run = (program, analysis, overlay, entry);
    #[cfg(target_arch = "wasm32")]
    {
        decompile_in_run(run, cleanup, assume, witness)
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        stack::roomy(|| decompile_in_run(run, cleanup, assume, witness))
    }
}

/// [`decompile_with`] past the stack choice: pick the instruction set's
/// lifter.
///
/// # Arguments
///
/// * `run` - The loaded image, its discovery results, the user names and
///   comments, and the function's entry address.
/// * `cleanup` - Run [`cleanup_text`] on the body.
/// * `assume` - Parameter slots a scenario fixes, and their values.
/// * `witness` - Keep what the lifter knew about each block beside the
///   text, for [`replay`].
fn decompile_in_run(
    run: (&Program, &Analysis, &Overlay, u64),
    cleanup: bool,
    assume: &[(u8, u64)],
    witness: bool,
) -> Option<Decompiled> {
    match run.0.arch.isa()? {
        crate::isa::Isa::X86 { bits } => {
            decompile_in::<arch::X86>(run, bits, cleanup, assume, witness)
        }
        crate::isa::Isa::A64 => decompile_in::<arch::A64>(run, 64, cleanup, assume, witness),
        crate::isa::Isa::A32 => decompile_in::<arch::A32>(run, 32, cleanup, assume, witness),
    }
}

/// [`decompile_with`] for one instruction set's lifter.
///
/// # Arguments
///
/// * `run` - The loaded image, its discovery results, the user names and
///   comments, and the function's entry address.
/// * `bitness` - The register width in bits: 32 or 64.
/// * `cleanup` - Run [`cleanup_text`] on the body.
/// * `assume` - Parameter slots a scenario fixes, and their values.
/// * `witness` - Keep what the lifter knew about each block beside the
///   text, for [`replay`].
///
/// # Returns
///
/// The pseudo-C, or `None` when there is no such function.
fn decompile_in<L: Lifter>(
    run: (&Program, &Analysis, &Overlay, u64),
    bitness: u32,
    cleanup: bool,
    assume: &[(u8, u64)],
    witness: bool,
) -> Option<Decompiled> {
    let (program, analysis, overlay, entry) = run;
    let mut lap = crate::timing::Lap::new();
    let f = analysis.function(entry)?;
    let blocks = &f.blocks;
    let n = blocks.len();

    let idx: BTreeMap<u64, usize> = blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let mut succs: Vec<Vec<usize>> = blocks
        .iter()
        .map(|b| {
            b.successors
                .iter()
                .filter_map(|s| idx.get(s).copied())
                .collect()
        })
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ss) in succs.iter().enumerate() {
        for &s in ss {
            preds[s].push(i);
        }
    }
    let mut ctx = new_ctx(
        program,
        analysis,
        overlay,
        f,
        bitness,
        idx.keys().copied().collect(),
        assume,
    );
    let code = L::decode_blocks(&ctx, f);
    let twins = twin_tests::<L>(&code, &preds);
    for (&d, &o) in &twins {
        for p in std::mem::take(&mut preds[d]) {
            for s in &mut succs[p] {
                if *s == d {
                    *s = o;
                }
            }
            preds[o].push(p);
        }
    }
    let at = |va: &u64| idx.get(va).map(|&i| twins.get(&i).copied().unwrap_or(i));
    ctx.seh_frame = L::seh_frame(&ctx, &code);
    ctx.go_check = L::go_check(&ctx, f.entry, &code, &idx);
    let entry_block = ctx.entry_block;
    let shape = L::shape(&mut ctx, f, &code, &succs, entry_block);
    ctx.conv = shape.conv;
    ctx.params.clone_from(&shape.params);
    ctx.variadic = shape.variadic;
    ctx.this_param = shape.this_param;
    ctx.result_param = shape.result_param;
    ctx.stack_params = shape.stack;
    ctx.arg_count = shape.count;
    ctx.arg_floats = shape.floats();
    ctx.rax_written = L::writes_result(&ctx, &code);
    let word = u8::try_from(bitness).unwrap_or(64);
    let stated_returns = ctx.stated.map(|p| match &p.ret {
        None => lift::Returns::Nothing,
        Some(ty) => lift::Returns::of(ty.pass(&overlay.types, word, program.format), word),
    });
    ctx.unused_result = match (stated_returns, &f.signature) {
        (Some(r), _) => r == lift::Returns::Nothing,
        (None, Some(s)) => s.ret == "void",
        (None, None) => f.returns_value == Some(false),
    };
    let hidden =
        usize::from(ctx.stated.is_none() && f.signature.as_ref().is_some_and(|s| s.by_pointer));
    ctx.ret_lane = match stated_returns {
        Some(lift::Returns::Int(bits @ (8 | 16))) => bits,
        Some(_) => 64,
        None => L::ret_lane(
            &code,
            &succs,
            f.signature.as_ref().map(|s| s.ret.as_str()),
            analysis,
        ),
    };
    ctx.ret_float = match stated_returns {
        Some(r) => matches!(r, lift::Returns::Float(_)),
        None => f
            .signature
            .as_ref()
            .map_or(f.ret_float.is_some(), |s| float_return(&s.ret)),
    };
    ctx.ret_sse = bitness == 32
        && matches!(program.arch.isa(), Some(crate::isa::Isa::X86 { .. }))
        && ctx.stated.is_none()
        && f.signature.is_none()
        && f.ret_float.is_none()
        && lift::sse_callee(&ctx, Some(f.entry)).returns;
    if ctx.ret_sse {
        ctx.ret_float = true;
        ctx.unused_result = false;
    }
    ctx.rax_written |= ctx.ret_float && (bitness == 64 || ctx.ret_sse);
    let ret_width = match stated_returns {
        Some(lift::Returns::Float(w)) => Some(w),
        Some(lift::Returns::Nothing | lift::Returns::Int(_)) => None,
        None => ctx.ret_float.then(|| {
            f.ret_float.unwrap_or_else(|| {
                if f.signature.as_ref().is_some_and(|s| s.ret == "float") {
                    32
                } else {
                    64
                }
            })
        }),
    }
    .filter(|_| bitness == 64 || ctx.ret_sse);
    ctx.lanes = L::lanes(&code, ret_width);
    ctx.ret_rdx = bitness == 64 && f.hands_back_rdx && ctx.stated.is_none();
    if let Some(sig) = &f.signature {
        if ctx.this_param
            && let Some(c) = classes::class_of(&sig.name)
        {
            ctx.param_class.insert(0, c.to_owned());
        }
        let lead = usize::from(ctx.this_param) + hidden;
        for (j, ty) in sig.params.iter().enumerate() {
            if let (Some(c), Ok(i)) = (pointee_class(ty), u8::try_from(lead + j)) {
                ctx.param_class.insert(i, c.to_owned());
            }
        }
    }
    for (i, c) in &f.param_hints {
        ctx.param_class.entry(*i).or_insert_with(|| c.clone());
    }
    let plan = guarded::plan(program, analysis, overlay, f, &succs, ctx.entry_block);
    ctx.eh_roots.clone_from(&plan.roots);
    ctx.flag_readers = code.iter().map(|b| L::reads_inherited_flags(b)).collect();
    ctx.rebase_flags = vec![None; code.len()];
    let regs = L::live_in(&ctx, &code, &succs);
    let need = code
        .iter()
        .enumerate()
        .map(|(b, instrs)| {
            let mut out = FxHashMap::default();
            for &s in &succs[b] {
                lift::join_need(&mut out, &regs[s]);
            }
            L::need_after(&ctx, instrs, &out)
        })
        .collect();
    let mut live = Live {
        regs,
        need,
        slots: None,
    };
    lap.end(crate::timing::Step::Decode);
    let (_, _, mut recorded) = dataflow::<L>(&mut ctx, &code, &succs, &preds, &live, &[]);
    ctx.frame.solve(&ctx.overlay.choices);
    let floats: Vec<i64> = ctx.frame.floats().collect();
    ctx.sites.extend(floats.into_iter().map(Site::Slot));
    widen_slots(&mut recorded);
    let mut succs_eh = succs.clone();
    for (root, feeders) in &plan.roots {
        for &p in feeders {
            succs_eh[p].push(*root);
        }
    }
    live.slots = Some(slot_liveness(&recorded, &succs_eh));
    let assumes = block_assumptions::<L>(&code, &preds, &recorded);
    let (in_envs, processed, recorded) =
        dataflow::<L>(&mut ctx, &code, &succs, &preds, &live, &assumes);
    lap.end(crate::timing::Step::Lift);

    let mut succs_live = succs.clone();
    let mut preds_live = preds.clone();
    for (b, rec) in recorded.iter().enumerate() {
        let Some((taken, target, fall)) = rec.branch_const else {
            continue;
        };
        let dead = if taken { fall } else { target };
        let Some(d) = at(&dead) else { continue };
        succs_live[b].retain(|s| *s != d);
        preds_live[d].retain(|p| *p != b);
    }
    for (b, rec) in recorded.iter().enumerate() {
        let Some(live) = rec
            .switch_dest
            .filter(|t| idx.contains_key(t))
            .or_else(|| {
                rec.switch_const
                    .and_then(|k| blocks.get(b).and_then(|blk| table_target(analysis, blk, k)))
            })
            .and_then(|t| at(&t))
        else {
            continue;
        };
        for d in std::mem::replace(&mut succs_live[b], vec![live]) {
            if d != live {
                preds_live[d].retain(|p| *p != b);
            }
        }
    }

    let starts = blocks
        .iter()
        .enumerate()
        .fold(FxHashMap::default(), |mut m, (i, b)| {
            m.entry(b.start).or_insert(i);
            m
        });
    let mut st = Emit::<L> {
        blocks,
        starts,
        code: &code,
        succs: succs_live,
        preds: preds_live,
        in_envs: &in_envs,
        live: &live,
        processed: &processed,
        assumes: &assumes,
        emitted: vec![false; n],
        dead: vec![false; n],
        twins,
        bound: n,
        skipped: BTreeSet::new(),
        loops: Vec::new(),
        orders: Vec::new(),
        no_dup: BTreeSet::new(),
        copy_calls: false,
        tail_clones: 0,
        copy_stop: false,
        dup_stack: Vec::new(),
        copy_targets: BTreeSet::new(),
        entry: entry_block,
        eh_roots: plan.root_blocks().collect(),
    };
    let mut reached = vec![false; n];
    let mut work: Vec<usize> = std::iter::once(entry_block)
        .chain(plan.root_blocks())
        .collect();
    while let Some(b) = work.pop() {
        if b >= n || std::mem::replace(&mut reached[b], true) {
            continue;
        }
        work.extend(st.succs[b].iter().copied());
    }
    let unreachable = reached
        .iter()
        .enumerate()
        .filter(|(b, r)| !**r && !st.twins.contains_key(b))
        .count();
    for (b, r) in reached.iter().enumerate() {
        if !r {
            st.emitted[b] = true;
            st.dead[b] = true;
            st.succs[b].clear();
        }
    }
    for preds in &mut st.preds {
        preds.retain(|p| reached[*p]);
    }
    let handed = traces::LiveCfg {
        succs: st.succs.clone(),
    };
    let mut body = String::new();
    let entry_env = L::entry_env(&ctx);
    if let Some(joined) = in_envs.get(entry_block) {
        let names = ctx.names();
        for (k, v) in &entry_env.vals {
            if !joined.vals.contains_key(k) && live.is_live(entry_block, *k) {
                let _ = writeln!(body, "{} = {};", names.key(*k), v.render(&names));
            }
        }
    }
    let mut cursor = 0usize;
    let mut follow = Some(entry_block);
    let mut named: BTreeSet<u64> = BTreeSet::new();
    loop {
        let i = match follow.take().filter(|&x| !st.emitted[x]) {
            Some(x) => x,
            None => {
                while cursor < n && st.emitted[cursor] {
                    cursor += 1;
                }
                if cursor >= n {
                    break;
                }
                cursor
            }
        };
        if st.unread(i, &named) {
            st.emitted[i] = true;
            continue;
        }
        let at = body.len();
        emit_block(&mut ctx, &mut st, i, &mut body, 0);
        st.emitted[i] = true;
        note_jumps(&body[at..], &mut named);
        if FOLLOW_JUMPS {
            follow = trailing_goto(&body[at..]).and_then(|va| st.index_of(va));
        }
    }
    let skip = overlay.passes;
    let body = cir::fold(&body, &plan.regions, st.ends(&ctx, cleanup, skip).as_ref());
    let body = if skip.runs(Pass::DropReturnedValues)
        && f.returns_value == Some(false)
        && f.signature.is_none()
        && ctx.stated.is_none()
        && !ctx.ret_sse
    {
        drop_returned_values(&body)
    } else {
        body
    };
    let returns_nothing = match stated_returns {
        Some(r) => r == lift::Returns::Nothing,
        None => f.signature.as_ref().map_or_else(
            || {
                !body
                    .lines()
                    .any(|l| matches!(l.trim().strip_prefix("return "), Some(v) if v != ";"))
            },
            |s| s.ret == "void",
        ),
    };
    let (result_reg, second_reg) = L::result_names(bitness);
    let live_out = ctx.ret_rdx || (bitness == 32 && f.hands_back_rdx);
    lap.end(crate::timing::Step::Structure);
    let (body, settle) = if cleanup {
        cleanup_settled(&body, live_out.then_some(second_reg), skip)
    } else {
        (body, Settle::default())
    };
    lap.end(crate::timing::Step::Cleanup);
    let (body, canary) = if cleanup && skip.runs(Pass::Canary) {
        canary::fold(&body)
    } else {
        (body, None)
    };
    let (body, panic_checks) = if cleanup && skip.runs(Pass::PanicChecks) {
        panics::fold_checks(&panics::annotate(&body, program))
    } else {
        (body, Vec::new())
    };
    let body = if returns_nothing && skip.runs(Pass::DropDeadResults) {
        drop_dead_results(&body, result_reg)
    } else {
        body
    };
    let body = skip.apply(Pass::ApplyEnums, body, |body| match overlay.enum_source {
        EnumSource::Given => apply_enums(body, &overlay.enums),
        EnumSource::Binary => apply_enums(body, &called_tables(program, analysis, overlay, body)),
    });
    let body = skip.apply(Pass::ApplyResults, body, |body| {
        apply_results(body, &ctx.result_groups)
    });
    let names = ctx.names();
    let mut user_typed = typed_globals(
        overlay,
        &ctx.globals,
        &names,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    );
    user_typed.extend(declared::typed_pointers(
        overlay,
        f.entry,
        &names,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    ));
    for (var, fields) in declared::debug_pointers(
        &program.debug_types,
        &ctx.debug_params,
        &names,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    )
    .into_iter()
    .chain(api_typed(
        &body,
        program.format,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    ))
    .chain(globals::debug_typed(
        program,
        &ctx.globals,
        &names,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    )) {
        if !user_typed.iter().any(|(v, _)| *v == var) {
            user_typed.push((var, fields));
        }
    }
    let body = if user_typed.is_empty() || !skip.runs(Pass::RenameTyped) {
        body
    } else {
        rename_typed(&body, &user_typed)
    };
    let user_enums = user_enum_globals(overlay, &ctx.globals, &names);
    let body = if user_enums.is_empty() || !skip.runs(Pass::UserEnums) {
        body
    } else {
        apply_user_enums(&body, &user_enums)
    };

    let value_return = body
        .lines()
        .any(|l| matches!(l.trim().strip_prefix("return "), Some(v) if v != ";"));
    let inferred = match (value_return, ctx.ret_bits) {
        (false, _) => "void",
        (true, _) if f.ret_float == Some(32) || ctx.x87_ret == 32 => "float",
        (true, _) if f.ret_float.is_some() => "double",
        (true, 32) if ctx.ret_sse => "float",
        (true, _) if ctx.ret_sse => "double",
        (true, 8) => "uint8_t",
        (true, 16) => "uint16_t",
        (true, 32) => "uint32_t",
        (true, _) => word_type(ctx.bitness),
    };
    let recorded_ret = ctx.debug_ret.as_deref();
    let ret_ty = recorded_ret.unwrap_or(inferred);
    let typed = L::param_types(&ctx, &code, &succs, entry_block);
    let name = name_of(analysis, overlay, f.entry);
    let library = (ctx.stated.is_none()
        && f.signature.is_none()
        && ctx.debug_ret.is_none()
        && ctx.debug_params.is_empty())
    .then(|| {
        signature::library_prototype(
            crate::analysis::bare_name(&name),
            program.format,
            shape.count,
            ctx.variadic,
            value_return,
        )
    })
    .flatten();
    let declared: Vec<String> = match ctx.stated {
        Some(_) => ctx
            .debug_params
            .iter()
            .map(|p| p.type_name.clone().unwrap_or_default())
            .collect(),
        None => f.signature.as_ref().map_or_else(
            || {
                library.as_ref().map_or_else(Vec::new, |(_, params)| {
                    params.iter().map(|p| (*p).to_owned()).collect()
                })
            },
            |s| s.params.clone(),
        ),
    };
    let var_typed: BTreeSet<usize> = overlay
        .vars
        .get(&f.entry)
        .into_iter()
        .flatten()
        .filter_map(|(k, v)| match (k, &v.ty) {
            (crate::analysis::protos::VarKey::Param(i), Some(_)) => Some(usize::from(*i)),
            (crate::analysis::protos::VarKey::Param(_), None)
            | (crate::analysis::protos::VarKey::Slot(_), _) => None,
        })
        .collect();
    let class = classes::class_of(crate::analysis::bare_name(&name)).unwrap_or("");
    let ret_ty = f.signature.as_ref().map_or_else(
        || match &library {
            Some((ret, _)) => (*ret).to_owned(),
            None => f
                .ret_hint
                .as_ref()
                .filter(|_| f.ret_float.is_none())
                .map_or(ret_ty.to_owned(), |c| format!("{c} *")),
        },
        |s| s.ret.clone(),
    );
    let ret_ty = match ctx.stated {
        Some(_) => ctx.debug_ret.clone().unwrap_or_else(|| "void".to_owned()),
        None => ret_ty,
    };
    let result_at = ctx.result_param.map(usize::from);
    let lead = usize::from(ctx.this_param)
        + usize::from(result_at.is_some_and(|r| r <= usize::from(ctx.this_param)));
    let count = shape.count;
    let floats = shape.floats();
    let mut params: Vec<String> = (0..count)
        .map(|i| {
            let unread = || {
                ctx.debug_params
                    .get(i)
                    .map(|p| p.name.clone())
                    .filter(|n| !n.is_empty())
                    .unwrap_or_else(|| format!("a{}", i + 1))
            };
            let key = u8::try_from(i)
                .ok()
                .filter(|_| {
                    ctx.conv
                        .arg_reg(i, floats)
                        .is_some_and(|r| ctx.params.contains(&r))
                })
                .map_or_else(unread, |p| names.key(Key::Param(p)));
            if ctx.this_param && i == 0 {
                let this_class = if class.is_empty() {
                    f.param_hints.get(&0).map_or("void", String::as_str)
                } else {
                    class
                };
                return format!("{this_class} *this");
            }
            if result_at == Some(i) {
                return format!("{ret_ty} *result");
            }
            let hint = u8::try_from(i).ok().and_then(|p| f.param_hints.get(&p));
            let float_only = floats & (1u8 << i.min(7)) != 0;
            let plain = if float_only {
                "float"
            } else {
                word_type(ctx.bitness)
            };
            let hint = hint.filter(|_| !float_only);
            let recorded = ctx
                .debug_params
                .get(i)
                .and_then(|p| p.type_name.clone())
                .or_else(|| typed.get(&i).cloned());
            let stated_ty = recorded.clone().filter(|_| var_typed.contains(&i));
            match (
                stated_ty
                    .as_ref()
                    .or_else(|| i.checked_sub(lead).and_then(|j| declared.get(j))),
                hint,
                recorded,
            ) {
                (Some(ty), _, _) if ty.ends_with('*') || ty.ends_with('&') => {
                    format!("{ty}{key}")
                }
                (Some(ty), _, _) => format!("{ty} {key}"),
                (None, Some(c), _) => format!("{c} *{key}"),
                (None, None, Some(ty)) if ty.ends_with(['*', '&']) => format!("{ty}{key}"),
                (None, None, Some(ty)) => format!("{ty} {key}"),
                (None, None, None) => format!("{plain} {key}"),
            }
        })
        .collect();
    if let Some(r) = result_at.filter(|r| *r < params.len()) {
        let at = abi::indirect_result_position(ctx.this_param);
        let result = params.remove(r);
        params.insert(at.min(params.len()), result);
    }
    if ctx.variadic {
        params.push("...".to_owned());
    }
    let suffix = if f.signature.as_ref().is_some_and(|s| s.is_const) {
        " const"
    } else {
        ""
    };

    let mut out = String::new();
    let _ = writeln!(
        out,
        "// {name} @ {:#x}: {} instructions, {} blocks",
        f.entry, f.instr_count, n
    );
    let sep = if ret_ty.ends_with(['*', '&']) {
        ""
    } else {
        " "
    };
    let _ = writeln!(
        out,
        "// signature: {ret_ty}{sep}{}({}){suffix}",
        expr::bare(&name),
        params.join(", ")
    );
    if let Some((file, line)) = &ctx.debug_source {
        let _ = writeln!(out, "// source: {file}:{line}");
    }
    if let Some((_, folded)) = &ctx.go_check {
        let _ = writeln!(out, "// go stack check folded: {folded}");
    }
    if let Some(folded) = &canary {
        let _ = writeln!(out, "// folded: {}", folded.note());
    }
    let halves = !crate::analysis::runtime::microsoft(ctx.program.arch, ctx.program.format);
    let mut helpers: Vec<&crate::analysis::runtime::Helper> = f
        .callees
        .iter()
        .filter_map(|&c| lift::runtime_helper(&ctx, c))
        .filter(|h| !(halves && abi::runtime::Runtime::named(h.name).is_some()))
        .collect();
    helpers.sort_unstable_by_key(|h| h.name);
    helpers.dedup_by_key(|h| h.name);
    for h in helpers {
        let _ = writeln!(out, "// runtime: {}; computes {}", h.proto, h.means);
    }
    if !panic_checks.is_empty() {
        let _ = writeln!(
            out,
            "// note: calls to {} are left out: rust overflow and bounds checks folded",
            panic_checks.join(", ")
        );
    }
    if let Some(table) = enum_table(&body, &params) {
        /// Most members written into the header line.
        const SHOWN: usize = 8;
        let shown: Vec<String> = table
            .members
            .iter()
            .take(SHOWN)
            .map(|(k, lit)| format!("{lit} = {k}"))
            .collect();
        let more = table.members.len().saturating_sub(SHOWN);
        let tail = if more > 0 {
            format!(" (+{more} more)")
        } else {
            String::new()
        };
        let name = if table.name.is_empty() {
            String::new()
        } else {
            format!(" {}", table.name)
        };
        let _ = writeln!(
            out,
            "// enum{name}: {} values, {}{tail}",
            table.members.len(),
            shown.join(", ")
        );
    }
    if let Some(effects) = effects_line(&body) {
        let _ = writeln!(out, "// effects: {effects}");
    }
    let sent = crate::analysis::objc::sent_by(analysis, f);
    if !sent.is_empty() {
        /// Most messages written into the header line.
        const SENT_SHOWN: usize = 8;
        let more = sent.len().saturating_sub(SENT_SHOWN);
        let tail = if more > 0 {
            format!(" (+{more} more)")
        } else {
            String::new()
        };
        let shown: Vec<&str> = sent.iter().take(SENT_SHOWN).map(String::as_str).collect();
        let _ = writeln!(out, "// messages: {}{tail}", shown.join(", "));
    }
    if f.hands_back_rdx {
        let _ = writeln!(
            out,
            "// hands back {second_reg}: a caller reads it after the call"
        );
    }
    let against: Vec<String> = stated_returns
        .map(|r| declared::contradictions(f, &shape, r, bitness))
        .unwrap_or_default();
    if !against.is_empty() {
        let _ = writeln!(
            out,
            "// stated prototype contradicted: {}",
            against.join("; ")
        );
    }
    if let Some(asserts) = asserts_of(&body) {
        let _ = writeln!(out, "// asserts: {asserts}");
    }
    if let Some(code) = classes::class_of(crate::analysis::bare_name(&name))
        .and_then(|c| analysis.classes.ids.get(c))
    {
        let _ = writeln!(out, "// wire id: {}", classes::fourcc(*code));
    }
    if f.callers.len() >= PARAM_VALUE_SITES
        && let Some(values) = passed_values(analysis, entry, count)
    {
        let _ = writeln!(out, "// callers pass: {values}");
    }
    if let Some(evidence) = analysis.recognized.get(&entry) {
        let _ = writeln!(
            out,
            "// recognized: {}",
            crate::analysis::recognize::describe(evidence)
        );
    }
    let clones = analysis.clones_of(entry);
    if let Some(first) = clones.first().filter(|_| clones.len() > 1) {
        let _ = writeln!(
            out,
            "// clones: {} functions run this code, the first at {:#x}",
            clones.len(),
            first
        );
    }
    let shapes = analysis.shapes_of(entry);
    if shapes.len() > clones.len().max(1)
        && let Some(first) = shapes.iter().find(|e| **e != entry && !clones.contains(e))
    {
        let _ = writeln!(
            out,
            "// shape: {} more run this code with other operands, e.g. {:#x}",
            shapes.len() - clones.len().max(1),
            first
        );
    }
    if let Some(funclet) = f.funclet {
        let _ = writeln!(
            out,
            "// note: {} of {}; it runs on that function's frame, so ebp and the locals are its",
            funclet.role.describe(),
            name_of(analysis, overlay, funclet.parent)
        );
    }
    if let Some(f) = ctx.escape_floor {
        let _ = writeln!(
            out,
            "// note: &{} escapes; locals from there up are reloaded after calls",
            names.slot(f)
        );
    }
    if unreachable > 0 {
        let _ = writeln!(out, "// note: {unreachable} unreachable blocks omitted");
    }
    if !ctx.empty_calls.is_empty() {
        let names: Vec<String> = ctx
            .empty_calls
            .iter()
            .map(|&e| name_of(analysis, overlay, e))
            .collect();
        let _ = writeln!(
            out,
            "// note: calls to {} are left out: {} nothing but return",
            names.join(", "),
            if names.len() == 1 {
                "it does"
            } else {
                "they do"
            }
        );
    }
    if !ctx.read_in_place.is_empty() {
        let names: Vec<String> = ctx
            .read_in_place
            .iter()
            .map(|&e| name_of(analysis, overlay, e))
            .collect();
        let what = if names.len() == 1 {
            "is read in place: it only loads registers and returns or jumps on"
        } else {
            "are read in place: they only load registers and return or jump on"
        };
        let _ = writeln!(out, "// note: {} {what}", names.join(", "));
    }
    for (&e, reg) in &ctx.dispatches {
        let reg = format!("{reg:?}").to_ascii_lowercase();
        let _ = writeln!(
            out,
            "// note: {} only jumps through {reg}: a call to it is the call through {reg}",
            name_of(analysis, overlay, e)
        );
    }
    let used: BTreeSet<&str> = tokens(&body).collect();
    let slots = declared::collect_slots(
        &mut ctx.declared,
        n == 1
            && recorded
                .first()
                .is_some_and(|r| r.stores.get(&-16) == Some(&64)),
    );
    let mut by_type: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut notes: Vec<String> = Vec::new();
    let result_typed = typed_results(&body, &ctx.result_types);
    let slot_stated = declared::slot_types(overlay, f.entry, &ctx.declared, word, program.format);
    for (k, ty) in &ctx.declared {
        if matches!(k, Key::Slot(o) if names.stack_param(*o).is_some()) {
            continue;
        }
        let name = names.key(*k);
        if !declared::keep_decl(program.arch, *k, *ty, &name, &used, &names, &slots) {
            continue;
        }
        if let Key::Slot(o) = k {
            let overlapping: Vec<String> = slots
                .iter()
                .filter(|(o2, t2)| {
                    o2 != o
                        && overlaps(*o, ty.bits(), *o2, t2.bits())
                        && used.contains(names.slot(*o2).as_str())
                })
                .map(|(o2, _)| names.slot(*o2))
                .collect();
            if !overlapping.is_empty() {
                notes.push(format!("// {name} overlaps {}", overlapping.join(", ")));
            }
        }
        let stated = match k {
            Key::Reg(_) | Key::A64(_) | Key::A32(_) => result_typed.get(&name).cloned(),
            Key::Slot(o) => slot_stated.get(o).cloned(),
            Key::Global(..) | Key::Tmp(_) | Key::Param(_) => None,
        };
        by_type
            .entry(stated.unwrap_or_else(|| ty.name().to_owned()))
            .or_default()
            .push(name);
    }
    let declared_names: BTreeSet<&str> = by_type
        .values()
        .flatten()
        .map(String::as_str)
        .chain(std::iter::once("retaddr"))
        .collect();
    let debug_named: BTreeSet<&str> = names.debug_locals.values().map(String::as_str).collect();
    let scratch_slot = |w: &str| {
        let digits = w
            .strip_prefix("local_")
            .or_else(|| w.strip_prefix("home_"))
            .or_else(|| w.strip_prefix("arg_"))?;
        (!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_hexdigit())).then_some(())
    };
    let mut escaped: Vec<String> = used
        .iter()
        .filter(|w| {
            (scratch_slot(w).is_some() || debug_named.contains(**w))
                && !declared_names.contains(**w)
        })
        .map(|w| (*w).to_owned())
        .collect();
    escaped.sort();
    escaped.dedup();
    if !escaped.is_empty() {
        by_type
            .entry("uint64_t".to_owned())
            .or_default()
            .extend(escaped);
    }
    let locals: Vec<cir::Decl> = by_type
        .iter()
        .map(|(ty, names_of_ty)| cir::Decl {
            ty: cir::CTy::parse(ty),
            names: names_of_ty.iter().map(|n| cir::Name::of(n)).collect(),
            note: None,
        })
        .collect();
    cir::print_decls(&locals, &mut out);
    for n in &notes {
        out.push_str(n);
        out.push('\n');
    }
    let mut tables: BTreeMap<u64, cir::Decl> = BTreeMap::new();
    for (addr, _) in &ctx.globals {
        let Some(t) = globals::table_holding(program, *addr) else {
            continue;
        };
        let table = names.key(Key::Global(t.start, 8));
        if used.contains(table.as_str()) {
            tables.entry(t.start).or_insert_with(|| cir::Decl {
                ty: cir::CTy::parse(&t.declared),
                names: vec![cir::Name::of(&format!("{table}[{}]", t.len))],
                note: Some(format!("@ {:#x}", t.start)),
            });
        }
    }
    let globals: Vec<cir::Decl> = tables
        .into_values()
        .chain(
            ctx.globals
                .iter()
                .filter(|(addr, ty)| ctx.global_types.get(addr).is_none_or(|t| t == ty))
                .filter(|(addr, _)| globals::table_holding(program, *addr).is_none())
                .filter_map(|(addr, ty)| {
                    let g = names.key(Key::Global(*addr, ty.bits()));
                    let import = names.import_at(*addr).is_some_and(|n| n == g);
                    let word = u64::try_from(ctx.conv.word).unwrap_or(8);
                    let (base, stars) = globals::stated(program, *addr, &g)
                        .filter(|s| s.is_pointer() && s.fits(*ty, word))
                        .map_or_else(
                            || (ty.name().to_owned(), String::new()),
                            |s| {
                                let base = s.spelled.trim_end_matches(['*', ' ']);
                                (base.to_owned(), s.spelled[base.len()..].replace(' ', ""))
                            },
                        );
                    (used.contains(g.as_str()) && !import).then(|| cir::Decl {
                        ty: cir::CTy::parse(&base),
                        names: vec![cir::Name::of(&format!("{stars}{g}"))],
                        note: Some(match expr::tls_slot(*addr) {
                            Some(off) => format!("TLS slot {off:#x}"),
                            None => format!("@ {addr:#x}"),
                        }),
                    })
                }),
        )
        .collect();
    cir::print_decls(&globals, &mut out);
    out.push('\n');
    out.push_str(&body);
    let emitted = blocks
        .iter()
        .map(|b| ctx.effects.contains_key(&b.start))
        .collect();
    let effects = lift::Packed::new(
        blocks
            .iter()
            .map(|b| ctx.effects.remove(&b.start).unwrap_or_default()),
    );
    let witness = witness.then(|| {
        Box::new(replay::Witness {
            code: L::witness(code),
            ins: in_envs,
            processed,
            assumes,
            live,
            emitted,
            flag_readers: std::mem::take(&mut ctx.flag_readers),
            conv: ctx.conv,
            ret_bits: ctx.ret_bits,
            ret_float: ctx.ret_float,
            ret_xmm: ctx.ret_float && (bitness == 64 || ctx.ret_sse),
            result_read: f.returns_value == Some(true) || ctx.ret_float,
            stated_contradicted: !against.is_empty(),
            dispatches: std::mem::take(&mut ctx.pointer_dispatches)
                .into_iter()
                .chain(std::mem::take(&mut ctx.dispatches))
                .collect(),
            defs: recorded.into_iter().map(|r| r.stores).collect(),
            seh_frame: ctx.seh_frame,
            slot_bits: ctx
                .declared
                .iter()
                .filter_map(|(k, ty)| match k {
                    Key::Slot(o) => Some((*o, ty.bits())),
                    Key::Reg(_)
                    | Key::Tmp(_)
                    | Key::Param(_)
                    | Key::Global(..)
                    | Key::A64(_)
                    | Key::A32(_) => None,
                })
                .collect(),
            reg_ty: ctx
                .reg_ty
                .iter()
                .chain(&ctx.declared)
                .filter_map(|(k, ty)| match ty {
                    Ty::F32 | Ty::F64 => Some((*k, *ty)),
                    _ => None,
                })
                .chain(params.iter().enumerate().filter_map(|(i, p)| {
                    let floats = [("float ", Ty::F32), ("double ", Ty::F64)];
                    let (_, ty) = floats.into_iter().find(|(t, _)| p.starts_with(t))?;
                    Some((Key::Param(u8::try_from(i).ok()?), ty))
                }))
                .collect(),
        })
    });
    lap.end(crate::timing::Step::Header);
    Some(Decompiled {
        text: out,
        virtual_callees: ctx.vcalls.iter().copied().collect(),
        blocks: n,
        cut: unreachable,
        live: handed,
        effects,
        witness: std::sync::Mutex::new(witness),
        settle,
        sites: ctx.sites.iter().copied().collect(),
    })
}

/// Indents a structured body by one level (two spaces; empty lines stay empty).
///
/// # Arguments
///
/// * `body` - The lines to indent.
fn indent(body: &str) -> String {
    let mut out = String::with_capacity(body.len() + body.lines().count() * 2);
    for l in body.lines() {
        if !l.is_empty() {
            out.push_str("  ");
        }
        out.push_str(l);
        out.push('\n');
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    /// The lifter agrees with the emulator on integer and stack arithmetic.
    ///
    /// Every register it writes, the ones it leaves alone and the stack
    /// pointer match. Each 32-bit write clears the upper half (`shr r9d`
    /// shifts only the low half in, a byte merged into `r12d` keeps it
    /// clear, `mov edx, edx` and a `cmov` not taken clear it) and `movsxd`
    /// sign-extends.
    #[test]
    fn the_lifter_agrees_with_the_emulator() {
        let p = crate::program::Program::raw_x64(&[
            0x48, 0x89, 0xc8, // ASM: mov rax, rcx
            0x48, 0x01, 0xd0, // ASM: add rax, rdx
            0x48, 0xc1, 0xe0, 0x03, // ASM: shl rax, 3
            0x8d, 0x0c, 0x12, // ASM: lea ecx, [rdx+rdx]
            0x0f, 0xaf, 0xc1, // ASM: imul eax, ecx
            0x48, 0x83, 0xec, 0x10, // ASM: sub rsp, 0x10
            0x48, 0x89, 0x04, 0x24, // ASM: mov [rsp], rax
            0x48, 0x8b, 0x5c, 0x24, 0x08, // ASM: mov rbx, [rsp+8]
            0x48, 0x0f, 0xb6, 0xf3, // ASM: movzx rsi, bl
            0x49, 0x89, 0xc9, // ASM: mov r9, rcx
            0x41, 0xc1, 0xe9, 0x04, // ASM: shr r9d, 4
            0x41, 0x89, 0xc4, // ASM: mov r12d, eax
            0x41, 0x80, 0xf4, 0x01, // ASM: xor r12b, 1
            0x89, 0xd2, // ASM: mov edx, edx
            0x48, 0x63, 0x7c, 0x24, 0x08, // ASM: movsxd rdi, [rsp+8]
            0x31, 0xc0, // ASM: xor eax, eax
            0x85, 0xc0, // ASM: test eax, eax
            0x44, 0x0f, 0x45, 0xc1, // ASM: cmovne r8d, ecx (not taken)
            0x48, 0x83, 0xc4, 0x10, // ASM: add rsp, 0x10
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        for seed in 1..=4 {
            let v = super::verify::verify(&p, &a, &[0x1000], seed);
            assert_eq!(v.checked, 1, "{v:?}");
            assert!(v.compared >= 16, "{v:?}");
            assert!(v.mismatches.is_empty(), "{}", super::verify::verify_tsv(&v));
        }
    }

    /// A scenario folds the branches on its parameter: under `a2 = 2` only
    /// the arm for 2 is written, and the header counts the cut blocks.
    #[test]
    fn a_scenario_keeps_the_code_that_can_run() {
        let p = crate::program::Program::raw_x64(&[
            0x83, 0xfa, 0x02, // ASM: cmp edx, 2
            0x74, 0x0b, // ASM: je 0x1010
            0x83, 0xfa, 0x03, // ASM: cmp edx, 3
            0x74, 0x0c, // ASM: je 0x1016
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
            0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax, 20 (0x1010)
            0xc3, // ASM: ret
            0xb8, 0x1e, 0x00, 0x00, 0x00, // ASM: mov eax, 30 (0x1016)
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let all = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(
            all.contains("return 20;") && all.contains("return 30;"),
            "{all}"
        );
        let two = super::decompile_scenario(&p, &a, &o, 0x1000, &[(1, 2)]).expect("decompiles");
        assert!(
            two.starts_with("// scenario: a2 = 2; 3 of 5 blocks cannot run\n"),
            "{two}"
        );
        assert!(
            two.contains("return 20;") && !two.contains("return 30;"),
            "{two}"
        );
        assert!(!two.contains("return 1;"), "{two}");
        assert_eq!(
            super::parse_scenario("a2=5, a1=0x10"),
            Ok(vec![(1, 5), (0, 0x10)])
        );
        assert_eq!(super::parse_scenario("a3=-1"), Ok(vec![(2, u64::MAX)]));
        assert!(super::parse_scenario("b2=5").is_err());
        assert!(super::parse_scenario("").is_err());
        let cases = super::explode(&p, &a, &o, 0x1000, 1, &[0, 2, 3, 4, 5]);
        let text = super::explode_tsv(&cases, 1, 5);
        assert!(
            text.starts_with("# a2 over 5 values: 3 behaviours in a function of 5 blocks\n"),
            "{text}"
        );
        assert!(text.contains("\n0,4-5\t"), "{text}");
        assert!(text.contains("\t20\n"), "{text}");
        assert_eq!(super::parse_explosion("a2=0..4"), Ok((1, vec![0, 1, 2, 3])));
        assert_eq!(super::parse_explosion("a1=1|0x20"), Ok((0, vec![1, 0x20])));
        assert!(super::parse_explosion("a1=0..100000").is_err());
    }

    /// A sign test after a compare that overflows its width folds by the
    /// width's top bit: `0x7fffffff - -1` is negative at 32 bits, so the
    /// `js` is taken.
    #[test]
    fn a_sign_test_folds_at_the_compare_width() {
        let p = crate::program::Program::raw_x64(&[
            0xb9, 0xff, 0xff, 0xff, 0x7f, // ASM: mov ecx, 0x7fffffff
            0x83, 0xf9, 0xff, // ASM: cmp ecx, -1
            0x78, 0x06, // ASM: js 0x1010
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2 (0x1010)
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let text = super::decompile(&p, &a, &crate::analysis::Overlay::default(), 0x1000)
            .expect("decompiles");
        assert!(
            text.contains("return 2;") && !text.contains("return 1;"),
            "{text}"
        );
    }

    /// A value used when set and a fallback otherwise is written once; a
    /// value that calls something, or a test of one value that uses
    /// another, stays as it is.
    #[test]
    fn a_value_or_its_fallback_is_written_once() {
        assert_eq!(
            super::elvis("rbx = (rax->heapBuffer != 0 ? rax->heapBuffer : rax);"),
            "rbx = (rax->heapBuffer ?: rax);"
        );
        assert_eq!(
            super::elvis(
                "g(\"s\", (*(uint64_t*)(rax + 0x30) != 0 ? *(uint64_t*)(rax + 0x30) : rax));"
            ),
            "g(\"s\", (*(uint64_t*)(rax + 0x30) ?: rax));"
        );
        let call = "x = (f(a) != 0 ? f(a) : b);";
        assert_eq!(super::elvis(call), call);
        let other = "x = (a != 0 ? b : c);";
        assert_eq!(super::elvis(other), other);
    }

    /// A plain name combined with one value is a compound assignment.
    /// A sum of two values, a call, and a store through a pointer stay
    /// assignments, and an add is not `++`.
    #[test]
    fn a_name_added_to_itself_is_a_compound_assignment() {
        assert_eq!(
            super::finish::compound_assign("  var1 = var1 + var2;"),
            "  var1 += var2;"
        );
        assert_eq!(
            super::finish::compound_assign("var1 = var1 - 1;"),
            "var1 -= 1;"
        );
        assert_eq!(
            super::finish::compound_assign("var1 = var1 << 2;"),
            "var1 <<= 2;"
        );
        assert_eq!(
            super::finish::compound_assign("var1 = var1 & 0xff;"),
            "var1 &= 0xff;"
        );
        let sum = "var1 = var1 + var2 + var3;";
        assert_eq!(super::finish::compound_assign(sum), sum);
        let call = "var1 = var1 + f();";
        assert_eq!(super::finish::compound_assign(call), call);
        let star = "*p = *p + 1;";
        assert_eq!(super::finish::compound_assign(star), star);
        let other = "var1 = var2 + var1;";
        assert_eq!(super::finish::compound_assign(other), other);
        assert!(!super::finish::compound_assign("var1 = var1 + 1;").contains("++"));
    }

    /// An `if` block that opens with the assignment the line before its
    /// `if` made drops the repeat; a loop, a condition that names the
    /// variable, and a value that is no constant or name keep theirs.
    #[test]
    fn a_repeated_assignment_into_an_if_goes() {
        let text = concat!(
            "var1 = 0;\n",
            "if ((uint32_t)a1 != 0) {\n",
            "  var1 = 0;\n",
            "  var2 = a1;\n",
            "}\n",
            "var3 = 0;\n",
            "while (a2 != 0) {\n",
            "  var3 = 0;\n",
            "}\n",
            "var4 = 1;\n",
            "if (var4 != a2) {\n",
            "  var4 = 1;\n",
            "}\n",
            "var5 = f();\n",
            "if (a2 != 0) {\n",
            "  var5 = f();\n",
            "}\n",
        );
        let out = super::finish::polish(text, 64, &crate::pack::Packs::default());
        assert_eq!(out.matches("var1 = 0;").count(), 1, "{out}");
        assert_eq!(out.matches("var3 = 0;").count(), 2, "{out}");
        assert_eq!(out.matches("var4 = 1;").count(), 2, "{out}");
        assert_eq!(out.matches("var5 = f();").count(), 2, "{out}");
    }

    /// A pointer compared with zero is `nullptr`. An integer, a field, a
    /// cast to an integer and a string stay on `0`.
    #[test]
    fn a_pointer_compared_with_zero_is_nullptr() {
        let text = concat!(
            "// signature: int32_t f(uint32_t*a1, int32_t a2, void *this)\n",
            "uint64_t *var1;\n",
            "if (a1 == 0 || *(uint8_t**)a1 != 0) {\n",
            "  return 0;\n",
            "}\n",
            "if (a2 == 0 || *(uint32_t*)a1 == 0) {\n",
            "  return 1;\n",
            "}\n",
            "if (this == 0 && var1 != 0 && 0 == a1) {\n",
            "  return 2;\n",
            "}\n",
            "if (this->head == 0 || (uint32_t)a1 == 0 || a1 + a2 == 0) {\n",
            "  return 3;\n",
            "}\n",
            "f(\"a1 == 0\");\n",
            "return *(uint32_t*)a1;\n",
        );
        let out = super::finish::spell_nullptr(text);
        assert!(
            out.contains("if (a1 == nullptr || *(uint8_t**)a1 != nullptr)"),
            "{out}"
        );
        assert!(out.contains("return 0;"), "{out}");
        assert!(out.contains("if (a2 == 0 || *(uint32_t*)a1 == 0)"), "{out}");
        assert!(
            out.contains("if (this == nullptr && var1 != nullptr && nullptr == a1)"),
            "{out}"
        );
        assert!(
            out.contains("if (this->head == 0 || (uint32_t)a1 == 0 || a1 + a2 == 0)"),
            "{out}"
        );
        assert!(out.contains("f(\"a1 == 0\");"), "{out}");
        assert!(!out.contains("NULL"), "{out}");
    }

    /// Each class whose `Singleton` a function reads is found once, in the
    /// order it is first read; a longer identifier is not one.
    #[test]
    fn the_singletons_a_function_reads_are_found() {
        let lines: Vec<String> = [
            "// effects: reads Audio::Mgr::Singleton",
            "if (Game::World::Singleton == 0) {",
            "rax = *(uint32_t*)(Game::World::Singleton + 0x70);",
            "rsi = Audio::Mgr::Singleton;",
            "rdi = Game::World::SingletonCount;",
            "sub_1(Game::World::Singleton);",
        ]
        .iter()
        .map(|l| (*l).to_owned())
        .collect();
        assert_eq!(
            super::singleton_classes(&lines, "::Singleton"),
            vec!["Game::World".to_owned(), "Audio::Mgr".to_owned()]
        );
    }

    /// A byte a call returned, moved into another byte register whose upper
    /// bits nothing reads, needs no mask: it fills the lane already.
    #[test]
    fn a_returned_byte_moved_to_a_byte_register_is_not_masked() {
        let p = crate::program::Program::raw_x64(&[
            0x53, // ASM: push rbx
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
            0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x88, 0xc3, // ASM: mov bl, al
            0x0f, 0xb6, 0xcb, // ASM: movzx ecx, bl
            0xe8, 0x0c, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
            0x5b, // ASM: pop rbx
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
            0x33, 0xc0, // ASM: xor eax, eax (0x1020)
            0x85, 0xc9, // ASM: test ecx, ecx
            0x0f, 0x94, 0xc0, // ASM: sete al
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("return sub_1020("), "{text}");
        assert!(!text.contains("& 0xff"), "{text}");
    }

    /// Parentheses left around a bare variable go, unless they are a
    /// call's: a mask stripped from `sub_1020(rax & 0xff)` leaves the call.
    #[test]
    fn unwrapping_a_variable_keeps_call_parentheses() {
        assert_eq!(
            super::unwrap_parens("x = sub_1020(rax) + (rax);", "rax"),
            "x = sub_1020(rax) + rax;"
        );
        assert_eq!(
            super::strip_width("return sub_1020(rax & 0xff);", "rax", &[], Some(8)),
            "return sub_1020(rax);"
        );
    }

    /// A callee that only loads registers and jumps on to a named function
    /// reads as that call, and one that loads a global and returns reads as
    /// the global; a field getter stays a call.
    #[test]
    fn a_callee_that_only_loads_is_read_in_place() {
        let p = crate::program::Program::raw_x64(&[
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, 0x2f, 0x00, 0x00,
            0x00, // ASM: call 0x1038 (the target, so it is a function)
            0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call 0x1020 (a field getter)
            0x48, 0x8b, 0xc8, // ASM: mov rcx, rax
            0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call 0x1028 (the forwarder)
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
            0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8] (0x1020)
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
            0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7 (0x1028)
            0xe9, 0x06, 0x00, 0x00, 0x00, // ASM: jmp 0x1038
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
            0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx] (0x1038)
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let mut o = crate::analysis::Overlay::default();
        o.names.insert(0x1038, "Sum::Add".to_owned());
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("Sum::Add(sub_1020(a1), 7);"), "{text}");
        assert!(!text.contains("sub_1028("), "{text}");
        assert!(text.contains("sub_1028 is read in place"), "{text}");
    }

    /// A call to a function whose body is `ret` is no statement, and the
    /// header says which callee was left out.
    #[test]
    fn a_call_to_a_function_that_only_returns_is_left_out() {
        let p = crate::program::Program::raw_x64(&[
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xba, 0x10, 0x00, 0x00, 0x00, // ASM: mov edx, 16
            0xe8, 0x0a, 0x00, 0x00, 0x00, // ASM: call 0x1018
            0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
            0xc3, // ASM: ret (0x1018, the empty callee)
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(!text.contains("sub_1018("), "{text}");
        assert!(text.contains("calls to sub_1018 are left out"), "{text}");
        assert!(text.contains("return 7;"), "{text}");
    }

    /// A byte count the structurer closed as `while (1)` with its exit
    /// folded in reads as the `strlen` it is.
    #[test]
    fn a_strlen_loop_closed_as_while_reads_as_strlen() {
        let text = [
            "rax = 0;",
            "if (a2 != 0) {",
            "  r8 = -1;",
            "  while (1) {",
            "    r8 += 1;",
            "    if (*(uint8_t*)(a2 + r8) != 0) continue;",
            "    rax = r8;",
            "    break;",
            "  }",
            "}",
            "return f(a1, a2, rax);",
        ];
        let mut lines: Vec<String> = text.iter().map(|l| (*l).to_owned()).collect();
        assert!(super::strlen_loops(&mut lines));
        assert_eq!(
            lines.join(
                "
"
            ),
            "rax = 0;
if (a2 != 0) {
  r8 = strlen(a2);
  rax = r8;
}
return f(a1, a2, rax);"
        );
    }

    /// A signed division by a power of two reads as one, however the
    /// compiler rounded it toward zero.
    #[test]
    fn signed_power_of_two_divisions_read_as_divisions() {
        let dc = |code: &[u8]| {
            let p = crate::program::Program::raw_x64(code);
            let a = crate::analysis::Analysis::compute(&p);
            let o = crate::analysis::Overlay::default();
            super::decompile(&p, &a, &o, 0x1000).expect("decompiles")
        };
        let half = dc(&[
            0x8b, 0xc1, // ASM: mov eax, ecx
            0x99, // ASM: cdq
            0x2b, 0xc2, // ASM: sub eax, edx
            0xd1, 0xf8, // ASM: sar eax, 1
            0xc3, // ASM: ret
        ]);
        assert!(half.contains("a1 / 2;"), "{half}");
        assert!(!half.contains(">> 31"), "{half}");
        let quarter = dc(&[
            0x8b, 0xc1, // ASM: mov eax, ecx
            0x99, // ASM: cdq
            0x83, 0xe2, 0x03, // ASM: and edx, 3
            0x03, 0xc2, // ASM: add eax, edx
            0xc1, 0xf8, 0x02, // ASM: sar eax, 2
            0xc3, // ASM: ret
        ]);
        assert!(quarter.contains("/ 4"), "{quarter}");
        let wide = dc(&[
            0x48, 0x8b, 0xc1, // ASM: mov rax, rcx
            0x48, 0x99, // ASM: cqo
            0x48, 0x2b, 0xc2, // ASM: sub rax, rdx
            0x48, 0xd1, 0xf8, // ASM: sar rax, 1
            0xc3, // ASM: ret
        ]);
        assert!(wide.contains("/ 2"), "{wide}");
        assert!(!wide.contains(">> 63"), "{wide}");
    }

    /// An integer store of a float's bits reads as the float; a flag word
    /// that happens to spell a float stays an integer.
    #[test]
    fn a_float_stored_as_bits_reads_as_a_float() {
        let p = crate::program::Program::raw_x64(&[
            0xc7, 0x41, 0x10, 0x00, 0x00, 0x80, 0x3f, // ASM: mov dword [rcx+0x10], 0x3f800000
            0xc7, 0x01, 0x00, 0x00, 0x00, 0x40, // ASM: mov dword [rcx], 0x40000000
            0xc7, 0x41, 0x08, 0x43, 0x46, 0x45, 0x52, // ASM: mov dword [rcx+8], 'REFC'
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("= 1.0f;"), "{text}");
        assert!(!text.contains("0x3f800000"), "{text}");
        assert!(text.contains("0x40000000"), "{text}");
        assert!(!text.contains("= 212"), "{text}");
        let p = crate::program::Program::raw_x64(&[
            0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00,
            0x3f, // ASM: mov dword [rsp+8], 0x3f000000
            0xf3, 0x0f, 0x10, 0x44, 0x24, 0x08, // ASM: movss xmm0, [rsp+8]
            0xf3, 0x0f, 0x59, 0xc1, // ASM: mulss xmm0, xmm1
            0xf3, 0x0f, 0x11, 0x01, // ASM: movss [rcx], xmm0
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("0.5f"), "{text}");
        assert!(!text.contains("0x3f000000"), "{text}");
    }

    /// A temporary that only copies a register gives way to the register,
    /// unless a loop, a write of the register or a label comes between.
    #[test]
    fn temporaries_that_copy_a_register_fold() {
        let run = |text: &str| {
            let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
            super::fold_temp_copies(&mut lines);
            lines.join("\n")
        };
        assert_eq!(
            run("rax = f();
tmp_1 = rcx = rax;
rax = 0;
if (tmp_1 != 0) {
  rax = g(rcx);
}
return rax;"),
            "rax = f();
rcx = rax;
rax = 0;
if (rcx != 0) {
  rax = g(rcx);
}
return rax;"
        );
        assert_eq!(
            run("tmp_4 = rbx;
h(tmp_4);"),
            "h(rbx);"
        );
        let looped = "tmp_2 = rbx = rdi;
while (1) {
  f(tmp_2);
  rbx = 5;
}";
        assert_eq!(run(looped), looped);
        let rewritten = "tmp_3 = rsi = rax;
rsi = 0;
g(tmp_3);";
        assert_eq!(run(rewritten), rewritten);
        let labeled = "tmp_5 = rsi = rax;
L_1:
g(tmp_5);";
        assert_eq!(run(labeled), labeled);
    }

    /// An atomic whose flags nothing reads is a statement: a reference
    /// count taken leaves no temporary behind.
    ///
    /// # Panics
    ///
    /// When the atomic is missing or assigned to a temporary.
    #[test]
    fn an_atomic_nothing_tests_is_a_statement() {
        let p = crate::program::Program::raw_x64(&[
            0xf0, 0xff, 0x41, 0x08, // ASM: lock inc dword [rcx+8]
            0xc3, // ASM: ret
        ]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("atomic_add32("), "{text}");
        assert!(!text.contains("tmp_"), "{text}");
    }

    /// A call's class-pointer result is bound until it is written again.
    ///
    /// The line that writes it still reads it on its right-hand side, a
    /// copy is bound too, a write inside an `if` ends the run at itself, and
    /// a write inside a loop ends the run before the loop.
    ///
    /// # Panics
    ///
    /// When a binding's variable, class or run differs.
    #[test]
    fn call_results_are_bound_for_their_run() {
        let text = [
            "rax = Core::Ptr<Game::Entity>::operator ->(a1 + 80);",
            "rdi = *(uint32_t*)(rax + 0x60);",
            "rax = Core::Ptr<Db::ValueTable>::operator ->(rax + 88);",
            "rbx = rax;",
            "if (*(uint8_t*)(rbx + 8) != 0) {",
            "  rbx = sub_1(rbx);",
            "}",
            "while (1) {",
            "  rax = sub_2(rax);",
            "}",
            "L_1:",
            "local_8 = Core::Ptr<Db::ValueTable>::operator ->(a1);",
            "sub_3(&local_8);",
        ];
        let lines: Vec<String> = text.iter().map(|l| (*l).to_owned()).collect();
        let bindings = super::result_bindings(&lines, |rhs| {
            let callee = super::callee_of(rhs)?;
            let inner = callee
                .strip_prefix("Core::Ptr<")?
                .strip_suffix(">::operator ->")?;
            Some(inner.to_owned())
        });
        let got: Vec<(&str, &str, usize, usize, bool)> = bindings
            .iter()
            .map(|b| (b.var.as_str(), b.class.as_str(), b.from, b.to, b.rewritten))
            .collect();
        assert_eq!(
            got,
            vec![
                ("rax", "Game::Entity", 1, 2, true),
                ("rax", "Db::ValueTable", 3, 7, false),
                ("rbx", "Db::ValueTable", 4, 5, true),
            ]
        );
        assert!(super::writes_var("(rax = sub_1()) != 0", "rax"));
        assert!(super::writes_var("rax += 8;", "rax"));
        assert!(!super::writes_var("if (rax == 0) {", "rax"));
        assert!(!super::writes_var("*(uint32_t*)(rax + 8) = 0;", "rax"));
        assert!(!super::writes_var("rax2 = 0;", "rax"));
        let names: std::collections::BTreeMap<u64, String> =
            [(0x110, "itemTemplate".to_owned())].into();
        assert_eq!(
            super::rename_fields("  rbx = rax + 0x110;", "rax", &names),
            "  rbx = &rax->itemTemplate;"
        );
        assert_eq!(
            super::rename_fields("  rbx = rax + 0x118;", "rax", &names),
            "  rbx = rax + 0x118;"
        );
    }

    /// Junk that computes nothing produces no statements.
    ///
    /// An obfuscator pads code with instructions whose effect cancels: a
    /// register moved to itself, a zero added, a push and its pop, a `not`
    /// twice. A lifter that tracks values rather than instructions drops all
    /// of it without a rule per pattern, and this is the test that says so,
    /// because the property is easy to lose and invisible when lost.
    ///
    /// # Panics
    ///
    /// When any of the junk reaches the output.
    #[test]
    fn junk_that_computes_nothing_is_not_rendered() {
        // ASM: mov eax,3; mov rax,rax; add rax,0; or rax,0; and rax,-1;
        //      xor rax,0; push rcx; pop rcx; not rax; not rax; xchg rax,rax;
        //      lea rax,[rax]; nop; ret
        let code: &[u8] = &[
            0xb8, 0x03, 0x00, 0x00, 0x00, 0x48, 0x89, 0xc0, 0x48, 0x83, 0xc0, 0x00, 0x48, 0x83,
            0xc8, 0x00, 0x48, 0x83, 0xe0, 0xff, 0x48, 0x83, 0xf0, 0x00, 0x51, 0x59, 0x48, 0xf7,
            0xd0, 0x48, 0xf7, 0xd0, 0x48, 0x90, 0x48, 0x8d, 0x00, 0x90, 0xc3,
        ];
        let mut bytes = vec![0u8; 0x2000];
        bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
        let sections = vec![crate::program::Section {
            name: ".text".to_owned(),
            va: crate::program::Va(0x1000),
            vsize: 0x1000,
            file_off: crate::program::FileOff(0x1000),
            file_size: 0x1000,
            readable: true,
            writable: false,
            executable: true,
        }];
        let section_index = crate::program::Program::index_sections(&sections);
        let p = crate::program::Program {
            path: std::path::PathBuf::new(),
            bytes,
            format: crate::program::BinaryFormat::Raw,
            arch: crate::program::Arch::X86_64,
            is_64: true,
            entry: Some(0x1000),
            image_base: 0,
            sections,
            section_index,
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: crate::headers::Headers::default(),
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            debug_typedefs: std::collections::BTreeMap::new(),
            debug_globals: Vec::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
            relocs: crate::reloc::Relocs::default(),
            go: None,
            clr: None,
            parent: None,
            modes: crate::isa::a32::Modes::default(),
        };
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        for junk in ["rax = rax", "+ 0", "| 0", "^ 0", "~~", "push", "pop", "nop"] {
            assert!(
                !text.contains(junk),
                "{junk} survived:
{text}"
            );
        }
        assert!(
            text.contains("return 3"),
            "the one real effect is missing:
{text}"
        );
    }

    /// The accesses through a pointer name what it points at.
    ///
    /// One width at offset zero is a pointer to that; anything else is a
    /// structure, a lone field away from the start included, and `void *`
    /// says so rather than inventing a layout.
    #[test]
    fn accesses_name_the_pointee() {
        use std::collections::BTreeSet;
        let set = |v: &[usize]| v.iter().copied().collect::<BTreeSet<usize>>();
        let at = |v: &[i64]| v.iter().copied().collect::<BTreeSet<i64>>();
        for (widths, offsets, want) in [
            (set(&[1]), at(&[0]), "uint8_t *"),
            (set(&[2]), at(&[0]), "uint16_t *"),
            (set(&[4]), at(&[0]), "uint32_t *"),
            (set(&[8]), at(&[0]), "uint64_t *"),
            (set(&[8]), at(&[0, 0x18]), "void *"),
            (set(&[4]), at(&[0x14]), "void *"),
            (set(&[8]), at(&[-0x18]), "void *"),
            (set(&[1, 8]), at(&[0]), "void *"),
            (set(&[]), at(&[]), "void *"),
        ] {
            assert_eq!(
                super::pointee_type(&widths, &offsets),
                want,
                "{widths:?} at {offsets:?}"
            );
        }
    }

    /// A block whose whole body was elided folds onto one line.
    ///
    /// Three lines saying "there was a body here" become one, and only when
    /// the closing brace belongs to the block that opened.
    #[test]
    fn an_elided_block_folds_onto_one_line() {
        let mut lines: Vec<String> = [
            "if (a) {",
            "  ...",
            "}",
            "while (b) {",
            "  ...",
            "} else {",
            "  keep();",
            "}",
        ]
        .iter()
        .map(|l| (*l).to_owned())
        .collect();
        super::fold_elided_blocks(&mut lines);
        assert_eq!(
            lines,
            vec![
                "if (a) { ... }",
                "while (b) { ... } else {",
                "  keep();",
                "}",
            ]
        );
    }

    /// A block with real content is left alone.
    #[test]
    fn a_block_with_content_is_not_folded() {
        let mut lines: Vec<String> = ["if (a) {", "  work();", "}"]
            .iter()
            .map(|l| (*l).to_owned())
            .collect();
        let before = lines.clone();
        super::fold_elided_blocks(&mut lines);
        assert_eq!(lines, before);
    }

    /// Identical statements in a row fold to one and a count.
    ///
    /// A label between two of them ends the run, so nothing a `goto` names
    /// can be inside what was removed.
    #[test]
    fn repeated_statements_fold() {
        let mut lines: Vec<String> = [
            "  throw_error(\"append\");",
            "  throw_error(\"append\");",
            "  throw_error(\"append\");",
            "  L_1400:",
            "  throw_error(\"append\");",
        ]
        .iter()
        .map(|l| (*l).to_owned())
        .collect();
        super::fold_repeated_statements(&mut lines);
        assert_eq!(
            lines,
            vec![
                "  throw_error(\"append\");   // and 2 more the same",
                "  L_1400:",
                "  throw_error(\"append\");",
            ]
        );
    }

    use super::{
        LIFT_TMP_BASE, SKELETON_LINE_MAX, clip_statement, fold_guarded_runs, impure,
        normalize_temps,
    };

    /// Builds the three lines of one guarded call over `local`.
    ///
    /// # Arguments
    ///
    /// * `local` - The local the guard and the call name.
    /// * `name` - The called function.
    fn guarded(local: &str, name: &str) -> Vec<String> {
        vec![
            format!("  if ({local} != &buf) {{"),
            format!("    {name}({local});"),
            String::from("  }"),
        ]
    }

    /// A run of inlined destructors folds to the call it repeats.
    #[test]
    fn a_run_of_guarded_calls_folds() {
        let mut lines = vec![String::from("x = 1;")];
        for i in 0..40 {
            lines.extend(guarded(&format!("local_{i}"), "release"));
        }
        lines.push(String::from("return;"));
        fold_guarded_runs(&mut lines);
        assert_eq!(lines.len(), 3, "{lines:?}");
        assert_eq!(lines[1], "  // 40 guarded release(...) calls elided");
    }

    /// Two guarded calls are left alone; a run must be worth folding.
    #[test]
    fn a_short_run_of_guarded_calls_is_left_alone() {
        let mut lines = guarded("a", "release");
        lines.extend(guarded("b", "release"));
        let before = lines.clone();
        fold_guarded_runs(&mut lines);
        assert_eq!(lines, before);
    }

    /// A run calling different functions is not one run.
    #[test]
    fn guarded_calls_to_different_functions_do_not_fold() {
        let mut lines = guarded("a", "release");
        lines.extend(guarded("b", "flush"));
        lines.extend(guarded("c", "release"));
        let before = lines.clone();
        fold_guarded_runs(&mut lines);
        assert_eq!(lines, before);
    }

    /// An over-long conditional jump keeps its destination and loses condition.
    ///
    /// Cutting the tail instead leaves `goto L_140...;`, a label that names
    /// nowhere and that the dangling-goto check cannot resolve.
    #[test]
    fn clipping_a_statement_keeps_a_trailing_goto() {
        let mut line = format!("if ({}) goto L_14000a58f;", "a || ".repeat(40));
        assert!(line.len() > SKELETON_LINE_MAX);
        clip_statement(&mut line);
        assert!(line.ends_with(" goto L_14000a58f;"), "{line}");
        assert!(line.contains("..."), "{line}");
    }

    /// A statement with no `goto` still loses its tail to the cap.
    #[test]
    fn clipping_a_statement_without_a_goto_cuts_the_tail() {
        let mut line = format!("x = {};", "a + ".repeat(40));
        clip_statement(&mut line);
        assert!(line.ends_with("...;"), "{line}");
        assert!(line.len() <= SKELETON_LINE_MAX, "{line}");
    }

    /// A statement that already fits is untouched.
    #[test]
    fn clipping_leaves_a_short_statement_alone() {
        let mut line = String::from("goto L_1000;");
        clip_statement(&mut line);
        assert_eq!(line, "goto L_1000;");
    }

    /// A call is impure whether or not its name carries template arguments.
    ///
    /// So `drop_returned_values` keeps it as a statement in a `void` function
    /// instead of discarding the whole tail call. A plain value stays pure.
    #[test]
    fn a_templated_call_counts_as_impure() {
        assert!(impure("f(x)"), "plain call not impure");
        assert!(impure("ns::g(a, b)"), "qualified call not impure");
        assert!(
            impure("FrameSync::Data::OwnerSetup<Shared::ModelEntityShared>(rax)"),
            "templated call not impure"
        );
        assert!(
            impure("(rax + 8)->vtable[4](this, 34)"),
            "vtable call not impure"
        );
        assert!(!impure("rax + 1"), "arithmetic wrongly impure");
        assert!(!impure("*(uint32_t*)(this + 0x30)"), "load wrongly impure");
    }

    /// A leaked lift-pass temporary is renumbered just past the readable ones,
    /// while a real `tmp_1` and unrelated tokens are left untouched.
    #[test]
    fn normalize_temps_renumbers_a_leaked_id() {
        let big = LIFT_TMP_BASE + 1;
        let input = format!("local_4 = tmp_1;\nif (rbx == tmp_{big}) {{\n");
        let out = normalize_temps(&input);
        assert!(
            out.contains("rbx == tmp_2"),
            "leaked id not renumbered: {out}"
        );
        assert!(
            out.contains("local_4 = tmp_1;"),
            "readable temp changed: {out}"
        );
        assert!(
            !out.contains(&format!("tmp_{big}")),
            "raw internal id survived: {out}"
        );
    }

    /// The same leaked id maps to the same name; distinct ids stay distinct.
    #[test]
    fn normalize_temps_is_consistent() {
        let a = LIFT_TMP_BASE + 5;
        let b = LIFT_TMP_BASE + 9;
        let input = format!("a = tmp_{a}; b = tmp_{b}; c = tmp_{a};\n");
        let out = normalize_temps(&input);
        assert_eq!(
            out, "a = tmp_1; b = tmp_2; c = tmp_1;\n",
            "inconsistent remap: {out}"
        );
    }

    /// Text with no leaked temporary is returned unchanged, and a longer
    /// identifier ending in `tmp_<n>` is not mistaken for one.
    #[test]
    fn normalize_temps_leaves_clean_text_alone() {
        let input = "local_4 = tmp_1 + tmp_2; call sub_tmp_3();\n";
        assert_eq!(normalize_temps(input), input);
    }
}
