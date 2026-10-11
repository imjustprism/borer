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
//! [`fields`], [`types`], [`enums`], [`wire`], [`tidy`] and [`finish`]
//! rework the text. [`outline`] and [`scenario`] are other views of the
//! same function; [`opaque`] spots conditions that always go one way;
//! [`traces`] checks the text's control flow against the binary's.

mod asserts;
mod ctext;
mod emit;
mod enums;
mod expr;
mod fields;
mod finish;
pub(crate) mod interp;
mod ladder;
pub(crate) mod lift;
mod line;
mod liveness;
mod opaque;
mod outline;
mod params;
pub mod replay;
mod rewrite;
mod scenario;
pub(crate) mod signature;
mod structure;
mod tidy;
pub mod traces;
mod types;
pub mod verify;
mod wire;

pub use asserts::*;
use emit::*;
pub use enums::*;
use fields::*;
pub use finish::*;
use line::*;
pub(in crate::analysis) use liveness::*;
pub use outline::*;
use params::*;
use rewrite::*;
pub use scenario::*;
use structure::*;
pub use tidy::*;
use types::*;
use wire::*;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::isa::{
    ConditionCode, Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory,
    Mnemonic, OpAccess, OpKind, Register,
};

use expr::{Cc, Expr, Flags, Key, Names, Ty};
use lift::{BlockFacts, BlockOut, Branch, Conv, Env, Rebase, SlotUse, exec_block};

use super::{
    Analysis, BasicBlock, BlockTerm, EnumSource, Funclet, Function, Overlay, classes,
    decompiled_cached, name_of, plain_text_cached,
};
use crate::fxmap::FxHashMap;
use crate::program::Program;
use crate::strings::{cstr_at, cstr_text_at, wide_run_start, wstr_at};

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
    /// Parameters detected from calling-convention registers read first.
    params: Vec<Register>,
    /// Text variables assigned somewhere in the body, with their type.
    declared: BTreeMap<Key, Ty>,
    /// The stack slots among `declared`, shared with the renderer
    /// ([`Names::slot_types`]).
    slot_types: std::sync::Arc<BTreeMap<i64, Ty>>,
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
    /// Parameter index to the class it points at, from the declared
    /// signature (`this`, `Foo *`, `const Foo &`), for virtual calls.
    param_class: BTreeMap<u8, String>,
    /// Bare name of the function, so its own `__FUNCSIG__` literal renders
    /// as the macro.
    own_name: std::sync::Arc<str>,
    /// The return type the debug information recorded, `None` for `void` or
    /// when the program carries none.
    debug_ret: Option<String>,
    /// Parameters the debug information recorded, in order.
    ///
    /// The compiler wrote these down, so they beat `a1`, `a2`, `a3` and
    /// `uint64_t` in both the signature and the body: a condition on
    /// `dwReason` says what it tests, where one on `a2` says only where the
    /// value came from.
    debug_params: std::sync::Arc<[crate::dwarf::Parameter]>,
    /// The source file and line the debug information states the function
    /// was written in, for the header's `// source:` line; `None` when
    /// nothing was recorded, which leaves the line to what the body's own
    /// assertions cite. The PDB's rows are read lazily ([`pdb_sources`]),
    /// so the first header that states one pays their walk once.
    debug_source: Option<(String, u32)>,
    /// The frame-relative locals the debug information states, as slot
    /// offset to name; the names render where the synthesized `local_N`
    /// would. The offsets are facts the file states, so they name slots
    /// without touching their widths, which the lifting's own declarations
    /// keep stating.
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
        if i.code() == crate::isa::Code::INVALID {
            return None;
        }
        Some(i)
    }

    /// Returns the name resolver for rendering.
    fn names(&self) -> Names<'a> {
        Names {
            program: self.program,
            analysis: self.analysis,
            overlay: self.overlay,
            this_param: self.this_param,
            result_param: self.result_param,
            own_name: self.own_name.clone(),
            debug_params: self.debug_params.clone(),
            debug_locals: self.debug_locals.clone(),
            first_stack: self.conv.word + self.conv.shadow,
            stack_params: self.stack_params,
            reg_params: u32::try_from(self.conv.args.len()).unwrap_or(0),
            word: self.conv.word,
            slot_types: self.slot_types.clone(),
        }
    }
}

/// Renders the literal at `addr` compactly.
///
/// A signature or source-path string is read in full (up to 512 bytes) and
/// shortened by [`expr::compact_literal`]; anything else is the capped
/// [`string_at`] text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - The literal's address.
/// * `own_name` - Bare name of the function being rendered.
pub(super) fn literal_at(program: &Program, addr: u64, own_name: &str) -> Option<String> {
    /// Longest signature or path read in full.
    const FULL: usize = 512;
    if program.section_at(addr).is_none_or(|s| s.executable) {
        return None;
    }
    if let Some(literal) = super::qt::literal(program, addr) {
        return Some(literal);
    }
    if let Some((_, raw)) = cstr_at(program, addr, 4, FULL) {
        let quoted = format!("\"{}\"", raw.replace('\\', "\\\\").replace('"', "\\\""));
        let compact = expr::compact_literal(&quoted, own_name);
        if compact != quoted {
            return Some(compact);
        }
    }
    string_at(program, addr)
}

/// Reads the quoted string literal at a mapped, non-executable address.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - Address of the candidate string.
///
/// # Returns
///
/// `"text"` or `L"text"` with backslashes and quotes escaped as C does,
/// capped at 120 characters and at least four long, or shorter in read-only
/// data when a terminator follows (`"%d"`, `";"`); `None` when no string
/// lives there or the address is code.
///
/// A wide literal in read-only data reads as a one-character narrow string
/// followed by its own high byte, so `L"SHA256"` renders as `"S"` unless the
/// two candidates are weighed against each other. The wide reading wins when
/// the narrow one is shorter than a literal's minimum and the wide one is
/// longer still, which is the only shape where a narrow reading carries less
/// than the bytes hold.
fn string_at(program: &Program, addr: u64) -> Option<String> {
    /// Shortest run accepted as a literal in writable data, where a small
    /// object's first bytes may happen to read as text.
    const MIN: usize = 4;
    /// Shortest run accepted in read-only data, where the empty string is a
    /// lone terminator and reads as `""`.
    const MIN_RODATA: usize = 1;
    /// Longest text rendered.
    const CAP: usize = 120;
    let section = program.section_at(addr)?;
    if section.executable {
        return None;
    }
    if !section.writable
        && let Some(head) = program.read_va_upto(addr, 2)
        && head.first() == Some(&0)
    {
        // INVARIANT: the empty string lives in a string pool, so either the
        // byte after its terminator is the next literal's first character
        // or the bytes before it end the previous literal, text then its
        // terminator; a zero byte on both sides is a table, a GUID or a
        // zeroed object, and naming that `""` loses the address for nothing.
        let after_a_literal = addr
            .checked_sub(2)
            .and_then(|at| program.read_va(at, 2))
            .is_some_and(|b| {
                b.first().is_some_and(|c| (0x20..0x7f).contains(c)) && b.get(1) == Some(&0)
            });
        let before_a_literal = head
            .get(1)
            .is_some_and(|b| crate::strings::literal_byte(*b));
        return (before_a_literal || after_a_literal).then(|| String::from("\"\""));
    }
    let min = if section.writable { MIN } else { MIN_RODATA };
    // A C string is null-terminated; a printable run that ends on a non-zero
    // byte is not one. The only run without a terminator in the window is a
    // string longer than the cap, truncated at it, so accept the no-terminator
    // case only at the cap. This rejects the low bytes of a pointer or vtable
    // (a store of `&vtable` whose first function pointer reads as `"$d-@"`),
    // while every genuine literal, short or long, still renders.
    let terminated = |len: usize| {
        len >= CAP
            || u64::try_from(len)
                .ok()
                .and_then(|n| program.read_va_upto(addr.wrapping_add(n), 1))
                .is_some_and(|b| b.first() == Some(&0))
    };
    let sanitize = |t: String| crate::strings::escape_text(&t);
    let narrow = cstr_text_at(program, addr, min, CAP).filter(|&(len, _)| terminated(len));
    let wide = wide_run_start(program, addr)
        .then(|| wstr_at(program, addr, min.max(2), CAP))
        .flatten()
        .filter(|&(len, _)| terminated(len.saturating_mul(2)));
    match (narrow, wide) {
        (Some((n, _)), Some((w, t))) if n < MIN && w > n => Some(format!("L\"{}\"", sanitize(t))),
        (Some((_, t)), _) => Some(format!("\"{}\"", sanitize(t))),
        (None, Some((_, t))) => Some(format!("L\"{}\"", sanitize(t))),
        (None, None) => None,
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

/// A function's pseudo-C as one of the decompile entry points renders it.
type Render = fn(&Program, &Analysis, &Overlay, u64) -> Option<String>;

/// Renders many functions with `render`, one stripe of them per core, the
/// results in the order of `entries`.
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
fn render_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
    render: Render,
) -> Vec<Option<String>> {
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(entries.len().max(1));
    let mut out: Vec<Option<String>> = vec![None; entries.len()];
    if threads <= 1 {
        for (slot, &entry) in out.iter_mut().zip(entries) {
            *slot = render(program, analysis, overlay, entry);
        }
        return out;
    }
    let stripes: Vec<Vec<(usize, Option<String>)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                scope.spawn(move || {
                    entries
                        .iter()
                        .enumerate()
                        .skip(t)
                        .step_by(threads)
                        .map(|(i, &entry)| (i, render(program, analysis, overlay, entry)))
                        .collect::<Vec<_>>()
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
    let bitness = program.arch.bitness().unwrap_or(64);
    decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry)
        .as_ref()
        .as_ref()
        .map(|d| polish(&d.text, bitness, &analysis.packs))
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
    let bitness = program.arch.bitness().unwrap_or(64);
    decompile_plain_full(program, analysis, overlay, entry)
        .map(|d| polish(&d.text, bitness, &analysis.packs))
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
    Ctx {
        program,
        analysis,
        overlay,
        overlay_key: overlay.fingerprint(),
        bitness,
        conv: lift::conv(program, bitness),
        assume: {
            let conv = lift::conv(program, bitness);
            assume
                .iter()
                .filter_map(|&(slot, v)| Some((*conv.args.get(usize::from(slot))?, v)))
                .collect()
        },
        block_starts,
        symbolic_only: false,
        probe: None,
        seh_frame: false,
        params: Vec::new(),
        declared: BTreeMap::new(),
        slot_types: std::sync::Arc::default(),
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
        param_class: BTreeMap::new(),
        own_name: std::sync::Arc::from(expr::bare(&name_of(analysis, overlay, f.entry))),
        debug_ret: program
            .debug_functions
            .iter()
            .find(|d| d.low_pc == f.entry)
            .and_then(|d| d.return_type.clone()),
        debug_params: program
            .debug_functions
            .iter()
            .find(|d| d.low_pc == f.entry)
            .map_or_else(
                || std::sync::Arc::from([]),
                |d| std::sync::Arc::from(d.parameters.clone()),
            ),
        debug_source: pdb_sources(program, analysis).get(&f.entry).cloned(),
        debug_locals: program
            .debug_functions
            .iter()
            .find(|d| d.low_pc == f.entry)
            .map_or_else(std::sync::Arc::default, |d| {
                std::sync::Arc::new(d.locals.clone())
            }),
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
        callee_arity: BTreeMap::new(),
        stack_params: f.stack_args,
        funclet: f.funclet,
        entry_block: f
            .blocks
            .iter()
            .position(|b| b.start == f.entry)
            .unwrap_or(0),
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
/// treatment of [`decompile`].
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
    let text = plain_text_cached(program, analysis, overlay, overlay.fingerprint(), entry)?;
    name_fields(program, analysis, overlay, entry, &text)
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
        || replay::check_answer(program, analysis, overlay, entry),
        |c| c.as_ref().map_or(0, replay::TextCheck::bytes),
    )
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
}

/// Renders the fields of class-typed objects in a plain decompilation by
/// name and polishes it: the work of [`decompile_named`] after the plain
/// text.
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
/// The pseudo-C, or `None` when no function starts at `entry`.
fn name_fields(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
) -> Option<String> {
    let f = analysis.function(entry)?;
    let name = name_of(analysis, overlay, entry);
    let own =
        classes::class_of(expr::bare(&name)).or_else(|| f.param_hints.get(&0).map(String::as_str));
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
    // The names the asserts give parameters, locals and registers, last:
    // the field and result names above read the variables by the names
    // the lifter gave them.
    for Rename { var, name } in assert_names(&lines) {
        for line in &mut lines {
            *line = rename_word(line, &var, &name);
        }
    }
    let mut out = lines.join("\n");
    out.push('\n');
    Some(polish(
        &out,
        program.arch.bitness().unwrap_or(64),
        &analysis.packs,
    ))
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
/// The pseudo-C, or `None` when there is no such function or no lifter.
fn decompile_with(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    cleanup: bool,
    assume: &[(u8, u64)],
    witness: bool,
) -> Option<Decompiled> {
    let f = analysis.function(entry)?;
    let bitness = program.arch.bitness()?;
    let blocks = &f.blocks;
    let n = blocks.len();

    let idx: BTreeMap<u64, usize> = blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let succs: Vec<Vec<usize>> = blocks
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
    let code = decode_blocks(&ctx, f);
    ctx.seh_frame = seh_frame(&ctx, &code);
    // INVARIANT: the parameters are read once per function and overlay
    // ([`callee_shape`]), so the signature below lists exactly what every
    // call to the function passes.
    let entry_block = ctx.entry_block;
    let shape = callee_shape(&ctx, f.entry)
        .unwrap_or_else(|| std::sync::Arc::new(shape_of(&mut ctx, f, &code, &succs, entry_block)));
    ctx.conv = shape.conv;
    ctx.params.clone_from(&shape.params);
    ctx.variadic = shape.variadic;
    ctx.this_param = shape.this_param;
    ctx.result_param = shape.result_param;
    ctx.stack_params = shape.stack;
    ctx.rax_written = writes_rax(&ctx, &code);
    ctx.unused_result = match &f.signature {
        Some(s) => s.ret == "void",
        None => f.returns_value == Some(false),
    };
    let hidden = usize::from(f.signature.as_ref().is_some_and(|s| s.by_pointer));
    ctx.ret_lane = lift::ret_lane(
        &code,
        &succs,
        f.signature.as_ref().map(|s| s.ret.as_str()),
        analysis,
    );
    ctx.ret_float = f
        .signature
        .as_ref()
        .map_or(f.ret_float.is_some(), |s| float_return(&s.ret));
    // INVARIANT: a 32-bit function a whole-program compiler gave a
    // convention of its own hands its double back in `xmm0` (`movsd xmm0,
    // [ebp-0x10]` on one exit, `xorps xmm0, xmm0` on the other), where its
    // callers read it; read as returning nothing, its every `return` lost
    // the value.
    ctx.ret_sse = bitness == 32
        && f.signature.is_none()
        && f.ret_float.is_none()
        && lift::sse_callee(&ctx, Some(f.entry)).returns;
    if ctx.ret_sse {
        ctx.ret_float = true;
        ctx.unused_result = false;
    }
    // INVARIANT: a float result in `xmm0` is the register `ret` hands
    // back, written on the way to every exit.
    ctx.rax_written |= ctx.ret_float && (bitness == 64 || ctx.ret_sse);
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
    ctx.flag_readers = code.iter().map(|b| reads_inherited_flags(b)).collect();
    ctx.rebase_flags = vec![None; code.len()];
    let regs = lift::live_in(&ctx, &code, &succs);
    let need = code
        .iter()
        .enumerate()
        .map(|(b, instrs)| {
            let mut out = FxHashMap::default();
            for &s in &succs[b] {
                lift::join_need(&mut out, &regs[s]);
            }
            lift::need_after(&ctx, instrs, &out)
        })
        .collect();
    let mut live = Live {
        regs,
        need,
        slots: None,
    };
    let (_, _, mut recorded) = dataflow(&mut ctx, &code, &succs, &preds, &live, &[]);
    widen_slots(&mut recorded);
    live.slots = Some(slot_liveness(&recorded, &succs));
    let assumes = block_assumptions(&code, &preds, &recorded);
    let (in_envs, processed, recorded) = dataflow(&mut ctx, &code, &succs, &preds, &live, &assumes);

    let mut succs_live = succs.clone();
    let mut preds_live = preds.clone();
    for (b, rec) in recorded.iter().enumerate() {
        let Some((taken, target, fall)) = rec.branch_const else {
            continue;
        };
        let dead = if taken { fall } else { target };
        let Some(&d) = idx.get(&dead) else { continue };
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
            .and_then(|t| idx.get(&t).copied())
        else {
            continue;
        };
        for d in std::mem::replace(&mut succs_live[b], vec![live]) {
            if d != live {
                preds_live[d].retain(|p| *p != b);
            }
        }
    }

    let mut st = Emit {
        blocks,
        code: &code,
        succs: succs_live,
        preds: preds_live,
        in_envs: &in_envs,
        live: &live,
        processed: &processed,
        assumes: &assumes,
        emitted: vec![false; n],
        bound: n,
        skipped: BTreeSet::new(),
        loops: Vec::new(),
        orders: Vec::new(),
        no_dup: BTreeSet::new(),
        copy_calls: false,
        copy_stop: false,
        dup_stack: Vec::new(),
        entry: entry_block,
    };
    let mut reached = vec![false; n];
    let mut work = vec![entry_block];
    while let Some(b) = work.pop() {
        if b >= n || std::mem::replace(&mut reached[b], true) {
            continue;
        }
        work.extend(st.succs[b].iter().copied());
    }
    let unreachable = reached.iter().filter(|r| !**r).count();
    for (b, r) in reached.iter().enumerate() {
        if !r {
            st.emitted[b] = true;
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
    let entry_env = entry_env(&ctx);
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
    // INVARIANT: a float handed back in `xmm0` is read by callers that
    // read no `eax` ([`Ctx::ret_sse`]), whatever the verdict on `eax` says.
    let body = if f.returns_value == Some(false) && f.signature.is_none() && !ctx.ret_sse {
        drop_returned_values(&body)
    } else {
        body
    };
    // INVARIANT: a function whose every `return` is bare returns nothing,
    // and so a call's result assigned to the return register right before
    // one is dead: kept on one path for a join that hands back nothing.
    let returns_nothing = f.signature.as_ref().map_or_else(
        || {
            !body
                .lines()
                .any(|l| matches!(l.trim().strip_prefix("return "), Some(v) if v != ";"))
        },
        |s| s.ret == "void",
    );
    let body = if cleanup { cleanup_text(&body) } else { body };
    let body = if returns_nothing {
        drop_dead_results(&body, if bitness == 64 { "rax" } else { "eax" })
    } else {
        body
    };
    let body = match overlay.enum_source {
        EnumSource::Given => apply_enums(&body, &overlay.enums),
        EnumSource::Binary => apply_enums(&body, &called_tables(program, analysis, overlay, &body)),
    };
    let names = ctx.names();
    // The fields of globals a user type points at: named here, in the text
    // every reader of the memo gets, so the layout pass below counts them
    // the way it counts a class-named field, and before the user enums
    // below, whose entries key the access a renamed field renders.
    let user_typed = typed_globals(
        overlay,
        &ctx.globals,
        &names,
        u64::try_from(ctx.conv.word).unwrap_or(8),
    );
    let body = if user_typed.is_empty() {
        body
    } else {
        rename_typed(&body, &user_typed)
    };
    // The constants a user-enum-typed global is compared against: named
    // here, beside the binary's own tables, so a decompilation memoized
    // under the overlay's fingerprint carries them like any other name.
    let user_enums = user_enum_globals(overlay, &ctx.globals, &names);
    let body = if user_enums.is_empty() {
        body
    } else {
        apply_user_enums(&body, &user_enums)
    };

    let value_return = body
        .lines()
        .any(|l| matches!(l.trim().strip_prefix("return "), Some(v) if v != ";"));
    // The compiler's own return type, where it recorded one. Inference reads
    // the width of what the body leaves in `rax`, which cannot see a `double`
    // coming back in `xmm0` at all: `ldexp` inferred as `void`.
    // INVARIANT: a result every exit writes as `eax` is 32 bits wide, the
    // upper half zeroed; any other result wider than a byte or a word is the
    // register, and the register is the machine's word.
    let inferred = match (value_return, ctx.ret_bits) {
        (false, _) => "void",
        (true, _) if f.ret_float == Some(32) => "float",
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
    let typed = param_types(&ctx, &code, &succs, entry_block);
    let name = name_of(analysis, overlay, f.entry);
    let declared: Vec<String> = f
        .signature
        .as_ref()
        .map(|s| s.params.clone())
        .unwrap_or_default();
    let class = classes::class_of(expr::bare(&name)).unwrap_or("");
    let ret_ty = f.signature.as_ref().map_or_else(
        || {
            f.ret_hint
                .as_ref()
                .filter(|_| f.ret_float.is_none())
                .map_or(ret_ty.to_owned(), |c| format!("{c} *"))
        },
        |s| s.ret.clone(),
    );
    let lead = usize::from(ctx.this_param) + usize::from(ctx.result_param.is_some());
    // INVARIANT: the shape's count is what every call passes, so it is
    // what the signature lists; a stack slot the body reads past it reads
    // as the `arg_` slot it is.
    let count = shape.count;
    let floats = shape.floats();
    let mut params: Vec<String> = (0..count)
        .map(|i| {
            // A parameter the body never reads still has a name when the
            // compiler recorded one, and it belongs in the signature.
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
            // INVARIANT: `this` is the class the name gives, else the one
            // its callers and tables typed it as (a 32-bit `thiscall` its
            // name gives no class).
            if ctx.this_param && i == 0 {
                let this_class = if class.is_empty() {
                    f.param_hints.get(&0).map_or("void", String::as_str)
                } else {
                    class
                };
                return format!("{this_class} *this");
            }
            if ctx.result_param.is_some() && i + 1 == lead {
                return format!("{ret_ty} *result");
            }
            let hint = u8::try_from(i).ok().and_then(|p| f.param_hints.get(&p));
            let float_only = floats & (1u8 << i.min(7)) != 0;
            let plain = if float_only {
                "float"
            } else {
                word_type(ctx.bitness)
            };
            // INVARIANT: a slot the body reads as floating point holds no
            // object, whatever a caller happened to leave in the integer
            // register.
            let hint = hint.filter(|_| !float_only);
            // The type the compiler recorded, where no signature declared one,
            // and failing that what the code shows the parameter to be.
            let recorded = ctx
                .debug_params
                .get(i)
                .and_then(|p| p.type_name.clone())
                .or_else(|| typed.get(&i).cloned());
            match (declared.get(i - lead), hint, recorded) {
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
    if f.hands_back_rdx {
        let rdx = if ctx.bitness == 64 { "rdx" } else { "edx" };
        let _ = writeln!(out, "// hands back {rdx}: a caller reads it after the call");
    }
    if let Some(asserts) = asserts_of(&body) {
        let _ = writeln!(out, "// asserts: {asserts}");
    }
    if let Some(code) =
        classes::class_of(expr::bare(&name)).and_then(|c| analysis.classes.ids.get(c))
    {
        let _ = writeln!(out, "// wire id: {}", classes::fourcc(*code));
    }
    if f.callers.len() >= PARAM_VALUE_SITES
        && let Some(values) = passed_values(analysis, entry, count)
    {
        let _ = writeln!(out, "// callers pass: {values}");
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
    let slots: Vec<(i64, Ty)> = ctx
        .declared
        .iter()
        .filter_map(|(k, t)| match k {
            Key::Slot(o) => Some((*o, *t)),
            Key::Reg(_) | Key::Global(..) | Key::Tmp(_) | Key::Param(_) => None,
        })
        .collect();
    let mut by_type: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    let mut notes: Vec<String> = Vec::new();
    for (k, ty) in &ctx.declared {
        if matches!(k, Key::Slot(o) if names.stack_param(*o).is_some()) {
            continue;
        }
        let name = names.key(*k);
        if !used.contains(name.as_str()) {
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
        by_type.entry(ty.name()).or_default().push(name);
    }
    // A stack slot whose address escapes to a call but that the function
    // never reads or writes directly has no entry in `declared`, yet
    // `&local_N`, `&home_N` or `&arg_N` appears in the body. Stack parameters
    // render as `aN`, so any `local_`/`home_`/`arg_` name here is a scratch
    // slot; declare each so the text is valid C. (`home_N` is the register
    // home area the caller reserved, and `arg_N` a slot above the return
    // address the caller left for arguments; the function reuses both, and
    // neither is a parameter.) A local the debug information named is in the
    // same state when it only escapes, so it is declared the same way.
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
        by_type.entry("uint64_t").or_default().extend(escaped);
    }
    for (ty, names_of_ty) in &by_type {
        let _ = writeln!(out, "{ty} {};", names_of_ty.join(", "));
    }
    for n in &notes {
        out.push_str(n);
        out.push('\n');
    }
    for (addr, ty) in &ctx.globals {
        let g = names.key(Key::Global(*addr, ty.bits()));
        if used.contains(g.as_str()) {
            match expr::tls_slot(*addr) {
                Some(off) => {
                    let _ = writeln!(out, "{} {g}; // TLS slot {off:#x}", ty.name());
                }
                None => {
                    let _ = writeln!(out, "{} {g}; // @ {addr:#x}", ty.name());
                }
            }
        }
    }
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
            code,
            ins: in_envs,
            processed,
            assumes,
            live,
            emitted,
            flag_readers: std::mem::take(&mut ctx.flag_readers),
            conv: ctx.conv,
            ret_bits: ctx.ret_bits,
            ret_float: ctx.ret_float,
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
                    Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::Global(..) => None,
                })
                .collect(),
            reg_ty: ctx
                .reg_ty
                .iter()
                .filter_map(|(k, ty)| match ty {
                    Ty::F32 | Ty::F64 => Some((*k, *ty)),
                    _ => None,
                })
                .collect(),
        })
    });
    Some(Decompiled {
        text: out,
        virtual_callees: ctx.vcalls.iter().copied().collect(),
        blocks: n,
        cut: unreachable,
        live: handed,
        effects,
        witness: std::sync::Mutex::new(witness),
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
        assert!(text.contains("Sum::Add(rax, 7);"), "{text}");
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
        // 0x3f000000 read by movss from where an integer move put it is 0.5f.
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
            lines.join(
                "
",
            )
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
            0xb8, 0x03, 0x00, 0x00, 0x00, // mov eax,3
            0x48, 0x89, 0xc0, // mov rax,rax
            0x48, 0x83, 0xc0, 0x00, // add rax,0
            0x48, 0x83, 0xc8, 0x00, // or rax,0
            0x48, 0x83, 0xe0, 0xff, // and rax,-1
            0x48, 0x83, 0xf0, 0x00, // xor rax,0
            0x51, // push rcx
            0x59, // pop rcx
            0x48, 0xf7, 0xd0, // not rax
            0x48, 0xf7, 0xd0, // not rax
            0x48, 0x90, // xchg rax,rax
            0x48, 0x8d, 0x00, // lea rax,[rax]
            0x90, // nop
            0xc3, // ret
        ];
        let mut bytes = vec![0u8; 0x2000];
        bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
        let p = crate::program::Program {
            path: std::path::PathBuf::new(),
            bytes,
            format: crate::program::BinaryFormat::Raw,
            arch: crate::program::Arch::X86_64,
            is_64: true,
            entry: Some(0x1000),
            image_base: 0,
            sections: vec![crate::program::Section {
                name: ".text".to_owned(),
                va: 0x1000,
                vsize: 0x1000,
                file_off: 0x1000,
                file_size: 0x1000,
                readable: true,
                writable: false,
                executable: true,
            }],
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: crate::headers::Headers::default(),
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
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

    /// A pointer whose low bytes read as text is not a string.
    ///
    /// A vtable install stores `&vtable`, and a vtable's first function pointer
    /// (here `0x1402d6424`) begins with the printable bytes `$d-@` then a
    /// non-zero byte. A four-character run that is not null-terminated is no C
    /// string, so it does not render as `"$d-@"`; a genuine terminated literal
    /// still does.
    #[test]
    fn a_pointer_reading_as_text_is_not_a_string() {
        let mut bytes = vec![0u8; 0x2000];
        // At 0x2000: the pointer 0x1402d6424, low bytes "$d-@" then 0x01.
        bytes[0x1000..0x1008].copy_from_slice(&0x0000_0001_402d_6424u64.to_le_bytes());
        // At 0x2010: a genuine null-terminated string.
        bytes[0x1010..0x1016].copy_from_slice(b"hello\0");
        let p = crate::program::Program {
            path: std::path::PathBuf::new(),
            bytes,
            format: crate::program::BinaryFormat::Raw,
            arch: crate::program::Arch::X86_64,
            is_64: true,
            entry: None,
            image_base: 0,
            sections: vec![crate::program::Section {
                name: ".rdata".to_owned(),
                va: 0x2000,
                vsize: 0x1000,
                file_off: 0x1000,
                file_size: 0x1000,
                readable: true,
                writable: false,
                executable: false,
            }],
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: crate::headers::Headers::default(),
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
        };
        assert_eq!(
            super::string_at(&p, 0x2000),
            None,
            "a pointer's printable low bytes rendered as a string"
        );
        assert_eq!(super::string_at(&p, 0x2010).as_deref(), Some("\"hello\""));
    }

    /// A zero byte is the empty string only beside another literal.
    ///
    /// The last byte of a pointer followed by a bytecode table (`00 03 00
    /// 5a`) is no string pool, so it keeps its address; a terminator the
    /// next literal follows (`00 "AB" 00`) or the previous one ends is `""`.
    #[test]
    fn a_zero_before_a_table_is_no_empty_string() {
        use crate::program::{Arch, Program, Section};
        let mut bytes = vec![0u8; 0x1000];
        bytes[0x10..0x14].copy_from_slice(&[0x00, 0x03, 0x00, 0x5a]);
        bytes[0x20..0x24].copy_from_slice(b"\0AB\0");
        bytes[0x30..0x34].copy_from_slice(b"AB\0\0");
        let rdata = Section::mapped(".rdata", 0x2000, 0, 0x1000, false, false);
        let p = Program::raw(bytes, Arch::X86_64, 0, None, vec![rdata]);
        assert_eq!(super::string_at(&p, 0x2010), None);
        assert_eq!(super::string_at(&p, 0x2020).as_deref(), Some("\"\""));
        assert_eq!(super::string_at(&p, 0x2033).as_deref(), Some("\"\""));
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
        // No readable temps present, so leaked ids start at tmp_1.
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
