//! borer MCP server: exposes the analysis engine over stdio JSON-RPC.
//!
//! The server layer stays thin on purpose: everything interesting lives in
//! `borer-engine` (sync, pure, testable). Tool outputs are plain text with
//! server-side filtering, hard caps, and a showing-N-of-M header on any
//! list-shaped result. With command-line arguments the same binary runs
//! one-shot CLI commands ([`cli`]); without them it is the relay that keeps
//! the client's pipes and runs the server as a worker process ([`relay`]).
//!
//! This file holds the server state, the tool router, the prompts and the
//! resource dispatch. The parameter types are in [`params`], the
//! `borer://` handlers in [`resources`], and the answer memory and byte
//! budget every reply passes through in [`recall`].

use std::collections::HashSet;
use std::fmt::Write as _;
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// The allocator the shipped binary uses.
///
/// Analysis and decompilation are allocation-bound: an expression tree is
/// boxed per node and a function's dataflow builds a map per instruction.
/// The Windows system allocator serializes more of that than mimalloc does,
/// and the choice is global to a binary, so it belongs here rather than in
/// the engine, which stays free of it and wasm-buildable.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod cli;
mod doctor;
mod paging;
mod params;
mod playbooks;
mod recall;
mod relay;
mod resources;
mod session;
mod setup;
mod strwalk;
mod symsrv;

use borer_engine::analysis::{
    Analysis, EnumSource, Overlay, parse_addr, parse_off, render, resolve,
};
use borer_engine::layout::Layout;
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Feature, Program};
use borer_engine::{disasm, entropy, hexdump as hexfmt, memory, num};
use rayon::prelude::*;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{
    CacheScope, CallToolRequestParams, CallToolResponse, ClientNotification, CompleteRequestParams,
    CompleteResult, CompletionInfo, ContentBlock, CustomRequest, CustomResult, ErrorCode,
    InitializeRequestParams, JsonRpcMessage, ListResourceTemplatesResult, ListResourcesResult,
    ListToolsResult, PaginatedRequestParams, PromptMessage, ProtocolVersion,
    ReadResourceRequestParams, ReadResourceResponse, ReadResourceResult, Reference, RequestId,
    Resource, ResourceContents, ResourceTemplate, ResultType, Role, Tool,
};
use rmcp::service::{RequestContext, RxJsonRpcMessage, TxJsonRpcMessage};
use rmcp::transport::Transport;
use rmcp::transport::async_rw::AsyncRwTransport;
use rmcp::{
    ErrorData, RoleServer, ServerHandler, ServiceExt, prompt, prompt_handler, prompt_router, tool,
    tool_handler, tool_router,
};

use borer::project::Identity;
use borer_engine::live::{self as live, Memory as _, Rebase, Snapshot};
use borer_engine::strings::{find_ascii_spans, find_wide_spans};
use params::{
    Annotation, AnnotationsParams, CallgraphParams, CfgParams, ClassLayoutParams, CryptoParams,
    DecompileBatchParams, DecompileParams, Detail, DisassembleFunctionParams, DisassembleParams,
    EntropyParams, ExplainFunctionArgs, FetchPdbParams, Filter, FindCheckArgs,
    FindFunctionByStringParams, FunctionDetailParams, FunctionParams, FunctionsParams,
    HexdumpParams, LiveAttachParams, LiveInstancesParams, LiveModulesParams, LiveObjectParams,
    LiveReadParams, LiveWatchParams, LoadBinaryParams, LoadProjectParams, Page, QueryParams,
    RawArch, ReachesParams, ReadParams, SaveProjectParams, ScriptParams, SearchKind, SearchParams,
    SetCommentParams, SetNameParams, SetTypeParams, StringEncoding, StringsParams, SymbolsParams,
    TypesParams, XrefsParams, count_param, frame_words, must_be_in_a_section, must_fit_a_row,
    plan_var, to_usize,
};
use recall::{Narrow, Recall, SINCE_ARG, Tag, budgeted};
use strwalk::StringRow;

// ---------------------------------------------------------------- server ----

/// The MCP server state: one loaded program, its lazily computed analysis,
/// and the annotation overlay.
///
/// Every field is shared behind a lock because rmcp clones the handler per
/// request; a poisoned lock is recovered rather than propagated
/// ([`read_lock`]). The default is a server with nothing loaded and no
/// packs.
#[derive(Debug, Clone, Default)]
struct BorerServer {
    /// What this session was last answered for each request, so an
    /// identical answer repeated is a one-line note, not the text again.
    recall: Arc<Mutex<Recall>>,
    /// What this session changed and asked, for `borer://session`.
    ledger: Arc<Mutex<session::Ledger>>,
    /// The loaded program, `None` before `load_binary`.
    program: Arc<RwLock<Option<Arc<Program>>>>,
    /// Whether the loaded program's companion PDB was applied: a
    /// comparison build loads the same way, or a diff of a binary against
    /// itself pairs functions a PDB names with ones it does not.
    pdb_applied: Arc<RwLock<bool>>,
    /// The `entry_file_offset` the loaded program was loaded with, so a
    /// reload loads it the same way.
    entry_file_offset: Arc<RwLock<Option<u64>>>,
    /// The raw layout the loaded program was mapped by, so a reload maps
    /// it the same way.
    raw_load: Arc<RwLock<RawLoad>>,
    /// Derived analysis of `program`, computed on first use and reset by `load_binary`.
    analysis: Arc<RwLock<Option<Arc<Analysis>>>>,
    /// The loaded program's string walks, computed on the first `strings`
    /// call and reset by `load_binary`; see [`strwalk`].
    strings: Arc<RwLock<Option<Arc<strwalk::StringWalks>>>>,
    /// User names and comments.
    overlay: Arc<RwLock<Overlay>>,
    /// The packs the user named in `BORER_PACKS`, read at start; every
    /// analysis runs with them.
    packs: Arc<Packs>,
    /// The packs the loaded program's analysis runs with: the pack
    /// directories' packs that fit it, then `packs`; set by `load_binary`.
    program_packs: Arc<RwLock<Arc<Packs>>>,
    /// The process attached for reading, `None` until `live_attach`.
    live: Arc<Mutex<Option<LiveSession>>>,
    /// The hand-over to the next worker: asked for by `reload`, carried out
    /// by the transport once the reload reply and every earlier one are
    /// written.
    hand_over: Arc<HandOver>,
}

/// The raw layout `load_binary` was asked to map a file by (its `arch`,
/// `base`, `entry` and `regions`, as given); all `None` when the file's
/// own headers were read.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct RawLoad {
    /// The architecture the bytes map as.
    arch: Option<RawArch>,
    /// Where the whole file maps.
    base: Option<String>,
    /// The entry address.
    entry: Option<String>,
    /// The parts of the file mapped instead of the whole.
    regions: Option<String>,
}

/// A process attached for reading, with where the loaded binary sits in it
/// and the snapshots taken of its memory.
#[derive(Debug)]
struct LiveSession {
    /// The process, open with read rights only.
    process: borer_live::Process,
    /// Where the loaded binary's image sits in the process, or why it is
    /// not mapped there; unmapped, addresses are taken as live.
    rebase: Result<Rebase, String>,
    /// Watches by name, so a diff names the fields that changed.
    snapshots: std::collections::BTreeMap<String, Watch>,
    /// The main thread's block of the image's thread-local storage, where
    /// the singletons the analysis placed at TLS offsets live; `None` when
    /// the image has no TLS or the block could not be read.
    tls_block: Option<u64>,
    /// The pointer width live reads use, in bytes: the mapped image's, else
    /// the process's own.
    word: usize,
}

impl LiveSession {
    /// Opens a session on a process with nothing mapped onto it yet.
    ///
    /// # Arguments
    ///
    /// * `process` - The process, open for reading.
    fn new(process: borer_live::Process) -> LiveSession {
        LiveSession {
            word: process.pointer_width(),
            process,
            rebase: Err(NO_BINARY.to_owned()),
            snapshots: std::collections::BTreeMap::new(),
            tls_block: None,
        }
    }

    /// Maps a binary onto the process.
    ///
    /// It finds the image among the modules by its headers
    /// ([`Rebase::of`]), the main thread's block of its thread-local
    /// storage, and the pointer width reads use. Called on attach and again
    /// on every `load_binary`, so the mapping is always the loaded binary's.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded binary, `None` when nothing is loaded.
    ///
    /// # Returns
    ///
    /// The lines saying where the image sits, or why it is not mapped.
    fn map(&mut self, program: Option<&Program>) -> String {
        self.tls_block = None;
        self.word = self.process.pointer_width();
        let Some(p) = program else {
            self.rebase = Err(NO_BINARY.to_owned());
            return "no binary loaded: load_binary the process's executable so live memory is named and typed\n".to_owned();
        };
        let file = p
            .path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        self.rebase = Rebase::of(p, &self.process);
        let r = match &self.rebase {
            Ok(r) => *r,
            Err(why) => {
                return format!(
                    "the loaded binary {file} is not mapped onto this process: {why}; static addresses and names do not apply, numbers are taken as live addresses, and reads use the process's {}-byte pointers\n",
                    self.word
                );
            }
        };
        self.word = word_size(Some(p));
        let mut out = format!(
            "image {file} at live {:#x} = static {:#x} ({:#x} bytes), its headers match the file: static addresses and names rebase automatically\n",
            r.live_base,
            r.static_base,
            r.static_end - r.static_base
        );
        self.tls_block = p.headers.tls_index.and_then(|index| {
            let tid = self.process.threads().ok()?.into_iter().next()?;
            let teb = self.process.teb_of(tid).ok()?;
            live::tls_block(&self.process, &r, index, teb)
        });
        if let Some(b) = self.tls_block {
            let _ = writeln!(
                out,
                "thread-local storage: the main thread's block is at {b:#x}; a class's singleton there reads as Class::instance"
            );
        }
        out
    }

    /// The mapping, for a tool that types memory by the loaded binary.
    ///
    /// # Errors
    ///
    /// When the loaded binary is not mapped onto the process, saying why.
    fn mapped(&self) -> Result<Rebase, String> {
        self.rebase
            .as_ref()
            .copied()
            .map_err(|why| format!("{NOT_A_MODULE}: {why}"))
    }
}

/// Bytes of the process kept under a watch name.
#[derive(Debug, Clone)]
struct Watch {
    /// The bytes as they were when the watch was set or last reported.
    snapshot: Snapshot,
    /// The object's fields by offset, empty when its class is unknown; a
    /// diff names a change by them. Taken when the watch is set.
    fields: std::collections::BTreeMap<u64, live::Field>,
}

/// Bytes a watch covers when neither a length nor a class's fields say.
const WATCH_DEFAULT: usize = 256;

/// The prefix that makes a live tool take a number as a process address
/// as it is, never rebased from the loaded binary's static range.
const LIVE_PREFIX: &str = "live:";

/// Modules `live_attach` lists before pointing at `live_modules`.
const ATTACH_MODULES: usize = 16;

/// Watch names a re-attach lists when it drops them.
const DROPPED_NAMES: usize = 8;

/// The refusal every tool answers before `load_binary`.
const NO_BINARY: &str = "no binary loaded; call load_binary first";

/// The line `load_binary` ends with: the one call that answers what the
/// first ten of a triage would, where `binary_info` would only repeat the
/// summary.
const LOAD_NEXT: &str = "# next: query borer://triage (a whole triage in one call)\n";

/// The refusal of a live tool that types memory by the loaded binary's
/// classes when the binary is not loaded in the process.
const NOT_A_MODULE: &str =
    "the loaded binary is not a module of the process, so its classes do not apply";

/// Splits one `offset:name:type` field statement.
///
/// # Arguments
///
/// * `f` - The statement, colons separating its three parts.
///
/// # Errors
///
/// When the statement is not three parts.
fn field_of(f: &str) -> Result<(&str, &str, &str), String> {
    f.split_once(':')
        .and_then(|(off, rest)| rest.split_once(':').map(|(name, ty)| (off, name, ty)))
        .ok_or_else(|| format!("field {f} is not offset:name:type"))
}

/// Builds an "invalid params" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
fn err_params(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::INVALID_PARAMS, msg.to_string(), None)
}

/// Builds an "internal error" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
fn err_internal(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::INTERNAL_ERROR, msg.to_string(), None)
}

/// Builds a "resource not found" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
fn err_not_found(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::RESOURCE_NOT_FOUND, msg.to_string(), None)
}

/// Reads under a lock, through a poisoning.
///
/// The value under every server lock is whole at any instant (each is
/// replaced, never edited in place), so a fault on another request leaves
/// it readable and the session alive.
///
/// # Arguments
///
/// * `lock` - The lock.
fn read_lock<T>(lock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
    lock.read().unwrap_or_else(PoisonError::into_inner)
}

/// Writes under a lock, through a poisoning (see [`read_lock`]).
///
/// # Arguments
///
/// * `lock` - The lock.
fn write_lock<T>(lock: &RwLock<T>) -> RwLockWriteGuard<'_, T> {
    lock.write().unwrap_or_else(PoisonError::into_inner)
}

/// Takes a mutex, through a poisoning (see [`read_lock`]).
///
/// # Arguments
///
/// * `mutex` - The mutex.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Says that the attached process has exited, for every live tool asked
/// after it did.
///
/// # Arguments
///
/// * `process` - The attached process.
/// * `code` - Its exit code.
fn exited(process: &borer_live::Process, code: u32) -> String {
    format!(
        "{} (pid {}) has exited (exit code {code:#x}), so nothing of it is left to read; live_attach a running process",
        process.name(),
        process.pid()
    )
}

/// The pointer width in bytes of a program, or of the host when none is
/// loaded.
///
/// # Arguments
///
/// * `program` - The loaded program, if any.
fn word_size(program: Option<&Program>) -> usize {
    program.map_or(8, |p| if p.is_64 { 8 } else { 4 })
}

/// Lines of pseudo-C one `decompile` answer holds unless a limit says
/// otherwise.
const DECOMPILE_LINES_DEFAULT: usize = 300;

/// Narrows a decompiled function to the lines a caller asked for.
///
/// A function of a few thousand instructions renders to a few thousand lines, and an agent
/// that wants one call site pays for all of them. The filter is spelled the way the rest of
/// borer spells one - plain text, case-insensitive, no pattern language to get wrong.
///
/// A function that fits the page is returned untouched when nothing was asked for, so the
/// usual answer and its determinism are exactly what they were; one longer than
/// [`DECOMPILE_LINES_DEFAULT`] lines is paged unasked, since a 2,500-line function was 98 KB
/// in one answer. Once anything is asked for, or the page cuts, every line is numbered from
/// one, because a filtered line is worth little without the address of the window to ask
/// for next. A cut page's header names that window, `offset=N continues`, and an unfiltered
/// page that starts inside the declarations says the line they end on
/// ([`borer_engine::analysis::decompile::declarations_end`]): on optimized code the first
/// page can be mostly declarations, and the agent paged blind past them.
///
/// A filtered or paged line is shown under the signature and the `if`/`else`/loop/`switch`/
/// `case` headers enclosing it ([`render::scope_headers`]), each once, numbered `^N` so it
/// reads as context and not as a line the filter kept: most lines of a function run only
/// under a condition the line does not carry, and the bare line states it as unconditional.
///
/// # Arguments
///
/// * `text` - The decompiled function.
/// * `filter` - Keep only lines containing this text, case-insensitively.
/// * `offset` - Lines to skip, counted after filtering.
/// * `limit` - Most lines to return; absent is the default page, zero is every line.
///
/// # Returns
///
/// The chosen lines with their enclosing headers, numbered, under a header saying what was
/// shown of what.
fn window(text: &str, filter: Option<&str>, offset: Option<u32>, limit: Option<u32>) -> String {
    let take = match limit {
        None => DECOMPILE_LINES_DEFAULT,
        Some(0) => usize::MAX,
        Some(n) => to_usize(n),
    };
    let lines: Vec<&str> = text.lines().collect();
    let total = lines.len();
    if filter.is_none() && offset.is_none() && total <= take {
        return text.to_owned();
    }
    let needle = Filter::new(filter);
    let picked: Vec<usize> = (0..total).filter(|&i| needle.accepts(lines[i])).collect();
    let from = to_usize(offset.unwrap_or(0));
    let shown: Vec<usize> = picked.iter().skip(from).take(take).copied().collect();
    let context = render::scope_headers(&lines, &shown);
    let next = from + shown.len();
    let more = if next < picked.len() {
        format!("; offset={next} continues")
    } else {
        String::new()
    };
    let mut out = match needle.needle() {
        Some(n) => format!(
            "// {} of {total} lines carry {n:?}, showing {} from {from}{more}",
            picked.len(),
            shown.len()
        ),
        None => {
            let declared = borer_engine::analysis::decompile::declarations_end(text)
                .filter(|&end| from < end)
                .map_or(String::new(), |end| {
                    format!("; declarations end at line {end}")
                });
            format!(
                "// showing {} of {total} lines from {from}{declared}{more}",
                shown.len()
            )
        }
    };
    if !context.is_empty() {
        out.push_str(render::SCOPE_NOTE);
    }
    out.push('\n');
    let mut rows = shown;
    rows.extend(&context);
    rows.sort_unstable();
    for i in rows {
        let number = if context.contains(&i) {
            format!("^{}", i + 1)
        } else {
            (i + 1).to_string()
        };
        let _ = writeln!(out, "{number:>5}  {}", lines[i]);
    }
    out
}

/// One function of a `decompile_batch` answer cut at its share: whole lines
/// up to `cap` bytes, then a note naming where `decompile` picks it up.
///
/// The note counts lines as `decompile` numbers them, its header lines
/// ([`decompile_header`]) included, so the offset it gives continues from
/// the last line shown; it also names the line the declarations end on,
/// since the share of a function with hundreds of locals can be all
/// declarations.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C, without the header lines.
/// * `cap` - Most bytes kept.
/// * `entry` - The function's entry.
/// * `header` - How many lines `decompile` puts under the text's first line.
///
/// # Returns
///
/// The kept lines and the note, ending in a newline.
fn truncated(text: &str, cap: usize, entry: u64, header: usize) -> String {
    let end = text[..text.floor_char_boundary(cap)]
        .rfind('\n')
        .map_or(0, |i| i + 1);
    let kept = &text[..end];
    let shift = |line: usize| if line > 1 { line + header } else { line };
    let shown = shift(kept.lines().count());
    let total = shift(text.lines().count());
    let declared = borer_engine::analysis::decompile::declarations_end(text)
        .map_or(String::new(), |end| {
            format!("; declarations end at line {}", shift(end))
        });
    format!(
        "{kept}// truncated at line {shown} of {total}{declared}; decompile(address={entry:#x}, offset={shown}) continues\n"
    )
}

/// The lines a `decompile` answer puts under its first line: what of the
/// text was checked against the binary, then a `// next:` line per resource
/// the function's facts point at ([`render::next_steps`]).
///
/// The check is read first, so the decompilation it memoizes keeps the
/// lifter's witness, and the text the answer shows reads the same cell.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis.
/// * `o` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
fn decompile_header(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    let mut lines: Vec<String> = borer_engine::analysis::decompile::checked_header(p, a, o, entry)
        .into_iter()
        .collect();
    lines.extend(
        render::next_steps(p, a, o, entry)
            .iter()
            .map(|step| format!("// next: {step}")),
    );
    (!lines.is_empty()).then(|| lines.join("\n"))
}

/// A function's text with each line that reads a variable no line sets
/// first marked ([`borer_engine::analysis::decompile::mark_unset`]).
///
/// A text the closure check cannot read is left as it is: its lines are no
/// more proven for it, and the check's line says later text passes went
/// unchecked.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis.
/// * `o` - Names in force.
/// * `entry` - The function's entry.
/// * `text` - Its text as `decompile_named` wrote it.
///
/// # Returns
///
/// The text, its flagged lines marked.
fn marked(p: &Program, a: &Analysis, o: &Overlay, entry: u64, text: &str) -> String {
    use borer_engine::analysis::decompile;
    match decompile::unset_reads(p, a, o, entry, text) {
        Ok(reads) => decompile::mark_unset(text, &reads),
        Err(_) => text.to_owned(),
    }
}

impl BorerServer {
    /// The packs an analysis of a program runs with: the pack directories'
    /// packs that fit it, then the named ones.
    ///
    /// # Arguments
    ///
    /// * `program` - The program.
    ///
    /// # Returns
    ///
    /// The packs, and a line for each pack that loaded by itself.
    fn packs_for(&self, program: &Program) -> (Arc<Packs>, Vec<String>) {
        borer::packs::for_program(program, &self.packs, borer::packs::auto_enabled())
    }

    /// Loads another build of the loaded program for the comparison surfaces.
    ///
    /// # Arguments
    ///
    /// * `other` - Path of the other build.
    ///
    /// # Errors
    ///
    /// When the file does not load, has no code analysis, or is not the
    /// architecture of the loaded program: a diff between a 32-bit build and a
    /// 64-bit one pairs functions that share nothing and reports it as a
    /// change.
    fn load_other(&self, other: &str) -> Result<Program, ErrorData> {
        let prog = Program::load_with_symsrv(
            &PathBuf::from(other),
            *read_lock(&self.pdb_applied),
            symsrv::cache_dir().as_deref(),
        )
        .map_err(|e| err_params(format!("load failed: {e:#}")))?;
        if !prog.arch.supports(Feature::Discover) {
            return Err(err_params(format!(
                "arch '{}' has no code analysis",
                prog.arch.name()
            )));
        }
        if let Some(p) = self.loaded()
            && p.arch != prog.arch
        {
            return Err(err_params(format!(
                "{other} is {} and the loaded binary is {}; a comparison across architectures would pair functions that share nothing",
                prog.arch.name(),
                p.arch.name()
            )));
        }
        Ok(prog)
    }

    /// The loaded program, `None` before `load_binary`.
    fn loaded(&self) -> Option<Arc<Program>> {
        read_lock(&self.program).clone()
    }

    /// The loaded program, for a tool that needs it outside a tool body.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded.
    fn require_loaded(&self) -> Result<Arc<Program>, ErrorData> {
        self.loaded().ok_or_else(|| err_params(NO_BINARY))
    }

    /// The analysis, for a resource read outside a tool body that needs
    /// `feature` of the program's code.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the resource reads ([`Program::refuses`]).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the engine does not do
    /// `feature` with its architecture, as [`Self::with_analysis`] refuses
    /// both: the request came too early or asked the wrong file, and the
    /// server did not fail.
    fn analysis(&self, feature: Feature) -> Result<Arc<Analysis>, ErrorData> {
        if let Some(why) = self.require_loaded()?.refuses(feature) {
            return Err(err_params(why));
        }
        self.ensure_analysis().map_err(err_params)
    }

    /// Runs `f` against the loaded program.
    ///
    /// A fault in an analysis pass would unwind out of the handler and take
    /// the session with it: the call gets no reply at all, the agent cannot
    /// tell a crash from a hang, and everything learned so far in the
    /// session is gone with the process. Every tool body reaching a program
    /// comes through here, so one boundary turns a fault into an answer the
    /// caller can read and act on. The panic hook is left alone on purpose:
    /// unlike a damaged file, which is the job and expected, a fault here is
    /// a bug and worth a backtrace in the log.
    ///
    /// # Arguments
    ///
    /// * `f` - The tool body; its `Err` text becomes an invalid-params error,
    ///   since a body refuses only what it was asked (an address that names
    ///   nothing, a function that is not there) and does no I/O that could
    ///   fail on its own.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or `f` refuses the request;
    /// internal error only when `f` faults.
    fn with_program(
        &self,
        f: impl FnOnce(&Program) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let guard = read_lock(&self.program);
        let Some(p) = guard.as_ref() else {
            return Err(err_params(NO_BINARY));
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(p))) {
            Ok(answer) => answer.map_err(err_params),
            Err(e) => Err(err_internal(format!(
                "the analysis faulted on this binary: {}. The session is still up; another tool or another address may still answer.",
                fault_text(e.as_ref())
            ))),
        }
    }

    /// The derived analysis, or an empty one when the architecture has none.
    ///
    /// Some answers are facts of the file rather than of its code: the symbol
    /// table is parsed out of the headers, and a crypto constant is found by
    /// scanning bytes. Both read the analysis only to say more - which
    /// function a constant sits in, which import nothing calls - so refusing
    /// the whole answer on an architecture borer cannot disassemble threw
    /// away what it had already parsed. An arm64 image reported "locals: 2
    /// named functions" in its summary and then refused to list them.
    ///
    /// Tools that need the code itself keep using [`Self::ensure_analysis`],
    /// because an empty answer from those would read as "nothing found"
    /// rather than "not supported here". A tool body runs under
    /// [`Self::with_program`], so a binary is loaded and the architecture is
    /// the one way the analysis can be missing.
    fn analysis_or_empty(&self) -> Arc<Analysis> {
        self.ensure_analysis().unwrap_or_default()
    }

    /// Returns the derived analysis of the current program, computing and
    /// caching it on first use.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or its architecture has no code analysis.
    fn ensure_analysis(&self) -> Result<Arc<Analysis>, String> {
        if let Some(a) = read_lock(&self.analysis).clone() {
            return Ok(a);
        }
        let program = self.loaded().ok_or(NO_BINARY)?;
        if let Some(why) = program.refuses(Feature::Discover) {
            return Err(why);
        }
        let packs = Arc::clone(&read_lock(&self.program_packs));
        let a = Arc::new(Analysis::compute_with(&program, packs));
        *write_lock(&self.analysis) = Some(a.clone());
        Ok(a)
    }

    /// Runs `f` against the loaded program, its analysis and a snapshot of
    /// the overlay: the prologue of every tool that reads code.
    ///
    /// A tool names the stage it reads, so a program whose instruction set
    /// has functions but no lifter yet answers the discovery tools and
    /// refuses the rest with the sentence [`Program::refuses`] gives,
    /// rather than an answer read as "nothing found".
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the tool reads: [`Feature::Discover`] for
    ///   functions, blocks, references and calls, [`Feature::Decompile`]
    ///   for anything read from lifted code, [`Feature::Emulate`] for
    ///   anything that runs it.
    /// * `f` - The tool body; its `Err` text becomes an internal error.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded; internal error when the
    /// engine does not do `feature` with the architecture or `f` fails or
    /// faults.
    fn with_analysis(
        &self,
        feature: Feature,
        f: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            if let Some(why) = p.refuses(feature) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            f(p, &a, &self.overlay())
        })
    }

    /// Returns a snapshot of the annotation overlay, rendering constants by
    /// the binary's name tables.
    ///
    /// Every tool takes the same snapshot, so an answer never depends on
    /// which calls came before it. A decompilation reads only the tables of
    /// the functions it calls, each computed once ([`EnumSource::Binary`]),
    /// so no call waits for the binary's every table.
    fn overlay(&self) -> Overlay {
        Overlay {
            enum_source: EnumSource::Binary,
            ..self.overlay_plain()
        }
    }

    /// Returns the annotation overlay as the user left it, without the
    /// binary's name tables.
    fn overlay_plain(&self) -> Overlay {
        read_lock(&self.overlay).clone()
    }

    /// Lets the analysis go of what it read under names the session has
    /// moved past, after a rename, a comment or a loaded project changed
    /// them ([`borer_engine::analysis::Derived::forget_names_but`]): a
    /// rename otherwise leaves every text and catalog read under the old
    /// names in memory for good.
    fn names_changed(&self) {
        if let Some(a) = read_lock(&self.analysis).as_ref() {
            a.derived.forget_names_but(&self.overlay_plain());
        }
    }

    /// Resolves an address argument: `0x`-hex text, else a name looked up
    /// through the analysis, symbols and overlay (agents name things), else
    /// decimal or bare-hex text ([`resolve`]).
    ///
    /// A name comes before the number reading, so a function named `cafe`
    /// or `1234` is reachable by its name; only `0x` text skips the lookup.
    /// A program with no code analysis looks names up in its symbols and
    /// the overlay alone.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name, naming the
    /// names nearest it ([`borer_engine::analysis::resolve_suggesting`]).
    fn addr(&self, p: &Program, text: &str) -> Result<u64, String> {
        if borer_engine::analysis::hex_prefixed(text)
            && let Some(va) = parse_addr(text)
        {
            return Ok(va);
        }
        borer_engine::analysis::resolve_suggesting(
            p,
            &self.analysis_or_empty(),
            &self.overlay(),
            text,
        )
    }

    /// Resolves an argument to the entry of the discovered function containing it.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `a` - Its analysis.
    /// * `text` - Address or name (see [`Self::addr`]).
    ///
    /// # Errors
    ///
    /// When the text does not resolve or no function contains the address
    /// ([`borer_engine::analysis::function_entry`] says an import's slot is
    /// one).
    fn function_entry(&self, p: &Program, a: &Analysis, text: &str) -> Result<u64, String> {
        let va = self.addr(p, text)?;
        borer_engine::analysis::function_entry(p, a, va).map_err(|e| {
            let digits = text.trim();
            let hint = u64::from_str_radix(digits, 16)
                .ok()
                .filter(|hex| {
                    digits.bytes().all(|b| b.is_ascii_digit()) && a.function_at(*hex).is_some()
                })
                .map_or_else(String::new, |hex| {
                    format!("; bare digits are decimal, write {hex:#x} for the hex address")
                });
            format!("{e}{hint}")
        })
    }

    /// Answers a recovered layout's plan: what it would define and state,
    /// or, applied, what it did.
    ///
    /// The struct and the prototypes are written to the overlay unless
    /// `dry`, as `class_layout` and `borer://layout/...,apply=<Name>` do.
    ///
    /// # Arguments
    ///
    /// * `plan` - The plan ([`borer_engine::analysis::apply`]).
    /// * `a` - The analysis, to name the functions.
    /// * `o` - The overlay the plan was made under.
    /// * `dry` - Say what would be done and write nothing.
    ///
    /// # Returns
    ///
    /// A line saying what was (or would be) done, then the plan's lines.
    fn answer_plan(
        &self,
        plan: borer_engine::analysis::apply::Plan,
        a: &Analysis,
        o: &Overlay,
        dry: bool,
    ) -> String {
        let head = format!(
            "{} struct {} and {} {} prototype(s); decompile then names the fields:\n",
            if dry {
                "dry-run: would define"
            } else {
                "defined"
            },
            plan.name,
            if dry { "state" } else { "stated" },
            plan.prototypes.len()
        );
        let mut out = head;
        for line in plan.describe(a, o) {
            out.push_str(&line);
            out.push('\n');
        }
        if dry {
            out.push_str("pass dry_run=false to apply.\n");
            return out;
        }
        plan.apply(&mut write_lock(&self.overlay));
        self.names_changed();
        out
    }

    /// Defines the types C declarations state, laid out by the loaded
    /// binary's ABI ([`borer_engine::analysis::cdecl`]): `set_type` with
    /// `type` alone.
    ///
    /// # Arguments
    ///
    /// * `text` - The declarations.
    /// * `dry` - Say what would be defined and write nothing.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the text is refused (a construct the
    /// subset does not read, an offset assertion that fails), or the types
    /// with the overlay's would not validate.
    fn declare_c(&self, text: &str, dry: bool) -> Result<String, ErrorData> {
        /// Types a reply describes before it counts the rest.
        const SHOWN: usize = 64;
        self.with_program(|p| {
            let abi = borer_engine::analysis::cdecl::Abi::of(p);
            let o = self.overlay_plain();
            let declared = borer_engine::analysis::cdecl::parse(text, &o.types, abi)
                .map_err(|e| e.to_string())?;
            let mut types = o.types.clone();
            for (name, ty, _) in &declared.types {
                types.insert(name.clone(), ty.clone());
            }
            borer_engine::analysis::utypes::validate(&types, &o.applied)
                .map_err(|e| e.to_string())?;
            let lines = borer_engine::analysis::cdecl::describe(&declared);
            let mut out = format!(
                "{} {} type(s) from C, laid out for {}:\n",
                if dry {
                    "dry-run: would define"
                } else {
                    "defined"
                },
                declared.types.len(),
                abi.name()
            );
            for line in lines.iter().take(SHOWN) {
                out.push_str(line);
                out.push('\n');
            }
            if lines.len() > SHOWN {
                out.push_str(&format!(
                    "# showing {SHOWN} of {} lines; `types` lists every type\n",
                    lines.len()
                ));
            }
            if dry {
                out.push_str("pass dry_run=false to apply.\n");
                return Ok(out);
            }
            write_lock(&self.overlay)
                .types
                .extend(declared.types.into_iter().map(|(name, ty, _)| (name, ty)));
            self.names_changed();
            Ok(out)
        })
    }
}

#[tool_router]
impl BorerServer {
    /// Loads a file as the current program and resets analysis and overlay.
    ///
    /// A session's names must not leak into another image, so the overlay
    /// is cleared; a session that has not saved them is told what it lost.
    /// An attached process is mapped onto the new binary
    /// ([`LiveSession::map`]), so live addresses never rebase by a binary
    /// no longer loaded.
    ///
    /// # Arguments
    ///
    /// * `LoadBinaryParams` - Destructured tool parameters (see its field docs).
    ///
    /// A refused load changes nothing: the program, its names and the
    /// load options of the session stay what they were.
    ///
    /// With `arch`, the file is not parsed: its bytes map where `base` or
    /// `regions` say ([`Layout`]), so raw code and memory dumps analyze
    /// with every other tool; without it the load is what it always was.
    ///
    /// # Errors
    ///
    /// Invalid params when the file does not load, the entry offset is
    /// past its end or in no section's file bytes, the stated layout does
    /// not parse or the file cannot hold it, or `entry` and
    /// `entry_file_offset` are both given.
    #[tool(
        description = "Load a PE, ELF or Mach-O file (a fat Mach-O: its x86-64 slice), or any other file as raw bytes, as the current program; returns its summary. pdb=false skips the companion PDB; entry_file_offset overrides the entry; arch maps raw code or a dump.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn load_binary(
        &self,
        Parameters(LoadBinaryParams {
            path,
            entry_file_offset,
            pdb,
            arch,
            base,
            entry,
            regions,
        }): Parameters<LoadBinaryParams>,
    ) -> Result<String, ErrorData> {
        let apply_pdb = pdb.unwrap_or(true);
        if entry.is_some() && entry_file_offset.is_some() {
            return Err(err_params(
                "entry and entry_file_offset both name the entry; give one",
            ));
        }
        let raw = RawLoad {
            arch,
            base,
            entry,
            regions,
        };
        let layout = Layout::parse(
            raw.arch.map(Into::into),
            raw.base.as_deref(),
            raw.entry.as_deref(),
            raw.regions.as_deref(),
        )
        .map_err(|e| err_params(format!("load failed: {e:#}")))?;
        let loaded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let path = PathBuf::from(&path);
            match &layout {
                Some(layout) => Program::load_layout(&path, layout),
                None => {
                    Program::load_with_symsrv(&path, apply_pdb, symsrv::cache_dir().as_deref())
                }
            }
        }))
        .map_err(|e| {
            err_internal(format!(
                "loading faulted on this file: {}. The session is still up and keeps the program it had.",
                fault_text(e.as_ref())
            ))
        })?;
        let mut program = loaded.map_err(|e| err_params(format!("load failed: {e:#}")))?;
        if let Some(off) = entry_file_offset {
            if off >= num::from_usize(program.bytes.len()) {
                return Err(err_params(format!(
                    "entry_file_offset {off:#x} beyond file size {:#x}",
                    program.bytes.len()
                )));
            }
            let va = program.offset_to_va(off).ok_or_else(|| {
                err_params(format!(
                    "entry_file_offset {off:#x} is in no section's file bytes, so it maps to no address; sections: {}",
                    program.section_list()
                ))
            })?;
            program.entry = Some(va);
        }
        let mut summary = program.summary();
        let dropped = std::mem::take(&mut *write_lock(&self.overlay));
        if !dropped.names.is_empty() || !dropped.comments.is_empty() {
            let previous = self.loaded().map_or_else(
                || "the previous binary".to_owned(),
                |p| p.path.display().to_string(),
            );
            summary.push_str(&format!(
                "note: discarded {} name(s) and {} comment(s) set on {previous}; save_project before load_binary keeps them\n",
                dropped.names.len(),
                dropped.comments.len()
            ));
        }
        let (packs, notes) = self.packs_for(&program);
        for note in notes {
            let _ = writeln!(summary, "{note}");
        }
        *write_lock(&self.pdb_applied) = apply_pdb;
        *write_lock(&self.entry_file_offset) = entry_file_offset;
        *write_lock(&self.raw_load) = raw;
        if let Some(s) = lock(&self.live).as_mut() {
            let mapped = s.map(Some(&program));
            let _ = write!(
                summary,
                "live {} (pid {}): {mapped}",
                s.process.name(),
                s.process.pid()
            );
        }
        if !summary.ends_with('\n') {
            summary.push('\n');
        }
        summary.push_str(LOAD_NEXT);
        *write_lock(&self.program_packs) = packs;
        *write_lock(&self.program) = Some(Arc::new(program));
        *write_lock(&self.analysis) = None;
        *write_lock(&self.strings) = None;
        Ok(summary)
    }

    /// Fetches the loaded PE's missing companion PDB from a symbol server.
    ///
    /// Off by default like every side effect: a dry run says the URL and
    /// the cache destination and touches nothing. A PDB of this build
    /// already on disk (beside the binary, at its recorded path, or in the
    /// cache) is named instead of fetched: a load with `pdb=false` leaves
    /// it unapplied. A confirmed fetch checks
    /// the cache first (a hit answers without the network), downloads with
    /// `curl`, and keeps the file only when its GUID and age name this
    /// binary, so a wrong or hostile download is discarded, never cached.
    /// The landed PDB applies on the next `load_binary`.
    ///
    /// # Arguments
    ///
    /// * `FetchPdbParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded, the image names no PDB, no
    /// cache directory resolves, the name or server is refused, or the
    /// fetch or its validation fails.
    #[tool(
        description = "Fetch the loaded PE's missing companion PDB from a symbol server into the cache; guid+age must match; dry-run unless dry_run=false; the next load_binary applies it.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = true
        )
    )]
    fn fetch_pdb(
        &self,
        Parameters(FetchPdbParams { dry_run, server }): Parameters<FetchPdbParams>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            if let Some(outcome) = &p.pdb
                && matches!(outcome, borer_engine::pdb::Outcome::Applied { .. })
            {
                return Ok(format!(
                    "the companion pdb already applied ({}); nothing to fetch",
                    outcome.render()
                ));
            }
            let Some(record) = p.pdb_record.as_ref() else {
                return Err("the loaded binary names no companion pdb (no codeview record: not a PE, or a build without debug info)".to_owned());
            };
            let Some(root) = symsrv::cache_dir() else {
                return Err(format!(
                    "no cache directory: set {}, LOCALAPPDATA, XDG_CACHE_HOME or HOME",
                    symsrv::CACHE_ENV
                ));
            };
            if let Some(found) = borer_engine::pdb::resolved(&p.path, record, Some(&root)) {
                return Ok(format!(
                    "{} is this build's pdb and did not apply to this load (load_binary passed pdb=false, or it landed since): load_binary with pdb=true applies it; nothing to fetch",
                    found.display()
                ));
            }
            symsrv::obtain(
                record,
                &root,
                server.as_deref().unwrap_or(symsrv::DEFAULT_SERVER),
                dry_run.unwrap_or(true),
                symsrv::curl,
            )
        })
    }

    /// Returns the program summary.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Summary of the current program: format, arch, entry, sections with entropy, imports/exports.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn binary_info(&self) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let more = if p.refuses(Feature::Decompile).is_some() {
                "borer://triage reads the whole file in one call".to_owned()
            } else {
                template_names()
            };
            Ok(format!("{}# more: {more}\n", p.summary()))
        })
    }

    /// Disassembles a run of instructions at an address or name.
    ///
    /// # Arguments
    ///
    /// * `DisassembleParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address does not resolve or is unmapped, or
    /// the architecture has no decoder.
    #[tool(
        description = "Disassemble `count` instructions (default 32, max 256) at an address or name as `va text` rows (bytes=true adds bytes); whole functions: disassemble_function.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn disassemble(
        &self,
        Parameters(DisassembleParams {
            address,
            count,
            bytes,
        }): Parameters<DisassembleParams>,
    ) -> Result<String, ErrorData> {
        let count = count_param(count, 32, 256, "count")?;
        let n = count.n;
        let with_bytes = bytes.unwrap_or(false);
        self.with_program(|p| {
            let asked = self.addr(p, &address)?;
            let isa = p.isa_for(Feature::Disasm)?;
            let a = self.analysis_or_empty();
            let va = render::instruction_at_or_before(p, &a, asked).unwrap_or(asked);
            let snapped = if va == asked {
                String::new()
            } else {
                format!("; {asked:#x} is inside an instruction, listing from {va:#x}")
            };
            // PERF: a 16 KiB window covers 256 instructions and bounds the read.
            let code = p.read_va_upto(va, 16 * 1024).ok_or_else(|| {
                format!(
                    "address {va:#x} is not mapped to file bytes; sections: {}",
                    p.section_list()
                )
            })?;
            let limit = render::sweep_limit(&a, va);
            let window = limit
                .and_then(|end| usize::try_from(end - va).ok())
                .and_then(|n| code.get(..n.min(code.len())))
                .unwrap_or(code);
            let lines = disasm::disassemble_isa(window, va, isa, n);
            let o = self.overlay();
            let ends = limit.map_or(String::new(), |end| {
                format!("; code ends at {end:#x}, what follows is data")
            });
            let caveat = Some(render::listing_caveat(p, &a, va))
                .filter(|c| !c.is_empty())
                .map_or(String::new(), |c| format!("; {c}"));
            let mut out = format!(
                "# {} instructions at {:#x}{snapped}{ends}{caveat}\n",
                lines.len(),
                va
            );
            for l in &lines {
                if let Some(n) = o.names.get(&l.va) {
                    out.push_str(&format!("            ; = {n} =\n"));
                }
                let mut text = l.text.clone();
                if let Some(c) = o.comments.get(&l.va) {
                    text.push_str(&format!("  // {c}"));
                }
                if with_bytes {
                    let mut hexb = String::new();
                    for b in &l.bytes {
                        hexb.push_str(&format!("{b:02x} "));
                    }
                    out.push_str(&format!("{:#x}  {:<24} {text}\n", l.va, hexb.trim_end()));
                } else {
                    out.push_str(&format!("{:#x}  {text}\n", l.va));
                }
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Disassembles a whole function block by block.
    ///
    /// # Arguments
    ///
    /// * `DisassembleFunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Disassemble a whole function block by block with `L_<addr>:` labels and named call/jmp targets (max_instrs default 400, max 2000).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn disassemble_function(
        &self,
        Parameters(DisassembleFunctionParams {
            address,
            max_instrs,
            bytes,
        }): Parameters<DisassembleFunctionParams>,
    ) -> Result<String, ErrorData> {
        let max = count_param(max_instrs, 400, 2000, "max_instrs")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::disasm_function(p, a, o, entry, max.n, bytes.unwrap_or(false))
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
        .map(|text| max.noted(text))
    }

    /// Reads typed values at an address or name.
    ///
    /// Reading stops at the first address that is not there, and the header
    /// says so: returning fewer values than were asked for without a word
    /// would leave the caller to notice the shortfall by counting rows.
    /// With `type`, a user type is laid over the bytes instead
    /// ([`render::typed_tsv`]): `count` records of it, or as many as the
    /// type's own array states.
    ///
    /// # Arguments
    ///
    /// * `ReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind, a type that does not parse, or
    /// both a kind and a type; internal error when the address does not
    /// resolve or the bytes are not mapped.
    #[tool(
        description = "Read `count` typed values (kind u8..u64, i8..i64, f32, f64, ptr, cstr, wstr; default u64, count 1, max 256) as `va value` rows; pointers are named. `type` reads a user type instead: one row per field.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn read(
        &self,
        Parameters(ReadParams {
            address,
            kind,
            r#type: ty,
            count,
        }): Parameters<ReadParams>,
    ) -> Result<String, ErrorData> {
        let count = count_param(count, 1, 256, "count")?;
        let n = count.n;
        if let Some(spelled) = ty {
            if kind.is_some() {
                return Err(err_params(
                    "`kind` and `type` both say what the bytes are; give one",
                ));
            }
            let parsed = borer_engine::analysis::utypes::parse_type(&spelled)
                .map_err(|e| err_params(e.to_string()))?;
            let parsed = if n > 1 {
                borer_engine::analysis::utypes::TypeExpr::Array(
                    Box::new(parsed),
                    num::from_usize(n),
                )
            } else {
                parsed
            };
            return self
                .with_program(|p| {
                    if parse_off(&address).is_some() {
                        return Err(
                            "a typed read takes an address; off: reads by `kind`".to_owned()
                        );
                    }
                    let va = self.addr(p, &address)?;
                    let analysis = read_lock(&self.analysis).clone();
                    render::typed_tsv(p, analysis.as_deref(), &self.overlay(), va, &parsed)
                })
                .map(|text| count.noted(text));
        }
        let kind_text = kind.unwrap_or_default();
        let kind: memory::Kind = kind_text.into();
        self.with_program(|p| {
            let (start, values, place) = match parse_off(&address) {
                Some(off) => (off, memory::read_values_at_offset(p, off, kind, n)?, "off:"),
                None => {
                    let va = self.addr(p, &address)?;
                    (va, memory::read_values(p, va, kind, n)?, "")
                }
            };
            let analysis = read_lock(&self.analysis).clone();
            let o = self.overlay();
            let sec = if place.is_empty() {
                p.section_at(start)
                    .map_or_else(String::new, |s| format!(" in {}", s.name))
            } else {
                String::from(", rows by file offset")
            };
            let mut out = format!("# {} x {kind_text} at {place}{start:#x}{sec}", values.len());
            if values.len() < n {
                let next = values
                    .last()
                    .map_or(start, |v| v.at.wrapping_add(num::from_usize(v.size)));
                out.push_str(&format!(
                    "; asked for {n}, nothing readable at {place}{next:#x}"
                ));
            }
            out.push('\n');
            for v in &values {
                let mut text = v.text.clone();
                if let Some(name) = v
                    .target
                    .and_then(|t| render::pointee_name(p, analysis.as_deref(), &o, t))
                {
                    text.push_str(&format!(" -> {name}"));
                }
                out.push_str(&format!("{:<12} {text}\n", format!("{:#x}", v.at)));
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Lists high-entropy regions over every byte of the file.
    ///
    /// # Arguments
    ///
    /// * `EntropyParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the threshold is outside 0..8 or the
    /// limit is zero.
    #[tool(
        description = "High-entropy regions (packed/encrypted data) as `off va len entropy` rows at or above threshold bits/byte (default 7.2, window 1024) under a `# showing N of M` header; paging (200, max 200; the scan stops at 200 regions).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn entropy(
        &self,
        Parameters(EntropyParams {
            window,
            threshold,
            offset,
            limit,
        }): Parameters<EntropyParams>,
    ) -> Result<String, ErrorData> {
        let window = to_usize(window.unwrap_or(1024));
        let threshold = entropy_threshold(threshold.unwrap_or(7.2)).map_err(err_params)?;
        let page = Page::new(
            offset,
            limit,
            None,
            entropy::REGIONS_MAX,
            entropy::REGIONS_MAX,
        )?;
        self.with_program(|p| {
            Ok(entropy::report(
                p,
                window,
                threshold,
                page.offset,
                page.limit.n,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Scans every byte of the file for known crypto and hash constants,
    /// grouped by algorithm, with one page of the per-site rows.
    ///
    /// The tool takes paging parameters and so refuses one it does not
    /// know, where it took no parameters and ignored any it was given.
    ///
    /// # Arguments
    ///
    /// * `CryptoParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Crypto tables and constants (AES, SHA-1/2, MD5, CRC-32, ChaCha, Blowfish, RC5/6, xxHash/FNV/SipHash, Base64) anywhere in the file: `va section algorithm` rows per algorithm (`off=<n>` if unmapped), offset/limit (200, max 500).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn find_crypto_constants(
        &self,
        Parameters(CryptoParams { offset, limit }): Parameters<CryptoParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, None, 200, 500)?;
        self.with_program(|p| {
            Ok(render::crypto_tsv(
                p,
                &self.analysis_or_empty(),
                &self.overlay(),
                page.offset,
                page.limit.n,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Returns the one-call triage of a function.
    ///
    /// # Arguments
    ///
    /// * `FunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "One-call triage of a function: shape, loops, jump tables, callers/callees by name, strings and data it references; `# next:` lines name what to read next.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn function_summary(
        &self,
        Parameters(FunctionParams { address }): Parameters<FunctionParams>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let a = self.ensure_analysis()?;
            let entry = self.function_entry(p, &a, &address)?;
            render::function_summary(p, &a, &self.overlay(), entry)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists the string literals a function references.
    ///
    /// # Arguments
    ///
    /// * `FunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "String literals a function references as `site string_va text` rows (max 100).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn function_strings(
        &self,
        Parameters(FunctionParams { address }): Parameters<FunctionParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::function_strings_tsv(p, a, o, entry)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists the functions referencing a string that matches a filter.
    ///
    /// # Arguments
    ///
    /// * `FindFunctionByStringParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Functions referencing strings containing `filter`: a `# showing N of M` header, a numbered `# strings:` legend, then `entry name: 1 2 5` rows; offset/limit page rows and legend (50, max 300).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn find_function_by_string(
        &self,
        Parameters(FindFunctionByStringParams {
            filter,
            offset,
            limit,
        }): Parameters<FindFunctionByStringParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        let limit = count_param(limit, 50, 300, "limit")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            Ok(render::functions_by_string_tsv(
                p, a, o, &filter, offset, limit.n,
            ))
        })
        .map(|text| limit.noted(text))
    }

    /// Runs `f` with the attached process.
    ///
    /// A process that has exited is said to have, before `f` runs: its
    /// memory is gone, and a read, a scan or a diff would otherwise answer
    /// "not readable" or "0 instances" as if the address were the problem.
    ///
    /// Every refusal is invalid params, as [`Self::with_program`]'s are: a
    /// body refuses what it was asked (an address not readable, a name or
    /// class that is not there, a process that is gone), and the agent's
    /// next move is to change the call, so one code says so for every live
    /// tool and for the static ones alike.
    ///
    /// # Arguments
    ///
    /// * `f` - The tool body over the session.
    ///
    /// # Errors
    ///
    /// Invalid params when no process is attached, it has exited, or `f`
    /// refuses the request.
    fn with_live(
        &self,
        f: impl FnOnce(&mut LiveSession) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let mut guard = lock(&self.live);
        let session = guard
            .as_mut()
            .ok_or_else(|| err_params("no process attached: live_attach first"))?;
        if let Some(code) = session.process.exit_code() {
            return Err(err_params(exited(&session.process, code)));
        }
        f(session).map_err(err_params)
    }

    /// Resolves an address an agent gave for the process: a name or a
    /// static address of the loaded binary moves into the process, any
    /// other number is taken as live, and a number after `live:` is live
    /// even inside the image's static range (a heap the process placed
    /// there).
    ///
    /// A singleton the analysis placed in thread-local storage has no
    /// static address: its slot is at the offset in the thread's block.
    ///
    /// # Arguments
    ///
    /// * `session` - The attached process.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name.
    fn live_addr(&self, session: &LiveSession, text: &str) -> Result<u64, String> {
        let program = self.loaded();
        if let (Some(_), Some(block)) = (&program, session.tls_block)
            && let Some(class) = text.trim().to_lowercase().strip_suffix("::instance")
            && let Ok(a) = self.ensure_analysis()
            && let Some((off, _)) = a
                .classes
                .tls_slots
                .iter()
                .find(|(_, c)| c.to_lowercase() == class)
        {
            return block
                .checked_add(*off)
                .ok_or_else(|| format!("{text}: the TLS offset overflows"));
        }
        if let Some(live) = text.trim().strip_prefix(LIVE_PREFIX) {
            return parse_addr(live).ok_or_else(|| {
                format!("{text}: after {LIVE_PREFIX} comes a number (0x-hex or decimal)")
            });
        }
        if let Some(va) = parse_addr(text) {
            return Ok(session.rebase.as_ref().map_or(va, |r| r.live_of(va)));
        }
        let Some(p) = program else {
            return Err(format!(
                "{text} is not an address, and no binary is loaded to look the name up in"
            ));
        };
        let va = self.addr(&p, text)?;
        let r = session.rebase.as_ref().map_err(|why| {
            format!("{text} is {va:#x} in the loaded binary, which is not mapped onto the process ({why}), so it has no live address")
        })?;
        Ok(r.live_of(va))
    }

    /// Follows a singleton's slot to its object: `Class::instance` names
    /// the slot that holds the pointer, and the object is what it points at.
    ///
    /// # Arguments
    ///
    /// * `session` - The attached process.
    /// * `text` - The address argument as given.
    /// * `va` - What it resolved to.
    /// * `word` - The pointer width in bytes.
    ///
    /// # Errors
    ///
    /// When the slot is not readable or holds no object.
    fn through_singleton(
        session: &LiveSession,
        text: &str,
        va: u64,
        word: usize,
    ) -> Result<(u64, String), String> {
        if !text.trim().to_lowercase().ends_with("::instance") {
            return Ok((va, String::new()));
        }
        let values = live::read_values(&session.process, va, memory::Kind::Ptr, 1, word)?;
        let target = values.first().and_then(|v| v.target).unwrap_or(0);
        if target == 0 {
            return Err(format!(
                "{text}: the slot at {va:#x} holds no object (null)"
            ));
        }
        Ok((
            target,
            format!("{text}: slot {va:#x} -> object {target:#x}\n"),
        ))
    }

    /// Attaches to a running process for reading.
    ///
    /// # Arguments
    ///
    /// * `LiveAttachParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process matches, several do, or the system refuses a read handle.
    #[tool(
        description = "Attach read-only to a running process (name or pid); maps the loaded binary onto it so live tools take static addresses and names.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    fn live_attach(
        &self,
        Parameters(LiveAttachParams { process }): Parameters<LiveAttachParams>,
    ) -> Result<String, ErrorData> {
        let proc = borer_live::Process::attach(&process).map_err(err_params)?;
        let modules = proc.modules();
        let mut out = format!(
            "attached to {} (pid {}), {} modules, read-only\n",
            proc.name(),
            proc.pid(),
            modules.len()
        );
        let mut session = LiveSession::new(proc);
        out.push_str(&session.map(self.loaded().as_deref()));
        out.push_str("modules:\n");
        for m in modules.iter().take(ATTACH_MODULES) {
            let _ = writeln!(out, "  {:#x} {:>10} {}", m.base, m.size, m.name);
        }
        if modules.len() > ATTACH_MODULES {
            let _ = writeln!(
                out,
                "  ... {} more: live_modules(offset={ATTACH_MODULES}) lists them, live_modules(filter=...) finds one",
                modules.len() - ATTACH_MODULES
            );
        }
        out.push_str("next: live_object(address or singleton name), live_instances(class), live_read(address, kind), live_watch(name, address)\n");
        if let Some(was) = lock(&self.live).replace(session) {
            let _ = write!(
                out,
                "note: detached from {} (pid {}) first",
                was.process.name(),
                was.process.pid()
            );
            if was.snapshots.is_empty() {
                out.push('\n');
            } else {
                let names: Vec<&str> = was
                    .snapshots
                    .keys()
                    .take(DROPPED_NAMES)
                    .map(String::as_str)
                    .collect();
                let more = was.snapshots.len() - names.len();
                let _ = writeln!(
                    out,
                    "; its {} watch(es) are dropped: {}{}",
                    was.snapshots.len(),
                    names.join(", "),
                    if more > 0 {
                        format!(", +{more} more")
                    } else {
                        String::new()
                    }
                );
            }
        }
        Ok(out)
    }

    /// Detaches from the process.
    ///
    /// # Errors
    ///
    /// Never; detaching with nothing attached is a no-op.
    #[tool(
        description = "Detach from the attached process and drop its watches.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn live_detach(&self) -> Result<String, ErrorData> {
        let was = lock(&self.live).take();
        Ok(match was {
            Some(s) => format!(
                "detached from {} (pid {}){}",
                s.process.name(),
                s.process.pid(),
                s.process
                    .exit_code()
                    .map_or_else(String::new, |code| format!(
                        ", which had exited (exit code {code:#x})"
                    ))
            ),
            None => "no process was attached".to_owned(),
        })
    }

    /// Lists the attached process's modules, a page at a time.
    ///
    /// # Arguments
    ///
    /// * `LiveModulesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for a zero limit, or when no process is attached or
    /// it has exited.
    #[tool(
        description = "List the attached process's modules.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = true
        )
    )]
    fn live_modules(
        &self,
        Parameters(LiveModulesParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<LiveModulesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 50, 500)?;
        let filter = Filter::new(filter.as_deref());
        self.with_live(|s| {
            let image = s.rebase.as_ref().ok().map(|r| r.live_base);
            let (total, table) = live::modules_page(
                &s.process.modules(),
                filter.needle(),
                page.offset,
                page.limit.n,
                image,
            );
            Ok(if page.count_only {
                format!("# {total} modules\n")
            } else {
                table
            })
        })
        .map(|text| page.limit.noted(text))
    }

    /// Reads typed values from the process.
    ///
    /// # Arguments
    ///
    /// * `LiveReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind, or when no process is attached,
    /// the address does not resolve, or its first value does not read.
    #[tool(
        description = "Read typed values from the attached process; pointers say what they point at.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    fn live_read(
        &self,
        Parameters(LiveReadParams {
            address,
            kind,
            count,
        }): Parameters<LiveReadParams>,
    ) -> Result<String, ErrorData> {
        let kind_text = kind.unwrap_or_default();
        let kind: memory::Kind = kind_text.into();
        let count = count_param(count, 1, 256, "count")?;
        let n = count.n;
        let program = self.loaded();
        let overlay = self.overlay();
        self.with_live(|s| {
            let va = self.live_addr(s, &address)?;
            let word = s.word;
            let values = live::read_values(&s.process, va, kind, n, word)?;
            let rebase = s.rebase.as_ref().ok().copied();
            let analysis = match (rebase, values.iter().any(|v| v.target.is_some())) {
                (Some(_), true) => self.ensure_analysis().ok(),
                _ => None,
            };
            let origin = rebase
                .and_then(|r| r.to_static(va))
                .map_or_else(String::new, |st| format!(" (= static {st:#x})"));
            let mut out = format!(
                "# {} {kind_text} value(s) at live {va:#x}{origin}",
                values.len()
            );
            if values.len() < n {
                let next = values
                    .last()
                    .map_or(va, |v| v.at.wrapping_add(num::from_usize(v.size)));
                let _ = write!(
                    out,
                    "; asked for {n}, nothing readable as {kind_text} at {next:#x}"
                );
            }
            out.push('\n');
            for v in &values {
                let note = match (v.target, &program, &analysis, rebase) {
                    (Some(t), Some(p), Some(a), Some(r)) => r
                        .describe(p, a, &overlay, t)
                        .map(|d| format!("  -> {d}"))
                        .or_else(|| {
                            live::class_at(&s.process, &r, a, t, word)
                                .map(|c| format!("  -> {c} object"))
                        })
                        .unwrap_or_default(),
                    _ => String::new(),
                };
                let _ = writeln!(out, "{:#x}  {}{note}", v.at, v.text);
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Reads an object of the process with its class's fields.
    ///
    /// # Arguments
    ///
    /// * `LiveObjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached or no binary is loaded, the address does
    /// not resolve, the class is unknown, or the object is not readable.
    #[tool(
        description = "Read an object in the attached process as its class: each field's name, type, live value, and what pointers point at.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    fn live_object(
        &self,
        Parameters(LiveObjectParams { address, class }): Parameters<LiveObjectParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            self.with_live(|s| {
                let r = s.mapped()?;
                let va = self.live_addr(s, &address)?;
                let (va, via) = Self::through_singleton(s, &address, va, s.word)?;
                let text = live::object(&s.process, p, a, o, &r, va, class.as_deref())?;
                Ok(format!("{via}{text}"))
            })
            .map_err(|e| e.message.to_string())
        })
    }

    /// Finds the instances of a class in the process.
    ///
    /// # Arguments
    ///
    /// * `LiveInstancesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached or no binary is loaded, or the analysis
    /// knows no vtable for the class.
    #[tool(
        description = "Find a class's live objects by vtable in the attached process's data; live_object reads one.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    fn live_instances(
        &self,
        Parameters(LiveInstancesParams {
            class,
            offset,
            limit,
            count_only,
        }): Parameters<LiveInstancesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 64, 512)?;
        let collect = if page.count_only {
            live::COUNT_MAX
        } else {
            page.offset.saturating_add(page.limit.n)
        };
        self.with_analysis(Feature::Decompile, |_, a, _| {
            self.with_live(|s| {
                let r = s.mapped()?;
                let scan = live::instances(&s.process, &r, a, &class, s.word, collect)?;
                let mut out = live::instances_page(
                    &scan,
                    &class,
                    page.offset,
                    page.limit.n,
                    page.count_only,
                );
                if !scan.hits.is_empty() && !page.count_only {
                    out.push_str("next: live_object(address) for the fields; live_watch(name, address), then live_watch(name) for what changes\n");
                }
                Ok(out)
            })
            .map_err(|e| e.message.to_string())
        })
        .map(|text| page.limit.noted(text))
    }

    /// Watches memory of the process: starts a watch, or lists what changed.
    ///
    /// # Arguments
    ///
    /// * `LiveWatchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached, the address does not resolve or is not
    /// readable, the class given is unknown, or no watch has the name.
    #[tool(
        description = "Watch attached-process memory: with an address, keep its bytes under the name; without, list what changed, naming fields when the class is known.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    fn live_watch(
        &self,
        Parameters(LiveWatchParams {
            name,
            address,
            length,
            class,
        }): Parameters<LiveWatchParams>,
    ) -> Result<String, ErrorData> {
        must_fit_a_row(&name, Annotation::Name)?;
        let length = length
            .map(|n| count_param(Some(n), 1, live::READ_MAX, "length"))
            .transpose()?;
        let program = self.loaded();
        let overlay = self.overlay();
        self.with_live(|s| {
            let Some(address) = address else {
                let watch = s
                    .snapshots
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| format!("no watch is named {name}; pass an address to start one"))?;
                let diff = watch.snapshot.diff(&s.process, &watch.fields, s.word)?;
                let mut out = live::render_changes(&watch.snapshot, &diff, &watch.fields);
                if diff.now != watch.snapshot {
                    out.push_str("(the watch now holds these bytes)\n");
                    s.snapshots.insert(
                        name.clone(),
                        Watch {
                            snapshot: diff.now,
                            fields: watch.fields,
                        },
                    );
                }
                return Ok(out);
            };
            let va = self.live_addr(s, &address)?;
            let analysis = match (&program, &class) {
                (Some(_), Some(_)) => Some(self.ensure_analysis()?),
                (Some(_), None) if s.rebase.is_ok() => self.ensure_analysis().ok(),
                _ => None,
            };
            let (class, fields) = match (class, &program, &analysis) {
                (Some(c), None, _) => {
                    return Err(format!(
                        "class {c} names fields of a loaded binary, and none is loaded"
                    ));
                }
                (Some(c), Some(p), Some(a)) => {
                    let fields = live::fields_of(p, a, &overlay, &c)
                        .ok_or_else(|| format!("no function belongs to class {c}"))?;
                    (Some(c), fields)
                }
                (Some(c), Some(_), None) => {
                    return Err(format!("no function belongs to class {c}"));
                }
                (None, Some(p), Some(a)) => {
                    let found = s
                        .rebase
                        .as_ref()
                        .ok()
                        .and_then(|r| live::class_at(&s.process, r, a, va, s.word));
                    let fields = found
                        .as_deref()
                        .and_then(|c| live::fields_of(p, a, &overlay, c))
                        .unwrap_or_default();
                    (found, fields)
                }
                (None, None, _) | (None, Some(_), None) => (None, std::collections::BTreeMap::new()),
            };
            let size = fields
                .iter()
                .map(|(off, f)| {
                    usize::try_from(*off)
                        .unwrap_or(live::READ_MAX)
                        .saturating_add(f.len)
                })
                .max()
                .unwrap_or(WATCH_DEFAULT);
            let len = length.map_or(size.clamp(8, live::READ_MAX), |asked| asked.n);
            let snapshot = Snapshot::take(&s.process, va, len)?;
            let readable = if snapshot.bytes.len() < snapshot.len {
                format!("{} of {} bytes readable", snapshot.bytes.len(), snapshot.len)
            } else {
                format!("{} bytes", snapshot.len)
            };
            let out = format!(
                "watch {name}: {readable} at {va:#x}{}; live_watch(\"{name}\") after the change you want to see",
                class
                    .as_ref()
                    .map_or_else(String::new, |c| format!(" ({c}, {} fields)", fields.len()))
            );
            s.snapshots
                .insert(name.clone(), Watch { snapshot, fields });
            Ok(out)
        })
        .map(|text| match length {
            Some(asked) => asked.noted(text),
            None => text,
        })
    }

    /// Restarts the server on the binary at its own path, keeping the session.
    ///
    /// The answer is written first; the hand-over itself follows it
    /// ([`Self::call_tool`], [`HandOver`]): the relay gives this worker no
    /// request after this one, the worker ends once this reply and those of
    /// the requests before it are written, and the relay starts the binary
    /// again, which resumes the session ([`relay`]). A request the client
    /// sends as soon as the reply arrives waits in the relay for it.
    ///
    /// An attached process is not carried over: its handle and watches end
    /// with this worker, and the reply says so, so the agent attaches again
    /// rather than meeting "no process attached" on its next live call.
    ///
    /// # Errors
    ///
    /// Never.
    #[tool(
        description = "Restart the server on the binary at its path, keeping the session, the loaded file and its names and comments: use after rebuilding borer, instead of restarting the client.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = false
        )
    )]
    fn reload(&self) -> Result<String, ErrorData> {
        let exe = std::env::args().next().unwrap_or_default();
        let loaded = self.loaded().map(|p| p.path.display().to_string());
        let live = lock(&self.live).as_ref().map_or_else(String::new, |s| {
            format!(
                "; the live session with {} (pid {}) and its {} watch(es) end with this server: live_attach again once it is up",
                s.process.name(),
                s.process.pid(),
                s.snapshots.len()
            )
        });
        Ok(format!(
            "reloading borer from {exe}{}{live}; the tool list is announced again once the new server is up",
            loaded.map_or_else(String::new, |p| format!(", reloading {p}"))
        ))
    }

    /// Hexdumps a byte range at an address or name.
    ///
    /// A hexdump is a "show me what is there" tool, so a length that runs
    /// off the end of the section gives back the bytes that are there rather
    /// than nothing: the header states the range it actually covers, so the
    /// short answer says so itself. Only an address with nothing at all
    /// behind it is refused, and then the message blames the address rather
    /// than the length, which is what was actually wrong.
    ///
    /// # Arguments
    ///
    /// * `HexdumpParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the range is not entirely mapped.
    #[tool(
        description = "Hexdump `length` bytes (default 64, max 4096) at `address`.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn hexdump(
        &self,
        Parameters(HexdumpParams { address, length }): Parameters<HexdumpParams>,
    ) -> Result<String, ErrorData> {
        let length = count_param(length, 64, 4096, "length")?;
        self.with_program(|p| {
            if let Some(off) = parse_off(&address) {
                return hexfmt::file_hexdump(p, off, length.n);
            }
            let va = self.addr(p, &address)?;
            let code = p.read_va_upto(va, length.n).ok_or_else(|| {
                format!(
                    "address {va:#x} not mapped; sections: {}{}",
                    p.section_list(),
                    memory::by_offset_hint(p)
                )
            })?;
            let sec = p
                .section_at(va)
                .map_or_else(String::new, |s| format!(" {}", s.name));
            Ok(format!(
                "# {va:#x}..{:#x}{sec}\n{}",
                va + num::from_usize(code.len()),
                hexfmt::hexdump(code, va)
            ))
        })
        .map(|text| length.noted(text))
    }

    /// Lists printable strings with filtering and paging.
    ///
    /// # Arguments
    ///
    /// * `StringsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the encoding is unknown.
    #[tool(
        description = "Printable ASCII/UTF-16LE strings as `off va len enc \"text\"` rows.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn strings(
        &self,
        Parameters(StringsParams {
            min_length,
            filter,
            encoding,
            offset,
            limit,
            count_only,
        }): Parameters<StringsParams>,
    ) -> Result<String, ErrorData> {
        let min = to_usize(min_length.unwrap_or(5).max(4));
        let filter = Filter::new(filter.as_deref());
        let encoding = encoding.unwrap_or_default();
        let page = Page::new(offset, limit, count_only, 200, 500)?;
        self.with_program(|p| {
            // A floor call (min_length below the cached default) walks
            // itself: its rows are nearly all noise, and holding them would
            // cost the cache an order of magnitude more memory.
            let rows: Vec<StringRow> = if min >= strwalk::WALK_MIN {
                strwalk::load_or_build(&self.strings, p).rows(encoding, min)
            } else {
                walk_rows(p, encoding, min)
            };
            Ok(strings_page(
                p,
                rows,
                &filter,
                (min, encoding),
                (page.offset, page.limit.n),
                page.count_only,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Lists imports and exports with filtering and paging.
    ///
    /// An import nothing references is a redirected or leftover slot, the
    /// shape a patched binary leaves behind, so its row says so.
    ///
    /// # Arguments
    ///
    /// * `SymbolsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Imports/exports/forwards/locals/data as `kind addr name` rows under `# module:` lines, demangled (a forward ends `-> MODULE.name`); xrefs(import) lists its call sites.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn symbols(
        &self,
        Parameters(SymbolsParams {
            kind,
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<SymbolsParams>,
    ) -> Result<String, ErrorData> {
        let want = kind.map(borer_engine::program::SymbolKind::from);
        let page = Page::new(offset, limit, count_only, 50, 1000)?;
        self.with_program(|p| {
            let (_, total, text) = render::symbols_tsv(
                p,
                &self.analysis_or_empty(),
                want,
                filter.as_deref(),
                page.offset,
                page.limit.n,
            );
            if page.count_only {
                return Ok(format!("# {total} symbols\n"));
            }
            Ok(text)
        })
        .map(|text| page.limit.noted(text))
    }
    /// Lists discovered functions with filtering and paging.
    ///
    /// The count alone is the table's header without its page: `filter=thunk`
    /// counts import thunks and says so, where a bare `functions` read as
    /// though it counted every function.
    ///
    /// # Arguments
    ///
    /// * `FunctionsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Discovered functions as `entry size blocks instrs callers callees src name` rows; filter on name or entry hex, sort=size for the largest first.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn functions(
        &self,
        Parameters(FunctionsParams {
            filter,
            sort,
            offset,
            limit,
            count_only,
        }): Parameters<FunctionsParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 50, 300)?;
        let order = sort.unwrap_or_default().into();
        self.with_analysis(Feature::Discover, |_, a, o| {
            let (shown, _, text) =
                render::functions_tsv(a, o, filter.as_deref(), order, page.offset, page.limit.n);
            if page.count_only {
                let head = text.lines().next().unwrap_or_default();
                let counted = head
                    .strip_prefix(&format!("# showing {shown} of "))
                    .unwrap_or(head);
                return Ok(format!("# {counted}\n"));
            }
            Ok(text)
        })
        .map(|text| page.limit.noted(text))
    }

    /// Returns one function's detail and one page of its basic-block table.
    ///
    /// # Arguments
    ///
    /// * `FunctionDetailParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "One function's detail: name, range, counts, callers/callees and its basic-block table (`start size term successors`, 300 a page by offset).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn function(
        &self,
        Parameters(FunctionDetailParams { address, offset }): Parameters<FunctionDetailParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::function_detail(a, o, entry, offset)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists cross-references to an address or name, or the functions using
    /// a class's field.
    ///
    /// A target that is neither an address nor a name is read as
    /// `Class+offset` ([`class_field`]): the readers and writers of that
    /// field through pointers typed as the class
    /// ([`borer_engine::analysis::classes::typed_field_uses`]), one row per
    /// function: a byte search by offset finds every object's field at that
    /// offset, and a filter on function names misses the unnamed writers.
    ///
    /// # Arguments
    ///
    /// * `XrefsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the target resolves to neither an address
    /// nor a class field.
    #[tool(
        description = "References to an address or name, one `function: site kind, ...` row per referencing function (calls, data reads, pointers in data), same-code functions folded; an import lists calls through its slot; `Class+0x24` lists who touches that field; paged by function (60, max 500).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn xrefs(
        &self,
        Parameters(XrefsParams {
            address,
            offset,
            limit,
            count_only,
        }): Parameters<XrefsParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(
            offset,
            limit,
            count_only,
            render::XREF_ROWS_DEFAULT,
            render::XREF_ROWS_MAX,
        )?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let va = match self.addr(p, &address) {
                Ok(va) => va,
                Err(unknown) => {
                    let (class, offset) = class_field(p, a, o, &address).ok_or_else(|| {
                        format!(
                            "{unknown}; nor is it Class+offset, a field of a class with methods or a vtable"
                        )
                    })?;
                    if let Some(why) = p.refuses(Feature::Decompile) {
                        return Err(format!(
                            "{class}+{offset:#x} is a field, read from decompiled methods: {why}"
                        ));
                    }
                    let uses = borer_engine::analysis::classes::typed_field_uses(p, a, o, &class, offset)
                        .ok_or_else(|| format!("no class {class}"))?;
                    return Ok(borer_engine::analysis::classes::typed_field_uses_tsv(
                        &uses,
                        a,
                        o,
                        offset,
                        page.offset,
                        page.limit.n,
                        page.count_only,
                    ));
                }
            };
            Ok(render::xrefs_tsv(
                a,
                o,
                va,
                page.offset,
                page.limit.n,
                page.count_only,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Renders a class layout recovered from its methods' field accesses,
    /// or with `apply` defines it as a user struct and types each method's
    /// object with it ([`borer_engine::analysis::apply::from_class`]).
    ///
    /// # Arguments
    ///
    /// * `ClassLayoutParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not a class method, nothing
    /// belongs to the class, or the struct to apply is refused.
    #[tool(
        description = "Class layout from its methods: field offset, width, reads/writes, methods, vftable; takes a class name or a method address; apply=Name defines it as a struct typing each method's object (dry-run unless dry_run=false).",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn class_layout(
        &self,
        Parameters(ClassLayoutParams {
            class,
            apply,
            dry_run,
        }): Parameters<ClassLayoutParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let name = match self.function_entry(p, a, &class) {
                Ok(entry) => {
                    let n = borer_engine::analysis::name_of(a, o, entry);
                    borer_engine::analysis::classes::class_of(&n)
                        .ok_or_else(|| format!("{n} is not a class method"))?
                        .to_owned()
                }
                Err(_) => class.clone(),
            };
            let layout =
                borer_engine::analysis::classes::class_layout(p, a, o, &name).ok_or_else(|| {
                    format!(
                        "no function belongs to class {}",
                        borer_engine::text::quoted(&name)
                    )
                })?;
            let Some(apply) = &apply else {
                return Ok(borer_engine::analysis::classes::render_layout(
                    &layout, a, o,
                ));
            };
            let plan = borer_engine::analysis::apply::from_class(p, a, o, &layout, apply)?;
            Ok(self.answer_plan(plan, a, o, dry_run.unwrap_or(true)))
        })
    }

    /// Renders the callee graph from a function as mermaid.
    ///
    /// Walking callers from an import or a data symbol answers who
    /// references it; it has no body to walk callees from.
    ///
    /// # Arguments
    ///
    /// * `CallgraphParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Callgraph from a function as mermaid: callees (callers=true: what reaches it), six per function before the rest is shared out, imports as leaves; a trailing %% line counts what was hidden (max_nodes 30, max 100).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn callgraph(
        &self,
        Parameters(CallgraphParams {
            address,
            max_nodes,
            callers,
        }): Parameters<CallgraphParams>,
    ) -> Result<String, ErrorData> {
        let max = count_param(max_nodes, 30, 100, "max_nodes")?;
        let callers = callers.unwrap_or(false);
        self.with_analysis(Feature::Discover, |p, a, o| {
            let root = match self.function_entry(p, a, &address) {
                Ok(root) => root,
                Err(e) => {
                    let va = self.addr(p, &address)?;
                    if callers && (a.symbol_at(p, va).is_some() || a.xrefs.contains_key(&va)) {
                        va
                    } else {
                        return Err(e);
                    }
                }
            };
            Ok(render::callgraph_mermaid(p, a, o, root, max.n, callers))
        })
        .map(|text| max.noted_with("%%", text))
    }

    /// Answers whether one function reaches another through calls.
    ///
    /// The goal may be an import with no thunk, called through its slot:
    /// it was refused for want of a function containing the slot.
    ///
    /// # Arguments
    ///
    /// * `ReachesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, `from` is not inside a discovered function,
    /// or `to` is neither inside one nor an import.
    #[tool(
        description = "Shortest call chain from one function to another (or to an import, called through its slot or a thunk), or that there is none and how far it looked: answers \"does this ever reach the send / this check\" on a whole binary.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn reaches(
        &self,
        Parameters(ReachesParams { from, to, depth }): Parameters<ReachesParams>,
    ) -> Result<String, ErrorData> {
        let deep = count_param(depth, 24, 64, "depth")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let start = self.function_entry(p, a, &from)?;
            let goal = match self.function_entry(p, a, &to) {
                Ok(goal) => goal,
                Err(e) => {
                    let va = self.addr(p, &to)?;
                    if a.symbol_at(p, va)
                        .is_some_and(|s| s.kind == borer_engine::program::SymbolKind::Import)
                    {
                        va
                    } else {
                        return Err(e);
                    }
                }
            };
            Ok(render::call_path(p, a, o, start, goal, deep.n))
        })
        .map(|text| deep.noted(text))
    }

    /// Renders a function's control-flow graph as mermaid.
    ///
    /// # Arguments
    ///
    /// * `CfgParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Control-flow graph of a function as mermaid: basic blocks (start, terminator) and successor edges, 300 blocks a page by offset; a trailing %% line says when blocks were cut.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn cfg(
        &self,
        Parameters(CfgParams { address, offset }): Parameters<CfgParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::cfg_mermaid(a, o, entry, offset)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }
    /// Returns the pseudo-C of one function.
    ///
    /// `detail` is an enum: anything but `skeleton` used to fall through to
    /// the whole function, so a caller who misspelled it read a complete
    /// decompilation believing it was the outline and was never told
    /// otherwise. Every other choice of words in these tools refuses one it
    /// does not know.
    ///
    /// The answer's second line says what of it was checked against the
    /// binary ([`borer_engine::analysis::decompile::checked_header`]); only
    /// this rendering carries it, never the text other readers parse.
    ///
    /// # Arguments
    ///
    /// * `DecompileParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not inside a discovered function,
    /// or the decompiler produces nothing.
    #[tool(
        description = "Pseudo-C with locals local_N/arg_N, named calls and if/else/while/for/switch; /* asm */ marks unmodeled code, goto unproven flow. Line 2 says what the binary checked, `// next:` lines what to read next.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn decompile(
        &self,
        Parameters(DecompileParams {
            address,
            detail,
            filter,
            offset,
            limit,
        }): Parameters<DecompileParams>,
    ) -> Result<String, ErrorData> {
        use borer_engine::analysis::decompile;
        self.with_program(|p| {
            if let Some(why) = p.refuses(Feature::Decompile) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            let entry = self.function_entry(p, &a, &address)?;
            let o = self.overlay();
            let header = decompile_header(p, &a, &o, entry);
            let text = decompile::decompile_named(p, &a, &o, entry)
                .ok_or_else(|| format!("decompilation failed at {entry:#x}"))?;
            let text = match detail.unwrap_or_default() {
                Detail::Full => marked(p, &a, &o, entry, &text),
                Detail::Skeleton => decompile::skeleton(&text),
            };
            let text = decompile::with_header(&text, header.as_deref());
            Ok(window(&text, filter.as_deref(), offset, limit))
        })
    }

    /// Returns the pseudo-C of several functions, decompiled in parallel and
    /// emitted in discovery order.
    ///
    /// # Arguments
    ///
    /// * `DecompileBatchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Pseudo-C for many functions: filter on name or entry hex, max_functions (10, max 50); 6000 chars per function, 40000 total.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn decompile_batch(
        &self,
        Parameters(DecompileBatchParams {
            filter,
            max_functions,
        }): Parameters<DecompileBatchParams>,
    ) -> Result<String, ErrorData> {
        /// Longest text kept per function.
        const PER_FN: usize = 6_000;
        /// Longest total output.
        const TOTAL: usize = 40_000;
        let cap = count_param(max_functions, 10, 50, "max_functions")?;
        let max = cap.n;
        let filter = Filter::new(filter.as_deref());
        self.with_program(|p| {
            if let Some(why) = p.refuses(Feature::Decompile) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            let o = self.overlay();
            let matches = |f: &&borer_engine::analysis::Function| match filter.needle() {
                Some(q) => {
                    borer_engine::analysis::name_of(&a, &o, f.entry)
                        .to_lowercase()
                        .contains(q)
                        || format!("{:x}", f.entry).contains(q.strip_prefix("0x").unwrap_or(q))
                }
                None => true,
            };
            let all: Vec<u64> = a
                .functions
                .iter()
                .filter(matches)
                .map(|f| f.entry)
                .collect();
            let total_matching = all.len();
            let classes: Vec<(u64, Vec<u64>)> =
                a.dedupe_clones(&all).into_iter().take(max).collect();
            let matched: Vec<u64> = classes.iter().map(|(e, _)| *e).collect();
            let skipped: std::collections::BTreeMap<u64, Vec<u64>> = classes.into_iter().collect();
            // PERF: functions decompile independently; fan out, then emit in order.
            let texts: Vec<(u64, String)> = matched
                .par_iter()
                .map(|&entry| {
                    (
                        entry,
                        borer_engine::analysis::decompile::decompile_named(p, &a, &o, entry)
                            .unwrap_or_else(|| format!("// decompilation failed at {entry:#x}")),
                    )
                })
                .collect();
            let mut spent = 0usize;
            let printed = texts
                .iter()
                .take_while(|(_, text)| {
                    let room = spent < TOTAL;
                    spent += text.len().min(PER_FN);
                    room
                })
                .count();
            // PERF: only a cut function's header is read, a check each, in
            // parallel: the note under its cut counts lines as decompile
            // numbers them, header included.
            let headers: std::collections::BTreeMap<u64, usize> = texts[..printed]
                .par_iter()
                .filter(|(_, text)| text.len() > PER_FN)
                .map(|(entry, _)| {
                    let lines = decompile_header(p, &a, &o, *entry).map_or(0, |h| h.lines().count());
                    (*entry, lines)
                })
                .collect();
            // INVARIANT: the header counts the functions the body prints and
            // the clones of those alone, so a body the total cap cut short
            // never claims the functions it left out.
            let mut body = String::new();
            let (mut shown, mut folded) = (0usize, 0usize);
            for (entry, text) in &texts[..printed] {
                let name = borer_engine::analysis::name_of(&a, &o, *entry);
                let same = skipped.get(entry).filter(|c| !c.is_empty());
                let clones = same.map_or(String::new(), |c| {
                    let named: Vec<String> = c
                        .iter()
                        .take(6)
                        .map(|e| borer_engine::analysis::name_of(&a, &o, *e))
                        .collect();
                    let more = c.len().saturating_sub(6);
                    if more > 0 {
                        format!(" (same code: {}, +{more} more)", named.join(", "))
                    } else {
                        format!(" (same code: {})", named.join(", "))
                    }
                });
                let _ = write!(body, "
==== {name} @ {entry:#x} ===={clones}
");
                if text.len() > PER_FN {
                    body.push_str(&truncated(
                        text,
                        PER_FN,
                        *entry,
                        headers.get(entry).copied().unwrap_or(0),
                    ));
                } else {
                    body.push_str(text);
                }
                shown += 1;
                folded += same.map_or(0, Vec::len);
            }
            let mut out = format!(
                "# decompiled {shown} of {total_matching} matching functions (max {max}){}
",
                if folded > 0 {
                    format!("; {folded} more are clones of these")
                } else {
                    String::new()
                }
            );
            out.push_str(&body);
            let cut = texts.len().saturating_sub(shown);
            if let Some((first, _)) = texts.get(shown) {
                let _ = writeln!(
                    out,
                    "# total output cap of {TOTAL} chars reached: {cut} more decompiled, not shown, the first {} @ {first:#x}; narrow the filter or lower max_functions",
                    borer_engine::analysis::name_of(&a, &o, *first)
                );
            }
            Ok(out)
        })
        .map(|text| cap.noted(text))
    }
    /// Searches every section, then the bytes no section maps, for a byte
    /// pattern or a text substring.
    ///
    /// A text query of spaces or a tab is text to find; only a byte
    /// pattern with no token is empty.
    ///
    /// # Arguments
    ///
    /// * `SearchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the query is empty, the pattern does not
    /// parse, or the kind is unknown.
    #[tool(
        description = "Search the whole file for bytes (AOB hex, ?? wildcards) or kind=text substring; hits as `function: va va ...` rows, `off=<n>` where unmapped; offset/limit (200, max 500).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn search(
        &self,
        Parameters(SearchParams {
            query,
            kind,
            offset,
            limit,
            count_only,
        }): Parameters<SearchParams>,
    ) -> Result<String, ErrorData> {
        let kind = kind.unwrap_or_default();
        let offset = offset.unwrap_or(0);
        let limit = count_param(limit, 200, borer_engine::search::HITS_MAX, "limit")?;
        let count_only = count_only.unwrap_or(false);
        let empty = match kind {
            SearchKind::Bytes => query.trim().is_empty(),
            SearchKind::Text => query.is_empty(),
        };
        if empty {
            return Err(err_params(
                "the query is empty: give hex bytes with ?? wildcards, or kind=text and a substring",
            ));
        }
        self.with_program(|p| {
            let mut hits = match kind {
                SearchKind::Bytes => {
                    let pattern = borer_engine::search::parse_pattern(&query).ok_or_else(|| {
                        format!(
                            "bad byte pattern {}: use hex tokens or ??",
                            borer_engine::text::quoted(&query)
                        )
                    })?;
                    borer_engine::search::find_bytes(p, &pattern, offset)
                }
                SearchKind::Text => borer_engine::search::find_text(p, &query, offset),
            };
            hits.hits.truncate(limit.n);
            let a = self.analysis_or_empty();
            let o = self.overlay();
            Ok(render_hits(&hits, offset, count_only, (&a, &o)))
        })
        .map(|text| limit.noted(text))
    }

    /// Names a function or data address in the overlay (dry-run by default).
    ///
    /// # Arguments
    ///
    /// * `SetNameParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address does not resolve, or no section
    /// holds it.
    #[tool(
        description = "Name a function (any address inside it) or a data global in the overlay, not the binary; dry-run unless dry_run=false.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn set_name(
        &self,
        Parameters(SetNameParams {
            address,
            name,
            dry_run,
        }): Parameters<SetNameParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        must_fit_a_row(&name, Annotation::Name)?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let va = self.addr(p, &address)?;
            must_be_in_a_section(p, va, Annotation::Name)?;
            let target = a.function_at(va).map_or(va, |f| f.entry);
            let old = borer_engine::analysis::name_of(a, o, target);
            let what = if a.function(target).is_some() {
                "function"
            } else {
                "data"
            };
            let numeric = parse_addr(&name).map_or_else(String::new, |n| {
                format!(
                    "
# note: '{name}' also reads as the number {n:#x}; an address argument finds the name first, and 0x-prefixed text is always an address"
                )
            });
            if dry {
                return Ok(format!(
                    "dry-run: would set name of {what} {target:#x} ({old}) to '{name}'. pass dry_run=false to apply.{numeric}"
                ));
            }
            write_lock(&self.overlay)
                .names
                .insert(target, name.clone());
            self.names_changed();
            Ok(format!("renamed {what} {target:#x}: {old} -> {name}{numeric}"))
        })
    }

    /// Attaches a comment to an address in the overlay (dry-run by default).
    ///
    /// # Arguments
    ///
    /// * `SetCommentParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address does not resolve, or no section
    /// holds it.
    #[tool(
        description = "Comment an address in the overlay; dry-run unless dry_run=false.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn set_comment(
        &self,
        Parameters(SetCommentParams {
            address,
            comment,
            dry_run,
        }): Parameters<SetCommentParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        must_fit_a_row(&comment, Annotation::Comment)?;
        self.with_program(|p| {
            let va = self.addr(p, &address)?;
            must_be_in_a_section(p, va, Annotation::Comment)?;
            if dry {
                return Ok(format!(
                    "dry-run: would set comment at {va:#x}. pass dry_run=false to apply."
                ));
            }
            write_lock(&self.overlay)
                .comments
                .insert(va, comment.clone());
            self.names_changed();
            Ok(format!("comment set at {va:#x}"))
        })
    }

    /// Defines a user type, applies one at an address, states a function's
    /// prototype or one of its variables.
    ///
    /// `name` with `fields` defines a struct; `name` with `values` defines
    /// an enum; `name` with `type` alone defines a typedef. `address` with
    /// `type` applies the type at that data global: the decompiler types the
    /// variable it renders there, so a `Player *` names every field read
    /// through it (`g->hp` at the width the field states) and a `State`
    /// applied at a global names every constant compared with it. At a
    /// function, `type` is its prototype as C
    /// ([`borer_engine::analysis::protos::Proto`]), which its signature,
    /// its body and every call to it follow; with `var` (`a1`, `local_58`,
    /// or a name stated before), `name` and an optional `type` name and
    /// type that variable. `type` alone is C declarations, laid out by the
    /// binary's ABI ([`BorerServer::declare_c`]). Everything is validated
    /// before anything is written: types the language does not spell,
    /// references to names nothing defines, fields that overlap, a size
    /// that does not cover the last field and an offset assertion that
    /// fails are refused with a message naming the offender.
    ///
    /// # Arguments
    ///
    /// * `SetTypeParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, a definition, an application, a prototype
    /// or a variable is refused, or the address does not resolve or no
    /// section holds it.
    #[tool(
        description = "Define a user type and/or apply one: at a data global, `type` types it (a `Player *` names the fields read through it, an enum the constants compared with it); at a function, `type` is its C prototype, or with `var` (a1, local_58) names/types that variable; `type` alone defines C structs. Dry-run unless dry_run=false.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]

    fn set_type(
        &self,
        Parameters(SetTypeParams {
            name,
            fields,
            values,
            size,
            address,
            r#type: ty,
            var,
            dry_run,
        }): Parameters<SetTypeParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        if let (None, None, None, None, None, None, Some(decl)) =
            (&name, &address, &var, &fields, &values, size, &ty)
        {
            return self.declare_c(decl, dry);
        }
        if name.is_none() && address.is_none() {
            return Err(err_params(
                "set_type needs `name` (+ `fields`, `values` or `type`) to define a type, `address` + `type` to apply one, or `type` alone holding C declarations",
            ));
        }
        for text in name
            .iter()
            .chain(&ty)
            .chain(&var)
            .chain(fields.iter().flatten())
            .chain(values.iter().flatten())
        {
            must_fit_a_row(text, Annotation::Type)?;
        }
        self.with_analysis(Feature::Discover, |p, a, o| {
            let word: u64 = if p.is_64 { 8 } else { 4 };
            // A function's address states its prototype, or with `var` one
            // of its variables, where a data global's applies a type.
            let function = match &address {
                Some(text) => {
                    let va = self.addr(p, text)?;
                    must_be_in_a_section(p, va, Annotation::Type)?;
                    a.function_at(va).map(|f| f.entry)
                }
                None => None,
            };
            if let Some(var) = &var {
                let entry = function.ok_or_else(|| {
                    "`var` names a variable of a function: give the function's `address`".to_owned()
                })?;
                let (key, stated) = plan_var(p, o, entry, var, name.as_deref(), ty.as_deref())?;
                let (stack, shadow) = frame_words(p);
                let what = format!(
                    "{} of {} ({entry:#x}) {}",
                    key.spell(stack, shadow),
                    borer_engine::analysis::name_of(a, o, entry),
                    stated.spell()
                );
                if dry {
                    return Ok(format!(
                        "dry-run: would name {what}; decompile then renders it so. pass dry_run=false to apply."
                    ));
                }
                write_lock(&self.overlay)
                    .vars
                    .entry(entry)
                    .or_default()
                    .insert(key, stated);
                self.names_changed();
                return Ok(format!("named {what}"));
            }
            // The definition half: built and validated against the types
            // already in the overlay before anything is written.
            let defined = match (&name, &fields, &values) {
                (Some(n), Some(fs), vs) if !fs.is_empty() => {
                    if vs.is_some() {
                        return Err(format!(
                            "type {n} states both fields and values; a struct takes fields, an enum values"
                        ));
                    }
                    let mut stated: Vec<(u64, String, borer_engine::analysis::utypes::TypeExpr)> =
                        Vec::with_capacity(fs.len());
                    for f in fs {
                        let (off, stated_name, ty) = field_of(f)?;
                        let ty = borer_engine::analysis::utypes::parse_type(ty)
                            .map_err(|e| format!("field {stated_name}: {e}"))?;
                        let off = off
                            .strip_prefix("0x")
                            .map_or_else(
                                || off.parse::<u64>().ok(),
                                |h| u64::from_str_radix(h, 16).ok(),
                            )
                            .ok_or_else(|| {
                                format!("field {stated_name}: offset {off} is not a number")
                            })?;
                        stated.push((off, stated_name.to_owned(), ty));
                    }
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_struct(n, size, &stated, &o.types, word)
                            .map_err(|e| e.to_string())?,
                    ))
                }
                (Some(n), Some(_), _) => {
                    return Err(format!(
                        "struct {n} states no fields; give fields, `values` for an enum, or a `type` for a typedef"
                    ));
                }
                (Some(n), _, Some(vs)) if !vs.is_empty() => {
                    let mut stated: Vec<(u64, String)> = Vec::with_capacity(vs.len());
                    for v in vs {
                        let Some((stated_name, value)) = v.split_once(':') else {
                            return Err(format!("value {v} is not name:value"));
                        };
                        let value = value
                            .strip_prefix("0x")
                            .map_or_else(
                                || value.parse::<u64>().ok(),
                                |h| u64::from_str_radix(h, 16).ok(),
                            )
                            .ok_or_else(|| {
                                format!("value {stated_name}: {value} is not a number")
                            })?;
                        stated.push((value, stated_name.to_owned()));
                    }
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_enum(
                            n,
                            size.unwrap_or(4),
                            &stated,
                        )
                        .map_err(|e| e.to_string())?,
                    ))
                }
                (Some(n), _, Some(_)) => {
                    return Err(format!(
                        "enum {n} states no values; give them as name:value"
                    ));
                }
                (Some(n), None, None) if function.is_some() => {
                    return Err(format!(
                        "at a function `type` is its prototype; define typedef {n} in a call of its own"
                    ));
                }
                (Some(n), None, None) => {
                    let target = ty.as_deref().ok_or_else(|| {
                        format!("typedef {n} needs the `type` it stands for")
                    })?;
                    let parsed = borer_engine::analysis::utypes::parse_type(target)
                        .map_err(|e| e.to_string())?;
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_alias(n, &parsed, &o.types, word)
                            .map_err(|e| e.to_string())?,
                    ))
                }
                (None, _, _) => None,
            };
            // The application half: a data global's type, resolved and in
            // a section, or a function's prototype.
            let applied = match &address {
                Some(text) if function.is_none() => {
                    let spelled = ty.as_deref().ok_or_else(|| {
                        "applying a type needs the `type` to apply".to_owned()
                    })?;
                    let parsed = borer_engine::analysis::utypes::parse_type(spelled)
                        .map_err(|e| e.to_string())?;
                    let va = self.addr(p, text)?;
                    Some((va, parsed))
                }
                Some(_) | None => None,
            };
            let stated = match function {
                Some(entry) => {
                    let decl = ty.as_deref().ok_or_else(|| {
                        "at a function `type` is its prototype: `int f(Player *p, uint32_t n)`"
                            .to_owned()
                    })?;
                    // INVARIANT: a plain type at a function is a type for a
                    // data global given the wrong address, and says so.
                    let proto =
                        borer_engine::analysis::protos::Proto::parse(decl).map_err(|e| {
                            if decl.contains('(') {
                                e.to_string()
                            } else {
                                format!(
                                    "{entry:#x} is inside {}; types apply to data globals, and at a function `type` is its prototype (`int f(Player *p)`)",
                                    borer_engine::analysis::name_of(a, o, entry)
                                )
                            }
                        })?;
                    if o.prototypes.len() >= borer_engine::analysis::protos::PROTOTYPES_MAX
                        && !o.prototypes.contains_key(&entry)
                    {
                        return Err(format!(
                            "the overlay states {} prototypes, the most it holds",
                            o.prototypes.len()
                        ));
                    }
                    Some((entry, proto))
                }
                None => None,
            };
            // INVARIANT: an application that also defines its type resolves
            // against the defined-and-current set, so both halves of one
            // call agree.
            let mut types = o.types.clone();
            if let Some((n, ty)) = &defined {
                types.insert(n.clone(), ty.clone());
            }
            let applied = applied
                .map(|(va, ty)| {
                    borer_engine::analysis::utypes::width_of(&types, &ty, word).ok_or_else(|| {
                        format!(
                            "the type {} names nothing defined; set_type(name=..., fields=[...]) first",
                            ty.spell()
                        )
                    }).map(|w| (va, ty, w))
                })
                .transpose()?;
            let mut done: Vec<String> = Vec::new();
            let mut would: Vec<String> = Vec::new();
            if let Some((n, ty)) = &defined {
                match ty {
                    borer_engine::analysis::utypes::UserType::Struct(s) => {
                        done.push(format!(
                            "defined struct {n}: {} field(s), {:#x} byte(s)",
                            s.fields.len(),
                            s.size
                        ));
                        would.push(format!(
                            "define struct {n}: {} field(s), {:#x} byte(s)",
                            s.fields.len(),
                            s.size
                        ));
                    }
                    borer_engine::analysis::utypes::UserType::Enum(e) => {
                        done.push(format!(
                            "defined enum {n}: {} value(s), {:#x} byte(s)",
                            e.values.len(),
                            e.size
                        ));
                        would.push(format!(
                            "define enum {n}: {} value(s), {:#x} byte(s)",
                            e.values.len(),
                            e.size
                        ));
                    }
                    borer_engine::analysis::utypes::UserType::Alias(inner) => {
                        done.push(format!("defined typedef {n}: {}", inner.spell()));
                        would.push(format!("define typedef {n}: {}", inner.spell()));
                    }
                }
            }
            if let Some((va, ty, width)) = &applied {
                // An applied enum names the constants compared with the
                // global; every other type names the fields read through it.
                let renders = if borer_engine::analysis::utypes::named_enum(&types, ty).is_some() {
                    "names its values"
                } else {
                    "names its fields"
                };
                done.push(format!(
                    "applied {} at {va:#x} ({width} byte(s)); decompile {renders}",
                    ty.spell()
                ));
                would.push(format!(
                    "apply {} at {va:#x} ({width} byte(s)); decompile then {renders}",
                    ty.spell()
                ));
            }
            let mut note = String::new();
            if let Some((entry, proto)) = &stated {
                let fname = borer_engine::analysis::name_of(a, o, *entry);
                done.push(format!("stated {fname} ({entry:#x}) as {}", proto.spell()));
                would.push(format!(
                    "state {fname} ({entry:#x}) as {}; decompile then renders its signature, its body and every call to it by it",
                    proto.spell()
                ));
                let bits = u8::try_from(word * 8).unwrap_or(64);
                let unknown: Vec<String> = proto
                    .ret
                    .iter()
                    .chain(proto.params.iter().map(|q| &q.ty))
                    .filter(|t| t.pass(&types, bits, p.format).is_none())
                    .map(borer_engine::analysis::protos::CType::spell)
                    .collect();
                if !unknown.is_empty() {
                    note = format!(
                        "\n# note: {} names no user type or C type word borer knows, so it passes as a word",
                        unknown.join(", ")
                    );
                }
            }
            if dry {
                return Ok(format!(
                    "dry-run: would {}. pass dry_run=false to apply.{note}",
                    would.join("; ")
                ));
            }
            let mut overlay = write_lock(&self.overlay);
            if let Some((n, ty)) = defined {
                overlay.types.insert(n, ty);
            }
            if let Some((va, ty, _)) = applied {
                overlay.applied.insert(va, ty);
            }
            if let Some((entry, proto)) = stated {
                overlay.prototypes.insert(entry, proto);
            }
            drop(overlay);
            self.names_changed();
            Ok(format!("{}{note}", done.join("; ")))
        })
    }

    /// Lists the user types and where they are applied.
    ///
    /// # Arguments
    ///
    /// * `TypesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When `limit` is zero.
    #[tool(
        description = "List user-defined types and where they are applied; filter pages like every list.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn types(
        &self,
        Parameters(TypesParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<TypesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(
            offset,
            limit,
            count_only,
            50,
            borer_engine::analysis::utypes::TYPES_ROWS_MAX,
        )?;
        let o = read_lock(&self.overlay);
        let stated = borer_engine::analysis::protos::rows(&o.prototypes, &o.vars);
        let (_, total, table) = borer_engine::analysis::utypes::list_tsv(
            &o.types,
            &o.applied,
            &stated,
            filter.as_deref(),
            page.offset,
            page.limit.n,
        );
        let (types, applied) = (o.types.len(), o.applied.len());
        drop(o);
        if page.count_only {
            return Ok(format!(
                "# {total} rows ({types} type(s), {applied} applied)\n"
            ));
        }
        Ok(page.limit.noted(table))
    }

    /// Saves the overlay to a JSON project file.
    ///
    /// # Arguments
    ///
    /// * `SaveProjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded; internal error when the file cannot
    /// be written.
    #[tool(
        description = "Save the annotation overlay (names, comments, types) to a JSON project file, keyed to the binary by its SHA-256.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn save_project(
        &self,
        Parameters(SaveProjectParams { path }): Parameters<SaveProjectParams>,
    ) -> Result<String, ErrorData> {
        let program = self.require_loaded()?;
        let pf = borer::project::ProjectFile::from_overlay(
            &program.path.display().to_string(),
            Some(borer::project::identity(&program.bytes)),
            &read_lock(&self.overlay),
        );
        pf.save(&path).map_err(err_internal)?;
        let vars: usize = pf.vars.values().map(std::collections::BTreeMap::len).sum();
        let stated = if pf.prototypes.is_empty() && vars == 0 {
            String::new()
        } else {
            format!(" + {} prototypes + {vars} variables", pf.prototypes.len())
        };
        Ok(format!(
            "saved {} names + {} comments + {} types{stated} to {path}",
            pf.names.len(),
            pf.comments.len(),
            pf.types.len()
        ))
    }

    /// Loads a JSON project file into the overlay, replacing it.
    ///
    /// A project's addresses belong to the binary it was saved for, and
    /// loading replaces every annotation the session holds, so a project
    /// saved for another binary ([`borer::project::ProjectFile::identify`]:
    /// by its SHA-256, or by its path in a project older than the hash) is
    /// refused, leaving the overlay as it was, unless `force` says to load
    /// it anyway; a rebuild is pointed at `borer://carry`, which moves the
    /// names to it, and a project judged by path says so. Either way the
    /// annotations `set_name`, `set_comment` and
    /// `set_type` would refuse of the loaded binary, at an address no
    /// section holds or with blank text, are skipped and listed
    /// ([`borer::project::keep_placeable`]), and the counts said are of what
    /// the overlay then holds.
    ///
    /// # Arguments
    ///
    /// * `LoadProjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded, the file does not parse or
    /// states something the overlay cannot hold, or it was saved for
    /// another binary and `force` is not set.
    #[tool(
        description = "Load a JSON project file into the annotation overlay, replacing it. A project saved for another binary (by SHA-256) is refused unless force=true; names, comments and types at addresses no section holds, or blank, are skipped and listed.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn load_project(
        &self,
        Parameters(LoadProjectParams { path, force }): Parameters<LoadProjectParams>,
    ) -> Result<String, ErrorData> {
        /// Most left-out annotations the answer names before counting the rest.
        const LEFT_OUT_SHOWN: usize = 8;
        /// Hex digits of a SHA-256 a message shows.
        const HASH_SHOWN: usize = 12;
        let program = self.require_loaded()?;
        let pf = borer::project::ProjectFile::load(&path).map_err(err_params)?;
        let identity = pf.identify(&program);
        let foreign = matches!(identity, Identity::Other | Identity::OtherPath);
        let saved_for = borer_engine::text::short_path(&pf.program);
        let loaded_path = program.path.display().to_string();
        if foreign && !force.unwrap_or(false) {
            let short = |hash: &str| hash.chars().take(HASH_SHOWN).collect::<String>();
            return Err(err_params(match &pf.sha256 {
                Some(saved) => format!(
                    "the project was saved for another build (sha-256 {}... at {saved_for}), but {} is sha-256 {}...; nothing was loaded. Its addresses belong to that build: load it with this project, then borer://carry/{} carries the names to this one; or pass force=true to load the project anyway",
                    short(&borer_engine::text::one_line(saved)),
                    borer_engine::text::short_path(&loaded_path),
                    short(&borer::project::identity(&program.bytes)),
                    borer_engine::text::short_path(&loaded_path.replace('\\', "/"))
                ),
                None => format!(
                    "the project was saved for {saved_for}, but {} is loaded; nothing was loaded. Its addresses belong to that binary: load it first, or pass force=true to load the project anyway",
                    borer_engine::text::short_path(&loaded_path)
                ),
            }));
        }
        let mut loaded = pf.to_overlay().map_err(err_params)?;
        let left_out = borer::project::keep_placeable(&mut loaded, &program);
        let vars: usize = loaded
            .vars
            .values()
            .map(std::collections::BTreeMap::len)
            .sum();
        let stated = if loaded.prototypes.is_empty() && vars == 0 {
            String::new()
        } else {
            format!(
                " + {} prototypes + {vars} variables",
                loaded.prototypes.len()
            )
        };
        let mut said = format!(
            "loaded {} names + {} comments + {} types + {} applied{stated}\n",
            loaded.names.len(),
            loaded.comments.len(),
            loaded.types.len(),
            loaded.applied.len()
        );
        if !left_out.is_empty() {
            let shown = left_out.len().min(LEFT_OUT_SHOWN);
            let _ = writeln!(
                said,
                "# skipped {total} (showing {shown} of {total}): {}",
                left_out[..shown].join(", "),
                total = left_out.len()
            );
        }
        if foreign {
            let _ = writeln!(
                said,
                "# forced: the project was saved for {saved_for}, so its names may sit on other code here"
            );
        }
        if matches!(identity, Identity::PathOnly | Identity::OtherPath) {
            said.push_str("# the project names its binary by path alone (saved before projects recorded its sha-256), so a rebuild at that path loads it too; save_project records the hash\n");
        }
        *write_lock(&self.overlay) = loaded;
        self.names_changed();
        Ok(said)
    }

    /// Lists the overlay's entries: names, then findings, then open
    /// questions, a page at a time.
    ///
    /// A comment opening with a question mark is a hypothesis, not a
    /// finding. Separating the two is what makes the overlay a ledger an
    /// agent can return to: a conclusion it proved is worth building on,
    /// and one it guessed at is worth checking before it does. The ledger
    /// grows with the session, so it pages like every list: the header
    /// says `showing N of M` of the rows the filter keeps.
    ///
    /// # Arguments
    ///
    /// * `AnnotationsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When `limit` is zero.
    #[tool(
        description = "List the annotation overlay: names, findings and open questions (comments opening with ?); filter pages like every list.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn annotations(
        &self,
        Parameters(AnnotationsParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<AnnotationsParams>,
    ) -> Result<String, ErrorData> {
        /// Rows a page holds when `limit` is absent.
        const ROWS_DEFAULT: usize = 200;
        /// Most rows a page holds.
        const ROWS_MAX: usize = 1000;
        let page = Page::new(offset, limit, count_only, ROWS_DEFAULT, ROWS_MAX)?;
        let filter = Filter::new(filter.as_deref());
        let o = read_lock(&self.overlay);
        let (open, settled): (Vec<_>, Vec<_>) = o
            .comments
            .iter()
            .partition(|(_, c)| c.trim_start().starts_with('?'));
        let rows: Vec<String> = o
            .names
            .iter()
            .map(|(va, name)| format!("{:<12} name: {name}", format!("{va:#x}")))
            .chain(
                settled
                    .iter()
                    .map(|(va, c)| format!("{:<12} found: {c}", format!("{va:#x}"))),
            )
            .chain(open.iter().map(|(va, c)| {
                let claim = c.trim_start().trim_start_matches('?').trim_start();
                format!("{:<12} open:  {claim}", format!("{va:#x}"))
            }))
            .filter(|row| filter.accepts(row))
            .collect();
        let counts = format!(
            "{} names, {} findings, {} open question(s)",
            o.names.len(),
            settled.len(),
            open.len()
        );
        let total = rows.len();
        if page.count_only {
            return Ok(format!("# {total} annotations ({counts})\n"));
        }
        let shown: Vec<&String> = rows.iter().skip(page.offset).take(page.limit.n).collect();
        let mut out = format!(
            "# showing {} of {total} annotations ({counts})\n# addr annotation\n",
            shown.len()
        );
        for row in shown {
            let _ = writeln!(out, "{row}");
        }
        if !o.comments.is_empty() {
            out.push_str(
                "# a comment opening with ? is an open question; drop the ? once it is proved\n",
            );
        }
        Ok(page.limit.noted(out))
    }

    /// Reads a `borer://` resource by URI, for an agent whose host has no
    /// way to read MCP resources: without it the resources (scenarios,
    /// grep, taint, emulate and the rest) are out of its reach.
    ///
    /// The answer is [`BorerServer::read_uri`]'s, which `resources/read`
    /// sends too: the same text, the same errors, and one answer memory, so
    /// a URI read one way is remembered for the other.
    ///
    /// # Arguments
    ///
    /// * `QueryParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// As `resources/read`: resource-not-found for an unknown URI, naming
    /// the resources nearest it; otherwise the resource's own error.
    #[tool(
        description = "Read a borer:// resource as resources/read does (same text, errors and memory), for hosts that cannot read resources, e.g. borer://triage or borer://scenarios/0x401000/a1=0..8; a template read bare (borer://emulate) says its grammar; !offset=N!limit=N page a listing; borer://help lists all.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn query(
        &self,
        Parameters(QueryParams { uri }): Parameters<QueryParams>,
    ) -> Result<String, ErrorData> {
        self.read_uri(&uri).map(|(_, text)| text)
    }

    /// Runs an agent's Rhai script against the loaded program in borer's
    /// sandbox, answering its `query` calls from the resources.
    ///
    /// The script runs on a snapshot of the analysis and the overlay and
    /// holds no lock while it runs, so each `query` takes the locks any
    /// request does. A `query` of `borer://script/...` is refused, since a
    /// script that ran scripts could recurse without end, and so is one
    /// saying `dry_run=false` (a layout applied), since a script only
    /// proposes and `dry_run` here decides what is applied. A failed script
    /// still answers what it printed and proposed before its error, and
    /// applies nothing; a proposal the listings could not show, or at an
    /// address no section holds, is skipped and counted.
    ///
    /// # Arguments
    ///
    /// * `ScriptParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or borer does not disassemble its
    /// architecture; a failing script is an answer, not an error.
    #[tool(
        description = "Run a sandboxed Rhai script over the loaded program, for what no single tool answers: what it printed, then the names and comments it proposed (dry-run unless dry_run=false). print(help()) lists every call; query(uri) reads any borer:// resource, rows(uri) its table.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = false
        )
    )]
    fn script(
        &self,
        Parameters(ScriptParams { code, dry_run }): Parameters<ScriptParams>,
    ) -> Result<String, ErrorData> {
        let program = self.require_loaded()?;
        if let Some(why) = program.refuses(Feature::Disasm) {
            return Err(err_params(why));
        }
        let analysis = self.analysis_or_empty();
        let server = self.clone();
        let query: borer_engine::script::Query = std::rc::Rc::new(move |uri: &str| {
            if uri.starts_with("borer://script/") {
                return Err(
                    "a script cannot query borer://script/...: scripts do not run scripts"
                        .to_owned(),
                );
            }
            if uri.contains("dry_run=false") {
                return Err(
                    "a script proposes and applies nothing through query: drop dry_run=false"
                        .to_owned(),
                );
            }
            server
                .listing(&paging::Asked::read(uri)?)
                .map_err(|e| e.message.into_owned())
        });
        let run = borer_engine::script::run_with(
            Arc::clone(&program),
            Arc::clone(&analysis),
            Arc::new(self.overlay()),
            &code,
            &[],
            Some(query),
        );
        let mut text = borer_engine::script::run_tsv(&run);
        let proposed = run.names.len() + run.comments.len();
        if proposed == 0 {
            return Ok(text);
        }
        if run.error.is_some() {
            text.push_str("# nothing applied: the script failed\n");
            return Ok(text);
        }
        if dry_run.unwrap_or(true) {
            text.push_str("# dry-run: pass dry_run=false to apply these\n");
            return Ok(text);
        }
        let (mut named, mut commented) = (HashSet::new(), HashSet::new());
        let mut skipped = 0usize;
        {
            let mut overlay = write_lock(&self.overlay);
            for (at, name) in &run.names {
                if must_fit_a_row(name, Annotation::Name).is_ok()
                    && must_be_in_a_section(&program, *at, Annotation::Name).is_ok()
                {
                    let target = analysis.function_at(*at).map_or(*at, |f| f.entry);
                    overlay.names.insert(target, name.clone());
                    named.insert(target);
                } else {
                    skipped += 1;
                }
            }
            for (at, comment) in &run.comments {
                if must_fit_a_row(comment, Annotation::Comment).is_ok()
                    && must_be_in_a_section(&program, *at, Annotation::Comment).is_ok()
                {
                    overlay.comments.insert(*at, comment.clone());
                    commented.insert(*at);
                } else {
                    skipped += 1;
                }
            }
        }
        if !named.is_empty() || !commented.is_empty() {
            self.names_changed();
        }
        let _ = writeln!(
            text,
            "# applied names at {} addresses and comments at {}, the last proposal for an address winning; {skipped} skipped (empty, unprintable, or in no section)",
            named.len(),
            commented.len()
        );
        Ok(text)
    }
}

/// The message a caught panic carries, for an answer that says a tool
/// faulted.
///
/// # Arguments
///
/// * `e` - The panic's payload, as `catch_unwind` hands it back.
///
/// # Returns
///
/// The payload's text, or `no message` when it is neither `&str` nor
/// `String`.
fn fault_text(e: &(dyn std::any::Any + Send)) -> String {
    e.downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| e.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "no message".to_owned())
}

/// Percent-decodes a resource URI argument.
///
/// A URI carries an argument in a path segment, where `,`, `=` and `:` are
/// reserved, so a correct client may send them escaped: an experiment spec
/// like `0x1400,rax=1` can arrive as `0x1400%2Crax%3D1`. The escaped form is
/// canonical, so decoding it is what makes those URIs resolve. A `%` that
/// does not begin a valid escape is left alone, so a name containing one
/// still resolves, and bytes that are not UTF-8 leave the text as it came.
///
/// # Arguments
///
/// * `text` - The raw path segment.
///
/// # Returns
///
/// The decoded argument.
fn percent_decode(text: &str) -> String {
    if !text.contains('%') {
        return text.to_owned();
    }
    let raw = text.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let escape = if raw[i] == b'%' {
            let hex = |k: usize| {
                raw.get(k)
                    .copied()
                    .map(char::from)
                    .and_then(|c| c.to_digit(16))
            };
            hex(i + 1).zip(hex(i + 2))
        } else {
            None
        };
        if let Some((high, low)) = escape {
            out.push(u8::try_from(high * 16 + low).unwrap_or(b'%'));
            i += 3;
        } else {
            out.push(raw[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_owned())
}

/// Walks a program's strings of one encoding, without the session's cache.
///
/// A .NET assembly's user strings are read whole from its `#US` heap in
/// place of the UTF-16LE runs the walk finds there
/// ([`borer_engine::clr::split_user_strings`]).
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `encoding` - Which walks: ASCII, UTF-16LE, or both merged by offset.
/// * `min` - Shortest run kept.
///
/// # Returns
///
/// The rows in offset order.
fn walk_rows(p: &Program, encoding: StringEncoding, min: usize) -> Vec<StringRow> {
    let ascii = || {
        find_ascii_spans(&p.bytes, min)
            .into_iter()
            .map(StringRow::Span)
    };
    let wide = || {
        let (spans, user) =
            borer_engine::clr::split_user_strings(p, find_wide_spans(&p.bytes, min), min);
        spans
            .into_iter()
            .map(StringRow::Span)
            .chain(user.into_iter().map(StringRow::Hit))
    };
    match encoding {
        StringEncoding::Ascii => ascii().collect(),
        StringEncoding::Utf16 => wide().collect(),
        StringEncoding::Both => {
            let mut all: Vec<StringRow> = ascii().chain(wide()).collect();
            all.sort_by_key(StringRow::off);
            all
        }
    }
}

/// Whether `raw` holds `needle` under ASCII case folding, byte for byte
/// with no copy of the text.
///
/// # Arguments
///
/// * `raw` - The bytes a string's whole text spells.
/// * `needle` - The lowered filter text, all ASCII.
fn contains_fold_ascii(raw: &[u8], needle: &[u8]) -> bool {
    needle.is_empty()
        || raw.len() >= needle.len()
            && raw
                .windows(needle.len())
                .any(|w| w.iter().zip(needle).all(|(b, n)| b.eq_ignore_ascii_case(n)))
}

/// Whether the UTF-16LE code units `raw` spells hold `needle` under ASCII
/// case folding, tested against the units in place.
///
/// # Arguments
///
/// * `raw` - The run's bytes: one ASCII low byte and one zero high byte
///   per unit.
/// * `needle` - The lowered filter text, all ASCII.
fn contains_fold_wide(raw: &[u8], needle: &[u8]) -> bool {
    let units = raw.len() / 2;
    if needle.is_empty() {
        return true;
    }
    if units < needle.len() {
        return false;
    }
    (0..=units - needle.len()).any(|u| {
        needle
            .iter()
            .enumerate()
            .all(|(k, n)| raw[2 * (u + k) + 1] == 0 && raw[2 * (u + k)].eq_ignore_ascii_case(n))
    })
}

/// Whether one row passes `filter`, the span's bytes tested where they
/// lie in the program and no text decoded.
///
/// A span's whole text is pure printable ASCII, so an ASCII needle is a
/// folded byte search over the run and any other needle answers `false`
/// without a copy; a .NET user string's text may hold what its bytes'
/// walk could not, so its row decodes.
///
/// # Arguments
///
/// * `p` - The loaded program, for the bytes a span indexes.
/// * `row` - The row tested.
/// * `filter` - Keeps the rows whose text contains it.
fn row_matches(p: &Program, row: &StringRow, filter: &Filter) -> bool {
    let Some(needle) = filter.needle() else {
        return true;
    };
    let bytes = needle.as_bytes();
    if !bytes.is_ascii() {
        // INVARIANT: a span's whole text is printable ASCII, which no
        // non-ASCII needle is contained in; a user string's text may hold
        // one, so its row decodes.
        return match row {
            StringRow::Span(_) => false,
            StringRow::Hit(_) => filter.accepts(&row.full_text(&p.bytes)),
        };
    }
    match row {
        StringRow::Span(s) => {
            let raw = s.raw_bytes(&p.bytes);
            if s.encoding == borer_engine::strings::Encoding::Ascii {
                contains_fold_ascii(raw, bytes)
            } else {
                contains_fold_wide(raw, bytes)
            }
        }
        StringRow::Hit(_) => filter.accepts(&row.full_text(&p.bytes)),
    }
}

/// Renders one page of string rows, the answer `strings` gives and the
/// command line prints alike.
///
/// The filter tests a row's whole text ([`StringRow::full_text`]), not
/// the display text a long string is cut to, and a span's text is tested
/// in place: only the rows the page prints are materialized.
///
/// # Arguments
///
/// * `p` - The loaded program, for the addresses and the whole texts.
/// * `rows` - The walked rows, in offset order.
/// * `filter` - Keeps the rows whose text contains it.
/// * `walk` - The shortest run kept and the encoding, for the header.
/// * `window` - Rows to skip and most rows shown.
/// * `count_only` - Answer the header's count alone.
///
/// # Returns
///
/// A `# showing N of M matches` header, a column header and one
/// `va len enc "text"` row per string, `off=<n>` for bytes no section maps.
fn strings_page(
    p: &Program,
    rows: Vec<StringRow>,
    filter: &Filter,
    walk: (usize, StringEncoding),
    window: (usize, usize),
    count_only: bool,
) -> String {
    let (min, encoding) = walk;
    let (offset, limit) = window;
    let total = rows
        .iter()
        .filter(|row| row_matches(p, row, filter))
        .count();
    if count_only {
        return format!("# {total} matches (min_len={min}, encoding={encoding})\n");
    }
    let shown = total.saturating_sub(offset).min(limit);
    let mut out = format!(
        "# showing {shown} of {total} matches (min_len={min}, encoding={encoding}; filter=/offset= to narrow)\n# va len enc text\n"
    );
    for row in rows
        .into_iter()
        .filter(|row| row_matches(p, row, filter))
        .skip(offset)
        .take(limit)
    {
        let va = p
            .offset_to_va(row.off())
            .map_or_else(|| format!("off={:#x}", row.off()), |v| format!("{v:#x}"));
        let _ = writeln!(
            out,
            "{va} {} {} \"{}\"",
            row.len(),
            row.encoding().name(),
            row.display_text(&p.bytes)
        );
    }
    out
}

/// Reads an entropy threshold, the same for `entropy` and the command line.
///
/// # Arguments
///
/// * `threshold` - Minimum bits per byte, as given.
///
/// # Errors
///
/// When the threshold is outside `0..=8` bits per byte: no window holds
/// more than eight, and a negative one would report every window
/// ([`entropy::threshold_error`]).
fn entropy_threshold(threshold: f64) -> Result<f64, String> {
    entropy::threshold_error(threshold).map_or(Ok(threshold), Err)
}

/// Renders one page of search hits, one `function: va va` row per run of
/// hits inside one function, under a header that says how many there are
/// in all and where the page starts.
///
/// A byte pattern hits a hundred times inside one function, and a row per
/// hit named the function on every one: 321 of 500 rows on kernel32 shared
/// a function with the row before. Consecutive hits in one function share
/// a row; a hit outside every function is under `-`. The file offset is
/// left out where it follows from the address and the section table; a hit
/// in bytes no section maps has no address, so it is written `off=<n>`,
/// the form `hexdump` and `read` take back.
///
/// # Arguments
///
/// * `page` - The page and the total.
/// * `offset` - Where the page starts, for the header.
/// * `count_only` - Answer the count alone, with no page to speak of.
/// * `names` - The analysis and the overlay, for the function names.
///
/// # Returns
///
/// A `# N hits, showing S of N from O` header, a column header and the
/// rows; `# N hits` alone for a count.
fn render_hits(
    page: &borer_engine::search::Hits,
    offset: usize,
    count_only: bool,
    names: (&Analysis, &Overlay),
) -> String {
    let (a, o) = names;
    if count_only {
        return format!("# {} hits\n", page.total);
    }
    let mut out = format!(
        "# {} hits, showing {} of {} from {offset}\n# function: va ...\n",
        page.total,
        page.hits.len(),
        page.total
    );
    let entry_of =
        |h: &borer_engine::search::Hit| h.va.and_then(|v| a.function_at(v)).map(|f| f.entry);
    for run in page.hits.chunk_by(|x, y| entry_of(x) == entry_of(y)) {
        let Some(first) = run.first() else {
            continue;
        };
        let name = entry_of(first).map_or_else(
            || "-".to_owned(),
            |e| borer_engine::analysis::name_of(a, o, e),
        );
        let _ = write!(out, "{name}:");
        for h in run {
            match h.va {
                Some(va) => {
                    let _ = write!(out, " {va:#x}");
                }
                None => {
                    let _ = write!(out, " off={:#x}", h.file_off);
                }
            }
        }
        out.push('\n');
    }
    out
}

/// Parses a field offset: `0x10`, `16` or `-0x8`.
///
/// Hex takes its `0x`, as an address does: an offset is read in a context
/// full of decimal counts, and reading bare digits as hex turned `16` into a
/// guess and `abc` into `0xabc` without a word.
///
/// # Arguments
///
/// * `text` - The offset as typed: an optional minus sign, then `0x` and hex
///   digits or decimal digits alone.
///
/// # Errors
///
/// When the text is not one of those forms, or the magnitude does not fit
/// a signed displacement.
fn parse_field_offset(text: &str) -> anyhow::Result<i64> {
    use anyhow::Context as _;
    let (negative, digits) = text.strip_prefix('-').map_or((false, text), |d| (true, d));
    let (radix, digits) = match digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        Some(hex) => (16, hex),
        None => (10, digits),
    };
    let magnitude = Some(digits)
        .filter(|d| !d.is_empty() && d.chars().all(|c| c.is_digit(radix)))
        .and_then(|d| u64::from_str_radix(d, radix).ok())
        .with_context(|| format!("bad offset {}", borer_engine::text::quoted(text)))?;
    let value = i64::try_from(magnitude)
        .with_context(|| format!("offset {text} does not fit a signed displacement"))?;
    Ok(if negative { -value } else { value })
}

/// Agent workflows offered as MCP prompts: know-how shipped next to the
/// tools, whose texts the `borer://playbook` resources serve too
/// ([`playbooks`]).
#[prompt_router]
impl BorerServer {
    /// Returns the end-to-end triage workflow.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "triage",
        description = "Triage the loaded binary end to end (what it is, what it imports, what it hides, where to read first) in a token-frugal tool order."
    )]
    fn triage(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(Role::User, playbooks::TRIAGE)]
    }

    /// Returns the workflow that maps a client's protocol and message system.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "protocol",
        description = "Map how a networked client talks and dispatches: wire ids, every command's record, the message classes with their fields and handlers, and the registration tables, in a token-frugal order."
    )]
    fn protocol(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(Role::User, playbooks::PROTOCOL)]
    }

    /// Returns the workflow that locates a validation routine.
    ///
    /// # Arguments
    ///
    /// * `FindCheckArgs` - What is being validated.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "find_check",
        description = "Locate and explain the code that validates something (serial, license, password): from strings and constants to the comparison, ending with a rename plan."
    )]
    fn find_check(
        &self,
        Parameters(FindCheckArgs { what }): Parameters<FindCheckArgs>,
    ) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            playbooks::FIND_CHECK.replace("<what>", &what),
        )]
    }

    /// Returns the workflow that explains one function.
    ///
    /// # Arguments
    ///
    /// * `ExplainFunctionArgs` - The function's address or name.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "explain_function",
        description = "Explain one function from its summary, decompilation and callers, then propose names to apply."
    )]
    fn explain_function(
        &self,
        Parameters(ExplainFunctionArgs { address }): Parameters<ExplainFunctionArgs>,
    ) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            playbooks::EXPLAIN_FUNCTION.replace("<address>", &address),
        )]
    }
}

#[tool_handler]
#[prompt_handler]
impl ServerHandler for BorerServer {
    /// Returns capabilities (tools, prompts, resources, completions), the
    /// implementation name and version, and the agent-facing instructions,
    /// built from the routers and the resource tables
    /// ([`playbooks::instructions`]).
    fn get_info(&self) -> rmcp::model::ServerInfo {
        let tools: Vec<String> = Self::tool_router()
            .list_all()
            .into_iter()
            .map(|t| t.name.into_owned())
            .collect();
        rmcp::model::ServerInfo::new(
            rmcp::model::ServerCapabilities::builder()
                .enable_tools()
                .enable_prompts()
                .enable_resources()
                .enable_completions()
                .build(),
        )
        .with_server_info(rmcp::model::Implementation::new(
            "borer",
            env!("CARGO_PKG_VERSION"),
        ))
        .with_instructions(playbooks::instructions(
            &tools,
            &Self::prompt_router().list_all(),
        ))
    }

    /// Runs a tool, then passes its text through the session's answer
    /// memory, the byte budget and the evidence line.
    ///
    /// Any tool takes a `since` argument the schemas leave out (every tool
    /// would pay for it in the tool list): the tag of the answer the reader
    /// holds, taken off here before the tool parses its arguments
    /// ([`recall::Recall`]); `"since": null` is no tag, as null is no value
    /// for every other parameter. A `reload` call schedules the hand-over whatever
    /// it answers: the relay holds the client's lines from that call on
    /// until this worker has ended, so a worker that stayed would hold them
    /// for good. A `query` answer has been through both already, keyed by
    /// its URI as a resource read is ([`BorerServer::read_uri`]), so its tag
    /// goes on the URI, where a URI's own tag goes ([`recall::tagged_uri`]).
    /// An argument the parser refuses is named in the
    /// message, from the tool's schema ([`params::misfit`]): serde words
    /// the value alone.
    ///
    /// # Arguments
    ///
    /// * `request` - The tool and its arguments.
    /// * `context` - Request context.
    ///
    /// # Errors
    ///
    /// When the tool is unknown, its arguments do not parse, or `since` is
    /// not a tag.
    async fn call_tool(
        &self,
        mut request: CallToolRequestParams,
        context: RequestContext<RoleServer>,
    ) -> Result<CallToolResponse, ErrorData> {
        let since = request
            .arguments
            .as_mut()
            .and_then(|a| a.remove(SINCE_ARG))
            .and_then(|v| match v {
                serde_json::Value::Null => None,
                serde_json::Value::String(s) => Some(Tag::parse(&s)),
                other => Some(Tag::parse(&other.to_string())),
            })
            .transpose()
            .map_err(err_params)?;
        if let Some(tag) = since
            && request.name == "query"
            && let Some(serde_json::Value::String(uri)) =
                request.arguments.as_mut().and_then(|a| a.get_mut("uri"))
        {
            *uri = recall::tagged_uri(uri, tag);
        }
        let args = request
            .arguments
            .as_ref()
            .map(|a| serde_json::to_string(a).unwrap_or_default())
            .unwrap_or_default();
        let key = format!("tool:{}:{args}", request.name);
        let again = format!(
            "calling {}",
            borer_engine::text::one_line(format!("{} {args}", request.name).trim_end())
        );
        let remembered = request.name != "query";
        let reloading = request.name == "reload";
        let peer_info = context.peer.peer_info();
        let named = (request.name.clone(), request.arguments.clone());
        let call = rmcp::handler::server::tool::ToolCallContext::new(self, request, context);
        let response = Self::tool_router().call(call).await;
        if reloading {
            self.hand_over.schedule(Resume {
                peer_info: peer_info.as_deref().cloned(),
                project: self.loaded().map(|p| {
                    borer::project::ProjectFile::from_overlay(
                        &p.path.display().to_string(),
                        None,
                        &read_lock(&self.overlay),
                    )
                }),
                pdb: Some(*read_lock(&self.pdb_applied)),
                entry_file_offset: *read_lock(&self.entry_file_offset),
                raw: read_lock(&self.raw_load).clone(),
            });
        }
        let response = response?;
        Ok(match response {
            CallToolResponse::Complete(mut result)
                if remembered && result.is_error != Some(true) =>
            {
                self.note_change(&named.0, named.1.as_ref(), &args);
                if let [ContentBlock::Text(t)] = result.content.as_mut_slice() {
                    let full = std::mem::take(&mut t.text);
                    let paged = named
                        .1
                        .as_ref()
                        .is_some_and(|a| a.contains_key("offset") || a.contains_key("limit"));
                    lock(&self.ledger).answered(
                        &key,
                        session::shows_fewer(&full) || recall::over_budget(full.len()),
                        paged,
                    );
                    let sent = match self.recall.lock() {
                        Ok(mut recall) => recall.answer(&key, since, &again, full),
                        Err(_) => full,
                    };
                    t.text = self.evidence(budgeted(sent, Narrow::Tool));
                }
                CallToolResponse::Complete(result)
            }
            CallToolResponse::Complete(mut result) if result.is_error == Some(true) => {
                if let [ContentBlock::Text(t)] = result.content.as_mut_slice()
                    && let Some(rest) = t.text.strip_prefix(params::DESERIALIZE_PREFIX)
                    && let (name, Some(args)) = &named
                    && let Some(field) = Self::tool_router()
                        .get(name)
                        .and_then(|tool| params::misfit(&tool.input_schema, args))
                {
                    t.text = format!("{} field `{field}`:{rest}", params::DESERIALIZE_PREFIX);
                }
                CallToolResponse::Complete(result)
            }
            other => other,
        })
    }

    /// Lists the tools with slimmed schemas.
    ///
    /// The list never changes while the server runs, so clients speaking
    /// protocol 2026-07-28 or newer get a one-hour public cache hint.
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused; the list is complete).
    /// * `context` - Request context carrying the negotiated protocol version.
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, ErrorData> {
        let cache = context
            .protocol_version()
            .is_some_and(|v| v >= ProtocolVersion::V_2026_07_28);
        Ok(ListToolsResult {
            result_type: Some(ResultType::COMPLETE),
            tools: Self::tool_router()
                .list_all()
                .into_iter()
                .map(slim_tool)
                .collect(),
            meta: None,
            next_cursor: None,
            ttl_ms: cache.then_some(3_600_000),
            cache_scope: cache.then_some(CacheScope::Public),
        })
    }

    /// Returns one tool with its slimmed schema.
    ///
    /// # Arguments
    ///
    /// * `name` - Tool name.
    fn get_tool(&self, name: &str) -> Option<Tool> {
        Self::tool_router().get(name).cloned().map(slim_tool)
    }

    /// Lists the fixed resources (`borer://info`, `borer://annotations`,
    /// `borer://enums`).
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused).
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_resources(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourcesResult, ErrorData> {
        Ok(ListResourcesResult::with_all_items(
            RESOURCES
                .iter()
                .map(|&(uri, description)| {
                    Resource::new(uri, resource_name(uri))
                        .with_description(description)
                        .with_mime_type(TEXT_PLAIN)
                })
                .collect(),
        ))
    }

    /// Lists the per-function resource templates (function, decompile, disasm).
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused).
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_resource_templates(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourceTemplatesResult, ErrorData> {
        Ok(ListResourceTemplatesResult::with_all_items(
            RESOURCE_TEMPLATES
                .iter()
                .map(|&(uri, description, _)| {
                    ResourceTemplate::new(uri, resource_name(uri))
                        .with_description(description)
                        .with_mime_type(TEXT_PLAIN)
                })
                .collect(),
        ))
    }

    /// Reads a `borer://` resource ([`BorerServer::read_uri`]).
    ///
    /// # Arguments
    ///
    /// * `request` - The resource URI.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI; otherwise the delegated tool's error.
    async fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResponse, ErrorData> {
        let (uri, text) = self.read_uri(&request.uri)?;
        Ok(ReadResourceResult::new(vec![ResourceContents::text(text, uri)]).into())
    }

    /// Completes prompt and resource-template arguments.
    ///
    /// Any `address` or `function` argument (the `{function}` of
    /// `borer://difffn`, `migrate`, `schema`, `encode` and `shape`)
    /// completes to function names; `find_check`'s `what` completes to the
    /// usual validation targets.
    ///
    /// # Arguments
    ///
    /// * `request` - The reference and the partial argument.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Internal error when the completion list exceeds the protocol's limits.
    async fn complete(
        &self,
        request: CompleteRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CompleteResult, ErrorData> {
        let prefix = request.argument.value.to_lowercase();
        let all: Vec<String> = match (&request.r#ref, request.argument.name.as_str()) {
            (Reference::Prompt(p), "what") if p.name == "find_check" => CHECK_KINDS
                .iter()
                .filter(|k| k.starts_with(&prefix))
                .map(|k| (*k).to_owned())
                .collect(),
            (_, "address" | "function") => self.complete_names(&prefix),
            _ => Vec::new(),
        };
        let total = all.len();
        let values: Vec<String> = all.into_iter().take(CompletionInfo::MAX_VALUES).collect();
        let has_more = total > values.len();
        let mut info = CompletionInfo::new(values).map_err(err_internal)?;
        info.total = Some(u32::try_from(total).unwrap_or(u32::MAX));
        info.has_more = Some(has_more);
        Ok(CompleteResult::new(info))
    }

    /// Answers a request no typed handler took: a method rmcp does not
    /// know, or one it knows whose params do not parse, which it hands
    /// over the same way.
    ///
    /// Both were answered method-not-found, so a `resources/read` sent
    /// without its `uri` read as a server with no resources at all. A
    /// method borer serves is refused as invalid params, with the shape
    /// its params take.
    ///
    /// # Arguments
    ///
    /// * `request` - The method and its params as sent.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Always: invalid params for a method borer serves, method-not-found
    /// for any other.
    async fn on_custom_request(
        &self,
        request: CustomRequest,
        _context: RequestContext<RoleServer>,
    ) -> Result<CustomResult, ErrorData> {
        match PARAMS_SHAPES
            .iter()
            .find(|(method, _)| *method == request.method)
        {
            Some((method, shape)) => Err(err_params(format!(
                "{method} needs params of the form {shape}"
            ))),
            None => Err(ErrorData::new(
                ErrorCode::METHOD_NOT_FOUND,
                request.method,
                None,
            )),
        }
    }
}

/// The methods borer serves that take params, each with the shape they
/// take, for the refusal of one sent without them
/// ([`BorerServer::on_custom_request`]).
const PARAMS_SHAPES: &[(&str, &str)] = &[
    ("resources/read", r#"{"uri": "borer://info"}"#),
    ("tools/call", r#"{"name": "<tool>", "arguments": {...}}"#),
    ("prompts/get", r#"{"name": "<prompt>", "arguments": {...}}"#),
    (
        "completion/complete",
        r#"{"ref": {...}, "argument": {"name": "...", "value": "..."}}"#,
    ),
];

impl BorerServer {
    /// Reads a `borer://` resource: the text its handler answers, through
    /// the session's answer memory, the byte budget and the evidence line.
    ///
    /// `resources/read` and the `query` tool both come here, so a URI is
    /// answered alike either way: the same text, the same errors, and one
    /// answer memory keyed by the URI and the page it asks for. The
    /// argument is percent-decoded: a client is free to escape the reserved
    /// characters an argument uses, and an experiment spec is full of them.
    /// An unknown URI is refused with the few resources nearest it, and
    /// `borer://help` lists every one, which is how an agent whose host
    /// lists no resources finds them. An evidence URI
    /// (`borer://session/evidence/<id>`) skips the memory, the budget's
    /// cut apart, and mints no evidence of its own: the text an id names
    /// comes back exactly as it was sent.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI as the client sent it, with any suffixes
    ///   ([`paging::Asked`]): `!offset=<n>` and `!limit=<n>` page a
    ///   listing, `!since=<tag>` passes back the tag of the answer the
    ///   reader holds, and `!fresh` asks for the text whole whatever tag
    ///   comes with it.
    ///
    /// # Returns
    ///
    /// The URI with only its page suffixes, and the text to send.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI; invalid-params for a suffix
    /// that does not read; otherwise the handler's error.
    fn read_uri(&self, uri: &str) -> Result<(String, String), ErrorData> {
        let asked = paging::Asked::read(uri).map_err(err_params)?;
        let text = self.listing(&asked)?;
        let key = asked.key();
        if asked.core.starts_with(EVIDENCE_URI) {
            return Ok((key, budgeted(text, Narrow::Uri)));
        }
        if asked.core != SESSION_URI {
            lock(&self.ledger).answered(
                &key,
                session::shows_fewer(&text) || recall::over_budget(text.len()),
                asked.paged(),
            );
        }
        let again = format!("reading {key} (resources/read or the query tool)");
        let text = match self.recall.lock() {
            Ok(mut recall) => recall.answer(&key, asked.since, &again, text),
            Err(_) => text,
        };
        Ok((key, self.evidence(budgeted(text, Narrow::Uri))))
    }

    /// The text of one resource, as its handler answers it: no answer
    /// memory, no byte budget, no suffix; what the tests read.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI, suffixes already taken off.
    ///
    /// # Errors
    ///
    /// As [`BorerServer::listing`].
    #[cfg(test)]
    fn resource_text(&self, uri: &str) -> Result<String, ErrorData> {
        self.listing(&paging::Asked::whole(uri))
    }

    /// The text of one resource, paged as its URI asks: no answer memory
    /// and no byte budget.
    ///
    /// [`BorerServer::read_uri`] wraps it for `resources/read` and the
    /// `query` tool, and a script's `query(uri)` calls it directly
    /// ([`BorerServer::script`]). A listing that pages itself
    /// (`attrs`, `messages`, `fieldrefs`, `grep`, `iocs`, `calls`, `clr`) is
    /// handed the page; any other answer's rows are paged here
    /// ([`borer_engine::table::page`]), under a `# showing N of M from K`
    /// line and over the URI that reads the next page.
    ///
    /// A template named without its argument (`borer://emulate`) answers
    /// how to read it ([`BorerServer::help_text`]).
    ///
    /// # Arguments
    ///
    /// * `asked` - The URI with its suffixes read off.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI, naming the resources nearest
    /// it ([`resources::unknown_resource`]); otherwise the handler's error.
    fn listing(&self, asked: &paging::Asked) -> Result<String, ErrorData> {
        let uri = asked.core.as_str();
        let Some(path) = uri.strip_prefix("borer://") else {
            return Err(resources::unknown_resource(uri));
        };
        let (kind, arg) = match path.split_once('/') {
            Some((k, a)) => (k, Some(percent_decode(a))),
            None => (path, None),
        };
        let text = match (kind, arg) {
            ("info", None) => self.binary_info()?,
            ("annotations", None) => self.annotations(Parameters(AnnotationsParams::default()))?,
            ("enums", None) => self.enums_text()?,
            ("dynimports", None) => self.dynamic_imports_text()?,
            ("checks", None) => self.checks_text()?,
            ("antianalysis", None) => self.anti_analysis_text()?,
            ("protection", None) => self.protection_text()?,
            ("iocs", None) => return self.iocs_text(&asked.spec_words("")),
            ("iocs", Some(filter)) => return self.iocs_text(&asked.spec_words(&filter)),
            ("calls", Some(spec)) => return self.calls_text(&asked.spec_words(&spec)),
            ("triage", None) => self.triage_text()?,
            ("fingerprint", None) => self.fingerprint_text()?,
            ("hashes", None) => self.hashes_text()?,
            ("children", None) => self.children_text()?,
            ("capabilities", None) => self.capabilities_text()?,
            ("qt", None) => self.qt_text()?,
            ("objc", None) => return self.objc_text("", asked),
            ("objc", Some(filter)) => return self.objc_text(&filter, asked),
            ("clr", None) => return self.clr_text(&asked.spec_words("")),
            ("clr", Some(filter)) => return self.clr_text(&asked.spec_words(&filter)),
            ("stackstrings", None) => self.stack_strings_text("")?,
            ("stackstrings", Some(filter)) => self.stack_strings_text(&filter)?,
            ("emulate", Some(address)) => self.emulate_text(&address)?,
            ("taint", Some(spec)) => self.taint_text(&spec)?,
            ("layout", Some(spec)) => self.layout_text(&spec)?,
            ("why", Some(target)) => self.why_text(&target)?,
            ("solve", Some(spec)) => self.solve_text(&spec)?,
            ("partial", Some(address)) => self.partial_text(&address)?,
            ("flat", None) => self.flattening_text("")?,
            ("flat", Some(filter)) => self.flattening_text(&filter)?,
            ("devirt", Some(address)) => self.devirtualize_text(&address)?,
            ("unpack", Some(address)) => self.unpack_text(&address)?,
            ("hidden", None) => self.hidden_text("")?,
            ("hidden", Some(filter)) => self.hidden_text(&filter)?,
            ("decoded", None) => return self.decoded_text(&asked.spec_words("")),
            ("decoded", Some(filter)) => return self.decoded_text(&asked.spec_words(&filter)),
            ("oracle", Some(address)) => self.oracle_text(&address)?,
            ("run", Some(spec)) => self.run_text(&spec)?,
            ("diverge", Some(spec)) => self.diverge_text(&spec)?,
            ("vectors", Some(spec)) => self.vectors_text(&spec)?,
            ("diff", Some(other)) => self.diff_text(&other)?,
            ("difffn", Some(spec)) => self.diff_function_text(&spec)?,
            ("migrate", Some(spec)) => self.migrate_text(&spec)?,
            ("carry", Some(path)) => self.carry_text(&path)?,
            ("vm", None) => self.vm_text("")?,
            ("vm", Some(address)) => self.vm_text(&address)?,
            ("asserts", None) => self.asserts_text("")?,
            ("asserts", Some(filter)) => self.asserts_text(&filter)?,
            ("sources", None) => self.sources_text("")?,
            ("sources", Some(filter)) => self.sources_text(&filter)?,
            ("classes", None) => self.classes_text("")?,
            ("classes", Some(filter)) => self.classes_text(&filter)?,
            ("singletons", None) => self.singletons_text("")?,
            ("singletons", Some(filter)) => self.singletons_text(&filter)?,
            ("fields", Some(address)) => self.fields_text(&address)?,
            ("fieldrefs", Some(spec)) => return self.fieldrefs_text(&spec, asked),
            ("vslot", Some(spec)) => self.vslot_text(&spec)?,
            ("grep", Some(text)) => return self.grep_text(&text, asked),
            ("packs", None) => self.packs_text()?,
            ("exportpack", Some(spec)) => self.export_pack_text(&spec)?,
            ("script", Some(path)) => self.script_text(&path)?,
            ("scenario", Some(spec)) => self.scenario_text(&spec)?,
            ("scenarios", Some(spec)) => self.scenarios_text(&spec)?,
            ("index", None) => self.index_text()?,
            ("bench", None) => self.bench_text()?,
            ("schema", Some(what)) => self.schema_text(&what)?,
            ("schemas", Some(spec)) => self.schemas_text(&spec)?,
            ("encode", Some(what)) => self.encode_text(&what)?,
            ("encodes", Some(spec)) => self.encodes_text(&spec)?,
            ("senders", Some(spec)) => self.senders_text(&spec)?,
            ("protocol", Some(spec)) => self.protocol_text(&spec)?,
            ("hooks", Some(spec)) => self.hooks_text(&spec)?,
            ("shape", Some(address)) => self.shape_text(&address)?,
            ("messages", None) => return self.messages_text("", asked),
            ("attrs", None) => return self.attrs_text("", asked),
            ("map", None) => self.map_text("")?,
            ("about", Some(name)) => self.about_text(&name)?,
            ("changes", Some(path)) => self.changes_text(&path)?,
            ("map", Some(namespace)) => self.map_text(&namespace)?,
            ("ports", None) => self.ports_text("")?,
            ("ports", Some(filter)) => self.ports_text(&filter)?,
            ("attrs", Some(filter)) => return self.attrs_text(&filter, asked),
            ("messages", Some(filter)) => return self.messages_text(&filter, asked),
            ("anchors", Some(path)) => self.anchors_text(&path)?,
            ("function", Some(address)) => {
                self.function_summary(Parameters(FunctionParams { address }))?
            }
            ("decompile", Some(address)) => self.decompile(Parameters(DecompileParams {
                address,
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))?,
            ("disasm", Some(address)) => {
                self.disassemble_function(Parameters(DisassembleFunctionParams {
                    address,
                    max_instrs: None,
                    bytes: None,
                }))?
            }
            ("playbook", Some(spec)) => resources::playbook_text(&spec)?,
            ("help", None) => resources::help_index(self.loaded().as_deref()),
            ("session", None) => self.session_text(),
            ("session", Some(spec)) => return self.session_evidence(&spec),
            ("help", Some(name)) => self.help_text(&name)?,
            (name, None)
                if RESOURCE_TEMPLATES
                    .iter()
                    .any(|t| resource_name(t.0) == name) =>
            {
                self.help_text(name)?
            }
            _ => return Err(resources::unknown_resource(uri)),
        };
        if !asked.paged() {
            return Ok(text);
        }
        Ok(borer_engine::table::page(
            &text,
            asked.offset.unwrap_or(0),
            asked.limit.unwrap_or(usize::MAX),
            &asked.again(),
        ))
    }
}

/// The session ledger's URI, whose reads the ledger does not list.
const SESSION_URI: &str = "borer://session";

/// The evidence retrieval prefix, whose reads return the retained text
/// verbatim instead of minting new evidence.
const EVIDENCE_URI: &str = "borer://session/evidence/";

impl BorerServer {
    /// Sends an answer with the evidence line naming it, and keeps the
    /// answer behind that line's id for `borer://session/evidence/<id>`
    /// ([`session::Evidence`]).
    ///
    /// One line is all the answer pays, whatever its size; the text stays
    /// server-side. The line goes after every other, a `# since=` line
    /// included, since it names the emission a reader cites.
    ///
    /// # Arguments
    ///
    /// * `text` - The answer as sent, the byte budget already applied.
    fn evidence(&self, mut text: String) -> String {
        if !text.ends_with('\n') {
            text.push('\n');
        }
        text.push_str(&lock(&self.ledger).evidence_line(&text));
        text
    }

    /// Records in the ledger a tool call that changed what the session
    /// holds: a load or a save, or a name, comment, type or script applied
    /// with `dry_run=false` ([`session::changes`]), and what a save or a
    /// load leaves saved.
    ///
    /// # Arguments
    ///
    /// * `tool` - The tool's name.
    /// * `arguments` - Its arguments, `None` for none.
    /// * `args` - The same as JSON, as the ledger lists them.
    fn note_change(
        &self,
        tool: &str,
        arguments: Option<&serde_json::Map<String, serde_json::Value>>,
        args: &str,
    ) {
        let dry_run = arguments
            .and_then(|a| a.get("dry_run"))
            .and_then(serde_json::Value::as_bool);
        if !session::changes(tool, dry_run) {
            return;
        }
        let saved = match tool {
            "save_project" | "load_project" => Some(Some(read_lock(&self.overlay).fingerprint())),
            "load_binary" => Some(None),
            _ => None,
        };
        let mut ledger = lock(&self.ledger);
        ledger.changed(tool, args);
        if let Some(saved) = saved {
            ledger.saved(saved);
        }
    }
}

/// What agents most often ask `find_check` about.
const CHECK_KINDS: &[&str] = &[
    "activation code",
    "checksum",
    "license key",
    "password",
    "registration",
    "serial",
    "signature",
    "token",
];

/// The MIME type of every resource: plain text tables, as the tools answer.
const TEXT_PLAIN: &str = "text/plain";

/// The fixed resources: URI and description. Each is listed under the name
/// its URI's path spells ([`resource_name`]).
const RESOURCES: &[(&str, &str)] = &[
    (
        "borer://help",
        "Every resource with what it answers, one line each; a template read without its argument (borer://emulate), or borer://help/<name>, gives its grammar and an example",
    ),
    (
        "borer://info",
        "Summary of the loaded program (binary_info)",
    ),
    (
        "borer://session",
        "Where this session stands: what is loaded, the overlay's counts and whether it is saved, the names, comments, types and loads it applied, and the requests it answered, each marked held (since=<tag> answers what changed), capped or paged",
    ),
    (
        "borer://annotations",
        "Annotation overlay: names and comments",
    ),
    (
        "borer://qt",
        "Qt classes from moc metadata: signals, slots, methods and properties, each mapped to its function",
    ),
    (
        "borer://objc",
        "Objective-C classes and categories from a Mach-O's runtime metadata, a row per method with its implementation (named -[Class sel]), 200 a page; borer://objc/<filter> narrows by class or selector",
    ),
    (
        "borer://capabilities",
        "What the program can do, grouped from its imports: networking, injection, crypto, persistence, anti-analysis and more",
    ),
    (
        "borer://clr",
        "A .NET assembly's metadata: its types, its methods with each body's address (IL is not decompiled; a mixed-mode image's native methods analyze as usual), P/Invokes as dll!export, the external members it uses, referenced assemblies and its user strings, 200 rows a page; borer://clr/<filter> narrows by kind (type, method, pinvoke, memberref, asmref, moduleref, string) or text",
    ),
    (
        "borer://hidden",
        "Strings the program generates at run time by mixing a keystream, recovered by running the generators",
    ),
    (
        "borer://decoded",
        "Strings a decoder function produces, recovered by running it at each of its call sites with that site's arguments (ciphertext pointer, length): a row per recovered string with its decoder and call site; a function that only copies yields nothing; borer://decoded/<filter> narrows by text",
    ),
    (
        "borer://stackstrings",
        "Strings a function builds on its stack a piece at a time, which malware does to keep text out of the data sections",
    ),
    (
        "borer://vm",
        "Dispatch loops: an interpreter's table jump with the handlers that return to it, which is what a virtualized function looks like",
    ),
    (
        "borer://dynimports",
        "The APIs and DLLs the program resolves at runtime via GetProcAddress/LoadLibrary, the imports a thin table hides",
    ),
    (
        "borer://checks",
        "Functions that decide whether a key, serial or license is valid, with the constants they test against",
    ),
    (
        "borer://antianalysis",
        "The anti-debug and anti-VM techniques the binary carries, at the instruction level and in its imports",
    ),
    (
        "borer://flat",
        "Functions whose control flow was flattened into one loop around a switch: every block a case, the block order destroyed, a state variable saying which runs next",
    ),
    (
        "borer://map",
        "The program's namespaces, each with its classes counted by role (from a pack's [roles] lines, else the role words in class names: managers, components, widgets, messages, commands), singletons and methods: a table of contents; borer://map/<namespace> lists one namespace's classes with role, parent, methods and instance",
    ),
    (
        "borer://attrs",
        "Every typed attribute the program registers (entity state: hit points, positions, timers), from the registrar a pack names ([attributes] registrar), with its four-character code, type, access mode, default and the functions using it, 200 rows a page; borer://attrs/<filter> narrows by name or code, and one exact match lists every user with the definition global",
    ),
    (
        "borer://packs",
        "The packs this session knows (named in BORER_PACKS, and every pack in the pack directories) and whether each loads for the loaded program: a pack loads by itself when all its [match] lines hold",
    ),
    (
        "borer://ports",
        "Every message every port (entity property, manager, UI handler) accepts and the function its dispatch calls for it, or inline, from the accept helpers a pack names ([messages] accept); borer://ports/<filter> narrows by component or message",
    ),
    (
        "borer://messages",
        "Every class that registered a four-character wire id, with its named fields and the functions that test for the id (the handlers), 200 rows a page, a function named in several cells numbered once in a # functions: legend; borer://messages/<filter> narrows by class name",
    ),
    (
        "borer://index",
        "Builds the decompilation index of the loaded program (every function's pseudo-C, cached on disk for borer://grep) and reports its size",
    ),
    (
        "borer://triage",
        "What the first ten calls of a triage would tell you, in one: format, protection, anti-analysis, crypto, generated strings, capabilities, and the functions to read first with the evidence for each; for a file with no code (data, an archive, another instruction set), its magic, entropy, high-entropy and encoded regions, and strings",
    ),
    (
        "borer://protection",
        "Whether the image is packed or protected, which protector the section names give away, and the evidence",
    ),
    (
        "borer://iocs",
        "Indicators to block or hunt: URLs, domains, IP and e-mail addresses, registry keys, file paths, pipe, mutex and kernel object names, user agents, each with where it came from (a stored string's address, a stack string, a generated string, decoded base64, an emulated API or syscall argument, an API call's argument), the function using it and a confidence, benign-common marking what every program carries; 200 rows a page, borer://iocs/<filter> narrows by type or text",
    ),
    (
        "borer://fingerprint",
        "The identity of this build's fingerprints: a digest, the counts, and how to write the sidecar a later borer://diff reads. The manifest itself is a file, written by the CLI, because one line per function is megabytes",
    ),
    (
        "borer://hashes",
        "The content hashes a file is correlated by: imphash (Mandiant's dll.function MD5 as pefile and VirusTotal compute it: table order, dll lowercased with .dll/.ocx/.sys stripped, ordinals named as pefile names them), authentihash (SHA-256 with the checksum, security directory and certificate table excluded, so signing does not move it), tlsh (Trend Micro's TLSH, the T1 string public feeds carry; none under 50 bytes or for too little variety) and borer-lsh (borer's own locality-sensitive hash, matching only another borer-lsh)",
    ),
    (
        "borer://children",
        "Programs and containers embedded in the file, each found by its signature and kept only when its headers validate (PE, ELF, Mach-O, zip, gzip, xz, 7z, cab, squashfs, cpio, uImage, cramfs, Android boot image), with offset, size and a one-line identity, plus the high-entropy runs no header explains: packed, compressed or encrypted bytes. load_binary path=<file>@<off> opens a program row as a program of its own; containers are listed, not extracted",
    ),
    (
        "borer://asserts",
        "The fields the binary's assertions name, with the classes that assert them",
    ),
    (
        "borer://sources",
        "The source files the binary's assertions name, by directory: the subsystems it was built from",
    ),
    (
        "borer://classes",
        "Every class that registered a four-character code, the code that identifies it on the wire, with its method count and first method",
    ),
    (
        "borer://singletons",
        "The program's singletons: the classes whose one instance lives at a fixed thread-local or global slot, with the slot and the ::Instance accessor - the engine's global object model",
    ),
    (
        "borer://enums",
        "Every name table the binary encodes (string-to-constant parsers and constant-to-string tables), one line per function",
    ),
    (
        "borer://bench",
        "Wall-clock speed of borer's hot queries on the loaded binary (AOB scan, string walks, indexed grep when the index is cached): one row per op with its answer size, fastest elapsed and throughput; timings differ run to run, the counts never do",
    ),
];

/// The resource templates: URI template, description, and an example.
///
/// The example is read with `{entry}` and `{path}` filled in from the
/// loaded binary ([`resources::example`]). Each is listed under the name
/// its first path segment spells ([`resource_name`]).
const RESOURCE_TEMPLATES: &[(&str, &str, &str)] = &[
    (
        "borer://help/{name}",
        "How to read one resource: its URI, what it answers and, for a template, an example built from the loaded binary",
        "borer://help/emulate",
    ),
    (
        "borer://session/evidence/{id}",
        "The answer its `# evidence:` line names, kept as it was sent; every answer carries one as its last line (a mermaid graph: `%% evidence:`), the id <n>-<8 hex digits>, and this returns the text behind it or says it was let go past the 256 the session keeps",
        "borer://session/evidence/1-00000000",
    ),
    (
        "borer://playbook/{name}",
        "A prompt's text, for an agent whose host offers prompts only to its user: triage, protocol, find_check/<what is validated> or explain_function/<function>",
        "borer://playbook/triage",
    ),
    (
        "borer://stackstrings/{filter}",
        "Stack strings whose text contains the filter",
        "borer://stackstrings/http",
    ),
    (
        "borer://flat/{address}",
        "Cases of one flattening dispatcher, in table order, each with where it ends. The table order is not the order they run",
        "borer://flat/{entry}",
    ),
    (
        "borer://solve/{spec}",
        "Find an argument value that makes a check answer differently: spec is <address>[,aN] (the decompiler's aN, a1 by default). Every constant the function compares against is tried and the answers grouped, so a value standing apart is the one it wants, with the comparison it came from",
        "borer://solve/{entry},a1",
    ),
    (
        "borer://partial/{address}",
        "A counted loop comparing a few bits of a product to a byte table: the iterations, the bit window, the table and the loop-invariant multiplicand. That shape is a hidden-number problem, solved by lattice reduction and not by more samples",
        "borer://partial/{entry}",
    ),
    (
        "borer://why/{address}",
        "What is at an address and how borer knows: where its name came from (the compiler's debug information, a symbol, inferred from code, or nothing), why the function was discovered, what refers to it, and any value recovered by running the code that builds it",
        "borer://why/{entry}",
    ),
    (
        "borer://layout/{spec}",
        "Propose a structure from what a function does through one pointer: spec is <address>[,<register>] (default rcx, the first argument). Each row is a field with the width of the access and what it is passed to. Add ,apply=<Name> at a function's entry to define the fields as struct Name and type that parameter with it, so decompile names them (a dry run; add ,dry_run=false to apply)",
        "borer://layout/{entry},rcx",
    ),
    (
        "borer://taint/{spec}",
        "Follow a value forward through its function: spec is <address>[,<register>] (default rax, where a call leaves its result). Reports the instructions that carry it, the calls it is passed to and as which argument, the memory it is stored into, and where it still is at the end",
        "borer://taint/{entry},rax",
    ),
    (
        "borer://emulate/{address}",
        "Run code and read the result. The address carries an experiment: comma-separated reg=val, aN=val (the argument the decompiler names aN; a1 is the first), w<addr>=<hexbytes> (set data or patch code), stop=<addr>, steps=<n> (at most 20000000), trace=<n> (what each of the last n instructions changed; a small steps= watches the start instead), origin=<v> (the instruction that first put the value v in a register or in memory), profile=<n> (the n most-run addresses and most-read pages, where the steps went; at most 64), dump=<addr>:<len> (at most 4096 bytes, ?? where nothing is mapped). Reports final registers, the imported APIs and syscalls it serviced as api(args) -> ret with each argument decoded (a string as text, a flag or handle named, an unknown pointer as ptr 0x...), decoded text and each dump.",
        "borer://emulate/{entry},a1=5,steps=10000",
    ),
    (
        "borer://devirt/{address}",
        "Run a virtualized function and recover the program it executes: handlers summarized once, the trace cleaned of dead stores (writes nothing that runs after them reads) and cut into straight-line runs at every virtual branch, one line per step. The address carries comma-separated settings: budget=<n> raises the step cap (2000000 by default, at most 200000000) for a protector whose dispatch starts after a long bootstrap; strict faults on the first read of an import or of memory the loader would fill, where by default it reads zero and goes on; reg=<value> presets a register, such as the VM's context pointer the entry does not build",
        "borer://devirt/{entry},budget=4000000",
    ),
    (
        "borer://unpack/{address}",
        "Run a packer's bootstrap and report the code it decrypts into memory, with the original entry point. Append ,budget=N to raise the step cap toward a fuller unpack",
        "borer://unpack/{entry}",
    ),
    (
        "borer://calls/{callee}",
        "Every call site of a function or import (direct, through its slot or a thunk) with the arguments the decompiler resolves at each: a constant in hex, a string quoted, a global by name, else the expression, ? where the lifter saw none (an import is padded to its declared parameters). <callee>[,aN=<value>]...: aN=0x40 keeps the calls whose argument aN is that number, aN=text the ones whose argument or string contains it, aN=? the unseen ones; aN!=, aN> and aN< too; offset=<n> for the next page (200 rows a page, 500 callers decompiled at most)",
        "borer://calls/{entry}",
    ),
    (
        "borer://iocs/{filter}",
        "Indicators of one type (url, domain, ip, ipv4, ipv6, email, registry, path, pipe, mutex, object, useragent) or whose value contains the text, comma-separated; offset=<n> for the next page",
        "borer://iocs/url",
    ),
    (
        "borer://hidden/{filter}",
        "Run-time generated strings whose text or generator matches {filter}",
        "borer://hidden/http",
    ),
    (
        "borer://decoded/{filter}",
        "Decoder-recovered strings whose text contains {filter}; offset=<n> for the next page",
        "borer://decoded/http",
    ),
    (
        "borer://oracle/{address}",
        "Run the function at {address} over a probe string in every argument shape and report what it does with it",
        "borer://oracle/{entry}",
    ),
    (
        "borer://run/{spec}",
        "Call a function on inputs typed by its recovered signature and check its decompiled text on them: <function>[,steps=N]/<input>[;<input>...], each input its arguments in order: 5, -1, \"text\", hex:0102 or out:16 (a zeroed buffer). A row per input: the return value, the stop, the steps, the bytes each buffer holds after, and whether the text run as C agrees, differs (at a line) or is unchecked (at most 64 inputs, 1000000 steps each by default); then the imported APIs and syscalls the runs serviced as api(args) -> ret with each argument decoded",
        "borer://run/{entry}/5;-1",
    ),
    (
        "borer://diverge/{spec}",
        "Call a function on two inputs and report where the runs part ways: the first step that differs (the comparison that split them), the calls each side then makes, and the writes and serviced calls that differ: <function>[,steps=N]/<input>;<input>",
        "borer://diverge/{entry}/5;-1",
    ),
    (
        "borer://vectors/{spec}",
        "Test vectors for reimplementing a function: <function>[,count=N][,steps=N]. Inputs from the constants it compares and generated from its recovered signature (16 by default, at most 64), each run in the emulator: a row per input with what it returned and left in its buffers, then a C harness asserting the vectors that returned",
        "borer://vectors/{entry}",
    ),
    (
        "borer://diff/{path}",
        "Compare the loaded binary against another version at {path} and report which functions changed, were added or removed",
        "borer://diff/{path}",
    ),
    (
        "borer://difffn/{function}/{path}",
        "Show how one function changed between the loaded binary and another version at {path}, as a diff of the decompilations",
        "borer://difffn/{entry}/{path}",
    ),
    (
        "borer://carry/{path}",
        "Carry this project's names to another build of the same program: each name with its new address and how the function was paired, by identical body or by shape. An update moves every address, and the fingerprints do not move",
        "borer://carry/{path}",
    ),
    (
        "borer://migrate/{function}/{path}",
        "Migrate the field offsets a function reads from the loaded build to the version at {path}: which offsets are unchanged, removed, added, or moved",
        "borer://migrate/{entry}/{path}",
    ),
    (
        "borer://vm/{address}",
        "The handlers of one dispatch loop, each with what it does",
        "borer://vm/{entry}",
    ),
    (
        "borer://asserts/{filter}",
        "Asserted fields whose name or class contains the filter",
        "borer://asserts/count",
    ),
    (
        "borer://sources/{filter}",
        "Source files whose path contains the filter, with their function counts",
        "borer://sources/net",
    ),
    (
        "borer://classes/{filter}",
        "Registered classes whose name or code contains the filter",
        "borer://classes/player",
    ),
    (
        "borer://messages/{filter}",
        "Classes with a registered wire id whose name contains the filter, each with its named fields and the handlers testing for the id (200 a page)",
        "borer://messages/move",
    ),
    (
        "borer://map/{namespace}",
        "One namespace's classes, each with its role, parent, methods and instance (5000 rows at most)",
        "borer://map/net",
    ),
    (
        "borer://ports/{filter}",
        "The messages ports accept and their handlers, for the components or messages whose name contains the filter (5000 rows at most)",
        "borer://ports/move",
    ),
    (
        "borer://attrs/{filter}",
        "Registered attributes whose name or code contains the filter (200 a page); one exact match lists every function reading or writing it with the definition global",
        "borer://attrs/health",
    ),
    (
        "borer://exportpack/{spec}",
        "The session's names as a pack that names the same functions in another build by their first bytes: <name>, or <name>,all to add the names borer recovered",
        "borer://exportpack/mine,all",
    ),
    (
        "borer://scenario/{spec}",
        "A function decompiled under assumptions, <function>/<a2=5,a3=0>: branches and switches on them fold, only the code that can run is written, and the first line counts the blocks cut",
        "borer://scenario/{entry}/a1=5",
    ),
    (
        "borer://scenarios/{spec}",
        "A dispatcher exploded, <function>/<a2=0..32> or <function>/<a2=1|5>: a scenario per value, the values that behave alike grouped, each row with its blocks kept, calls and returns",
        "borer://scenarios/{entry}/a1=0..8",
    ),
    (
        "borer://script/{path}",
        "Runs a Rhai script file against the loaded program in borer's sandbox: what it printed, and the names and comments it proposes (set_name applies one)",
        "borer://script/scan.rhai",
    ),
    (
        "borer://clr/{filter}",
        "A .NET assembly's metadata rows of one kind (type, method, pinvoke, memberref, asmref, moduleref, string) or whose name or detail contains the text, comma-separated; offset=<n> for the next page",
        "borer://clr/pinvoke",
    ),
    (
        "borer://singletons/{filter}",
        "Singletons whose class name contains the filter",
        "borer://singletons/manager",
    ),
    (
        "borer://function/{address}",
        "function_summary at an address or name",
        "borer://function/{entry}",
    ),
    (
        "borer://decompile/{address}",
        "Pseudo-C of the function at an address or name",
        "borer://decompile/{entry}",
    ),
    (
        "borer://disasm/{address}",
        "Disassembly of the function at an address or name",
        "borer://disasm/{entry}",
    ),
    (
        "borer://fields/{address}",
        "Field offsets the function at an address or name dereferences, by (base, offset)",
        "borer://fields/{entry}",
    ),
    (
        "borer://fieldrefs/{offset}",
        "Every instruction program-wide that reads, writes or takes the address of \
                     [reg+offset], with its function; `offset[,name-filter]`, 500 rows at most",
        "borer://fieldrefs/0x10",
    ),
    (
        "borer://vslot/{slot}",
        "Every recovered class whose virtual at a zero-based vtable slot returns a \
                     constant (a wire id, a type tag), by value; `slot[,class-filter]`",
        "borer://vslot/3",
    ),
    (
        "borer://schema/{function}",
        "The record a deserializer reads off its stream (fields, widths, nesting, \
                     repeats), for a function by address or name, or the reading virtual of a class",
        "borer://schema/{entry}",
    ),
    (
        "borer://schemas/{slot}",
        "Every class with a constant at a zero-based vtable slot and the record its \
                     reading virtual decodes, one line each: a protocol as a table; `slot[,class-filter]`",
        "borer://schemas/3",
    ),
    (
        "borer://encode/{function}",
        "What a serializer writes onto its stream (fields in wire order, widths, the \
                     object field each came from, helpers followed into the members they write), \
                     for a function by address or name, or the writing virtual of a class",
        "borer://encode/{entry}",
    ),
    (
        "borer://hooks/{slot}",
        "Every class with a constant at a zero-based vtable slot with the addresses \
                     a binding hooks: its encoder, its decoder, its handler and each call site \
                     the client sends it from; `slot[,class-filter]`",
        "borer://hooks/3",
    ),
    (
        "borer://protocol/{slot}",
        "Every class with a constant at a zero-based vtable slot on one row with \
                     who constructs it, the handler receiving it, what it writes onto the wire \
                     and what it reads back: the whole protocol as one table; `slot[,class-filter]`",
        "borer://protocol/3",
    ),
    (
        "borer://senders/{slot}",
        "Every class with a constant at a zero-based vtable slot and the functions \
                     calling its factory or constructors: who sends each command, as a table; \
                     `slot[,class-filter]`",
        "borer://senders/3",
    ),
    (
        "borer://encodes/{slot}",
        "Every class with a constant at a zero-based vtable slot and what its writing \
                     virtual puts on the wire, one line each: the outbound protocol as a table; \
                     `slot[,class-filter]`",
        "borer://encodes/3",
    ),
    (
        "borer://shape/{function}",
        "Every function running the same code as the one at an address or name over \
                     other operands, with the strings and data addresses that differ: a \
                     registration family as a table",
        "borer://shape/{entry}",
    ),
    (
        "borer://anchors/{path}",
        "Every pinned fact in a manifest file (`field <class> <name> <offset>`, \
                     `vconst <slot> <class> <value>`, `function <name> <rva>`, `encode <class> \
                     <layout>`, `decode <class> <layout>` lines) derived again from the loaded \
                     binary and reported held, moved, changed or gone",
        "borer://anchors/client.anchors",
    ),
    (
        "borer://changes/{path}",
        "What changed since a snapshot file of an earlier build (written by the CLI's \
                     `borer snapshot <binary> <file>`): commands, packet layouts, attributes, \
                     message routes and ids added, removed or changed, by stable name",
        "borer://changes/before.snapshot",
    ),
    (
        "borer://about/{name}",
        "Everything known about one name, from every table at once: the attribute \
                     (with each user reading or writing it), the class (role, parent, instance, \
                     virtuals, the messages it accepts or the components handling it, the wire \
                     for a command), and the function summary; start here with any name",
        "borer://about/{entry}",
    ),
    (
        "borer://grep/{text}",
        "Pseudo-C lines program-wide containing the text (percent-encoded), or \
                     matching it when written re:<expression>, with their function, its \
                     signature and the if/else/loop/switch/case lines enclosing them \
                     (numbered ^N); decompiles \
                     everything once into the index on first use; 200 matching lines at most",
        "borer://grep/memcpy",
    ),
];

/// The `# more:` line of `binary_info`: every resource template by name,
/// from [`RESOURCE_TEMPLATES`] itself.
///
/// The line was written by hand and named 14 of 45 templates, so an agent
/// reading it never learned of the rest.
fn template_names() -> String {
    let names: Vec<&str> = RESOURCE_TEMPLATES
        .iter()
        .map(|&(uri, _, _)| resource_name(uri))
        .collect();
    format!(
        "{} templated resources read by URI through resources/read or the query tool, each described by resources/templates/list or read without its argument: {}",
        names.len(),
        names.join(", ")
    )
}

/// The name a resource is listed under: the first segment of its path,
/// `vslot` for `borer://vslot/{slot}`.
///
/// # Arguments
///
/// * `uri` - The resource URI or URI template.
fn resource_name(uri: &str) -> &str {
    let path = uri.strip_prefix("borer://").unwrap_or(uri);
    path.split_once('/').map_or(path, |(name, _)| name)
}

/// Reads a `Class+offset` target: a class's field.
///
/// The class is a class name as
/// [`borer_engine::analysis::classes::resolve_class`] reads it, a class
/// known by its vtable alone, or the address or name of a class's vtable
/// (`0x140123450`, `Net::Client::vftable`); the offset is hex or
/// decimal.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, with the classes and their vtables.
/// * `o` - Names in force.
/// * `text` - The target as the agent passed it.
///
/// # Returns
///
/// The qualified class and the offset, or `None` when the text is not of
/// that form or names no class.
fn class_field(p: &Program, a: &Analysis, o: &Overlay, text: &str) -> Option<(String, u64)> {
    let (head, off) = text.rsplit_once('+')?;
    let offset = parse_addr(off)?;
    let head = head.trim();
    let class = borer_engine::analysis::classes::resolve_class(a, o, head)
        .or_else(|| {
            a.classes
                .by_name
                .contains_key(head)
                .then(|| head.to_owned())
        })
        .or_else(|| {
            resolve(p, a, o, head)
                .ok()
                .and_then(|va| a.classes.vtables.get(&va).cloned())
        })?;
    Some((class, offset))
}

/// Strips schema noise an agent never needs.
///
/// Gone are the draft URL, integer formats, non-negativity bounds (every
/// count documents its own default and maximum), the `null` alternative
/// schemars adds to an optional parameter's type or enum (leaving the
/// parameter out is how a client says null), and `additionalProperties:
/// false`, which every parameter struct enforces at the boundary through
/// `deny_unknown_fields` with an error that names the field. An enum
/// parameter's `$defs` entry is written into the parameter itself, with the
/// parameter's own description, so a client reads its choices in place
/// rather than following a `$ref`.
///
/// # Arguments
///
/// * `t` - The tool as generated by rmcp.
fn slim_tool(mut t: Tool) -> Tool {
    let mut schema = (*t.input_schema).clone();
    schema.remove("$schema");
    schema.remove("additionalProperties");
    let defs = match schema.remove("$defs") {
        Some(serde_json::Value::Object(defs)) => defs,
        _ => serde_json::Map::new(),
    };
    if let Some(serde_json::Value::Object(props)) = schema.get_mut("properties") {
        for p in props.values_mut() {
            if let serde_json::Value::Object(o) = p {
                o.remove("format");
                o.remove("minimum");
                if let Some(serde_json::Value::Array(any)) = o.get("anyOf") {
                    let mut rest = any.iter().filter(|s| s.get("type") != Some(&"null".into()));
                    if let (Some(serde_json::Value::Object(only)), None) =
                        (rest.next(), rest.next())
                    {
                        let only = only.clone();
                        o.remove("anyOf");
                        o.extend(only);
                    }
                }
                let inlined = o
                    .get("$ref")
                    .and_then(serde_json::Value::as_str)
                    .and_then(|r| r.strip_prefix("#/$defs/"))
                    .and_then(|name| defs.get(name))
                    .and_then(serde_json::Value::as_object)
                    .cloned();
                if let Some(def) = inlined {
                    o.remove("$ref");
                    for (k, v) in def {
                        if k != "description" || !o.contains_key("description") {
                            o.insert(k, v);
                        }
                    }
                }
                let only = match o.get("type") {
                    Some(serde_json::Value::Array(kinds)) => {
                        let mut rest = kinds.iter().filter(|k| k.as_str() != Some("null"));
                        match (rest.next(), rest.next()) {
                            (Some(kind), None) => Some(kind.clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                if let Some(kind) = only {
                    o.insert("type".to_owned(), kind);
                }
            }
        }
    }
    if !defs.is_empty()
        && serde_json::Value::Object(schema.clone())
            .to_string()
            .contains("\"$ref\"")
    {
        schema.insert("$defs".to_owned(), serde_json::Value::Object(defs));
    }
    t.input_schema = Arc::new(schema);
    t
}

impl BorerServer {
    /// Lists function names (overlay, symbols, `sub_X`) starting with a prefix.
    ///
    /// # Arguments
    ///
    /// * `prefix` - Lower-cased prefix; empty lists everything.
    ///
    /// # Returns
    ///
    /// Sorted, deduplicated names; empty when no analysis is available.
    fn complete_names(&self, prefix: &str) -> Vec<String> {
        let Ok(a) = self.ensure_analysis() else {
            return Vec::new();
        };
        let o = self.overlay();
        let mut names: Vec<String> = a
            .functions
            .iter()
            .map(|f| borer_engine::analysis::name_of(&a, &o, f.entry))
            .filter(|n| n.to_lowercase().starts_with(prefix))
            .collect();
        names.sort();
        names.dedup();
        names
    }
}

/// Runs a worker of the MCP server, the relay in front of it, or a CLI
/// command, by what the process was started with.
///
/// The host launches the binary with no arguments, which is the relay
/// ([`relay::run`]); the relay starts this same binary again as the worker
/// ([`relay::WORKER`]), which serves the session ([`serve`]). With
/// arguments it runs a CLI command.
///
/// Every one of them runs below normal priority
/// ([`borer_live::run_below_normal`]): an analysis takes every core it is
/// given, and a machine running several of them at once stays usable
/// because its desktop goes first. Its allocator commits memory as it is
/// touched ([`borer_live::commit_on_demand`]).
///
/// # Errors
///
/// When the tokio runtime cannot be built, the server or the relay fails,
/// or the CLI command fails.
fn main() -> anyhow::Result<()> {
    borer_live::run_below_normal();
    borer_live::commit_on_demand();
    if let Some(state) = std::env::var_os(relay::WORKER) {
        let resume = std::env::var_os(relay::RESUME).map(PathBuf::from);
        return tokio::runtime::Runtime::new()?.block_on(serve(PathBuf::from(state), resume));
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return relay::run();
    }
    end_quietly_when_stdout_closes();
    cli::cli(&args)
}

/// Serves the MCP session over this worker's standard handles.
///
/// A worker taking over from one that handed over serves without a
/// handshake, since the client initialized the session with an earlier
/// worker; it loads the file that worker had loaded, with its names and
/// comments, and tells the client the tools changed.
///
/// # Arguments
///
/// * `state` - The file this worker writes the session's state to when
///   `reload` hands it over ([`relay::WORKER`]).
/// * `resume` - The state of the worker before this one, when this one
///   takes over ([`relay::RESUME`]).
///
/// # Errors
///
/// When the handshake or the transport fails.
async fn serve(state: PathBuf, resume: Option<PathBuf>) -> anyhow::Result<()> {
    let server = BorerServer::new();
    let transport = HandOverTransport::new(Arc::clone(&server.hand_over), state);
    let Some(file) = resume else {
        server.serve(transport).await?.waiting().await?;
        return Ok(());
    };
    let resume = Resume::take(&file).unwrap_or_else(|e| {
        eprintln!("borer: the session resumes without its state: {e}");
        Resume::default()
    });
    let info = server.resume(resume);
    let service = rmcp::service::serve_directly(server, transport, info);
    if let Err(e) = service.peer().notify_tool_list_changed().await {
        eprintln!("borer: the client was not told the tools changed: {e}");
    }
    service.waiting().await?;
    Ok(())
}

impl BorerServer {
    /// A server with nothing loaded and the packs `BORER_PACKS` names.
    fn new() -> BorerServer {
        BorerServer {
            packs: read_packs(&env_pack_files()).unwrap_or_else(|e| {
                eprintln!("borer: {e:#}; running without packs");
                Arc::default()
            }),
            ..BorerServer::default()
        }
    }

    /// Loads the file the worker before this one had loaded, the way it was
    /// loaded (its `pdb`, `entry_file_offset` and raw layout), with its
    /// names and comments.
    ///
    /// A file that no longer loads is said on stderr and the session goes on
    /// without it.
    ///
    /// # Arguments
    ///
    /// * `resume` - The state that worker wrote.
    ///
    /// # Returns
    ///
    /// What the client sent at initialize, for this worker to serve the
    /// session with; `None` when the state does not hold it.
    fn resume(
        &self,
        Resume {
            peer_info,
            project,
            pdb,
            entry_file_offset,
            raw,
        }: Resume,
    ) -> Option<InitializeRequestParams> {
        if let Some(project) = project {
            let overlay = project.to_overlay();
            let reloaded = self.load_binary(Parameters(LoadBinaryParams {
                path: project.program,
                entry_file_offset,
                pdb,
                arch: raw.arch,
                base: raw.base,
                entry: raw.entry,
                regions: raw.regions,
            }));
            if let Err(e) = reloaded {
                eprintln!(
                    "borer: reloading the file after the hand-over: {}",
                    e.message
                );
            } else if let Err(e) = overlay {
                eprintln!("borer: the handed-over project's types: {e}");
            } else if let Ok(o) = overlay {
                *write_lock(&self.overlay) = o;
            }
        }
        peer_info
    }
}

// ------------------------------------------------------------- hand-over ----

/// What the worker taking over resumes from, written by the one handing
/// over to the file the relay names.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct Resume {
    /// What the client sent at initialize, for the next worker to serve the
    /// session with.
    peer_info: Option<InitializeRequestParams>,
    /// The loaded file with its names and comments, for the next worker to
    /// load again; `None` when nothing was loaded.
    project: Option<borer::project::ProjectFile>,
    /// Whether the loaded file's companion PDB applied (`load_binary`'s
    /// `pdb`), for the next worker to load it the same way.
    pdb: Option<bool>,
    /// The `entry_file_offset` the file was loaded with, for the next
    /// worker to load it the same way.
    entry_file_offset: Option<u64>,
    /// The raw layout the file was mapped by, for the next worker to map
    /// it the same way; absent from the state of a worker built before it.
    #[serde(default)]
    raw: RawLoad,
}

impl Resume {
    /// Writes the state to `file` and ends this worker with
    /// [`relay::HAND_OVER`], which the relay answers by starting the next
    /// one. A state that cannot be written is said on stderr; the next
    /// worker then serves the session without it.
    ///
    /// # Arguments
    ///
    /// * `file` - The file the relay named ([`relay::WORKER`]).
    fn hand_over(&self, file: &Path) -> ! {
        if let Err(e) = serde_json::to_vec(self)
            .map_err(std::io::Error::other)
            .and_then(|json| std::fs::write(file, json))
        {
            eprintln!(
                "borer: the session's state does not survive the reload ({}): {e}",
                file.display()
            );
        }
        std::process::exit(relay::HAND_OVER)
    }

    /// Reads the state the worker before this one wrote, and removes the
    /// file.
    ///
    /// # Arguments
    ///
    /// * `file` - The file the relay named ([`relay::RESUME`]).
    ///
    /// # Errors
    ///
    /// When the file cannot be read or does not parse.
    fn take(file: &Path) -> Result<Resume, String> {
        let json = std::fs::read(file).map_err(|e| format!("read {}: {e}", file.display()))?;
        if let Err(e) = std::fs::remove_file(file) {
            eprintln!("borer: remove {}: {e}", file.display());
        }
        serde_json::from_slice(&json).map_err(|e| format!("parse {}: {e}", file.display()))
    }
}

/// The hand-over to the next worker, shared between the server, which asks
/// for it from `reload`, and the transport, which carries it out once
/// nothing is in flight.
///
/// The relay passes this worker no request after the reload call, so the
/// worker ends once the reload reply and the replies to every request
/// before it have been written ([`HandOverTransport`]): none of those is
/// lost, and whatever the client sends after the call goes to the next
/// worker.
#[derive(Debug, Default)]
struct HandOver {
    /// The bookkeeping, under one lock.
    state: Mutex<HandOverState>,
}

/// What [`HandOver`] keeps.
#[derive(Debug, Default)]
struct HandOverState {
    /// The requests read and not yet answered or cancelled.
    in_flight: HashSet<RequestId>,
    /// The state to hand over once nothing is in flight; set by `reload`.
    pending: Option<Resume>,
}

impl HandOver {
    /// Notes a request read.
    ///
    /// # Arguments
    ///
    /// * `id` - The request's id.
    fn asked(&self, id: RequestId) {
        lock(&self.state).in_flight.insert(id);
    }

    /// Notes a request answered or cancelled, and hands over, ending this
    /// worker, when that leaves nothing in flight behind a scheduled reload.
    ///
    /// # Arguments
    ///
    /// * `id` - The request's id.
    /// * `file` - Where the state goes ([`relay::WORKER`]).
    fn answered(&self, id: &RequestId, file: &Path) {
        let mut s = lock(&self.state);
        s.in_flight.remove(id);
        if s.in_flight.is_empty()
            && let Some(resume) = s.pending.take()
        {
            resume.hand_over(file);
        }
    }

    /// Schedules the hand-over for when nothing is in flight.
    ///
    /// The reload call is itself in flight until its reply is written, so
    /// the hand-over always follows that reply ([`Self::answered`]).
    ///
    /// # Arguments
    ///
    /// * `resume` - What the next worker resumes from.
    fn schedule(&self, resume: Resume) {
        lock(&self.state).pending = Some(resume);
    }
}

/// The stdio transport with the hand-over wired in.
///
/// It notes each request read and each reply written, and hands over once
/// the reload reply and every earlier one are out. Each reply written also
/// hands the memory its request freed back to the system
/// ([`borer_live::release_free_memory`]), so a worker waiting for its next
/// request holds only what it uses.
struct HandOverTransport {
    /// The line-framed transport over standard input and output.
    inner: AsyncRwTransport<RoleServer, tokio::io::Stdin, tokio::io::Stdout>,
    /// The shared bookkeeping.
    hand_over: Arc<HandOver>,
    /// The file the state goes to on a hand-over ([`relay::WORKER`]).
    state: Arc<Path>,
}

impl HandOverTransport {
    /// A transport over this process's standard handles.
    ///
    /// # Arguments
    ///
    /// * `hand_over` - The server's hand-over state.
    /// * `state` - The file the state goes to on a hand-over.
    fn new(hand_over: Arc<HandOver>, state: PathBuf) -> HandOverTransport {
        HandOverTransport {
            inner: AsyncRwTransport::new(tokio::io::stdin(), tokio::io::stdout()),
            hand_over,
            state: state.into(),
        }
    }
}

impl Transport<RoleServer> for HandOverTransport {
    type Error = std::io::Error;

    fn send(
        &mut self,
        item: TxJsonRpcMessage<RoleServer>,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send + 'static {
        let answered = match &item {
            JsonRpcMessage::Response(r) => Some(r.id.clone()),
            JsonRpcMessage::Error(e) => e.id.clone(),
            JsonRpcMessage::Request(_) | JsonRpcMessage::Notification(_) => None,
        };
        let send = self.inner.send(item);
        let hand_over = Arc::clone(&self.hand_over);
        let state = Arc::clone(&self.state);
        async move {
            send.await?;
            if let Some(id) = answered {
                hand_over.answered(&id, &state);
                borer_live::release_free_memory();
            }
            Ok(())
        }
    }

    async fn receive(&mut self) -> Option<RxJsonRpcMessage<RoleServer>> {
        let msg = self.inner.receive().await?;
        match &msg {
            JsonRpcMessage::Request(r) => self.hand_over.asked(r.id.clone()),
            JsonRpcMessage::Notification(n) => {
                if let ClientNotification::CancelledNotification(c) = &n.notification
                    && let Some(id) = &c.params.request_id
                {
                    self.hand_over.answered(id, &self.state);
                }
            }
            JsonRpcMessage::Response(_) | JsonRpcMessage::Error(_) => {}
        }
        Some(msg)
    }

    fn close(&mut self) -> impl Future<Output = Result<(), Self::Error>> + Send {
        self.inner.close()
    }
}

/// Ends the process quietly, and successfully, when the reader of stdout
/// has gone (`borer functions x.exe | head`), which the print macros report
/// by panicking.
///
/// Every other panic still reaches the default hook.
fn end_quietly_when_stdout_closes() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let message = info
            .payload()
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| info.payload().downcast_ref::<&str>().copied())
            .unwrap_or("");
        if message.starts_with("failed printing to stdout") {
            std::process::exit(0);
        }
        default(info);
    }));
}

/// The pack files `BORER_PACKS` lists, in order ([`borer::packs::env_paths`]).
fn env_pack_files() -> Vec<String> {
    borer::packs::env_paths("BORER_PACKS")
        .unwrap_or_default()
        .iter()
        .map(|p| p.to_string_lossy().into_owned())
        .collect()
}

/// Reads pack files into the packs an analysis runs with, printing each
/// pack's warnings to stderr.
///
/// # Arguments
///
/// * `files` - The pack files, in load order.
///
/// # Errors
///
/// When a file cannot be read or is not a pack.
fn read_packs(files: &[String]) -> anyhow::Result<Arc<Packs>> {
    let mut packs = Vec::with_capacity(files.len());
    for file in files {
        let shown = borer_engine::text::short_path(file);
        let text = std::fs::read_to_string(file)
            .map_err(|e| anyhow::anyhow!("reading pack {shown}: {e}"))?;
        let (mut pack, warnings) = Pack::parse(&text, &shown).map_err(anyhow::Error::msg)?;
        for w in warnings {
            eprintln!("borer: {w}");
        }
        borer::packs::load_scripts(&mut pack, Path::new(file)).map_err(anyhow::Error::msg)?;
        packs.push(pack);
    }
    Ok(Arc::new(Packs { packs }))
}

#[cfg(test)]
mod tests {
    use super::percent_decode;

    /// The zero-copy span filter answers what the text filter answers for
    /// every row shape: ASCII and UTF-16 spans, case folds, a needle past
    /// the display cut, and a non-ASCII needle no walked text holds.
    ///
    /// # Panics
    ///
    /// When the byte test disagrees with the lowered-text test.
    #[test]
    fn span_filter_answers_what_the_text_filter_answers() {
        use borer_engine::program::{Arch, Program};
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(b"Kernel32.DLL\x00");
        bytes.extend_from_slice(b"short\x00");
        bytes.extend_from_slice(&[
            b'L', 0, b'o', 0, b'N', 0, b'g', 0, b'W', 0, b'i', 0, b'd', 0, b'e', 0,
        ]);
        bytes.push(0);
        let long: Vec<u8> = b"xyzABCDEFGH".iter().cycle().take(600).copied().collect();
        bytes.extend_from_slice(&long);
        bytes.push(0);
        let p = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
        let rows: Vec<super::StringRow> = borer_engine::strings::find_ascii_spans(&p.bytes, 4)
            .into_iter()
            .map(super::StringRow::Span)
            .chain(
                borer_engine::strings::find_wide_spans(&p.bytes, 4)
                    .into_iter()
                    .map(super::StringRow::Span),
            )
            .collect();
        assert_eq!(rows.len(), 4, "{rows:?}");
        for needle in [
            "kernel32",
            "KERNEL32.DLL",
            "short",
            "wide",
            "lOnGwIdE",
            "xyzabcdefgh",
            "ü",
            "",
        ] {
            let filter = super::Filter::new(Some(needle));
            for row in &rows {
                let want = filter.accepts(&row.full_text(&p.bytes));
                assert_eq!(
                    super::row_matches(&p, row, &filter),
                    want,
                    "{needle:?} at {:?}",
                    row.full_text(&p.bytes)
                );
            }
        }
    }

    /// The span filter and the text filter agree on the needle edge
    /// cases: mixed case, a needle longer than the string, one that is
    /// the string, and one holding NULs.
    ///
    /// # Panics
    ///
    /// When the span filter and the text filter disagree on a needle.
    #[test]
    fn span_filter_agrees_on_needle_edge_cases() {
        use borer_engine::program::{Arch, Program};
        let mut bytes: Vec<u8> = b"Kernel32.DLL\x00".to_vec();
        bytes.extend(b"LoNgWiDe".iter().flat_map(|b| [*b, 0]));
        bytes.push(0);
        let p = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
        let rows: Vec<super::StringRow> = borer_engine::strings::find_ascii_spans(&p.bytes, 4)
            .into_iter()
            .map(super::StringRow::Span)
            .chain(
                borer_engine::strings::find_wide_spans(&p.bytes, 4)
                    .into_iter()
                    .map(super::StringRow::Span),
            )
            .collect();
        assert_eq!(rows.len(), 2, "{rows:?}");
        for needle in [
            "Kernel32.DLL",
            "KERNEL32.dll",
            "LoNgWiDe",
            "lOnGwIdE",
            "Kernel32.DLL_EXTRA",
            "\0",
            "32.D\0L",
        ] {
            let filter = super::Filter::new(Some(needle));
            for row in &rows {
                let want = filter.accepts(&row.full_text(&p.bytes));
                assert_eq!(
                    super::row_matches(&p, row, &filter),
                    want,
                    "needle {needle:?} on {:?}",
                    row.full_text(&p.bytes)
                );
            }
        }
    }

    /// An answer with its evidence line taken off, so two emissions of one
    /// answer compare: the id names the emission, so that is the one line
    /// that differs between them.
    ///
    /// # Arguments
    ///
    /// * `sent` - An answer as sent.
    fn without_evidence(sent: &str) -> &str {
        let at = sent.trim_end_matches('\n').rfind('\n').map_or(0, |i| i + 1);
        let last = &sent[at..];
        if last.starts_with("# evidence:") || last.starts_with("%% evidence:") {
            &sent[..at]
        } else {
            sent
        }
    }

    /// Every answer ends with an evidence line naming it, and the id it
    /// names returns the answer exactly as it was sent.
    ///
    /// The line is the answer's last, a `# since=` line before it, and the
    /// id is `<n>-<8 hex digits>`; an id no `# evidence:` line carried is
    /// refused as invalid params.
    ///
    /// # Panics
    ///
    /// When the line is missing or malformed, or the read is not the text.
    #[test]
    fn an_answer_ends_with_evidence_that_returns_it() {
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x200];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x201, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let whole = server.read_uri("borer://disasm/0x1000").expect("reads").1;
        let last = whole.lines().last().expect("a last line");
        let id = last
            .strip_prefix("# evidence: ")
            .expect("the answer ends with its evidence line")
            .to_owned();
        let (counter, digest) = id.split_once('-').expect("the id is <n>-<digest>");
        assert!(!counter.is_empty() && counter.chars().all(|c| c.is_ascii_alphanumeric()));
        assert_eq!(digest.len(), 8, "{id}");
        assert!(digest.chars().all(|c| c.is_ascii_hexdigit()), "{id}");
        let evidence_uri = format!("borer://session/evidence/{id}");
        let (read_as, back) = server.read_uri(&evidence_uri).expect("reads");
        assert_eq!((read_as.as_str(), back), (evidence_uri.as_str(), whole));
        let refused = server
            .read_uri("borer://session/evidence/9999-00000000")
            .expect_err("never minted");
        assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS);
    }

    /// A fault inside a tool becomes an answer, not a dead session.
    ///
    /// An analysis pass that faults would otherwise unwind out of the handler
    /// and end the process: the call gets no reply, the agent cannot tell a
    /// crash from a hang, and the session's work is gone with it. Every tool
    /// body that reaches a program comes through one place, so the fault is
    /// turned into an error there and the message says what happened. The
    /// panic hook is silenced for the fault: the backtrace it would print is
    /// the point of leaving it alone in the real path, and only noise in a
    /// test that expects the fault. The server is then still usable, which
    /// is the whole point. Only a fault is an internal error: a body that
    /// refuses its request (an address naming nothing) answers invalid
    /// params, so the agent knows to fix the call rather than retry it.
    ///
    /// # Panics
    ///
    /// When a fault escapes, its message is lost on the way out, or a
    /// refusal and a fault share one error code.
    #[test]
    fn a_fault_inside_a_tool_is_answered_not_fatal() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let program = borer_engine::program::Program::load(&exe).expect("it loads itself");
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };

        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let faulted = server.with_program(|_| panic!("a pass fell over"));
        let sound = server.with_program(|p| Ok(format!("{} sections", p.sections.len())));
        let refused = server.with_program(|_| Err("'nowhere' names nothing".to_owned()));
        std::panic::set_hook(hook);

        let refused = refused.expect_err("the refusal reached the caller");
        assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS);
        let faulted = faulted.expect_err("the fault reached the caller");
        assert_eq!(faulted.code, super::ErrorCode::INTERNAL_ERROR);
        let err = faulted.message;
        assert!(err.contains("faulted"), "{err}");
        assert!(!err.contains("  "), "the message reads as one line: {err}");
        assert!(
            err.contains("a pass fell over"),
            "the message is lost: {err}"
        );
        assert!(sound.is_ok(), "the next call failed too");
    }

    /// A refused `load_binary` changes nothing.
    ///
    /// The session keeps the program it had and the load options it was loaded
    /// with. The `pdb` setting was written before the load was tried, so a
    /// failed load with `pdb=false` made the next comparison build skip its
    /// PDB.
    ///
    /// # Panics
    ///
    /// When a refused load changes the session.
    #[test]
    fn a_refused_load_changes_nothing() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let exe = exe.display().to_string();
        let load = |path: &str, pdb: Option<bool>, entry_file_offset: Option<u64>| {
            super::LoadBinaryParams {
                path: path.to_owned(),
                entry_file_offset,
                pdb,
                arch: None,
                base: None,
                entry: None,
                regions: None,
            }
        };
        let server = super::BorerServer::default();
        server
            .load_binary(super::Parameters(load(&exe, Some(true), None)))
            .expect("the test binary loads");
        let missing = server.load_binary(super::Parameters(load(
            "no/such/file.exe",
            Some(false),
            Some(0),
        )));
        assert!(missing.is_err());
        let past = server.load_binary(super::Parameters(load(&exe, Some(false), Some(u64::MAX))));
        assert!(past.is_err());
        assert!(
            *super::read_lock(&server.pdb_applied),
            "the pdb setting moved"
        );
        assert_eq!(*super::read_lock(&server.entry_file_offset), None);
        assert!(server.loaded().is_some(), "the program was dropped");
    }

    /// `fetch_pdb` names this build's PDB when one is on disk instead of
    /// offering to fetch it.
    ///
    /// A load with `pdb=false` leaves the PDB beside the binary unapplied, and
    /// the dry run offered a download of the file already there. A build
    /// without its PDB on disk has nothing to ask about, and nothing is
    /// asserted.
    ///
    /// # Panics
    ///
    /// When the dry run offers a fetch of a PDB on disk.
    #[test]
    fn fetch_pdb_names_a_pdb_already_on_disk() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let server = super::BorerServer::default();
        server
            .load_binary(super::Parameters(super::LoadBinaryParams {
                path: exe.display().to_string(),
                entry_file_offset: None,
                pdb: Some(false),
                arch: None,
                base: None,
                entry: None,
                regions: None,
            }))
            .expect("the test binary loads");
        let on_disk = server.loaded().and_then(|p| {
            let record = p.pdb_record.as_ref()?;
            borer_engine::pdb::resolved(&p.path, record, None)
        });
        if on_disk.is_none() {
            return;
        }
        let said = server
            .fetch_pdb(super::Parameters(super::FetchPdbParams {
                dry_run: None,
                server: None,
            }))
            .expect("the dry run answers");
        assert!(said.contains("nothing to fetch"), "{said}");
        assert!(!said.contains("would fetch"), "{said}");
    }

    /// A fresh session renders constants by the binary's name tables, as a
    /// session that has already decompiled does: no answer depends on the
    /// calls before it.
    ///
    /// # Panics
    ///
    /// When the snapshot reads no tables.
    #[test]
    fn every_overlay_snapshot_reads_the_binarys_tables() {
        let server = super::BorerServer::default();
        assert_eq!(
            server.overlay().enum_source,
            borer_engine::analysis::EnumSource::Binary,
            "a fresh session renders constants as one that has decompiled"
        );
    }

    /// Before `load_binary`, `functions` refuses the way every other tool
    /// does: invalid params, naming the call to make first.
    ///
    /// It read the analysis outside the tool-body boundary and answered the
    /// one refusal its siblings give as invalid params as an internal error
    /// instead, so a client telling the two codes apart saw a broken server
    /// where every other tool showed a missing step.
    ///
    /// # Panics
    ///
    /// When the refusal differs from a sibling's in code or message.
    #[test]
    fn functions_refuses_without_a_binary_like_every_other_tool() {
        let server = super::BorerServer::default();
        let refused = server
            .functions(super::Parameters(super::FunctionsParams {
                filter: None,
                sort: None,
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect_err("nothing is loaded");
        let sibling = server
            .function(super::Parameters(super::FunctionDetailParams {
                address: "0x1000".to_owned(),
                offset: None,
            }))
            .expect_err("nothing is loaded");
        assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS);
        assert_eq!(refused.code, sibling.code);
        assert_eq!(refused.message, sibling.message);
        assert_eq!(refused.message, super::NO_BINARY);
    }

    /// Every resource read before a binary is loaded is refused as invalid
    /// params, the code every tool answers then.
    ///
    /// `qt`, `map`, `classes`, `singletons` and `enums` answered an
    /// internal error, which reads as the server failing rather than the
    /// request coming too early.
    ///
    /// # Panics
    ///
    /// When a resource answers an internal error, or one of the five does
    /// not refuse with [`super::NO_BINARY`].
    #[test]
    fn every_resource_refuses_without_a_binary_as_invalid_params() {
        let server = super::BorerServer::default();
        for uri in ["qt", "map", "classes", "singletons", "enums"] {
            let refused = server
                .resource_text(&format!("borer://{uri}"))
                .expect_err("nothing is loaded");
            assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS, "{uri}");
            assert_eq!(refused.message, super::NO_BINARY, "{uri}");
        }
        let uris = super::RESOURCES
            .iter()
            .map(|r| r.0)
            .chain(super::RESOURCE_TEMPLATES.iter().map(|t| t.0))
            .map(|uri| {
                uri.split('/')
                    .map(|part| if part.starts_with('{') { "x" } else { part })
                    .collect::<Vec<_>>()
                    .join("/")
            });
        for uri in uris {
            if let Err(e) = server.resource_text(&uri) {
                assert_ne!(e.code, super::ErrorCode::INTERNAL_ERROR, "{uri}: {e:?}");
            }
        }
    }

    /// Asking for nothing returns a function that fits the page exactly as
    /// it was.
    ///
    /// The usual answer is what every existing caller and the determinism contract
    /// depend on, so the window is only opened on request or when the page cuts.
    ///
    /// # Panics
    ///
    /// When a decompile nobody narrowed comes back changed.
    #[test]
    fn a_decompile_nobody_narrowed_is_returned_whole() {
        let text = "// head\nint main() {\n  return 0;\n}\n";
        assert_eq!(super::window(text, None, None, None), text);
    }

    /// A function longer than the page is paged unasked, and `limit=0`
    /// asks for every line.
    ///
    /// # Panics
    ///
    /// When a long function comes back whole by default, or cut at zero.
    #[test]
    fn a_long_decompile_is_paged_by_default_and_zero_means_all() {
        let long: String = (0..super::DECOMPILE_LINES_DEFAULT + 1)
            .map(|i| format!("line {i}\n"))
            .collect();
        let paged = super::window(&long, None, None, None);
        let head = format!(
            "// showing {} of {} lines from 0; offset={} continues\n",
            super::DECOMPILE_LINES_DEFAULT,
            super::DECOMPILE_LINES_DEFAULT + 1,
            super::DECOMPILE_LINES_DEFAULT
        );
        assert!(paged.starts_with(&head), "{paged}");
        assert_eq!(paged.lines().count(), super::DECOMPILE_LINES_DEFAULT + 1);
        assert_eq!(super::window(&long, None, None, Some(0)), long);
    }

    /// A cut page names the line the declarations end on while it starts
    /// inside them, and the offset the next page starts at while one is
    /// left; the last page names neither.
    ///
    /// # Panics
    ///
    /// When a header misnames the declarations or the next offset.
    #[test]
    fn a_cut_page_names_where_the_declarations_end_and_what_comes_next() {
        let text: String = ["// f @ 0x1000\n// signature: void f(void)\n".to_owned()]
            .into_iter()
            .chain((0..400).map(|i| format!("uint64_t local_{i};\n")))
            .chain(std::iter::once("\n".to_owned()))
            .chain((0..600).map(|i| format!("x = {i};\n")))
            .collect();
        let head = |offset| {
            super::window(&text, None, offset, None)
                .lines()
                .next()
                .unwrap_or_default()
                .to_owned()
        };
        assert_eq!(
            head(None),
            "// showing 300 of 1003 lines from 0; declarations end at line 402; offset=300 continues"
        );
        assert_eq!(
            head(Some(300)),
            "// showing 300 of 1003 lines from 300; declarations end at line 402; offset=600 continues"
        );
        assert_eq!(
            head(Some(500)),
            "// showing 300 of 1003 lines from 500; offset=800 continues"
        );
        assert_eq!(head(Some(900)), "// showing 103 of 1003 lines from 900");
        let filtered = super::window(&text, Some("x = 1"), None, Some(5));
        assert!(
            filtered.starts_with(
                "// 111 of 1003 lines carry \"x = 1\", showing 5 from 0; offset=5 continues\n"
            ),
            "{filtered}"
        );
    }

    /// A function a batch cuts at its share ends with a note whose offset,
    /// passed to `decompile`, picks it up at the line after the last one
    /// the batch shows, counted as `decompile` numbers its lines.
    ///
    /// # Panics
    ///
    /// When the note is missing or its offset skips or repeats a line.
    #[test]
    fn a_cut_batch_function_says_where_decompile_continues() {
        use super::{DecompileBatchParams, DecompileParams, Parameters};
        use borer_engine::program::{Arch, Program, Section};
        let mut code = Vec::new();
        for n in 0u32..400 {
            // ASM: mov dword [rcx + n*8], n
            code.extend_from_slice(&[0xc7, 0x81]);
            code.extend_from_slice(&(n * 8).to_le_bytes());
            code.extend_from_slice(&n.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(1),
            }))
            .expect("batch");
        let note = batch
            .lines()
            .find(|l| l.starts_with("// truncated at line "))
            .unwrap_or_else(|| panic!("no cut note: {batch}"));
        let offset: u32 = note
            .split_once("offset=")
            .and_then(|(_, rest)| rest.split(')').next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no offset: {note}"));
        assert!(
            note.ends_with(&format!(
                "; decompile(address=0x1000, offset={offset}) continues"
            )),
            "{note}"
        );
        let decompile = |offset, limit| {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset,
                    limit: Some(limit),
                }))
                .expect("decompiles")
        };
        let whole = decompile(None, 0);
        let lines: Vec<&str> = whole.lines().collect();
        let at = usize::try_from(offset).expect("small");
        let kept: Vec<&str> = batch.lines().take_while(|l| *l != note).collect();
        assert_eq!(kept.last().copied(), lines.get(at - 1).copied(), "{batch}");
        let page = decompile(Some(offset), 1);
        let first = page
            .lines()
            .find(|l| !l.starts_with("//") && !l.trim_start().starts_with('^'))
            .unwrap_or_default();
        assert_eq!(
            first,
            format!(
                "{:>5}  {}",
                at + 1,
                lines.get(at).copied().unwrap_or_default()
            ),
            "{page}"
        );
    }

    /// A filter keeps the lines carrying the text, numbered where they were.
    ///
    /// The number is the point: a filtered line is worth little without the window to
    /// ask for next.
    ///
    /// # Panics
    ///
    /// When a carried line is dropped, renumbered, or a bystander kept.
    #[test]
    fn a_filter_keeps_the_lines_that_carry_it_with_their_own_numbers() {
        let text = "one\ntwo\nthree\ntwo again\n";
        let out = super::window(text, Some("two"), None, None);
        assert!(out.starts_with("// 2 of 4 lines carry"), "{out}");
        assert!(out.contains("    2  two\n"), "{out}");
        assert!(out.contains("    4  two again\n"), "{out}");
        assert!(!out.contains("three"), "{out}");
    }

    /// The filter ignores case, as every other filter in this tool does.
    ///
    /// # Panics
    ///
    /// When a line is kept only on an exact-case match.
    #[test]
    fn a_filter_ignores_case() {
        let out = super::window("Alpha\nbeta\n", Some("ALPHA"), None, None);
        assert!(out.contains("    1  Alpha\n"), "{out}");
    }

    /// Offset and limit page the answer, counting after the filter.
    ///
    /// # Panics
    ///
    /// When the window falls outside what was asked for.
    #[test]
    fn offset_and_limit_page_what_the_filter_left() {
        let text = "a\nb\nc\nd\n";
        let out = super::window(text, None, Some(1), Some(2));
        assert!(out.contains("    2  b\n"), "{out}");
        assert!(out.contains("    3  c\n"), "{out}");
        assert!(!out.contains("    1  a\n"), "{out}");
        assert!(!out.contains("    4  d\n"), "{out}");
    }

    /// A filter nothing carries says so rather than returning the whole text.
    ///
    /// # Panics
    ///
    /// When an empty answer is spelled as the whole function.
    #[test]
    fn a_filter_that_matches_nothing_returns_no_lines() {
        let out = super::window("a\nb\n", Some("zzz"), None, None);
        assert!(out.starts_with("// 0 of 2 lines carry"), "{out}");
        assert_eq!(out.lines().count(), 1, "{out}");
    }

    /// A filtered or paged line comes under the headers of the scopes
    /// enclosing it.
    ///
    /// Each header comes once, numbered `^N` and indented as in the text,
    /// and the header line says what `^N` means; a line no scope encloses
    /// comes alone, under the header it always had.
    ///
    /// A bare `rax = DeleteFileA(...)` reads as "always deletes"; under its
    /// `if` it reads as what it is.
    ///
    /// # Panics
    ///
    /// When a header is missing, a context line is numbered as a match, or
    /// an unnested line gains context.
    #[test]
    fn a_fragment_comes_with_the_headers_enclosing_it() {
        let text = "// f\n\nif ((a3 & 0x200) != 0) {\n  while (1) {\n    rax = DeleteFileA(a2);\n    rbx = DeleteFileA(a1);\n  }\n} else {\n  rax = 0;\n}\nreturn rax;\n";
        let note = super::render::SCOPE_NOTE;
        assert_eq!(
            super::window(text, Some("deletefilea"), None, None),
            format!(
                "// 2 of 11 lines carry \"deletefilea\", showing 2 from 0{note}\n   ^3  if ((a3 & 0x200) != 0) {{\n   ^4    while (1) {{\n    5      rax = DeleteFileA(a2);\n    6      rbx = DeleteFileA(a1);\n"
            )
        );
        assert_eq!(
            super::window(text, None, Some(8), Some(1)),
            format!(
                "// showing 1 of 11 lines from 8; offset=9 continues{note}\n   ^3  if ((a3 & 0x200) != 0) {{\n   ^8  }} else {{\n    9    rax = 0;\n"
            ),
            "a page opening inside an else"
        );
        assert_eq!(
            super::window(text, Some("return"), None, None),
            "// 1 of 11 lines carry \"return\", showing 1 from 0\n   11  return rax;\n"
        );
    }

    /// An escaped experiment spec decodes to the same spec sent plainly.
    ///
    /// A URI path segment reserves `,` and `=`, so a correct client may send
    /// them escaped; both spellings have to reach the harness as one spec.
    ///
    /// # Panics
    ///
    /// When an escaped spec does not decode to the plain one.

    #[test]
    fn an_escaped_spec_decodes() {
        assert_eq!(
            percent_decode("0x1400%2Crax%3D1%2Cw0x1400%3D90c3"),
            "0x1400,rax=1,w0x1400=90c3"
        );
        assert_eq!(percent_decode("0x1400%2crax%3d1"), "0x1400,rax=1");
        assert_eq!(percent_decode("0x1400,rax=1"), "0x1400,rax=1");
        assert_eq!(
            percent_decode("std%3A%3Astring%3A%3Aresize"),
            "std::string::resize"
        );
    }

    /// A server with a small raw image loaded: 0x100 bytes of `ret` mapped
    /// as `.text` at 0x1000, enough for the tools that read bytes and quick
    /// to analyze.
    fn raw_server() -> super::BorerServer {
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let program = Program::raw(vec![0xc3; 0x100], Arch::X86_64, 0, Some(0x1000), vec![text]);
        super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        }
    }

    /// The resource documentation says what the resources do.
    ///
    /// Every template the dispatcher answers is listed, `binary_info`
    /// names every template, no description carries a run of spaces from a
    /// broken line, and `emulate` and `devirt` describe every setting they
    /// read, `trace=` as the last steps it keeps.
    ///
    /// # Panics
    ///
    /// When a template is unlisted or unnamed, or a description misleads.
    #[test]
    fn the_resource_docs_say_what_the_resources_do() {
        let info = raw_server().binary_info().expect("info");
        let more = info
            .lines()
            .find_map(|l| l.strip_prefix("# more: "))
            .expect("a more line");
        for &(uri, _, _) in super::RESOURCE_TEMPLATES {
            let name = super::resource_name(uri);
            assert!(more.split([' ', ',']).any(|w| w == name), "{name}: {more}");
        }
        for uri in ["borer://map/{namespace}", "borer://ports/{filter}"] {
            assert!(
                super::RESOURCE_TEMPLATES.iter().any(|&(u, _, _)| u == uri),
                "{uri} is answered but not listed"
            );
        }
        let described_all = super::RESOURCES
            .iter()
            .copied()
            .chain(super::RESOURCE_TEMPLATES.iter().map(|&(u, d, _)| (u, d)));
        for (uri, text) in described_all {
            assert!(!text.contains("  "), "{uri}: {text}");
        }
        let described = |uri: &str| {
            super::RESOURCE_TEMPLATES
                .iter()
                .find(|&&(u, _, _)| u == uri)
                .map(|&(_, text, _)| text)
                .expect("listed")
        };
        let emulate = described("borer://emulate/{address}");
        assert!(
            emulate.contains("each of the last n instructions"),
            "{emulate}"
        );
        assert!(
            emulate.contains("origin=") && emulate.contains("profile="),
            "{emulate}"
        );
        let devirt = described("borer://devirt/{address}");
        for setting in ["budget=", "strict", "reg="] {
            assert!(devirt.contains(setting), "{setting}: {devirt}");
        }
    }

    /// The `decompile` answer says on its second line what of it was
    /// checked against the binary, and the outline does too; the batch and
    /// the text the other tools read do not carry the line.
    ///
    /// # Panics
    ///
    /// When the line is missing from the answer or found anywhere else.
    #[test]
    fn a_decompile_answer_says_what_was_checked() {
        use super::{DecompileBatchParams, DecompileParams, Detail, Parameters};
        let server = raw_server();
        let answer = |detail| {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail,
                    filter: None,
                    offset: None,
                    limit: Some(0),
                }))
                .expect("decompiles")
        };
        for detail in [None, Some(Detail::Skeleton)] {
            let text = answer(detail);
            let line = text.lines().nth(1).unwrap_or_default();
            assert!(
                line.starts_with("// checked vs binary: statements as emitted, 1/1 blocks"),
                "{text}"
            );
            assert!(
                text.lines().next().is_some_and(|l| l.contains("0x1000")),
                "{text}"
            );
        }
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(1),
            }))
            .expect("batch");
        assert!(!batch.contains("checked vs binary"), "{batch}");
        let a = server
            .analysis(super::Feature::Decompile)
            .expect("analyzed");
        let plain = server
            .with_program(|p| {
                borer_engine::analysis::decompile::decompile_named(p, &a, &server.overlay(), 0x1000)
                    .ok_or_else(|| "no text".to_owned())
            })
            .expect("text");
        assert!(!plain.contains("checked vs binary"), "{plain}");
    }

    /// The `decompile` answer lists, under the line saying what was
    /// checked, a `// next:` line per resource the function's facts point
    /// at, and the summary ends with the same steps as `# next:` lines.
    ///
    /// # Panics
    ///
    /// When a step is missing from either answer.
    #[test]
    fn a_decompile_answer_names_the_next_reads() {
        use super::{DecompileParams, FunctionParams, Parameters};
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![
            0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
            0x0f, 0x94, 0xc0, // ASM: sete al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let step = "borer://solve/0x1000 (compares against 0x1337abcd: the a1 it accepts)";
        let answer = server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(0),
            }))
            .expect("decompiles");
        let lines: Vec<&str> = answer.lines().collect();
        assert!(
            lines
                .get(1)
                .is_some_and(|l| l.starts_with("// checked vs binary")),
            "{answer}"
        );
        assert_eq!(
            lines.get(2).copied(),
            Some(format!("// next: {step}").as_str()),
            "{answer}"
        );
        let summary = server
            .function_summary(Parameters(FunctionParams {
                address: "0x1000".to_owned(),
            }))
            .expect("summarizes");
        assert!(summary.ends_with(&format!("# next: {step}\n")), "{summary}");
    }

    /// A batch the total output cap cuts short counts in its header the
    /// functions it prints, not the ones it decompiled and left out, and
    /// says how many those are.
    ///
    /// The image's entry calls twelve functions of 150 stores each, whose
    /// texts run past the total long before the twelfth.
    ///
    /// # Panics
    ///
    /// When the header counts a function the body does not print.
    #[test]
    fn a_batch_cut_by_the_total_cap_counts_what_it_prints() {
        use super::{DecompileBatchParams, Parameters};
        use borer_engine::program::{Arch, Program, Section};
        /// Functions the entry calls.
        const CALLEES: u32 = 12;
        /// Bytes between two callees.
        const STRIDE: u32 = 0x800;
        let mut code = Vec::new();
        for k in 0..CALLEES {
            let at = u32::try_from(code.len()).expect("small") + 5;
            // ASM: call 0x1000 + STRIDE * (k + 1)
            code.push(0xe8);
            code.extend_from_slice(&(STRIDE * (k + 1) - at).to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        for k in 0..CALLEES {
            code.resize(usize::try_from(STRIDE * (k + 1)).expect("small"), 0xcc);
            for n in 0u32..150 {
                // ASM: mov dword [rcx + n*8 + k], n
                code.extend_from_slice(&[0xc7, 0x81]);
                code.extend_from_slice(&(n * 8 + k).to_le_bytes());
                code.extend_from_slice(&n.to_le_bytes());
            }
            code.push(0xc3); // ASM: ret
        }
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(50),
            }))
            .expect("batch");
        let printed = batch.lines().filter(|l| l.starts_with("==== ")).count();
        assert!(printed < 13, "the cap cuts the batch short: {batch}");
        let header = batch.lines().next().unwrap_or_default();
        assert_eq!(
            header,
            format!("# decompiled {printed} of 13 matching functions (max 50)"),
            "{batch}"
        );
        assert!(
            batch.contains(&format!(
                "# total output cap of 40000 chars reached: {} more decompiled, not shown",
                13 - printed
            )),
            "{batch}"
        );
    }

    /// A rename and a comment each let go of the text read under the names
    /// before them: the old text is not kept beside the new one, and the
    /// new one carries the name.
    ///
    /// # Panics
    ///
    /// When a text read under replaced names stays held, or the text read
    /// after the rename lacks the new name.
    #[test]
    fn a_rename_lets_go_of_the_text_read_under_the_old_names() {
        use super::{DecompileParams, Parameters, SetCommentParams, SetNameParams};
        let server = raw_server();
        let decompile = || {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset: None,
                    limit: Some(0),
                }))
                .expect("decompiles")
        };
        let held = || {
            server
                .analysis(super::Feature::Decompile)
                .expect("analyzed")
                .derived
                .held("plain_text")
        };
        assert!(!decompile().contains("renamed"));
        assert_eq!(held(), 1);
        server
            .set_name(Parameters(SetNameParams {
                address: "0x1000".to_owned(),
                name: "renamed".to_owned(),
                dry_run: Some(false),
            }))
            .expect("renames");
        assert_eq!(held(), 0, "the text under the old name is let go");
        assert!(decompile().contains("renamed"));
        assert_eq!(held(), 1);
        server
            .set_comment(Parameters(SetCommentParams {
                address: "0x1000".to_owned(),
                comment: "seen".to_owned(),
                dry_run: Some(false),
            }))
            .expect("comments");
        assert_eq!(held(), 0, "the text without the comment is let go");
    }

    /// A search page says `showing N of M`, and a count states no page.
    ///
    /// # Panics
    ///
    /// When either header is worded otherwise.
    #[test]
    fn a_search_page_says_showing_n_of_m() {
        use super::{Parameters, SearchParams};
        let server = raw_server();
        let search = |count_only| {
            server
                .search(Parameters(SearchParams {
                    query: "c3".to_owned(),
                    kind: None,
                    offset: None,
                    limit: None,
                    count_only: Some(count_only),
                }))
                .expect("searches")
        };
        let page = search(false);
        assert!(
            page.starts_with("# 256 hits, showing 200 of 256 from 0\n"),
            "{page}"
        );
        assert_eq!(search(true), "# 256 hits\n");
    }

    /// A name that reads as a number is noted when set and reaches its
    /// function afterwards.
    ///
    /// `0x` text stays the address, and bare digits naming nothing are
    /// decimal, with the hex spelling suggested when that is the function
    /// meant.
    ///
    /// # Panics
    ///
    /// When the note is missing, the name does not resolve, or the decimal
    /// reading is not explained.
    #[test]
    fn a_name_that_reads_as_a_number_is_noted_and_reachable() {
        use super::{FunctionDetailParams, Parameters, SetNameParams};
        let server = raw_server();
        let set = server
            .set_name(Parameters(SetNameParams {
                address: "0x1000".to_owned(),
                name: "cafe".to_owned(),
                dry_run: Some(false),
            }))
            .expect("renames");
        assert!(set.contains("also reads as the number 0xcafe"), "{set}");
        let function = |address: &str| {
            server.function(Parameters(FunctionDetailParams {
                address: address.to_owned(),
                offset: None,
            }))
        };
        let by_name = function("cafe").expect("the name resolves");
        assert!(by_name.contains("cafe"), "{by_name}");
        assert!(function("0xcafe").is_err(), "0x text is the address");
        let decimal = function("1000").expect_err("decimal 1000 is 0x3e8");
        assert!(
            decimal
                .message
                .contains("bare digits are decimal, write 0x1000"),
            "{decimal:?}"
        );
    }

    /// `set_type` dry-runs by default, defines a struct and applies it at a
    /// data global, and `types` lists both.
    ///
    /// A type the language does not spell, a field naming nothing defined
    /// and a global inside a function are refused with a message naming
    /// the offender.
    ///
    /// # Panics
    ///
    /// When the dry run writes, the listing misses what was stated, or a
    /// refusal accepts.
    #[test]
    fn set_type_defines_applies_and_refuses() {
        use super::{Parameters, SetTypeParams, TypesParams};
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let fields = || vec!["0x18:hp:u32".to_owned(), "0x1c:mp:u32".to_owned()];
        // The dry run states what it would do and writes nothing.
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(fields()),
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("Player *".to_owned()),
                var: None,
                dry_run: None,
            }))
            .expect("dry-runs");
        assert!(
            out.starts_with("dry-run: would define struct Player"),
            "{out}"
        );
        let listed = server
            .types(Parameters(TypesParams {
                filter: None,
                offset: None,
                limit: None,
                count_only: Some(true),
            }))
            .expect("lists");
        assert!(listed.contains("0 rows (0 type(s), 0 applied)"), "{listed}");
        // Applying writes both halves, and the listing carries them.
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(fields()),
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("Player *".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines and applies");
        assert!(
            out.contains("defined struct Player: 2 field(s), 0x20 byte(s)"),
            "{out}"
        );
        assert!(out.contains("applied Player * at 0x2000"), "{out}");
        let listed = server
            .types(Parameters(TypesParams {
                filter: Some("player".to_owned()),
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("lists");
        assert!(
            listed.contains("struct\tPlayer\t0x20\t0x18 hp u32, 0x1c mp u32"),
            "{listed}"
        );
        assert!(listed.contains("applied\t0x2000\t-\tPlayer *"), "{listed}");
        // A type the language does not spell is refused, naming it.
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("three of them".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("garbage refused");
        assert!(bad.message.contains("'three of them'"), "{}", bad.message);
        // A field naming nothing defined is refused before anything is written.
        let mut unknown = fields();
        unknown.push("0x20:next:Missing *".to_owned());
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(unknown),
                values: None,
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("unknown name refused");
        assert!(
            bad.message.contains("resolves to no size"),
            "{}",
            bad.message
        );
        // An address inside a function takes no type.
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: Some("0x1000".to_owned()),
                r#type: Some("u32".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("code refused");
        assert!(
            bad.message.contains("types apply to data globals"),
            "{}",
            bad.message
        );
    }

    /// `borer://layout/...,apply=Name` and `class_layout(apply=)` define a
    /// struct and type the parameter, dry-run by default.
    ///
    /// The dry run names the struct and the prototype and writes nothing;
    /// `dry_run=false` writes both and the re-decompiled function reads
    /// `a1->f_10`; a script cannot apply through `query`.
    ///
    /// # Panics
    ///
    /// When the dry run writes, the applied text misses a field, or a
    /// refusal accepts.
    #[test]
    fn a_layout_applies_as_a_struct_on_request() {
        use super::{ClassLayoutParams, DecompileParams, Parameters, ScriptParams, TypesParams};
        use borer_engine::program::{Arch, Program, Section};
        let mut bytes = vec![0xccu8; 0x1000];
        bytes[..12].copy_from_slice(&[
            0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
            0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
            0xc6, 0x41, 0x20, 0x01, // ASM: mov byte [rcx+0x20], 1
            0xc3, // ASM: ret
        ]);
        let text = Section::mapped(".text", 0x401_000, 0, 0x1000, false, true);
        let program = Program::raw(bytes, Arch::X86_64, 0x400_000, Some(0x401_000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let types = || {
            server
                .types(Parameters(TypesParams {
                    filter: None,
                    offset: None,
                    limit: None,
                    count_only: Some(true),
                }))
                .expect("lists")
        };
        let dry = server
            .resource_text("borer://layout/0x401000,rcx,apply=Rec")
            .expect("a dry run");
        assert_eq!(
            dry,
            "dry-run: would define struct Rec and state 1 prototype(s); decompile then names the fields:\nstruct Rec (0x21 bytes): 0x10 f_10 u32, 0x18 f_18 u64, 0x20 f_20 u8\nprototype sub_401000 (0x401000): uint64_t (Rec *)\npass dry_run=false to apply.\n"
        );
        assert!(types().starts_with("# 0 rows"), "{}", types());
        let scripted = server
            .script(Parameters(ScriptParams {
                code: "print(query(\"borer://layout/0x401000,apply=Rec,dry_run=false\"));"
                    .to_owned(),
                dry_run: None,
            }))
            .expect("a script answers");
        assert!(
            scripted.contains("applies nothing through query"),
            "{scripted}"
        );
        assert!(types().starts_with("# 0 rows"), "{}", types());
        let done = server
            .resource_text("borer://layout/0x401000,apply=Rec,dry_run=false")
            .expect("applies");
        assert!(
            done.starts_with("defined struct Rec and stated 1 prototype(s)"),
            "{done}"
        );
        assert!(
            types().starts_with("# 2 rows (1 type(s), 0 applied)"),
            "{}",
            types()
        );
        let text = server
            .decompile(Parameters(DecompileParams {
                address: "0x401000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))
            .expect("decompiles");
        assert!(text.contains("a1->f_10"), "{text}");
        assert!(text.contains("a1->f_20 = 1;"), "{text}");
        let bad = server
            .resource_text("borer://layout/0x401003,apply=Rec")
            .expect_err("mid-function");
        assert!(
            bad.message.contains("carries no parameter"),
            "{}",
            bad.message
        );
        let no_class = server
            .class_layout(Parameters(ClassLayoutParams {
                class: "Nope".to_owned(),
                apply: Some("N".to_owned()),
                dry_run: None,
            }))
            .expect_err("no such class");
        assert!(
            no_class.message.contains("no function belongs"),
            "{}",
            no_class.message
        );
    }

    /// `set_type` with `type` alone reads C declarations by the binary's ABI.
    ///
    /// The dry run shows the offsets and writes nothing, the applied struct
    /// reads with `read type=`, and a failing offset assertion is refused
    /// with the field named.
    ///
    /// # Panics
    ///
    /// When a layout differs, the dry run writes, or a refusal accepts.
    #[test]
    fn set_type_reads_c_declarations() {
        use super::{Parameters, ReadParams, SetTypeParams, TypesParams};
        use borer_engine::program::{Arch, Program, Section};
        let decl = |server: &super::BorerServer, text: &str, dry_run: Option<bool>| {
            server.set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: None,
                r#type: Some(text.to_owned()),
                var: None,
                dry_run,
            }))
        };
        let server_for = |arch: Arch| {
            let mut bytes = vec![0u8; 0x200];
            bytes[0x100] = b'A';
            bytes[0x104..0x108].copy_from_slice(&7u32.to_le_bytes());
            let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
            let program = Program::raw(bytes, arch, 0, None, vec![data]);
            super::BorerServer {
                program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                    program,
                )))),
                pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
                ..super::BorerServer::default()
            }
        };
        let text = "#pragma pack(push, 8)\nstruct S {\n  char c;\n  int n;   // @0x4\n  char *p;\n};\n#pragma pack(pop)\nstatic_assert(sizeof(S) == 16);";
        let x64 = server_for(Arch::X86_64);
        let dry = decl(&x64, text, None).expect("dry-runs");
        assert_eq!(
            dry,
            "dry-run: would define 1 type(s) from C, laid out for x64 Windows:\nstruct S (0x10 bytes, align 8): 0x0 c char, 0x4 n i32, 0x8 p char *\npass dry_run=false to apply.\n"
        );
        let listed = x64
            .types(Parameters(TypesParams {
                filter: None,
                offset: None,
                limit: None,
                count_only: Some(true),
            }))
            .expect("lists");
        assert!(listed.contains("0 rows (0 type(s)"), "{listed}");
        let done = decl(&x64, text, Some(false)).expect("defines");
        assert!(done.starts_with("defined 1 type(s) from C"), "{done}");
        let read = x64
            .read(Parameters(ReadParams {
                address: "0x2000".to_owned(),
                kind: None,
                r#type: Some("S".to_owned()),
                count: None,
            }))
            .expect("reads");
        assert!(read.contains("0x2000       c char   'A'\n"), "{read}");
        assert!(read.contains("0x2004       n i32    7\n"), "{read}");
        let x86 = server_for(Arch::X86);
        let narrow = decl(&x86, "struct S { char c; int n; char *p; };", None).expect("x86");
        assert!(
            narrow.contains("laid out for x86 Windows:\nstruct S (0xc bytes, align 4)"),
            "{narrow}"
        );
        let wrong = decl(
            &x64,
            "struct T {\n  char c;\n  int n;   // @0x2\n};",
            Some(false),
        )
        .expect_err("a failing assertion");
        assert!(
            wrong.message.contains(
                "line 3: field n of struct T is at 0x4 under x64 Windows layout, not 0x2"
            ),
            "{}",
            wrong.message
        );
    }

    /// `read` with `type` lays a defined struct over the bytes: `count`
    /// records, each field a row with a `char` array quoted; a kind beside
    /// a type, and a file offset, are refused.
    ///
    /// # Panics
    ///
    /// When a row is missing or a refusal accepts.
    #[test]
    fn read_lays_a_user_type_over_the_bytes() {
        use super::params::ReadKind;
        use super::{Parameters, ReadParams, SetTypeParams};
        use borer_engine::program::{Arch, Program, Section};
        let mut bytes = vec![0u8; 0x200];
        bytes[0x100..0x104].copy_from_slice(&7u32.to_le_bytes());
        bytes[0x104..0x108].copy_from_slice(b"hi\0\0");
        bytes[0x108..0x10c].copy_from_slice(&9u32.to_le_bytes());
        bytes[0x10c..0x110].copy_from_slice(b"yo\0\0");
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(bytes, Arch::X86_64, 0, None, vec![data]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        server
            .set_type(Parameters(SetTypeParams {
                name: Some("Item".to_owned()),
                fields: Some(vec!["0:id:u32".to_owned(), "4:tag:char[4]".to_owned()]),
                values: None,
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines");
        let read = |kind: Option<ReadKind>, ty: &str, address: &str, count: Option<u32>| {
            server.read(Parameters(ReadParams {
                address: address.to_owned(),
                kind,
                r#type: Some(ty.to_owned()),
                count,
            }))
        };
        let text = read(None, "Item", "0x2000", Some(2)).expect("reads");
        assert!(
            text.starts_with("# showing 4 of 4 rows: Item[2] at 0x2000 in .data, 0x10 bytes\n"),
            "{text}"
        );
        assert!(
            text.contains("0x2004       [0].tag char[4] \"hi\"\n"),
            "{text}"
        );
        assert!(
            text.contains("0x2008       [1].id  u32     0x9\n"),
            "{text}"
        );
        let one = read(None, "Item", "0x2008", None).expect("reads one");
        assert!(one.contains("0x200c       tag char[4] \"yo\"\n"), "{one}");
        let both = read(Some(ReadKind::U8), "Item", "0x2000", None).expect_err("kind and type");
        assert!(both.message.contains("give one"), "{}", both.message);
        let off = read(None, "Item", "off:0x100", None).expect_err("an offset");
        assert!(off.message.contains("takes an address"), "{}", off.message);
        let bad = read(None, "Item[", "0x2000", None).expect_err("an open bracket");
        assert!(bad.message.contains("does not close"), "{}", bad.message);
    }

    /// `set_type` with `values` defines an enum, applies it at a data
    /// global, and `types` lists its values in value order.
    ///
    /// A value under two names, and fields stated beside values, are
    /// refused with a message naming the offender.
    ///
    /// # Panics
    ///
    /// When the listing misses the enum, or a refusal accepts.
    #[test]
    fn set_type_defines_enums_and_refuses() {
        use super::{Parameters, SetTypeParams, TypesParams};
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("State".to_owned()),
                fields: None,
                values: Some(vec!["Run:1".to_owned(), "Idle:0".to_owned()]),
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("State".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines and applies");
        assert!(
            out.contains("defined enum State: 2 value(s), 0x4 byte(s)"),
            "{out}"
        );
        assert!(
            out.contains("applied State at 0x2000 (4 byte(s)); decompile names its values"),
            "{out}"
        );
        let listed = server
            .types(Parameters(TypesParams {
                filter: Some("state".to_owned()),
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("lists");
        assert!(
            listed.contains("enum\tState\t0x4\tIdle = 0, Run = 1"),
            "{listed}"
        );
        assert!(listed.contains("applied\t0x2000\t-\tState"), "{listed}");
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Bad".to_owned()),
                fields: None,
                values: Some(vec!["A:0".to_owned(), "B:0".to_owned()]),
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("a duplicate value refused");
        assert!(
            bad.message.contains("names value 0 twice"),
            "{}",
            bad.message
        );
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Bad".to_owned()),
                fields: Some(vec!["0x0:f:u32".to_owned()]),
                values: Some(vec!["A:0".to_owned()]),
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("fields beside values refused");
        assert!(
            bad.message.contains("both fields and values"),
            "{}",
            bad.message
        );
    }

    /// `set_type` refuses a type with more pointers than the language
    /// holds, on a dry run too, rather than building a chain of boxes whose
    /// spelling and drop overflowed the stack and took the server down.
    ///
    /// # Panics
    ///
    /// When a deep type is accepted or the refusal does not say why.
    #[test]
    fn set_type_refuses_a_type_too_deep_to_walk() {
        use super::{Parameters, SetTypeParams};
        use borer_engine::program::{Arch, Program, Section};
        let data = Section::mapped(".data", 0x2000, 0, 0x100, true, false);
        let program = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, vec![data]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let refuse = |name: Option<&str>, address: Option<&str>, ty: &str| {
            server
                .set_type(Parameters(SetTypeParams {
                    name: name.map(str::to_owned),
                    fields: None,
                    values: None,
                    size: None,
                    address: address.map(str::to_owned),
                    r#type: Some(ty.to_owned()),
                    var: None,
                    dry_run: None,
                }))
                .expect_err("a type too deep to walk was accepted")
                .message
        };
        let deep = format!("u8 {}", "*".repeat(17));
        let long = format!("u8 {}", "*".repeat(20_000));
        for (name, address) in [(Some("Stars"), None), (None, Some("0x2000"))] {
            let refused = refuse(name, address, &deep);
            assert!(refused.contains("stacks 17 pointers"), "{refused}");
            let refused = refuse(name, address, &long);
            assert!(
                refused.contains("the type is 20003 characters"),
                "{refused}"
            );
        }
    }

    /// `set_type` at a function states its prototype, and with `var` one of
    /// its variables.
    ///
    /// Dry runs leave the overlay's fingerprint as it was; applying states
    /// the prototype, and a variable is then found by the name the
    /// prototype gave it; a register and a data address are refused.
    ///
    /// # Panics
    ///
    /// When a dry run writes, an application does not, or a refusal is
    /// accepted.
    #[test]
    fn set_type_states_prototypes_and_variables() {
        use super::{Parameters, SetTypeParams};
        use borer_engine::analysis::protos::VarKey;
        use borer_engine::program::{Arch, Program, Section};
        let mut bytes = vec![0xcc; 0x200];
        // ASM: lea eax, [rcx+1]; ret
        bytes[..4].copy_from_slice(&[0x8d, 0x41, 0x01, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, data]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let call = |address: &str,
                    ty: Option<&str>,
                    var: Option<&str>,
                    name: Option<&str>,
                    dry: Option<bool>| {
            server.set_type(Parameters(SetTypeParams {
                name: name.map(str::to_owned),
                fields: None,
                values: None,
                size: None,
                address: Some(address.to_owned()),
                r#type: ty.map(str::to_owned),
                var: var.map(str::to_owned),
                dry_run: dry,
            }))
        };
        let before = server.overlay_plain().fingerprint();
        let out = call("0x1000", Some("int f(int n)"), None, None, None).expect("dry-runs");
        assert!(
            out.starts_with("dry-run: would state sub_1000 (0x1000) as int (int n)"),
            "{out}"
        );
        assert_eq!(server.overlay_plain().fingerprint(), before);
        let out = call("0x1002", Some("int f(int n)"), None, None, Some(false)).expect("states");
        assert!(
            out.contains("stated sub_1000 (0x1000) as int (int n)"),
            "{out}"
        );
        let stated = server.overlay_plain().fingerprint();
        assert_ne!(stated, before);
        let out = call("0x1000", Some("Mystery *"), Some("n"), Some("thing"), None)
            .expect("dry-runs the variable");
        assert!(
            out.starts_with("dry-run: would name a1 of sub_1000 (0x1000) Mystery *thing"),
            "{out}"
        );
        assert_eq!(server.overlay_plain().fingerprint(), stated);
        call("0x1000", None, Some("n"), Some("count"), Some(false)).expect("names");
        let o = server.overlay_plain();
        assert_eq!(
            o.vars
                .get(&0x1000)
                .and_then(|v| v.get(&VarKey::Param(0)))
                .map(|v| v.name.as_str()),
            Some("count")
        );
        let refused = call("0x1000", None, Some("rax"), Some("x"), None)
            .expect_err("a register was named")
            .message;
        assert!(refused.contains("register"), "{refused}");
        let refused = call("0x2000", None, Some("a1"), Some("x"), None)
            .expect_err("a variable outside any function was named")
            .message;
        assert!(refused.contains("function"), "{refused}");
        let refused = call("0x1000", Some("int f(int n"), None, None, None)
            .expect_err("a prototype with an open parameter list was stated")
            .message;
        assert!(refused.contains("parameter list"), "{refused}");
        let refused = call("0x1000", Some("u32"), None, None, None)
            .expect_err("a plain type was stated at a function")
            .message;
        assert!(refused.contains("types apply to data globals"), "{refused}");
    }

    /// `load_project` holds a project to what the annotating tools accept
    /// and refuses one saved for another binary unless forced.
    ///
    /// A name or comment at an address no section holds, a blank one and a
    /// type applied outside every section are skipped and listed, and the
    /// counts said are of what the overlay then holds; a project saved for
    /// another path is refused and leaves the overlay as it was, and with
    /// `force` it loads and says so.
    ///
    /// # Panics
    ///
    /// When an entry no section holds is loaded, the counts miss, or a
    /// foreign project loads unforced.
    #[test]
    fn load_project_skips_what_set_name_refuses_and_guards_another_binary() {
        use super::{LoadProjectParams, Parameters};
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let dir = std::env::temp_dir().join(format!("borer-load-project-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let write = |name: &str, program: &str| {
            let path = dir.join(name);
            let json = format!(
                r#"{{"program":"{program}","names":{{"0x1010":"f","0x0":"zero","0x5000":"far"}},"comments":{{"0x2000":"c","0x2004":"   "}},"applied":{{"0x9000":"u32"}}}}"#
            );
            std::fs::write(&path, json).expect("the project is written");
            path.display().to_string()
        };
        let load = |path: String, force: Option<bool>| {
            server.load_project(Parameters(LoadProjectParams { path, force }))
        };
        let out = load(write("same.json", ""), None).expect("loads");
        assert!(
            out.starts_with("loaded 1 names + 1 comments + 0 types + 0 applied\n"),
            "{out}"
        );
        assert!(
            out.contains(
                "# skipped 4 (showing 4 of 4): name at 0x0 (in no section), name at 0x5000 (in no section), comment at 0x2004 (blank), type at 0x9000 (in no section)"
            ),
            "{out}"
        );
        let held = || {
            let o = super::read_lock(&server.overlay);
            (
                o.names.keys().copied().collect::<Vec<_>>(),
                o.comments.keys().copied().collect::<Vec<_>>(),
                o.applied.len(),
            )
        };
        assert_eq!(held(), (vec![0x1010], vec![0x2000], 0));
        super::write_lock(&server.overlay).names.clear();
        let foreign = write("foreign.json", "C:/elsewhere/other.exe");
        let refused = load(foreign.clone(), None).expect_err("a foreign project loaded");
        assert!(
            refused
                .message
                .contains("the project was saved for C:/elsewhere/other.exe"),
            "{}",
            refused.message
        );
        assert!(
            refused.message.contains("force=true"),
            "{}",
            refused.message
        );
        assert_eq!(held(), (vec![], vec![0x2000], 0));
        let forced = load(foreign, Some(true)).expect("a forced load loads");
        assert!(forced.starts_with("loaded 1 names"), "{forced}");
        assert!(
            forced.contains("# forced: the project was saved for C:/elsewhere/other.exe"),
            "{forced}"
        );
        assert_eq!(held(), (vec![0x1010], vec![0x2000], 0));
    }

    /// An arm64 program disassembles, lists its functions and decompiles.
    ///
    /// The `disassemble` tool lists from the word an address falls inside,
    /// a script's `disasm` reads the same words and its `functions` the one
    /// function, the `functions` tool lists it, and `decompile` writes it,
    /// with the line saying what of it was checked against the arm64
    /// machine.
    ///
    /// # Panics
    ///
    /// When a listing or the text differs.
    #[test]
    fn an_arm64_program_lists_and_decompiles_its_functions() {
        use super::{
            DecompileParams, DisassembleParams, FunctionsParams, Parameters, ScriptParams,
        };
        use borer_engine::program::{Arch, Program, Section};
        let code: Vec<u8> = [
            // ASM: bti c
            0xd503_245fu32,
            // ASM: ret
            0xd65f_03c0,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let text = Section::mapped(".text", 0x1000, 0, 8, false, true);
        let program = Program::raw(code, Arch::Arm64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let out = server
            .disassemble(Parameters(DisassembleParams {
                address: "0x1002".to_owned(),
                count: None,
                bytes: None,
            }))
            .expect("arm64 disassembles");
        assert!(
            out.starts_with(
                "# 2 instructions at 0x1000; 0x1002 is inside an instruction, listing from 0x1000;"
            ) && out.contains("\n0x1000  bti c\n0x1004  ret\n"),
            "{out}"
        );
        let out = server
            .script(Parameters(ScriptParams {
                code: "print(disasm(0x1000, 2)[1].text); print(functions().len);".to_owned(),
                dry_run: None,
            }))
            .expect("a script answers");
        assert!(out.starts_with("ret\n1\n"), "{out}");
        let listed = server
            .functions(Parameters(FunctionsParams {
                filter: None,
                sort: None,
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("arm64 functions are discovered");
        assert!(listed.lines().any(|l| l.starts_with("0x1000 ")), "{listed}");
        let text = server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))
            .expect("arm64 decompiles");
        assert!(
            text.contains("// signature: void sub_1000()")
                && text.contains("// checked vs binary: statements as emitted, 1/1 blocks")
                && text.contains("return;"),
            "{text}"
        );
    }

    /// An arm64 function runs under `borer://emulate` and `borer://run`,
    /// and a surface built on the x86 machine refuses it as an invalid
    /// request.
    ///
    /// # Panics
    ///
    /// When a run answers otherwise, or the refusal does not come.
    #[test]
    fn an_arm64_function_runs_under_emulate_and_run() {
        use borer_engine::program::{Arch, Program, Section};
        let code: Vec<u8> = [
            // ASM: add x0, x0, #0x1
            0x9100_0400u32,
            // ASM: ret
            0xd65f_03c0,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let text = Section::mapped(".text", 0x1000, 0, 8, false, true);
        let program = Program::raw(code, Arch::Arm64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let out = server
            .resource_text("borer://emulate/0x1000,x0=0x29")
            .expect("an arm64 routine runs");
        assert!(
            out.contains("returned after 2 steps") && out.contains("# registers: x0=0x2a x1=0x0"),
            "{out}"
        );
        let table = server
            .resource_text("borer://run/0x1000/41")
            .expect("an arm64 function runs on an input");
        assert!(
            table.contains("\t0x2a\treturned\t2\t-\tunchecked\n")
                && table.contains("a run's text is checked for x86 code only"),
            "{table}"
        );
        let refused = server
            .resource_text("borer://oracle/0x1000")
            .expect_err("the oracle drives the x86 machine");
        assert!(
            refused
                .message
                .contains("oracle runs x86 and x86-64 code only for now"),
            "{}",
            refused.message
        );
    }

    /// The `script` tool runs inline code and applies only on request.
    ///
    /// Its `query` calls are answered from the resources, `borer://script`
    /// refused; proposals stay a preview until `dry_run=false`, and then
    /// only those the listings can show at an address a section holds land.
    ///
    /// # Panics
    ///
    /// When an answer, a refusal or the overlay differs.
    #[test]
    fn script_runs_inline_code_queries_resources_and_applies_on_request() {
        use super::{Parameters, ScriptParams};
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x20];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x21, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let script = |code: &str, dry_run: Option<bool>| {
            server
                .script(Parameters(ScriptParams {
                    code: code.to_owned(),
                    dry_run,
                }))
                .expect("a script answers")
        };
        let out = script(
            r#"print(functions().len);
               print(query("borer://disasm/0x1000").contains("nop"));
               print(help().contains("query(uri)"));"#,
            None,
        );
        assert!(out.starts_with("1\ntrue\ntrue\n"), "{out}");
        let out = script(r#"query("borer://script/x.rhai");"#, None);
        assert!(out.contains("scripts do not run scripts"), "{out}");
        let out = script(r#"query("borer://nope");"#, None);
        assert!(
            out.contains("# script failed: Runtime error: unknown resource borer://nope"),
            "{out}"
        );
        let propose =
            r#"rename(0x1000, "start"); rename(0x9000, "gone"); comment(0x1001, "here");"#;
        let out = script(propose, None);
        assert!(out.contains("# dry-run: pass dry_run=false"), "{out}");
        assert!(super::read_lock(&server.overlay).names.is_empty());
        let out = script(propose, Some(false));
        assert!(
            out.contains("# applied names at 1 addresses and comments at 1, the last proposal for an address winning; 1 skipped"),
            "{out}"
        );
        let overlay = super::read_lock(&server.overlay);
        assert_eq!(
            overlay.names.get(&0x1000).map(String::as_str),
            Some("start")
        );
        assert_eq!(
            overlay.comments.get(&0x1001).map(String::as_str),
            Some("here")
        );
    }

    /// A script's `help("query")` lists every template with an example
    /// built from the loaded binary, and `rows` reads a page of a listing
    /// as maps.
    ///
    /// # Panics
    ///
    /// When a template is missing, its example is not filled in, or the
    /// rows differ.
    #[test]
    fn a_script_reads_every_resource_by_help_and_tables_by_rows() {
        use super::{Parameters, ScriptParams};
        let server = raw_server();
        let out = server
            .script(Parameters(ScriptParams {
                code: r#"print(help("query"));
                         let r = rows("borer://help!offset=1!limit=2");
                         print(`${r.len} ${r[0].text}`);"#
                    .to_owned(),
                dry_run: None,
            }))
            .expect("a script answers");
        for &(uri, _, _) in super::RESOURCE_TEMPLATES {
            assert!(out.contains(&format!("\n{uri}\t")), "{uri}: {out}");
        }
        assert!(
            out.contains("\te.g. borer://emulate/0x1000,a1=5,steps=10000\n"),
            "{out}"
        );
        assert!(out.contains("\n2 borer://info\t"), "{out}");
    }

    /// `query` answers a URI exactly as `resources/read` does.
    ///
    /// Both go through one answer memory: a URI without a tag is whole with
    /// its tag line every time, however often it was read before (a reader
    /// may no longer hold it); the URI with that tag appended is a note
    /// naming the read that returns the text, whichever way it is read;
    /// `!fresh` after the tag is whole again, and a tag that is not one is
    /// refused. An unknown URI is the same refusal both ways, listing every
    /// resource there is. The evidence line, the answer's last, names the
    /// emission and so differs between two reads of one answer; these
    /// assertions compare with it taken off.
    ///
    /// # Panics
    ///
    /// When the two ways answer differently, a repeat without a tag is not
    /// the whole text, or the note does not name the read returning it.
    #[test]
    fn query_answers_a_uri_as_resources_read_does() {
        use super::{Parameters, QueryParams};
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x200];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x201, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let query = |uri: &str| {
            server.query(Parameters(QueryParams {
                uri: uri.to_owned(),
            }))
        };
        let uri = "borer://disasm/0x1000";
        let (read_as, whole) = server.read_uri(uri).expect("reads");
        assert_eq!(read_as, uri);
        assert!(whole.len() > 512, "long enough to be remembered: {whole}");
        assert_eq!(
            without_evidence(&query(uri).expect("reads")),
            without_evidence(&whole),
            "a repeat is whole but for its evidence line"
        );
        let tag = whole
            .lines()
            .find_map(|l| l.strip_prefix("# since="))
            .expect("a long answer carries its tag");
        let tagged = format!("{uri}!since={tag}");
        let note = query(&tagged).expect("reads");
        assert!(
            note.starts_with(&format!("# unchanged since the answer tagged {tag}: ")),
            "{note}"
        );
        assert!(
            without_evidence(&note)
                .ends_with("; this note stands in for that text, and reading borer://disasm/0x1000 (resources/read or the query tool) returns it in full\n"),
            "{note}"
        );
        let (read_as, noted) = server.read_uri(&tagged).expect("reads");
        assert_eq!(
            (read_as.as_str(), without_evidence(&noted)),
            (uri, without_evidence(&note)),
            "one memory for both ways"
        );
        assert_eq!(
            without_evidence(&query(&format!("{tagged}!fresh")).expect("reads")),
            without_evidence(&whole)
        );
        assert_eq!(
            without_evidence(&query(&format!("{uri}!fresh")).expect("reads")),
            without_evidence(&whole)
        );
        let bad = query(&format!("{uri}!since=zz")).expect_err("not a tag");
        assert_eq!(bad.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        let refused = server.read_uri("borer://nope").expect_err("unknown");
        let queried = query("borer://nope").expect_err("unknown");
        assert_eq!(
            (refused.code, &refused.message),
            (queried.code, &queried.message)
        );
        assert!(
            refused
                .message
                .starts_with("unknown resource borer://nope; ")
                && refused
                    .message
                    .ends_with("; borer://help lists every resource"),
            "{}",
            refused.message
        );
    }

    /// The rows of a listing's URI read whole, its page suffixes taken off.
    ///
    /// # Arguments
    ///
    /// * `text` - A listing.
    fn listed_rows(text: &str) -> Vec<String> {
        borer_engine::table::classify(text)
            .into_iter()
            .filter(|(kind, _)| *kind == borer_engine::table::Line::Row)
            .map(|(_, line)| line.to_owned())
            .collect()
    }

    /// Page one and page two of a listing hold its first rows, in order.
    ///
    /// So they do whether the server pages the rows (`borer://help`) or
    /// the listing pages itself (`borer://fieldrefs`, `borer://calls`);
    /// each page says what it shows and names the next.
    ///
    /// # Panics
    ///
    /// When a page drops, repeats or reorders a row, or misnames the next.
    #[test]
    fn page_one_and_page_two_are_the_first_rows_of_the_whole() {
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![
            0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xc3, // ASM: ret
        ];
        code.resize(0x20, 0xcc);
        for n in 0u8..8 {
            code.extend_from_slice(&[0x89, 0x41, 0x10 + n * 8]); // ASM: mov [rcx+0x10+n*8], eax
        }
        code.extend_from_slice(&[0x89, 0x41, 0x10, 0x89, 0x41, 0x10, 0xc3]); // ASM: mov [rcx+0x10], eax (twice); ret
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let read = |uri: &str| server.read_uri(uri).expect("reads").1;
        for (uri, size) in [
            ("borer://help", 10),
            ("borer://fieldrefs/0x10", 1),
            ("borer://calls/0x1020", 1),
        ] {
            let whole = listed_rows(&server.resource_text(uri).expect("reads whole"));
            let one = read(&format!("{uri}!limit={size}"));
            let two = read(&format!("{uri}!offset={size}!limit={size}"));
            let paged: Vec<String> = listed_rows(&one)
                .into_iter()
                .chain(listed_rows(&two))
                .collect();
            assert!(whole.len() > 2 * size, "{uri}: {whole:?}");
            assert_eq!(paged, whole[..2 * size], "{uri}");
            assert!(
                one.contains(&format!("# showing {size} of {} from 0", whole.len()))
                    || one.contains(&format!("# {} sites touch", whole.len())),
                "{one}"
            );
            assert!(two.contains(" for the next page\n"), "{two}");
        }
        let help = read("borer://help!limit=10");
        assert!(
            help.contains("borer://help!limit=10!offset=10 for the next page"),
            "{help}"
        );
        let calls = read("borer://calls/0x1020!limit=1");
        assert!(
            calls.contains(",offset=1,limit=1 for the next page"),
            "{calls}"
        );
        let (asked, _) = server
            .read_uri("borer://help!limit=3!offset=1")
            .expect("reads");
        assert_eq!(asked, "borer://help!offset=1!limit=3");
        let refused = server
            .read_uri("borer://help!limit=0")
            .expect_err("no rows");
        assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS);
    }

    /// Every template read without its argument says how to read it.
    ///
    /// The answer is its URI, its description with the grammar in it, and
    /// an example built from the loaded binary, the same bytes each time;
    /// `borer://help/<name>` says the same of any resource, and
    /// `borer://help` lists each one once.
    ///
    /// # Panics
    ///
    /// When a template's bare read refuses or lacks a part, the example is
    /// not filled in, or the list misses or repeats a resource.
    #[test]
    fn a_template_read_bare_says_its_grammar_and_an_example() {
        let server = raw_server();
        for &(uri, description, _) in super::RESOURCE_TEMPLATES {
            let name = super::resource_name(uri);
            let fixed = super::RESOURCES
                .iter()
                .any(|r| super::resource_name(r.0) == name);
            let bare = if fixed {
                format!("borer://help/{name}")
            } else {
                format!("borer://{name}")
            };
            let help = server
                .resource_text(&bare)
                .expect("a bare template answers");
            assert!(
                help.contains(&format!("# {uri}\n{description}\n")),
                "{help}"
            );
            let example = help
                .lines()
                .find_map(|l| l.strip_prefix("# example: "))
                .unwrap_or_else(|| panic!("{uri} has no example: {help}"));
            assert!(
                example.starts_with(&format!("borer://{name}/")) && !example.contains('{'),
                "{uri}: {example}"
            );
            assert_eq!(server.resource_text(&bare).expect("again"), help);
        }
        let emulate = server.resource_text("borer://emulate").expect("answers");
        assert!(
            emulate.contains("# example: borer://emulate/0x1000,a1=5,steps=10000\n"),
            "{emulate}"
        );
        let triage = server
            .resource_text("borer://help/triage")
            .expect("answers");
        assert!(triage.starts_with("# borer://triage\n"), "{triage}");
        let index = server.resource_text("borer://help").expect("answers");
        let listed: Vec<&str> = index
            .lines()
            .skip(1)
            .filter_map(|l| l.split('\t').next())
            .collect();
        let every: Vec<&str> = super::RESOURCES
            .iter()
            .map(|r| r.0)
            .chain(super::RESOURCE_TEMPLATES.iter().map(|t| t.0))
            .collect();
        assert_eq!(listed, every, "{index}");
    }

    /// An unknown URI is refused with at most three resources nearest it.
    ///
    /// The refusal says where every resource is listed, in a few hundred
    /// bytes where the list of every resource took two thousand; a fixed
    /// resource given an argument is told it takes none, and a name nothing
    /// resembles says so.
    ///
    /// # Panics
    ///
    /// When a refusal is long, names the wrong resources, or reads as
    /// another error.
    #[test]
    fn an_unknown_uri_names_the_nearest_resources() {
        let server = raw_server();
        let refused = |uri: &str| {
            let e = server.resource_text(uri).expect_err("unknown");
            assert_eq!(e.code, super::ErrorCode::RESOURCE_NOT_FOUND, "{uri}");
            e.message.into_owned()
        };
        let typo = refused("borer://emulat");
        assert!(typo.len() < 600, "{} bytes: {typo}", typo.len());
        assert_eq!(
            typo,
            "unknown resource borer://emulat; nearest: borer://emulate/{address}; borer://help lists every resource"
        );
        let guessed = refused("borer://disassemble/0x1000");
        assert!(
            guessed.contains("; nearest: borer://disasm/{address}; "),
            "{guessed}"
        );
        let wide = refused("borer://ma");
        assert!(
            wide.contains("nearest: borer://map, ") && wide.matches(", ").count() == 2,
            "three at most: {wide}"
        );
        assert!(
            refused("borer://emulat/0x1000").contains("nearest: borer://emulate/{address}"),
            "the name is matched without its argument"
        );
        assert_eq!(
            refused("borer://triage/0x1000"),
            "borer://triage takes no argument; read borer://triage"
        );
        assert!(
            refused("borer://zzzzqqqq").contains("; no resource is near it; "),
            "nothing near"
        );
        assert!(
            refused("http://emulate").contains("a resource's URI starts with borer://"),
            "not a borer URI"
        );
        assert!(
            refused("borer://help/emulat").starts_with(
                "unknown resource borer://help/emulat; nearest: borer://emulate/{address}"
            ),
            "help for a misspelled name"
        );
    }

    /// A name nothing matches is refused with the names nearest it,
    /// wherever a tool takes an address or a name.
    ///
    /// # Panics
    ///
    /// When the refusal leaves the nearest name out.
    #[test]
    fn a_misspelled_name_is_refused_with_the_nearest() {
        use super::{FunctionParams, Parameters};
        let server = raw_server();
        super::write_lock(&server.overlay)
            .names
            .insert(0x1000, "check_serial".to_owned());
        let refused = server
            .function_summary(Parameters(FunctionParams {
                address: "chk_serial".to_owned(),
            }))
            .expect_err("no such name");
        assert!(
            refused.message.contains("; nearest: check_serial; "),
            "{}",
            refused.message
        );
    }

    /// `load_binary` ends by naming the call that answers a whole triage,
    /// where `binary_info`, which the instructions sent an agent to next,
    /// only repeats the summary.
    ///
    /// # Panics
    ///
    /// When the file does not load or the answer ends otherwise.
    #[test]
    fn load_binary_points_at_the_triage() {
        use super::{LoadBinaryParams, Parameters};
        let path = std::env::temp_dir().join(format!("borer-load-next-{}.bin", std::process::id()));
        std::fs::write(&path, [0xc3u8; 64]).expect("the file is written");
        let said = super::BorerServer::default().load_binary(Parameters(LoadBinaryParams {
            path: path.display().to_string(),
            entry_file_offset: None,
            pdb: Some(false),
            arch: None,
            base: None,
            entry: None,
            regions: None,
        }));
        std::fs::remove_file(&path).expect("the file is removed");
        let said = said.expect("any file loads");
        assert!(said.ends_with(super::LOAD_NEXT), "{said}");
    }

    /// `load_binary` with `arch` maps a headerless file where `base` says.
    ///
    /// The code tools then read it; without `arch` the same file loads as
    /// it always did, with no code; a layout that does not parse or fit,
    /// or an entry given twice, is refused and changes nothing.
    ///
    /// # Panics
    ///
    /// When a load answers otherwise or a refused one moves the session.
    #[test]
    fn load_binary_maps_raw_code_at_a_stated_layout() {
        use super::{FunctionsParams, LoadBinaryParams, Parameters, RawArch, RawLoad};
        // ASM: call 0x1000b; add rax, 1; ret; int3; mov eax, 42; ret
        const CODE: [u8; 17] = [
            0xe8, 0x06, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc0, 0x01, 0xc3, 0xcc, 0xb8, 0x2a, 0x00,
            0x00, 0x00, 0xc3,
        ];
        let path =
            std::env::temp_dir().join(format!("borer-raw-layout-{}.bin", std::process::id()));
        std::fs::write(&path, CODE).expect("the file is written");
        let shown = path.display().to_string();
        let load = |raw: RawLoad, entry_file_offset: Option<u64>| {
            super::BorerServer::default().load_binary(Parameters(LoadBinaryParams {
                path: shown.clone(),
                entry_file_offset,
                pdb: None,
                arch: raw.arch,
                base: raw.base,
                entry: raw.entry,
                regions: raw.regions,
            }))
        };
        let plain = load(RawLoad::default(), None);
        let server = super::BorerServer::default();
        let stated = RawLoad {
            arch: Some(RawArch::X64),
            base: Some("0x10000".to_owned()),
            entry: None,
            regions: None,
        };
        let mapped = server.load_binary(Parameters(LoadBinaryParams {
            path: shown.clone(),
            entry_file_offset: None,
            pdb: None,
            arch: stated.arch,
            base: stated.base.clone(),
            entry: None,
            regions: None,
        }));
        let functions = server.functions(Parameters(FunctionsParams {
            filter: None,
            sort: None,
            offset: None,
            limit: None,
            count_only: None,
        }));
        let past = server.load_binary(Parameters(LoadBinaryParams {
            path: shown.clone(),
            entry_file_offset: None,
            pdb: Some(false),
            arch: Some(RawArch::X64),
            base: None,
            entry: None,
            regions: Some("0x10000@0:0x40".to_owned()),
        }));
        let twice = load(
            RawLoad {
                entry: Some("0x10000".to_owned()),
                ..stated.clone()
            },
            Some(0),
        );
        let no_arch = load(
            RawLoad {
                base: Some("0x10000".to_owned()),
                ..RawLoad::default()
            },
            None,
        );
        std::fs::remove_file(&path).expect("the file is removed");

        let plain = plain.expect("any file loads");
        assert!(plain.contains("arch: unknown\n"), "{plain}");
        let mapped = mapped.expect("the layout maps");
        assert!(
            mapped.contains("format:  raw   arch: x86-64 (64-bit)\n"),
            "{mapped}"
        );
        assert!(mapped.contains("entry: 0x10000\n"), "{mapped}");
        assert!(mapped.contains("kind stated layout"), "{mapped}");
        let functions = functions.expect("it lists");
        assert!(
            functions.contains("0x10000 ") && functions.contains("0x1000b "),
            "{functions}"
        );
        let past = past.expect_err("refused").message;
        assert!(
            past.contains("runs past the end of the file at 0x11"),
            "{past}"
        );
        assert!(
            twice.expect_err("refused").message.contains("give one"),
            "both entries"
        );
        assert!(
            no_arch.expect_err("refused").message.contains("need arch"),
            "base alone"
        );
        assert_eq!(
            *super::read_lock(&server.raw_load),
            stated,
            "the refusal moved it"
        );
        assert!(server.loaded().is_some_and(|p| p.entry == Some(0x10000)));
    }

    /// A count above a tool's cap is cut to the cap and the answer opens by
    /// saying so, naming the parameter, what was asked and the cap; a count
    /// within the cap leaves the answer as it was.
    ///
    /// # Panics
    ///
    /// When a cut goes unsaid, or an uncut answer carries a note.
    #[test]
    fn a_count_above_the_cap_is_noted_in_the_answer() {
        use super::{FunctionsParams, HexdumpParams, Parameters, ReadParams, StringsParams};
        let server = raw_server();
        let functions = |limit| {
            server
                .functions(Parameters(FunctionsParams {
                    filter: None,
                    sort: None,
                    offset: None,
                    limit,
                    count_only: None,
                }))
                .expect("lists")
        };
        let capped = functions(Some(99_999));
        assert!(
            capped.starts_with("# limit 99999 capped at 300\n"),
            "{capped}"
        );
        assert_eq!(
            capped.strip_prefix("# limit 99999 capped at 300\n"),
            Some(functions(Some(300)).as_str()),
            "the note is the only difference"
        );
        assert!(!functions(Some(300)).contains("capped"));

        let strings = server
            .strings(Parameters(StringsParams {
                min_length: None,
                filter: None,
                encoding: None,
                offset: None,
                limit: Some(1_000),
                count_only: None,
            }))
            .expect("lists");
        assert!(
            strings.starts_with("# limit 1000 capped at 500\n# showing "),
            "{strings}"
        );
        let dump = server
            .hexdump(Parameters(HexdumpParams {
                address: "0x1000".to_owned(),
                length: Some(99_999),
            }))
            .expect("dumps");
        assert!(
            dump.starts_with("# length 99999 capped at 4096\n# 0x1000..0x1100 .text\n"),
            "{dump}"
        );
        let read = server
            .read(Parameters(ReadParams {
                address: "0x1000".to_owned(),
                kind: Some(super::params::ReadKind::U8),
                r#type: None,
                count: Some(300),
            }))
            .expect("reads");
        assert!(
            read.starts_with("# count 300 capped at 256\n# 256 x u8 at 0x1000"),
            "{read}"
        );
    }

    /// Every list tool refuses `limit: 0` alike, before anything is loaded,
    /// and so does a watch of no bytes; `decompile` reads zero as every line,
    /// as it documents.
    ///
    /// # Panics
    ///
    /// When a zero is answered, or refused another way.
    #[test]
    fn every_list_tool_refuses_a_zero_limit_alike() {
        use super::{
            DecompileParams, FindFunctionByStringParams, FunctionsParams, LiveInstancesParams,
            LiveModulesParams, LiveWatchParams, Parameters, SearchParams, StringsParams,
            SymbolsParams, XrefsParams,
        };
        let server = super::BorerServer::default();
        let refusals = [
            server.strings(Parameters(StringsParams {
                min_length: None,
                filter: None,
                encoding: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.symbols(Parameters(SymbolsParams {
                kind: None,
                filter: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.functions(Parameters(FunctionsParams {
                filter: None,
                sort: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.xrefs(Parameters(XrefsParams {
                address: "main".to_owned(),
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.search(Parameters(SearchParams {
                query: "90".to_owned(),
                kind: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.find_function_by_string(Parameters(FindFunctionByStringParams {
                filter: "x".to_owned(),
                offset: None,
                limit: Some(0),
            })),
            server.live_instances(Parameters(LiveInstancesParams {
                class: "Player".to_owned(),
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.live_modules(Parameters(LiveModulesParams {
                filter: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
        ];
        for refused in refusals {
            let e = refused.expect_err("a zero limit is refused");
            assert_eq!(e.code, super::ErrorCode::INVALID_PARAMS);
            assert_eq!(e.message, "limit must be at least 1");
        }
        let watch = server
            .live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: Some("0x1000".to_owned()),
                length: Some(0),
                class: None,
            }))
            .expect_err("a watch of no bytes is refused");
        assert_eq!(watch.code, super::ErrorCode::INVALID_PARAMS);
        assert_eq!(watch.message, "length must be at least 1");
        let all = server
            .decompile(Parameters(DecompileParams {
                address: "main".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(0),
            }))
            .expect_err("nothing is loaded");
        assert_eq!(
            all.message,
            super::NO_BINARY,
            "zero is every line, not refused"
        );
    }

    /// `set_comment` refuses an address in no section as `set_name` does,
    /// dry run or not, and still previews one inside a section.
    ///
    /// # Panics
    ///
    /// When a comment outside the image is accepted, the two refusals
    /// differ beyond the annotation's name, or a mapped address is refused.
    #[test]
    fn a_comment_outside_every_section_is_refused_as_a_name_is() {
        use super::{Parameters, SetCommentParams, SetNameParams};
        let server = raw_server();
        let comment = |address: &str, dry_run| {
            server.set_comment(Parameters(SetCommentParams {
                address: address.to_owned(),
                comment: "typo".to_owned(),
                dry_run,
            }))
        };
        let refused = comment("0x1", Some(false)).expect_err("outside the image");
        assert!(
            refused
                .message
                .starts_with("0x1 is in no section, so nothing there can take a comment; "),
            "{}",
            refused.message
        );
        assert!(comment("0x1", None).is_err(), "a dry run is refused too");
        let named = server
            .set_name(Parameters(SetNameParams {
                address: "0x1".to_owned(),
                name: "typo".to_owned(),
                dry_run: None,
            }))
            .expect_err("outside the image");
        assert_eq!(named.code, refused.code);
        assert_eq!(
            named.message,
            refused.message.replace("a comment", "a name")
        );
        let preview = comment("0x1010", None).expect("inside .text");
        assert!(
            preview.starts_with("dry-run: would set comment at 0x1010"),
            "{preview}"
        );
        assert!(super::read_lock(&server.overlay).comments.is_empty());
    }

    /// `xrefs` reads a target that is neither an address nor a name as
    /// `Class+offset`.
    ///
    /// It lists the functions using that field through a pointer typed as
    /// the class, with the value stored and the instruction; a class
    /// nothing belongs to is refused, saying which forms the target may
    /// take.
    ///
    /// # Panics
    ///
    /// When the field's writer is missing, or the refusal does not name
    /// the field form.
    #[test]
    fn xrefs_reads_a_class_and_an_offset_as_a_field() {
        use super::{Parameters, XrefsParams};
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0xc3; 0x100];
        // ASM: mov dword [rcx+0x24], 5; ret
        code[..8].copy_from_slice(&[0xc7, 0x41, 0x24, 0x05, 0x00, 0x00, 0x00, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut overlay = super::Overlay::default();
        overlay.names.insert(0x1000, "Foo::Set".to_owned());
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            overlay: std::sync::Arc::new(std::sync::RwLock::new(overlay)),
            ..super::BorerServer::default()
        };
        let xrefs = |address: &str| {
            server.xrefs(Parameters(XrefsParams {
                address: address.to_owned(),
                offset: None,
                limit: None,
                count_only: None,
            }))
        };
        let field = xrefs("Foo+0x24").expect("a field");
        assert!(
            field
                .starts_with("# Foo+0x24: 1 functions use it through a pointer typed as the class"),
            "{field}"
        );
        assert!(
            field.contains(
                "
0x1000	Foo::Set	a1	w	0x5	0x1000
"
            ),
            "{field}"
        );
        let refused = xrefs("Nope+0x24").expect_err("no such class");
        assert!(
            refused
                .message
                .ends_with("; nor is it Class+offset, a field of a class with methods or a vtable"),
            "{}",
            refused.message
        );
    }

    /// A field offset is hex with its `0x` and decimal without, as an
    /// address is; anything else is refused by name rather than guessed.
    ///
    /// # Panics
    ///
    /// When a form reads as another number, or a guess is accepted.
    #[test]
    fn a_field_offset_is_hex_with_0x_and_decimal_without() {
        let parse = |t: &str| super::parse_field_offset(t).map_err(|e| e.to_string());
        assert_eq!(parse("0x10"), Ok(16));
        assert_eq!(parse("0X1f"), Ok(31));
        assert_eq!(parse("16"), Ok(16));
        assert_eq!(parse("-0x8"), Ok(-8));
        assert_eq!(parse("-8"), Ok(-8));
        assert_eq!(parse("abc"), Err("bad offset 'abc'".to_owned()));
        for guess in ["1f", "", "-", "0x", "+5", "0x+5", "--8", "0x1g"] {
            assert!(
                parse(guess).is_err_and(|e| e.starts_with("bad offset ")),
                "{guess:?} was read"
            );
        }
        assert!(parse("0xffffffffffffffff").is_err_and(|e| e.contains("signed displacement")));
    }

    /// A `%` that begins no escape is left as it came.
    ///
    /// A name or filter can contain one, and mangling it would lose a lookup
    /// that works today.
    ///
    /// # Panics
    ///
    /// When a stray percent is altered.
    #[test]
    fn a_stray_percent_survives() {
        assert_eq!(percent_decode("100%"), "100%");
        assert_eq!(percent_decode("%zz"), "%zz");
        assert_eq!(percent_decode("%"), "%");
        assert_eq!(percent_decode("%2"), "%2");
        assert_eq!(percent_decode("a%%20b"), "a% b");
    }

    /// A server with a one-instruction program loaded, for a handler test
    /// that needs an analysis but not a real binary.
    fn tiny_server() -> super::BorerServer {
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 1, false, true);
        let program = Program::raw(vec![0xc3], Arch::X86_64, 0, Some(0x1000), vec![text]);
        super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        }
    }

    /// `borer://script` refuses a device by name, as the other file
    /// resources do, where reading `CON` waited on the console forever.
    ///
    /// # Panics
    ///
    /// When a device is read.
    #[test]
    fn a_script_resource_refuses_a_device() {
        if cfg!(windows) {
            let refused = tiny_server().script_text("CON").expect_err("a device");
            assert_eq!(refused.code, super::ErrorCode::INVALID_PARAMS);
            assert!(refused.message.contains("device"), "{}", refused.message);
        }
    }

    /// A failing script file answers as the `script` tool answers one:
    /// what it printed before the error, then the error; the resource
    /// answered the error alone and the printed lines were lost.
    ///
    /// # Panics
    ///
    /// When the failure loses its output or its error.
    #[test]
    fn a_failing_script_resource_keeps_what_it_printed() {
        let path = std::env::temp_dir().join(format!("borer-fail-{}.rhai", std::process::id()));
        std::fs::write(&path, "print(\"before the error\");\nlet x = 1 / 0;\n")
            .expect("the script is written");
        let answer = tiny_server().script_text(&path.to_string_lossy());
        std::fs::remove_file(&path).expect("the script is removed");
        let text = answer.expect("a failed script still answers");
        assert!(text.starts_with("before the error\n"), "{text}");
        assert!(text.contains("\n# script failed: "), "{text}");
    }

    /// `borer://anchors` refuses a manifest past its size or anchor cap by
    /// name and lists at most a page of rows, saying so; a 200 MB manifest
    /// ran for minutes and every row came back.
    ///
    /// # Panics
    ///
    /// When an oversized manifest is judged or the rows are not capped.
    #[test]
    fn the_anchors_resource_caps_its_manifest_and_rows() {
        let server = tiny_server();
        let dir = std::env::temp_dir();
        let id = std::process::id();
        let write = |name: &str, lines: usize| {
            let path = dir.join(format!("borer-anchors-{id}-{name}.txt"));
            std::fs::write(&path, "function nosuch 0x1\n".repeat(lines))
                .expect("the manifest is written");
            path
        };
        let huge = write("huge", 60_000);
        let many = write("many", 5001);
        let page = write("page", 600);
        let answers: Vec<_> = [&huge, &many, &page]
            .iter()
            .map(|p| server.anchors_text(&p.to_string_lossy()))
            .collect();
        for p in [&huge, &many, &page] {
            std::fs::remove_file(p).expect("the manifest is removed");
        }
        let [huge, many, page] = <[_; 3]>::try_from(answers).expect("three answers");
        let huge = huge.expect_err("past the size cap");
        assert!(huge.message.contains("bytes, past the"), "{}", huge.message);
        let many = many.expect_err("past the anchor cap");
        assert!(
            many.message.contains("has 5001 anchors, past the 5000"),
            "{}",
            many.message
        );
        let page = page.expect("a page of rows");
        assert!(
            page.starts_with(
                "# 600 anchors: 0 held, 0 moved, 0 changed, 600 gone, showing 500 of 600"
            ),
            "{page}"
        );
        assert_eq!(page.lines().count(), 502, "{page}");
    }

    /// Loads a file into a server, without its PDB, and returns the summary.
    ///
    /// # Panics
    ///
    /// When the file does not load.
    #[cfg(windows)]
    fn load_into(server: &super::BorerServer, path: &std::path::Path) -> String {
        use super::{LoadBinaryParams, Parameters};
        server
            .load_binary(Parameters(LoadBinaryParams {
                path: path.display().to_string(),
                entry_file_offset: None,
                pdb: Some(false),
                arch: None,
                base: None,
                entry: None,
                regions: None,
            }))
            .expect("the file loads")
    }

    /// A process attached before `load_binary` is mapped onto the binary
    /// the load brings.
    ///
    /// A static address then reads at its live place; a file that only
    /// shares the module's name is another build, refused with what
    /// differs and never mapped.
    ///
    /// # Panics
    ///
    /// When the load leaves the process unmapped, the read is not rebased,
    /// or the impostor is mapped.
    #[cfg(windows)]
    #[test]
    fn the_live_mapping_follows_load_binary_and_checks_headers() {
        use super::{LiveAttachParams, LiveReadParams, Parameters};
        let exe = std::env::current_exe().expect("the test binary has a path");
        let server = super::BorerServer::default();
        let attached = server
            .live_attach(Parameters(LiveAttachParams {
                process: std::process::id().to_string(),
            }))
            .expect("attach to self");
        assert!(attached.contains("no binary loaded"), "{attached}");
        let loaded = load_into(&server, &exe);
        assert!(loaded.contains("its headers match the file"), "{loaded}");
        let entry = server
            .loaded()
            .and_then(|p| p.entry)
            .expect("the test binary has an entry");
        let read = server
            .live_read(Parameters(LiveReadParams {
                address: format!("{entry:#x}"),
                kind: Some(super::params::ReadKind::U8),
                count: None,
            }))
            .expect("the entry is readable");
        assert!(read.contains(&format!("(= static {entry:#x})")), "{read}");
        let unrebased = server.live_read(Parameters(LiveReadParams {
            address: format!("live:{entry:#x}"),
            kind: Some(super::params::ReadKind::U8),
            count: None,
        }));
        assert!(
            unrebased.as_ref().map_or_else(
                |e| e
                    .message
                    .starts_with(&format!("{entry:#x} is not readable")),
                |text| text.starts_with(&format!("# 1 u8 value(s) at live {entry:#x}\n"))
            ),
            "live: is taken as it is: {unrebased:?}"
        );

        let dir = std::env::temp_dir().join(format!("borer-live-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp directory");
        let impostor = dir.join(exe.file_name().expect("a file name"));
        let mut bytes = std::fs::read(&exe).expect("read the test binary");
        let pe = usize::try_from(u32::from_le_bytes(
            bytes[0x3c..0x40].try_into().expect("four bytes"),
        ))
        .expect("fits");
        bytes[pe + 8] ^= 0xff;
        std::fs::write(&impostor, &bytes).expect("write the impostor");
        let loaded = load_into(&server, &impostor);
        std::fs::remove_dir_all(&dir).expect("remove the temp directory");
        assert!(loaded.contains("is another build (timestamp"), "{loaded}");
        assert!(
            super::lock(&server.live)
                .as_ref()
                .is_some_and(|s| s.rebase.is_err()),
            "the impostor is not mapped"
        );
        server.live_detach().expect("detach");
    }

    /// Every live refusal is invalid params, as a static one is, so one code
    /// tells the agent to change the call: nothing attached, an address not
    /// readable, a process name that is empty.
    ///
    /// # Panics
    ///
    /// When a refusal comes back as an internal error or says the wrong thing.
    #[test]
    fn a_live_refusal_is_invalid_params() {
        use super::{ErrorCode, LiveAttachParams, LiveReadParams, Parameters};
        let server = super::BorerServer::default();
        let read = |address: &str| {
            server
                .live_read(Parameters(LiveReadParams {
                    address: address.to_owned(),
                    kind: None,
                    count: None,
                }))
                .expect_err("refused")
        };
        let none = read("0x10");
        assert_eq!(none.code, ErrorCode::INVALID_PARAMS);
        assert_eq!(none.message, "no process attached: live_attach first");
        let attach = |process: &str| {
            server.live_attach(Parameters(LiveAttachParams {
                process: process.to_owned(),
            }))
        };
        let blank = attach("").expect_err("no process named");
        assert_eq!(blank.code, ErrorCode::INVALID_PARAMS);
        if cfg!(windows) {
            assert!(
                blank.message.starts_with("no process given: "),
                "{}",
                blank.message
            );
            attach(&std::process::id().to_string()).expect("attach to self");
            let unreadable = read("0x10");
            assert_eq!(unreadable.code, ErrorCode::INVALID_PARAMS);
            assert_eq!(unreadable.message, "0x10 is not readable in the process");
            server.live_detach().expect("detach");
        }
    }

    /// A second attach says it drops the first one's watches, `reload` says
    /// the live session ends with the server, and the module list pages.
    ///
    /// # Panics
    ///
    /// When a drop goes unsaid or the module list does not page.
    #[cfg(windows)]
    #[test]
    fn the_live_session_says_what_it_drops_and_pages_modules() {
        use super::{LiveAttachParams, LiveModulesParams, LiveWatchParams, Parameters};
        let server = raw_server();
        let attach = || {
            server
                .live_attach(Parameters(LiveAttachParams {
                    process: std::process::id().to_string(),
                }))
                .expect("attach to self")
        };
        attach();
        server
            .live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: Some("0x7ffe0000".to_owned()),
                length: Some(8),
                class: None,
            }))
            .expect("the shared user page is readable");
        let again = attach();
        assert!(
            again.contains("its 1 watch(es) are dropped: w\n"),
            "{again}"
        );
        let reload = server.reload().expect("reload answers");
        assert!(
            reload.contains("and its 0 watch(es) end with this server: live_attach again"),
            "{reload}"
        );
        let modules = |filter: Option<&str>, count_only| {
            server
                .live_modules(Parameters(LiveModulesParams {
                    filter: filter.map(str::to_owned),
                    offset: None,
                    limit: Some(1),
                    count_only,
                }))
                .expect("the module list")
        };
        let page = modules(Some(".dll"), None);
        assert!(page.starts_with("# showing 1 of "), "{page}");
        assert_eq!(page.lines().count(), 3, "{page}");
        let count = modules(None, Some(true));
        assert!(
            count.ends_with(" modules\n") && count.lines().count() == 1,
            "{count}"
        );
        server.live_detach().expect("detach");
    }

    /// Once the attached process exits, every live tool says it has exited
    /// instead of blaming the address, and so does the detach.
    ///
    /// # Panics
    ///
    /// When a tool answers after the exit, or blames the address.
    #[cfg(windows)]
    #[test]
    fn every_live_tool_says_the_process_exited() {
        use super::{LiveAttachParams, LiveReadParams, LiveWatchParams, Parameters};
        let mut child = std::process::Command::new("ping")
            .args(["-n", "60", "127.0.0.1"])
            .stdout(std::process::Stdio::null())
            .spawn()
            .expect("ping starts");
        let server = super::BorerServer::default();
        let mut tries = 0;
        while let Err(e) = server.live_attach(Parameters(LiveAttachParams {
            process: child.id().to_string(),
        })) {
            tries += 1;
            assert!(tries < 500, "{}", e.message);
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        let watch = |address: Option<&str>| {
            server.live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: address.map(str::to_owned),
                length: Some(8),
                class: None,
            }))
        };
        watch(Some("0x7ffe0000")).expect("the shared user page is readable");
        child.kill().expect("end ping");
        child.wait().expect("ping ended");
        let read = server
            .live_read(Parameters(LiveReadParams {
                address: "0x7ffe0000".to_owned(),
                kind: None,
                count: None,
            }))
            .expect_err("the process is gone");
        assert!(
            read.message.contains("has exited (exit code 0x1)"),
            "{}",
            read.message
        );
        let diff = watch(None).expect_err("the process is gone");
        assert!(diff.message.contains("has exited"), "{}", diff.message);
        let detached = server.live_detach().expect("detach");
        assert!(
            detached.ends_with(", which had exited (exit code 0x1)"),
            "{detached}"
        );
    }

    /// A watch refuses a class the analysis does not know, as `live_object`
    /// does.
    ///
    /// A watch without a class reports a change as the whole aligned word.
    ///
    /// # Panics
    ///
    /// When the unknown class is accepted or the change is not reported
    /// as the word's value.
    #[cfg(windows)]
    #[test]
    fn a_watch_refuses_an_unknown_class_and_reports_whole_words() {
        use super::{LiveAttachParams, LiveWatchParams, Parameters};
        let server = raw_server();
        server
            .live_attach(Parameters(LiveAttachParams {
                process: std::process::id().to_string(),
            }))
            .expect("attach to self");
        let cell = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0xff));
        let at = format!("{:#x}", cell.as_ptr() as usize);
        let watch = |class: Option<&str>, address: Option<&str>| {
            server.live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: address.map(str::to_owned),
                length: Some(8),
                class: class.map(str::to_owned),
            }))
        };
        let refused = watch(Some("Nope"), Some(&at)).expect_err("no such class");
        assert_eq!(refused.message, "no function belongs to class Nope");
        let started = watch(None, Some(&at)).expect("a watch of a heap word");
        assert!(started.starts_with("watch w: 8 bytes at "), "{started}");
        cell.store(0x100, std::sync::atomic::Ordering::SeqCst);
        let diff = watch(None, None).expect("the diff");
        assert!(diff.contains("(255 -> 256)"), "{diff}");
        server.live_detach().expect("detach");
    }
}
