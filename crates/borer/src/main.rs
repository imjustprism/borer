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
mod params;
mod recall;
mod relay;
mod resources;
mod setup;
mod strwalk;
mod symsrv;

use borer_engine::analysis::{
    Analysis, EnumSource, Overlay, parse_addr, parse_off, render, resolve,
};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::Program;
use borer_engine::{disasm, entropy, hexdump as hexfmt, memory, num, strings as strscan};
use rayon::prelude::*;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{
    CacheScope, CallToolRequestParams, CallToolResponse, ClientNotification, CompleteRequestParams,
    CompleteResult, CompletionInfo, ContentBlock, ErrorCode, InitializeRequestParams,
    JsonRpcMessage, ListResourceTemplatesResult, ListResourcesResult, ListToolsResult,
    PaginatedRequestParams, PromptMessage, ProtocolVersion, ReadResourceRequestParams,
    ReadResourceResponse, ReadResourceResult, Reference, RequestId, Resource, ResourceContents,
    ResourceTemplate, ResultType, Role, Tool,
};
use rmcp::service::{RequestContext, RxJsonRpcMessage, TxJsonRpcMessage};
use rmcp::transport::Transport;
use rmcp::transport::async_rw::AsyncRwTransport;
use rmcp::{
    ErrorData, RoleServer, ServerHandler, ServiceExt, prompt, prompt_handler, prompt_router, tool,
    tool_handler, tool_router,
};

use borer_engine::live::{self as live, Memory as _, Rebase, Snapshot};
use params::{
    Annotation, CallgraphParams, CfgParams, ClassLayoutParams, DecompileBatchParams,
    DecompileParams, Detail, DisassembleFunctionParams, DisassembleParams, EntropyParams,
    ExplainFunctionArgs, FetchPdbParams, Filter, FindCheckArgs, FindFunctionByStringParams,
    FunctionDetailParams, FunctionParams, FunctionsParams, HexdumpParams, LiveAttachParams,
    LiveInstancesParams, LiveObjectParams, LiveReadParams, LiveWatchParams, LoadBinaryParams,
    LoadProjectParams, Page, QueryParams, ReachesParams, ReadParams, SaveProjectParams,
    ScriptParams, SearchKind, SearchParams, SetCommentParams, SetNameParams, SetTypeParams,
    StringEncoding, StringsParams, SymbolsParams, TypesParams, XrefsParams, count_param,
    must_be_in_a_section, must_fit_a_row, to_usize,
};
use recall::{FRESH_SUFFIX, Recall, SINCE_ARG, SINCE_SUFFIX, Tag, budgeted};

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
    /// The loaded program, `None` before `load_binary`.
    program: Arc<RwLock<Option<Arc<Program>>>>,
    /// Whether the loaded program's companion PDB was applied: a
    /// comparison build loads the same way, or a diff of a binary against
    /// itself pairs functions a PDB names with ones it does not.
    pdb_applied: Arc<RwLock<bool>>,
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

/// A process attached for reading, with where the loaded binary sits in it
/// and the snapshots taken of its memory.
#[derive(Debug)]
struct LiveSession {
    /// The process, open with read rights only.
    process: borer_live::Process,
    /// Where the loaded binary's image sits in the process; `None` when the
    /// binary is not one of its modules (addresses are then taken as live).
    rebase: Option<Rebase>,
    /// Watches by name, so a diff names the fields that changed.
    snapshots: std::collections::BTreeMap<String, Watch>,
    /// The main thread's block of the image's thread-local storage, where
    /// the singletons the analysis placed at TLS offsets live; `None` when
    /// the image has no TLS or the block could not be read.
    tls_block: Option<u64>,
}

/// Bytes of the process kept under a watch name.
#[derive(Debug, Clone)]
struct Watch {
    /// The bytes as they were when the watch was set or last reported.
    snapshot: Snapshot,
    /// The class of the object the bytes are, when one is known, so a diff
    /// names the fields that changed.
    class: Option<String>,
}

/// The refusal every tool answers before `load_binary`.
const NO_BINARY: &str = "no binary loaded; call load_binary first";

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
/// for next.
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
    let mut out = match needle.needle() {
        Some(n) => format!(
            "// {} of {total} lines carry {n:?}, showing {} from {from}",
            picked.len(),
            shown.len()
        ),
        None => format!("// showing {} of {total} lines from {from}", shown.len()),
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
        if prog.arch.bitness().is_none() {
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

    /// The analysis, for a resource read outside a tool body.
    ///
    /// # Errors
    ///
    /// Internal error when no binary is loaded or its architecture has no
    /// code analysis.
    fn analysis(&self) -> Result<Arc<Analysis>, ErrorData> {
        self.ensure_analysis().map_err(err_internal)
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
            Err(e) => {
                let what = e
                    .downcast_ref::<&str>()
                    .map(|s| (*s).to_owned())
                    .or_else(|| e.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "no message".to_owned());
                Err(err_internal(format!(
                    "the analysis faulted on this binary: {what}. The session is still up; another tool or another address may still answer."
                )))
            }
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
        if let Some(why) = program.no_code() {
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
    /// # Arguments
    ///
    /// * `f` - The tool body; its `Err` text becomes an internal error.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded; internal error when the
    /// architecture has no code analysis or `f` fails or faults.
    fn with_analysis(
        &self,
        f: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
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

    /// Resolves an address argument: `0x`-hex or decimal text, else a name
    /// looked up through the analysis, symbols and overlay (agents name
    /// things).
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name.
    fn addr(&self, p: &Program, text: &str) -> Result<u64, String> {
        if let Some(va) = parse_addr(text) {
            return Ok(va);
        }
        let a = self.ensure_analysis()?;
        resolve(p, &a, &self.overlay(), text)
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
        borer_engine::analysis::function_entry(p, a, va)
    }
}

#[tool_router]
impl BorerServer {
    /// Loads a file as the current program and resets analysis and overlay.
    ///
    /// A session's names must not leak into another image, so the overlay
    /// is cleared; a session that has not saved them is told what it lost.
    ///
    /// # Arguments
    ///
    /// * `LoadBinaryParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when the file does not load or the entry offset is past its end.
    #[tool(
        description = "Load a PE/ELF (or raw) file as the current program; returns its summary.",
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
        }): Parameters<LoadBinaryParams>,
    ) -> Result<String, ErrorData> {
        let apply_pdb = pdb.unwrap_or(true);
        *write_lock(&self.pdb_applied) = apply_pdb;
        let mut program = Program::load_with_symsrv(
            &PathBuf::from(&path),
            apply_pdb,
            symsrv::cache_dir().as_deref(),
        )
        .map_err(|e| err_params(format!("load failed: {e:#}")))?;
        if let Some(off) = entry_file_offset {
            if off >= num::from_usize(program.bytes.len()) {
                return Err(err_params(format!(
                    "entry_file_offset {off:#x} beyond file size {:#x}",
                    program.bytes.len()
                )));
            }
            program.entry = Some(program.image_base + off);
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
        *write_lock(&self.program_packs) = packs;
        *write_lock(&self.program) = Some(Arc::new(program));
        *write_lock(&self.analysis) = None;
        *write_lock(&self.strings) = None;
        Ok(summary)
    }

    /// Fetches the loaded PE's missing companion PDB from a symbol server.
    ///
    /// Off by default like every side effect: a dry run says the URL and
    /// the cache destination and touches nothing. A confirmed fetch checks
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
            let more = if p.no_code().is_some() {
                "borer://triage reads the whole file in one call"
            } else {
                "templated resources read by URI (resources/templates/list): why, taint, layout, emulate, solve, devirt, unpack, flat, vm, fields, diff, difffn, carry, migrate"
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
            let bitness = p
                .arch
                .bitness()
                .ok_or_else(|| p.no_code().unwrap_or_default())?;
            let va = self
                .ensure_analysis()
                .ok()
                .and_then(|a| render::instruction_at_or_before(p, &a, asked))
                .unwrap_or(asked);
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
            let limit = self
                .ensure_analysis()
                .ok()
                .and_then(|a| render::sweep_limit(&a, va));
            let window = limit
                .and_then(|end| usize::try_from(end - va).ok())
                .and_then(|n| code.get(..n.min(code.len())))
                .unwrap_or(code);
            let lines = disasm::disassemble(window, va, bitness, n);
            let o = self.overlay();
            let ends = limit.map_or(String::new(), |end| {
                format!("; code ends at {end:#x}, what follows is data")
            });
            let caveat = self
                .ensure_analysis()
                .ok()
                .map(|a| render::listing_caveat(p, &a, va))
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
        self.with_analysis(|p, a, o| {
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
    ///
    /// # Arguments
    ///
    /// * `ReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind; internal error when the address does not
    /// resolve or the bytes are not mapped.
    #[tool(
        description = "Read `count` typed values (kind u8..u64, i8..i64, f32, f64, ptr, cstr, wstr; default u64, count 1, max 256) as `va value` rows; pointers are named.",
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
            count,
        }): Parameters<ReadParams>,
    ) -> Result<String, ErrorData> {
        let kind_text = kind.unwrap_or_default();
        let kind: memory::Kind = kind_text.into();
        let count = count_param(count, 1, 256, "count")?;
        let n = count.n;
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
                if let Some(t) = v.target {
                    if let Some(a) = &analysis
                        && let Some(f) = a.function_at(t)
                    {
                        text.push_str(&format!(
                            " -> {}",
                            borer_engine::analysis::name_of(a, &o, f.entry)
                        ));
                    } else if let Some(n) = o.names.get(&t) {
                        text.push_str(&format!(" -> {n}"));
                    } else if let Some(a) = &analysis
                        && let Some(s) = a.symbol_at(p, t)
                    {
                        text.push_str(&format!(
                            " -> {}",
                            borer_engine::search::demangled_name(&s.name)
                        ));
                    } else if let Some(s) = p.section_at(t) {
                        text.push_str(&format!(" -> {}", s.name));
                    }
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
    /// When no binary is loaded.
    #[tool(
        description = "High-entropy regions (packed/encrypted data) as `off va len entropy` rows at or above threshold bits/byte (default 7.2, window 1024, max 200).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn entropy(
        &self,
        Parameters(EntropyParams { window, threshold }): Parameters<EntropyParams>,
    ) -> Result<String, ErrorData> {
        let window = to_usize(window.unwrap_or(1024).max(64));
        let threshold = threshold.unwrap_or(7.2);
        if !(0.0..=8.0).contains(&threshold) {
            return Err(err_params(format!(
                "threshold {threshold} is outside 0..8 bits per byte"
            )));
        }
        let ceiling = entropy::ceiling(window);
        let unreachable = if threshold > ceiling {
            format!(
                "# note: random data averages about {ceiling:.2} bits in a {window}-byte window; above that only windows that beat chance pass, so widen the window or lower the threshold\n"
            )
        } else {
            String::new()
        };
        self.with_program(|p| {
            let regions = entropy::high_entropy_regions(p, window, threshold);
            Ok(format!(
                "# {} high-entropy regions (window={window}, threshold={threshold:.2}){}\n{unreachable}{}",
                regions.len(),
                if regions.len() >= entropy::REGIONS_MAX { " (cap reached)" } else { "" },
                entropy::regions_tsv(p, &regions)
            ))
        })
    }

    /// Scans every section for known crypto and hash constants.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Crypto tables and constants (AES, SHA-1/2, MD5, CRC-32, ChaCha, Blowfish, RC5/6, xxHash/FNV/SipHash, Base64) as `va section algorithm` rows (max 200).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn find_crypto_constants(&self) -> Result<String, ErrorData> {
        self.with_program(|p| {
            Ok(render::crypto_tsv(
                p,
                &self.analysis_or_empty(),
                &self.overlay(),
            ))
        })
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
        description = "One-call triage of a function: shape, loops, jump tables, callers/callees by name, strings and data it references.",
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
        self.with_analysis(|p, a, o| {
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
        description = "Functions referencing a string containing `filter`: a numbered `# strings:` legend, then one `entry name: 1 2 5` row per function (limit default 50, max 300, caps both rows and legend).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn find_function_by_string(
        &self,
        Parameters(FindFunctionByStringParams { filter, limit }): Parameters<
            FindFunctionByStringParams,
        >,
    ) -> Result<String, ErrorData> {
        let limit = count_param(limit, 50, 300, "limit")?;
        self.with_analysis(|p, a, o| Ok(render::functions_by_string_tsv(p, a, o, &filter, limit.n)))
            .map(|text| limit.noted(text))
    }

    /// Runs `f` with the attached process.
    ///
    /// # Arguments
    ///
    /// * `f` - The tool body over the session.
    ///
    /// # Errors
    ///
    /// Internal error when no process is attached or `f` fails.
    fn with_live(
        &self,
        f: impl FnOnce(&mut LiveSession) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let mut guard = lock(&self.live);
        let session = guard
            .as_mut()
            .ok_or_else(|| err_internal("no process attached: live_attach first"))?;
        f(session).map_err(err_internal)
    }

    /// Resolves an address an agent gave for the process: a name or a
    /// static address of the loaded binary moves into the process, any
    /// other number is taken as live.
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
        let va = match program {
            Some(p) => self.addr(&p, text)?,
            None => parse_addr(text).ok_or_else(|| {
                format!("{text} is not an address, and no binary is loaded to look the name up in")
            })?,
        };
        Ok(session.rebase.map_or(va, |r| r.live_of(va)))
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
        let proc = borer_live::Process::attach(&process).map_err(err_internal)?;
        let modules = proc.modules();
        let program = self.loaded();
        let rebase = program.as_ref().and_then(|p| Rebase::of(p, &modules));
        let mut out = format!(
            "attached to {} (pid {}), {} modules, read-only\n",
            proc.name(),
            proc.pid(),
            modules.len()
        );
        match (&program, rebase) {
            (Some(p), Some(r)) => {
                let _ = writeln!(
                    out,
                    "image {} at live {:#x} = static {:#x} ({:#x} bytes): static addresses and names rebase automatically",
                    p.path
                        .file_name()
                        .map_or_else(String::new, |n| n.to_string_lossy().into_owned()),
                    r.live_base,
                    r.static_base,
                    r.static_end - r.static_base
                );
            }
            (Some(p), None) => {
                let _ = writeln!(
                    out,
                    "the loaded binary {} is not a module of this process: addresses are taken as live and nothing is named",
                    p.path.display()
                );
            }
            (None, _) => {
                out.push_str("no binary loaded: load_binary the process's executable so live memory is named and typed\n");
            }
        }
        out.push_str("modules:\n");
        for m in modules.iter().take(16) {
            let _ = writeln!(out, "  {:#x} {:>10} {}", m.base, m.size, m.name);
        }
        if modules.len() > 16 {
            let _ = writeln!(out, "  ... {} more", modules.len() - 16);
        }
        let tls_block = match (&program, rebase) {
            (Some(p), Some(r)) => p.headers.tls_index.and_then(|index| {
                let tid = proc.threads().ok()?.into_iter().next()?;
                let teb = proc.teb_of(tid).ok()?;
                live::tls_block(&proc, &r, index, teb)
            }),
            _ => None,
        };
        if let Some(b) = tls_block {
            let _ = writeln!(
                out,
                "thread-local storage: the main thread's block is at {b:#x}; a class's singleton there reads as Class::instance"
            );
        }
        out.push_str("next: live_object(address or singleton name), live_instances(class), live_read(address, kind), live_watch(name, address)\n");
        *lock(&self.live) = Some(LiveSession {
            process: proc,
            rebase,
            snapshots: std::collections::BTreeMap::new(),
            tls_block,
        });
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
                "detached from {} (pid {})",
                s.process.name(),
                s.process.pid()
            ),
            None => "no process was attached".to_owned(),
        })
    }

    /// Reads typed values from the process.
    ///
    /// # Arguments
    ///
    /// * `LiveReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind; internal error when no process is
    /// attached, the address does not resolve or is not readable.
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
        let analysis = program.as_ref().and_then(|_| self.ensure_analysis().ok());
        let overlay = self.overlay();
        self.with_live(|s| {
            let va = self.live_addr(s, &address)?;
            let word = word_size(program.as_deref());
            let values = live::read_values(&s.process, va, kind, n, word)?;
            let origin = s
                .rebase
                .and_then(|r| r.to_static(va))
                .map_or_else(String::new, |st| format!(" (= static {st:#x})"));
            let mut out = format!(
                "# {} {kind_text} value(s) at live {va:#x}{origin}{}\n",
                values.len(),
                if values.len() < n {
                    ", fewer than asked: the rest is not readable"
                } else {
                    ""
                }
            );
            for v in &values {
                let note = match (v.target, &program, &analysis, s.rebase) {
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
        self.with_analysis(|p, a, o| {
            self.with_live(|s| {
                let r = s.rebase.ok_or(NOT_A_MODULE)?;
                let va = self.live_addr(s, &address)?;
                let (va, via) = Self::through_singleton(s, &address, va, word_size(Some(p)))?;
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
        Parameters(LiveInstancesParams { class, limit }): Parameters<LiveInstancesParams>,
    ) -> Result<String, ErrorData> {
        let limit = count_param(limit, 64, 4096, "limit")?;
        self.with_analysis(|p, a, _| {
            self.with_live(|s| {
                let r = s.rebase.ok_or(NOT_A_MODULE)?;
                let scan =
                    live::instances(&s.process, &r, a, &class, word_size(Some(p)), limit.n)?;
                let mut out = format!(
                    "# {} instance(s) of {class}{}; {} MiB read over {} regions\n",
                    scan.hits.len(),
                    if scan.truncated { " (stopped at the limit)" } else { "" },
                    scan.bytes >> 20,
                    scan.regions
                );
                for h in &scan.hits {
                    let _ = writeln!(out, "{h:#x}");
                }
                if !scan.hits.is_empty() {
                    out.push_str("next: live_object(address) for the fields; live_watch(name, address), then live_watch(name) for what changes\n");
                }
                Ok(out)
            })
            .map_err(|e| e.message.to_string())
        })
        .map(|text| limit.noted(text))
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
    /// readable, or no watch has the name.
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
        let analysis = program.as_ref().and_then(|_| self.ensure_analysis().ok());
        let overlay = self.overlay();
        let word = word_size(program.as_deref());
        self.with_live(|s| {
            let Some(address) = address else {
                let Watch {
                    snapshot: snap,
                    class,
                } = s
                    .snapshots
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| format!("no watch is named {name}; pass an address to start one"))?;
                let changes = snap.diff(&s.process)?;
                let names = match (&class, &program, &analysis) {
                    (Some(c), Some(p), Some(a)) => {
                        borer_engine::analysis::classes::field_labels(p, a, &overlay, c)
                            .into_iter()
                            .map(|(off, label)| (off, label.to_string()))
                            .collect()
                    }
                    _ => std::collections::BTreeMap::new(),
                };
                let mut out = live::render_changes(&snap, &changes, &names);
                if !changes.is_empty() {
                    let snapshot = Snapshot::take(&s.process, snap.va, snap.bytes.len())?;
                    s.snapshots.insert(name.clone(), Watch { snapshot, class });
                    out.push_str("(the watch now holds these bytes)\n");
                }
                return Ok(out);
            };
            let va = self.live_addr(s, &address)?;
            let class = class.or_else(|| {
                let (r, a) = (s.rebase?, analysis.as_ref()?);
                live::class_at(&s.process, &r, a, va, word)
            });
            let size = match (&class, &program, &analysis) {
                (Some(c), Some(p), Some(a)) => {
                    borer_engine::analysis::classes::class_layout(p, a, &overlay, c).map(|l| {
                        l.fields
                            .iter()
                            .map(|(off, f)| {
                                off + u64::from(f.widths.iter().max().copied().unwrap_or(64) / 8)
                            })
                            .max()
                            .unwrap_or(256)
                    })
                }
                _ => None,
            };
            let len = length.map_or_else(
                || {
                    usize::try_from(size.unwrap_or(256))
                        .unwrap_or(256)
                        .clamp(8, live::READ_MAX)
                },
                |asked| asked.n,
            );
            let snapshot = Snapshot::take(&s.process, va, len)?;
            let out = format!(
                "watch {name}: {} bytes at {va:#x}{}; live_watch(\"{name}\") after the change you want to see",
                snapshot.bytes.len(),
                class.as_ref().map_or_else(String::new, |c| format!(" ({c})"))
            );
            s.snapshots.insert(name.clone(), Watch { snapshot, class });
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
        Ok(format!(
            "reloading borer from {exe}{}; the tool list is announced again once the new server is up",
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
        description = "Printable ASCII/UTF-16LE strings as `off va len enc \"text\"` rows; encoding, min_length (5), filter, paging (200, max 500), count_only.",
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
            let walks;
            let fresh: Vec<strscan::StringHit>;
            let rows: Vec<&strscan::StringHit> = if min >= strwalk::WALK_MIN {
                walks = strwalk::load_or_build(&self.strings, p);
                walks.rows(encoding, min)
            } else {
                fresh = match encoding {
                    StringEncoding::Ascii => strscan::find_strings(&p.bytes, min),
                    StringEncoding::Utf16 => strscan::find_wide_strings(&p.bytes, min),
                    StringEncoding::Both => {
                        let mut all = strscan::find_strings(&p.bytes, min);
                        all.extend(strscan::find_wide_strings(&p.bytes, min));
                        all.sort_by_key(|h| h.off);
                        all
                    }
                };
                fresh.iter().collect()
            };
            let matched: Vec<_> = rows
                .into_iter()
                .filter(|h| filter.accepts(&h.text))
                .collect();
            let total = matched.len();
            if page.count_only {
                return Ok(format!(
                    "# {total} matches (min_len={min}, encoding={encoding})\n"
                ));
            }
            let shown = total.saturating_sub(page.offset).min(page.limit.n);
            let mut out = format!(
                "# showing {shown} of {total} matches (min_len={min}, encoding={encoding}; filter=/offset= to narrow)\n# va len enc text\n"
            );
            for h in matched.into_iter().skip(page.offset).take(page.limit.n) {
                let va = p
                    .offset_to_va(h.off).map_or_else(|| format!("off={:#x}", h.off), |v| format!("{v:#x}"));
                out.push_str(&format!(
                    "{va} {} {} \"{}\"\n",
                    h.len,
                    h.encoding.name(),
                    h.text
                ));
            }
            Ok(out)
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
        description = "Imports/exports/locals/data as `kind addr name` rows under `# module:` lines, demangled; kind (drops the column), filter, paging (50, max 1000), count_only; xrefs(import) lists its call sites.",
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
    /// # Arguments
    ///
    /// * `FunctionsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Discovered functions as `entry size blocks instrs callers callees src name` rows; filter on name or entry hex, sort=size for the largest first, paging (50, max 300), count_only.",
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
        self.with_analysis(|_, a, o| {
            let (_, total, text) =
                render::functions_tsv(a, o, filter.as_deref(), order, page.offset, page.limit.n);
            if page.count_only {
                return Ok(format!("# {total} functions\n"));
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
        self.with_analysis(|p, a, o| {
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
        self.with_analysis(|p, a, o| {
            let va = match self.addr(p, &address) {
                Ok(va) => va,
                Err(unknown) => {
                    let (class, offset) = class_field(p, a, o, &address).ok_or_else(|| {
                        format!(
                            "{unknown}; nor is it Class+offset, a field of a class with methods or a vtable"
                        )
                    })?;
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

    /// Renders a class layout recovered from its methods' field accesses.
    ///
    /// # Arguments
    ///
    /// * `ClassLayoutParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not a class method, or nothing
    /// belongs to the class.
    #[tool(
        description = "Class layout from its methods: field offset, width, reads/writes, methods, vftable; takes a class name or a method address.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn class_layout(
        &self,
        Parameters(ClassLayoutParams { class }): Parameters<ClassLayoutParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| {
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
            Ok(borer_engine::analysis::classes::render_layout(
                &layout, a, o,
            ))
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
        description = "Callgraph from a function as mermaid, callees breadth-first, imports as leaves (max_nodes default 30, max 100).",
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
        self.with_analysis(|p, a, o| {
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
        .map(|text| max.noted(text))
    }

    /// Answers whether one function reaches another through calls.
    ///
    /// # Arguments
    ///
    /// * `ReachesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or either address is not inside a discovered
    /// function.
    #[tool(
        description = "Shortest call chain from one function to another, or that there is none and how far it looked: answers \"does this ever reach the send / this check\" on a whole binary.",
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
        self.with_analysis(|p, a, o| {
            let start = self.function_entry(p, a, &from)?;
            let goal = self.function_entry(p, a, &to)?;
            Ok(render::call_path(a, o, start, goal, deep.n))
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
        description = "Control-flow graph of a function as mermaid: basic blocks (start, terminator) and successor edges; the first 300 blocks.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn cfg(
        &self,
        Parameters(CfgParams { address }): Parameters<CfgParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::cfg_mermaid(a, o, entry).ok_or_else(|| format!("no function at {entry:#x}"))
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
        description = "Pseudo-C with locals local_N/arg_N, named calls and if/else/while/for/switch; /* asm */ marks unmodeled code, goto unproven flow. Line 2 says what the binary checked. detail=skeleton: flow and calls only; filter keeps lines carrying the text; offset/limit page by line (300, 0 for all).",
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
            let a = self.ensure_analysis()?;
            let entry = self.function_entry(p, &a, &address)?;
            let o = self.overlay();
            // PERF: the check first, so the decompilation it memoizes keeps
            // the lifter's witness and the text below reads the same cell.
            let header = decompile::checked_header(p, &a, &o, entry);
            let text = decompile::decompile_named(p, &a, &o, entry)
                .ok_or_else(|| format!("decompilation failed at {entry:#x}"))?;
            let text = match detail.unwrap_or_default() {
                Detail::Full => text,
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
            let folded: usize = skipped.values().map(Vec::len).sum();
            let mut out = format!(
                "# decompiled {} of {} matching functions (max {max}){}
",
                matched.len(),
                total_matching,
                if folded > 0 {
                    format!("; {folded} more are clones of these")
                } else {
                    String::new()
                }
            );
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
            let mut used = 0usize;
            for (entry, text) in texts {
                if used >= TOTAL {
                    out.push_str(
                        "# total output cap reached
",
                    );
                    break;
                }
                let name = borer_engine::analysis::name_of(&a, &o, entry);
                let clones =
                    skipped
                        .get(&entry)
                        .filter(|c| !c.is_empty())
                        .map_or(String::new(), |c| {
                            let shown: Vec<String> = c
                                .iter()
                                .take(6)
                                .map(|e| borer_engine::analysis::name_of(&a, &o, *e))
                                .collect();
                            let more = c.len().saturating_sub(6);
                            if more > 0 {
                                format!(" (same code: {}, +{more} more)", shown.join(", "))
                            } else {
                                format!(" (same code: {})", shown.join(", "))
                            }
                        });
                out.push_str(&format!(
                    "
==== {name} @ {entry:#x} ===={clones}
"
                ));
                if text.len() > PER_FN {
                    out.push_str(&text[..PER_FN]);
                    out.push_str(
                        "
// truncated
",
                    );
                    used += PER_FN;
                } else {
                    out.push_str(&text);
                    used += text.len();
                }
            }
            Ok(out)
        })
        .map(|text| cap.noted(text))
    }
    /// Searches every section, then the bytes no section maps, for a byte
    /// pattern or a text substring.
    ///
    /// # Arguments
    ///
    /// * `SearchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the pattern does not parse, or the kind is unknown.
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
        if query.trim().is_empty() {
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
                SearchKind::Text => borer_engine::search::find_text(p, query.as_bytes(), offset),
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
        self.with_analysis(|p, a, o| {
            let va = self.addr(p, &address)?;
            must_be_in_a_section(p, va, Annotation::Name)?;
            let target = a.function_at(va).map_or(va, |f| f.entry);
            let old = borer_engine::analysis::name_of(a, o, target);
            let what = if a.function(target).is_some() {
                "function"
            } else {
                "data"
            };
            if dry {
                return Ok(format!(
                    "dry-run: would set name of {what} {target:#x} ({old}) to '{name}'. pass dry_run=false to apply."
                ));
            }
            write_lock(&self.overlay)
                .names
                .insert(target, name.clone());
            self.names_changed();
            Ok(format!("renamed {what} {target:#x}: {old} -> {name}"))
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

    /// Defines a user type, applies one at an address, or both.
    ///
    /// `name` with `fields` defines a struct; `name` with `values` defines
    /// an enum; `name` with `type` alone defines a typedef. `address` with
    /// `type` applies the type at that data global: the decompiler types the
    /// variable it renders there, so a `Player *` names every field read
    /// through it (`g->hp` at the width the field states) and a `State`
    /// applied at a global names every constant compared with it. Everything
    /// is validated before anything is written: types the language does not
    /// spell, references to names nothing defines, fields that overlap and a
    /// size that does not cover the last field are refused with a message
    /// naming the offender.
    ///
    /// # Arguments
    ///
    /// * `SetTypeParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, a definition or application is refused, the
    /// address does not resolve, no section holds it, or it is inside a
    /// function.
    #[tool(
        description = "Define a user type and/or apply one at a data global; dry-run unless dry_run=false. A `Player *` applied at a global makes decompile name the fields read through it; an enum applied there names the constants compared with it.",
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
            dry_run,
        }): Parameters<SetTypeParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        if name.is_none() && address.is_none() {
            return Err(err_params(
                "set_type needs `name` (+ `fields`, `values` or `type`) to define a type, or `address` + `type` to apply one",
            ));
        }
        self.with_analysis(|p, a, o| {
            let word: u64 = if p.is_64 { 8 } else { 4 };
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
            // The application half: resolved, in a section and not code.
            let applied = match &address {
                Some(text) => {
                    let spelled = ty.as_deref().ok_or_else(|| {
                        "applying a type needs the `type` to apply".to_owned()
                    })?;
                    let parsed = borer_engine::analysis::utypes::parse_type(spelled)
                        .map_err(|e| e.to_string())?;
                    let va = self.addr(p, text)?;
                    must_be_in_a_section(p, va, Annotation::Type)?;
                    if let Some(f) = a.function_at(va) {
                        return Err(format!(
                            "{va:#x} is inside {}; types apply to data globals",
                            borer_engine::analysis::name_of(a, o, f.entry)
                        ));
                    }
                    Some((va, parsed))
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
            if dry {
                return Ok(format!(
                    "dry-run: would {}. pass dry_run=false to apply.",
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
            drop(overlay);
            self.names_changed();
            Ok(done.join("; "))
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
        let (_, total, table) = borer_engine::analysis::utypes::list_tsv(
            &o.types,
            &o.applied,
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
        description = "Save the annotation overlay (names + comments) to a JSON project file.",
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
            &read_lock(&self.overlay),
        );
        pf.save(&path).map_err(err_internal)?;
        Ok(format!(
            "saved {} names + {} comments + {} types to {path}",
            pf.names.len(),
            pf.comments.len(),
            pf.types.len()
        ))
    }

    /// Loads a JSON project file into the overlay.
    ///
    /// # Arguments
    ///
    /// * `LoadProjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the file does not parse.
    #[tool(
        description = "Load a JSON project file into the annotation overlay (warns when it was saved for another binary).",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn load_project(
        &self,
        Parameters(LoadProjectParams { path }): Parameters<LoadProjectParams>,
    ) -> Result<String, ErrorData> {
        let program = self.require_loaded()?;
        let pf = borer::project::ProjectFile::load(&path).map_err(err_params)?;
        let n = pf.names.len();
        let c = pf.comments.len();
        let t = pf.types.len();
        let note = if pf.program == program.path.display().to_string() {
            String::new()
        } else {
            format!(
                " (note: project was saved for {})",
                borer_engine::text::one_line(&pf.program)
            )
        };
        let loaded = pf.to_overlay().map_err(err_params)?;
        *write_lock(&self.overlay) = loaded;
        self.names_changed();
        Ok(format!("loaded {n} names + {c} comments + {t} types{note}"))
    }

    /// Lists every overlay entry.
    ///
    /// A comment opening with a question mark is a hypothesis, not a
    /// finding. Separating the two is what makes the overlay a ledger an
    /// agent can return to: a conclusion it proved is worth building on,
    /// and one it guessed at is worth checking before it does.
    ///
    /// # Errors
    ///
    /// Never; the signature matches the other tools.
    #[tool(
        description = "List current annotation-overlay entries (names + comments).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    fn annotations(&self) -> Result<String, ErrorData> {
        let o = read_lock(&self.overlay);
        let (open, settled): (Vec<_>, Vec<_>) = o
            .comments
            .iter()
            .partition(|(_, c)| c.trim_start().starts_with('?'));
        let mut out = format!(
            "# {} names, {} findings, {} open question(s)\n# addr annotation\n",
            o.names.len(),
            settled.len(),
            open.len()
        );
        for (va, name) in &o.names {
            let _ = writeln!(out, "{:<12} name: {name}", format!("{va:#x}"));
        }
        for (va, c) in settled {
            let _ = writeln!(out, "{:<12} found: {c}", format!("{va:#x}"));
        }
        for (va, c) in open {
            let claim = c.trim_start().trim_start_matches('?').trim_start();
            let _ = writeln!(out, "{:<12} open:  {claim}", format!("{va:#x}"));
        }
        if !o.comments.is_empty() {
            out.push_str(
                "# a comment opening with ? is an open question; drop the ? once it is proved\n",
            );
        }
        Ok(out)
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
    /// every resource there is; otherwise the resource's own error.
    #[tool(
        description = "Read a borer:// resource as resources/read does (same text, errors and memory), for hosts that cannot read resources, e.g. borer://grep/CreateFileA or borer://scenarios/0x401000/a1=0..8; an unknown URI's error lists them all.",
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
    /// script that ran scripts could recurse without end. A failed script
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
    /// When no binary is loaded or the analysis fails; a failing script is
    /// an answer, not an error.
    #[tool(
        description = "Run a sandboxed Rhai script over the loaded program, for what no single tool answers: what it printed, then the names and comments it proposed (dry-run unless dry_run=false). print(help()) lists every call; query(uri) reads any borer:// resource.",
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
        let analysis = self.ensure_analysis().map_err(err_params)?;
        let server = self.clone();
        let query: borer_engine::script::Query = std::rc::Rc::new(move |uri: &str| {
            if uri.starts_with("borer://script/") {
                return Err(
                    "a script cannot query borer://script/...: scripts do not run scripts"
                        .to_owned(),
                );
            }
            server
                .resource_text(uri)
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
/// * `count_only` - Stop after the header.
/// * `names` - The analysis and the overlay, for the function names.
///
/// # Returns
///
/// The rendered rows.
fn render_hits(
    page: &borer_engine::search::Hits,
    offset: usize,
    count_only: bool,
    names: (&Analysis, &Overlay),
) -> String {
    let (a, o) = names;
    let mut out = format!(
        "# {} hits, showing {} from {offset}\n",
        page.total,
        page.hits.len()
    );
    if count_only {
        return out;
    }
    out.push_str("# function: va ...\n");
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

/// Agent workflows offered as MCP prompts: know-how shipped next to the tools.
#[prompt_router]
impl BorerServer {
    /// Returns the end-to-end triage workflow.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "triage",
        description = "Triage the loaded binary end to end (what it is, what it imports, what it hides, where to read first) in a token-frugal tool order."
    )]
    fn triage(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            "Triage the currently loaded binary with the borer tools, cheapest first, and stop \
             as soon as you can say what it is and where its interesting code lives.\n \
             1. The resource borer://triage answers most of this in one call: format, whether \
             it is packed, anti-analysis tricks, crypto, APIs resolved at runtime, the strings \
             it generates rather than stores, what its imports let it do, and the functions to \
             read first with the evidence for each. Start there.\n \
             2. Only where that leaves a question: borer://protection and entropy(threshold=7.5) \
             for a packer payload, borer://dynimports for APIs behind GetProcAddress, \
             borer://stackstrings and strings(filter=...) for text it stores, \
             find_function_by_string for the most telling of those, and borer://checks for \
             serial and license validators.\n \
             3. function_summary on each candidate from the reading list; decompile only the \
             ones whose summary (callees, strings) makes them worth reading. \
             borer://emulate/<addr> runs a generator or a decoder to read its plaintext, and \
             takes a whole experiment: registers, arguments, patched bytes, a stop address, a \
             step trace.\n \
             4. Report: purpose, capabilities, notable functions with addresses, and the next \
             three functions to read. Apply set_name(dry_run=false) for anything you \
             identified and save_project so the names persist.",
        )]
    }

    /// Returns the workflow that maps a client's protocol and message system.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "protocol",
        description = "Map how a networked client talks and dispatches: wire ids, every command's record, the message classes with their fields and handlers, and the registration tables, in a token-frugal order."
    )]
    fn protocol(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            "Map the loaded client's protocol with the borer resources, tables first, and read \
             code only where a table leaves a question.\n \
             1. borer://vslot/<slot> lists every class whose virtual at that slot returns a \
             constant; a command class answers its wire id that way, so try the low slots \
             (3 is common) and keep the one whose values look like an id space.\n \
             2. borer://protocol/<slot> puts every class on one row with who sends it, the \
             handler that receives it, what it writes and what it reads; the rest of these \
             steps are its columns in full. \
             borer://schemas/<slot> joins those classes with the record each one decodes: \
             kind@offset per field, nested records, repeats, field names where the class or \
             the message it mirrors names them. That table is the wire protocol.\n \
             3. borer://schema/<class> for one command in full, with the reader behind every \
             field; borer://schema/<function> for any deserializer by address. The other \
             direction is borer://encodes/<slot> and borer://encode/<class>: what each \
             command writes onto the wire, in order, with widths and the field each value \
             came from, packed buffers split into their parts; borer://senders/<slot> names \
             the functions constructing each command, which is where the client sends it, \
             and borer://hooks/<slot> gives the addresses to hook: encoder, decoder, handler \
             and each send call site.\n \
             4. borer://messages[/filter] lists every class that registered a four-character \
             id with its named fields, the global its id lives in, and the functions reading \
             that global: the handlers. A sender fills the message, a handler turns it into a \
             command; follow a handler to the command class and back to step 2.\n \
             5. borer://shape/<function> on any registration function lists its whole family \
             with the string and data each one registers: attributes, settings, factories.\n \
             6. borer://grep/<text> finds every pseudo-C line program-wide (a call, a field \
             write, a constant) once the index is built; borer://fieldrefs/<offset> finds \
             every instruction touching one field offset.\n \
             7. Write the facts you rely on as anchors (field, vconst, function lines, and \
             encode or decode lines holding a row of the protocol table) and keep the \
             manifest: borer://anchors/<path> re-derives and judges every one after the \
             next client update, a packet whose layout changed included.\n \
             Any name met on the way: borer://about/<name> answers from every table at once. \
             8. Inside the client a command becomes messages between components (borer://map \
             lays out the subsystems first): \
             borer://ports/<filter> lists which component accepts which message and the \
             function each is dispatched to, and borer://attrs/<filter> lists the entity \
             attributes with their codes, types and the functions using them.",
        )]
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
            format!(
                "Find the code that validates the {what} in the loaded binary.\n\
                 1. find_function_by_string with filters related to it (e.g. \"invalid\", \
                 \"wrong\", \"success\", \"registered\", \"{what}\") and search(kind=text) for \
                 UI text; note every function that references such strings.\n\
                 2. find_crypto_constants: a hash or cipher table near the check tells you how \
                 the value is transformed before comparison.\n\
                 3. function_summary, then decompile, the referencing functions; follow callers \
                 (xrefs) upward until you reach the function that branches on the result.\n\
                 4. In the decompilation, identify the comparison (== / != / memcmp-style loop), \
                 the inputs feeding it, and every transformation on the way; quote the exact \
                 pseudo-C lines with their addresses.\n\
                 5. Explain the algorithm in plain language, state what input would pass, and \
                 propose names for the functions and globals involved; apply them with \
                 set_name(dry_run=false) and set_comment, then save_project."
            ),
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
            format!(
                "Explain the function at {address}.\n\
                 1. function_summary({address}) for its shape, callers, callees and strings.\n\
                 2. decompile({address}); if a callee is unnamed and small, decompile it too so \
                 the call reads meaningfully; use read(kind=cstr/ptr) on globals it touches.\n\
                 3. xrefs to see how callers use it (arguments, return value).\n\
                 4. Write: purpose in one sentence, parameters and return value, side effects, \
                 notable constants or strings, and anything suspicious. Then propose a name for \
                 the function and for each global it uses and apply them with \
                 set_name(dry_run=false); attach a one-line set_comment at the entry."
            ),
        )]
    }
}

#[tool_handler]
#[prompt_handler]
impl ServerHandler for BorerServer {
    /// Returns capabilities (tools, prompts, resources, completions), the
    /// implementation name and version, and the agent-facing instructions.
    fn get_info(&self) -> rmcp::model::ServerInfo {
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
        .with_instructions(
            "borer: agent-native binary analysis (x86/x64 PE/ELF). Workflow: load_binary, then \
             binary_info; find_function_by_string / strings / symbols / find_crypto_constants to \
             locate interesting code; function_summary to triage a function; decompile for \
             pseudo-C; disassemble_function / cfg / callgraph / xrefs to go deeper; read and \
             hexdump for data. Every `address` accepts 0x-hex, decimal, or a name (function, \
             import, overlay name). set_name/set_comment annotate (dry-run by default), \
             set_type defines user structs and applies them at globals so decompile names \
             their fields, and save_project persists the overlay. For anything no single tool \
             answers, script runs a sandboxed Rhai script over the program in one call; its \
             query(uri) reads any resource. Outputs are capped and paged; count_only and \
             filter keep them small. An answer of 512 bytes or more ends with `# since=<tag>`; \
             the same request with \"since\": \"<tag>\" added (on a URI: !since=<tag>) answers \
             with a one-line note if nothing changed, else only the changed lines. \
             Prompts: triage, find_check(what), explain_function(address). \
             Beyond the tools, templated resources (resources/templates/list) read by URI, \
             through resources/read or the query tool: \
             borer://why/{address}, taint/{spec}, layout/{spec}, emulate/{address}, \
             run/{spec}, solve/{spec}, devirt/{address}, unpack/{address}, flat/{address}, vm/{address}, \
             fields/{address}, diff/{path}, difffn/{function}/{path}, carry/{path}, \
             migrate/{function}/{path}, and filtered \
             stackstrings, asserts, sources, classes, singletons, messages and attrs. Live: \
             live_attach(process) \
             opens the running program read-only and maps the binary onto it; then live_object \
             reads an object by its class's fields, live_instances finds a class's objects by \
             vtable, live_read reads typed values, and live_watch(name, address) then \
             live_watch(name) shows what changed; every live address may be a static address \
             or a name. After a rebuild of borer, reload restarts the server in place.",
        )
    }

    /// Runs a tool, then passes its text through the session's answer memory
    /// and the byte budget.
    ///
    /// Any tool takes a `since` argument the schemas leave out (every tool
    /// would pay for it in the tool list): the tag of the answer the reader
    /// holds, taken off here before the tool parses its arguments
    /// ([`recall::Recall`]). A `reload` call schedules the hand-over whatever
    /// it answers: the relay holds the client's lines from that call on
    /// until this worker has ended, so a worker that stayed would hold them
    /// for good. A `query` answer has been through both already, keyed by
    /// its URI as a resource read is ([`BorerServer::read_uri`]), so its tag
    /// goes on the URI.
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
            .map(|v| match v {
                serde_json::Value::String(s) => Tag::parse(&s),
                other => Tag::parse(&other.to_string()),
            })
            .transpose()
            .map_err(err_params)?;
        if let Some(tag) = since
            && request.name == "query"
            && let Some(serde_json::Value::String(uri)) =
                request.arguments.as_mut().and_then(|a| a.get_mut("uri"))
        {
            let _ = write!(uri, "{SINCE_SUFFIX}{tag}");
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
        let call = rmcp::handler::server::tool::ToolCallContext::new(self, request, context);
        let response = Self::tool_router().call(call).await;
        if reloading {
            self.hand_over.schedule(Resume {
                peer_info: peer_info.as_deref().cloned(),
                project: self.loaded().map(|p| {
                    borer::project::ProjectFile::from_overlay(
                        &p.path.display().to_string(),
                        &read_lock(&self.overlay),
                    )
                }),
            });
        }
        let response = response?;
        Ok(match response {
            CallToolResponse::Complete(mut result)
                if remembered && result.is_error != Some(true) =>
            {
                if let [ContentBlock::Text(t)] = result.content.as_mut_slice() {
                    let full = std::mem::take(&mut t.text);
                    let sent = match self.recall.lock() {
                        Ok(mut recall) => recall.answer(&key, since, &again, full),
                        Err(_) => full,
                    };
                    t.text = budgeted(sent);
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
                .map(|&(uri, description)| {
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
    /// Any `address` argument completes to function names; `find_check`'s
    /// `what` completes to the usual validation targets.
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
            (_, "address") => self.complete_names(&prefix),
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
}

impl BorerServer {
    /// Reads a `borer://` resource: the text its handler answers, through
    /// the session's answer memory and the byte budget.
    ///
    /// `resources/read` and the `query` tool both come here, so a URI is
    /// answered alike either way: the same text, the same errors, and one
    /// answer memory keyed by the URI. The argument is percent-decoded: a
    /// client is free to escape the reserved characters an argument uses,
    /// and an experiment spec is full of them. An unknown URI is refused
    /// with every resource there is, which is how an agent whose host lists
    /// no resources finds them.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI as the client sent it; a trailing `!since=<tag>`
    ///   passes back the tag of the answer the reader holds, and a trailing
    ///   `!fresh` asks for the text whole whatever tag comes before it.
    ///
    /// # Returns
    ///
    /// The URI without either suffix, and the text to send.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI; invalid-params for a tag that
    /// is not one; otherwise the handler's error.
    fn read_uri(&self, uri: &str) -> Result<(String, String), ErrorData> {
        let (uri, fresh) = match uri.strip_suffix(FRESH_SUFFIX) {
            Some(core) => (core, true),
            None => (uri, false),
        };
        let (uri, since) = match uri.rsplit_once(SINCE_SUFFIX) {
            Some((core, tag)) => (
                core.to_owned(),
                Some(Tag::parse(tag).map_err(err_params)?).filter(|_| !fresh),
            ),
            None => (uri.to_owned(), None),
        };
        let text = self.resource_text(&uri)?;
        let again = format!("reading {uri} (resources/read or the query tool)");
        let text = match self.recall.lock() {
            Ok(mut recall) => recall.answer(&uri, since, &again, text),
            Err(_) => text,
        };
        Ok((uri, budgeted(text)))
    }

    /// The text of one resource, as its handler answers it: no answer
    /// memory, no byte budget, no `!since` or `!fresh` suffix.
    ///
    /// [`BorerServer::read_uri`] wraps it for `resources/read` and the
    /// `query` tool, and a script's `query(uri)` calls it directly
    /// ([`BorerServer::script`]).
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI, suffixes already taken off.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI, naming every resource there
    /// is; otherwise the handler's error.
    fn resource_text(&self, uri: &str) -> Result<String, ErrorData> {
        let not_found = || {
            err_not_found(format!(
                "unknown resource {}; the resources are {}",
                borer_engine::text::one_line(uri),
                RESOURCES
                    .iter()
                    .chain(RESOURCE_TEMPLATES)
                    .map(|&(known, _)| known)
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        };
        let Some(path) = uri.strip_prefix("borer://") else {
            return Err(not_found());
        };
        let (kind, arg) = match path.split_once('/') {
            Some((k, a)) => (k, Some(percent_decode(a))),
            None => (path, None),
        };
        let text = match (kind, arg) {
            ("info", None) => self.binary_info()?,
            ("annotations", None) => self.annotations()?,
            ("enums", None) => self.enums_text()?,
            ("dynimports", None) => self.dynamic_imports_text()?,
            ("checks", None) => self.checks_text()?,
            ("antianalysis", None) => self.anti_analysis_text()?,
            ("protection", None) => self.protection_text()?,
            ("triage", None) => self.triage_text()?,
            ("fingerprint", None) => self.fingerprint_text()?,
            ("hashes", None) => self.hashes_text()?,
            ("capabilities", None) => self.capabilities_text()?,
            ("qt", None) => self.qt_text()?,
            ("stackstrings", None) => self.stack_strings_text("")?,
            ("stackstrings", Some(filter)) => self.stack_strings_text(&filter)?,
            ("emulate", Some(address)) => self.emulate_text(&address)?,
            ("taint", Some(spec)) => self.taint_text(&spec)?,
            ("layout", Some(spec)) => self.layout_text(&spec)?,
            ("why", Some(target)) => self.why_text(&target)?,
            ("solve", Some(spec)) => self.solve_text(&spec)?,
            ("flat", None) => self.flattening_text("")?,
            ("flat", Some(filter)) => self.flattening_text(&filter)?,
            ("devirt", Some(address)) => self.devirtualize_text(&address)?,
            ("unpack", Some(address)) => self.unpack_text(&address)?,
            ("hidden", None) => self.hidden_text("")?,
            ("hidden", Some(filter)) => self.hidden_text(&filter)?,
            ("oracle", Some(address)) => self.oracle_text(&address)?,
            ("run", Some(spec)) => self.run_text(&spec)?,
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
            ("fieldrefs", Some(spec)) => self.fieldrefs_text(&spec)?,
            ("vslot", Some(spec)) => self.vslot_text(&spec)?,
            ("grep", Some(text)) => self.grep_text(&text)?,
            ("packs", None) => self.packs_text()?,
            ("exportpack", Some(spec)) => self.export_pack_text(&spec)?,
            ("script", Some(path)) => self.script_text(&path)?,
            ("scenario", Some(spec)) => self.scenario_text(&spec)?,
            ("scenarios", Some(spec)) => self.scenarios_text(&spec)?,
            ("index", None) => self.index_text()?,
            ("schema", Some(what)) => self.schema_text(&what)?,
            ("schemas", Some(spec)) => self.schemas_text(&spec)?,
            ("encode", Some(what)) => self.encode_text(&what)?,
            ("encodes", Some(spec)) => self.encodes_text(&spec)?,
            ("senders", Some(spec)) => self.senders_text(&spec)?,
            ("protocol", Some(spec)) => self.protocol_text(&spec)?,
            ("hooks", Some(spec)) => self.hooks_text(&spec)?,
            ("shape", Some(address)) => self.shape_text(&address)?,
            ("messages", None) => self.messages_text("")?,
            ("attrs", None) => self.attrs_text("")?,
            ("map", None) => self.map_text("")?,
            ("about", Some(name)) => self.about_text(&name)?,
            ("changes", Some(path)) => self.changes_text(&path)?,
            ("map", Some(namespace)) => self.map_text(&namespace)?,
            ("ports", None) => self.ports_text("")?,
            ("ports", Some(filter)) => self.ports_text(&filter)?,
            ("attrs", Some(filter)) => self.attrs_text(&filter)?,
            ("messages", Some(filter)) => self.messages_text(&filter)?,
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
            _ => return Err(not_found()),
        };
        Ok(text)
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
        "borer://info",
        "Summary of the loaded program (binary_info)",
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
        "borer://capabilities",
        "What the program can do, grouped from its imports: networking, injection, crypto, persistence, anti-analysis and more",
    ),
    (
        "borer://hidden",
        "Strings the program generates at run time by mixing a keystream, recovered by running the generators",
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
        "borer://fingerprint",
        "The identity of this build's fingerprints: a digest, the counts, and how to write the sidecar a later borer://diff reads. The manifest itself is a file, written by the CLI, because one line per function is megabytes",
    ),
    (
        "borer://hashes",
        "The content hashes a file is correlated by: imphash (Mandiant's dll.function MD5 as pefile and VirusTotal compute it: table order, dll lowercased with .dll/.ocx/.sys stripped, ordinals named as pefile names them), authentihash (SHA-256 with the checksum, security directory and certificate table excluded, so signing does not move it) and tlsh (borer's locality-sensitive hash: same bytes the same hash, near bytes a small distance - correlates within borer, not with Trend Micro tlsh strings)",
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
];

/// The resource templates: URI template and description. Each is listed
/// under the name its first path segment spells ([`resource_name`]).
const RESOURCE_TEMPLATES: &[(&str, &str)] = &[
    (
        "borer://stackstrings/{filter}",
        "Stack strings whose text contains the filter",
    ),
    (
        "borer://flat/{address}",
        "Cases of one flattening dispatcher, in table order, each with where it ends. The table order is not the order they run",
    ),
    (
        "borer://solve/{spec}",
        "Find an argument value that makes a check answer differently: spec is <address>[,aN] (the decompiler's aN, a1 by default). Every constant the function compares against is tried and the answers grouped, so a value standing apart is the one it wants, with the comparison it came from",
    ),
    (
        "borer://why/{address}",
        "What is at an address and how borer knows: where its name came from (the compiler's debug information, a symbol, inferred from code, or nothing), why the function was discovered, what refers to it, and any value recovered by running the code that builds it",
    ),
    (
        "borer://layout/{spec}",
        "Propose a structure from what a function does through one pointer: spec is <address>[,<register>] (default rcx, the first argument). Each row is a field with the width of the access and what it is passed to",
    ),
    (
        "borer://taint/{spec}",
        "Follow a value forward through its function: spec is <address>[,<register>] (default rax, where a call leaves its result). Reports the instructions that carry it, the calls it is passed to and as which argument, the memory it is stored into, and where it still is at the end",
    ),
    (
        "borer://emulate/{address}",
        "Run code and read the result. The address carries an experiment: comma-separated reg=val, aN=val (the argument the decompiler names aN; a1 is the first), w<addr>=<hexbytes> (set data or patch code), stop=<addr>, steps=<n> (at most 20000000), trace=<n> (what each of the first n instructions changed), dump=<addr>:<len> (at most 4096 bytes, ?? where nothing is mapped). Reports final registers, the call trace, decoded text and each dump.",
    ),
    (
        "borer://devirt/{address}",
        "Run a virtualized function and recover the sequence of virtual instructions it executes",
    ),
    (
        "borer://unpack/{address}",
        "Run a packer's bootstrap and report the code it decrypts into memory, with the original entry point. Append ,budget=N to raise the step cap toward a fuller unpack",
    ),
    (
        "borer://hidden/{filter}",
        "Run-time generated strings whose text or generator matches {filter}",
    ),
    (
        "borer://oracle/{address}",
        "Run the function at {address} over a probe string in every argument shape and report what it does with it",
    ),
    (
        "borer://run/{spec}",
        "Call a function on inputs typed by its recovered signature and check its decompiled text on them: <function>[,steps=N]/<input>[;<input>...], each input its arguments in order: 5, -1, \"text\", hex:0102 or out:16 (a zeroed buffer). A row per input: the return value, the stop, the steps, the bytes each buffer holds after, and whether the text run as C agrees, differs (at a line) or is unchecked (at most 64 inputs, 1000000 steps each by default)",
    ),
    (
        "borer://diff/{path}",
        "Compare the loaded binary against another version at {path} and report which functions changed, were added or removed",
    ),
    (
        "borer://difffn/{function}/{path}",
        "Show how one function changed between the loaded binary and another version at {path}, as a diff of the decompilations",
    ),
    (
        "borer://carry/{path}",
        "Carry this project's names to another build of the same program: each name with its new address and how the function was paired, by identical body or by shape. An update moves every address, and the fingerprints do not move",
    ),
    (
        "borer://migrate/{function}/{path}",
        "Migrate the field offsets a function reads from the loaded build to the version at {path}: which offsets are unchanged, removed, added, or moved",
    ),
    (
        "borer://vm/{address}",
        "The handlers of one dispatch loop, each with what it does",
    ),
    (
        "borer://asserts/{filter}",
        "Asserted fields whose name or class contains the filter",
    ),
    (
        "borer://sources/{filter}",
        "Source files whose path contains the filter, with their function counts",
    ),
    (
        "borer://classes/{filter}",
        "Registered classes whose name or code contains the filter",
    ),
    (
        "borer://messages/{filter}",
        "Classes with a registered wire id whose name contains the filter, each with its named fields and the handlers testing for the id (200 a page)",
    ),
    (
        "borer://attrs/{filter}",
        "Registered attributes whose name or code contains the filter (200 a page); one exact match lists every function reading or writing it with the definition global",
    ),
    (
        "borer://exportpack/{spec}",
        "The session's names as a pack that names the same functions in another build by their first bytes: <name>, or <name>,all to add the names borer recovered",
    ),
    (
        "borer://scenario/{spec}",
        "A function decompiled under assumptions, <function>/<a2=5,a3=0>: branches and switches on them fold, only the code that can run is written, and the first line counts the blocks cut",
    ),
    (
        "borer://scenarios/{spec}",
        "A dispatcher exploded, <function>/<a2=0..32> or <function>/<a2=1|5>: a scenario per value, the values that behave alike grouped, each row with its blocks kept, calls and returns",
    ),
    (
        "borer://script/{path}",
        "Runs a Rhai script file against the loaded program in borer's sandbox: what it printed, and the names and comments it proposes (set_name applies one)",
    ),
    (
        "borer://singletons/{filter}",
        "Singletons whose class name contains the filter",
    ),
    (
        "borer://function/{address}",
        "function_summary at an address or name",
    ),
    (
        "borer://decompile/{address}",
        "Pseudo-C of the function at an address or name",
    ),
    (
        "borer://disasm/{address}",
        "Disassembly of the function at an address or name",
    ),
    (
        "borer://fields/{address}",
        "Field offsets the function at an address or name dereferences, by (base, offset)",
    ),
    (
        "borer://fieldrefs/{offset}",
        "Every instruction program-wide that reads, writes or takes the address of \
                     [reg+offset], with its function; `offset[,name-filter]`, 500 rows at most",
    ),
    (
        "borer://vslot/{slot}",
        "Every recovered class whose virtual at a zero-based vtable slot returns a \
                     constant (a wire id, a type tag), by value; `slot[,class-filter]`",
    ),
    (
        "borer://schema/{function}",
        "The record a deserializer reads off its stream (fields, widths, nesting,                      repeats), for a function by address or name, or the reading virtual of a class",
    ),
    (
        "borer://schemas/{slot}",
        "Every class with a constant at a zero-based vtable slot and the record its \
                     reading virtual decodes, one line each: a protocol as a table; `slot[,class-filter]`",
    ),
    (
        "borer://encode/{function}",
        "What a serializer writes onto its stream (fields in wire order, widths, the \
                     object field each came from, helpers followed into the members they write), \
                     for a function by address or name, or the writing virtual of a class",
    ),
    (
        "borer://hooks/{slot}",
        "Every class with a constant at a zero-based vtable slot with the addresses \
                     a binding hooks: its encoder, its decoder, its handler and each call site \
                     the client sends it from; `slot[,class-filter]`",
    ),
    (
        "borer://protocol/{slot}",
        "Every class with a constant at a zero-based vtable slot on one row with \
                     who constructs it, the handler receiving it, what it writes onto the wire \
                     and what it reads back: the whole protocol as one table; `slot[,class-filter]`",
    ),
    (
        "borer://senders/{slot}",
        "Every class with a constant at a zero-based vtable slot and the functions \
                     calling its factory or constructors: who sends each command, as a table; \
                     `slot[,class-filter]`",
    ),
    (
        "borer://encodes/{slot}",
        "Every class with a constant at a zero-based vtable slot and what its writing \
                     virtual puts on the wire, one line each: the outbound protocol as a table; \
                     `slot[,class-filter]`",
    ),
    (
        "borer://shape/{function}",
        "Every function running the same code as the one at an address or name over \
                     other operands, with the strings and data addresses that differ: a \
                     registration family as a table",
    ),
    (
        "borer://anchors/{path}",
        "Every pinned fact in a manifest file (`field <class> <name> <offset>`, \
                     `vconst <slot> <class> <value>`, `function <name> <rva>`, `encode <class> \
                     <layout>`, `decode <class> <layout>` lines) derived again from the loaded \
                     binary and reported held, moved, changed or gone",
    ),
    (
        "borer://changes/{path}",
        "What changed since a snapshot file of an earlier build (written by the CLI's \
                     `borer snapshot <binary> <file>`): commands, packet layouts, attributes, \
                     message routes and ids added, removed or changed, by stable name",
    ),
    (
        "borer://about/{name}",
        "Everything known about one name, from every table at once: the attribute \
                     (with each user reading or writing it), the class (role, parent, instance, \
                     virtuals, the messages it accepts or the components handling it, the wire \
                     for a command), and the function summary; start here with any name",
    ),
    (
        "borer://grep/{text}",
        "Pseudo-C lines program-wide containing the text (percent-encoded), or \
                     matching it when written re:<expression>, with their function, its \
                     signature and the if/else/loop/switch/case lines enclosing them \
                     (numbered ^N); decompiles \
                     everything once into the index on first use; 200 matching lines at most",
    ),
];

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
/// schemars adds to an optional parameter's type (leaving the parameter out
/// is how a client says null), and `additionalProperties: false`, which every
/// parameter struct enforces at the boundary through `deny_unknown_fields`
/// with an error that names the field.
///
/// # Arguments
///
/// * `t` - The tool as generated by rmcp.
fn slim_tool(mut t: Tool) -> Tool {
    let mut schema = (*t.input_schema).clone();
    schema.remove("$schema");
    schema.remove("additionalProperties");
    if let Some(serde_json::Value::Object(props)) = schema.get_mut("properties") {
        for p in props.values_mut() {
            if let serde_json::Value::Object(o) = p {
                o.remove("format");
                o.remove("minimum");
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

    /// Loads the file the worker before this one had loaded, with its names
    /// and comments; a file that no longer loads is said on stderr and the
    /// session goes on without it.
    ///
    /// # Arguments
    ///
    /// * `resume` - The state that worker wrote.
    ///
    /// # Returns
    ///
    /// What the client sent at initialize, for this worker to serve the
    /// session with; `None` when the state does not hold it.
    fn resume(&self, Resume { peer_info, project }: Resume) -> Option<InitializeRequestParams> {
        if let Some(project) = project {
            let overlay = project.to_overlay();
            let reloaded = self.load_binary(Parameters(LoadBinaryParams {
                path: project.program,
                entry_file_offset: None,
                pdb: None,
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
            "// showing {} of {} lines from 0\n",
            super::DECOMPILE_LINES_DEFAULT,
            super::DECOMPILE_LINES_DEFAULT + 1
        );
        assert!(paged.starts_with(&head), "{paged}");
        assert_eq!(paged.lines().count(), super::DECOMPILE_LINES_DEFAULT + 1);
        assert_eq!(super::window(&long, None, None, Some(0)), long);
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
                "// showing 1 of 11 lines from 8{note}\n   ^3  if ((a3 & 0x200) != 0) {{\n   ^8  }} else {{\n    9    rax = 0;\n"
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
        let a = server.analysis().expect("analyzed");
        let plain = server
            .with_program(|p| {
                borer_engine::analysis::decompile::decompile_named(p, &a, &server.overlay(), 0x1000)
                    .ok_or_else(|| "no text".to_owned())
            })
            .expect("text");
        assert!(!plain.contains("checked vs binary"), "{plain}");
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
                .analysis()
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
                dry_run: Some(false),
            }))
            .expect_err("code refused");
        assert!(
            bad.message.contains("types apply to data globals"),
            "{}",
            bad.message
        );
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
                dry_run: Some(false),
            }))
            .expect_err("fields beside values refused");
        assert!(
            bad.message.contains("both fields and values"),
            "{}",
            bad.message
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

    /// `query` answers a URI exactly as `resources/read` does.
    ///
    /// Both go through one answer memory: a URI without a tag is whole with
    /// its tag line every time, however often it was read before (a reader
    /// may no longer hold it); the URI with that tag appended is a note
    /// naming the read that returns the text, whichever way it is read;
    /// `!fresh` after the tag is whole again, and a tag that is not one is
    /// refused. An unknown URI is the same refusal both ways, listing every
    /// resource there is.
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
        assert_eq!(query(uri).expect("reads"), whole, "a repeat is whole");
        let tag = whole
            .lines()
            .last()
            .and_then(|l| l.strip_prefix("# since="))
            .expect("a long answer ends with its tag");
        let tagged = format!("{uri}!since={tag}");
        let note = query(&tagged).expect("reads");
        assert!(
            note.starts_with(&format!("# unchanged since the answer tagged {tag}: ")),
            "{note}"
        );
        assert!(
            note.ends_with("; this note stands in for that text, and reading borer://disasm/0x1000 (resources/read or the query tool) returns it in full\n"),
            "{note}"
        );
        let (read_as, noted) = server.read_uri(&tagged).expect("reads");
        assert_eq!(
            (read_as.as_str(), noted),
            (uri, note),
            "one memory for both ways"
        );
        assert_eq!(query(&format!("{tagged}!fresh")).expect("reads"), whole);
        assert_eq!(query(&format!("{uri}!fresh")).expect("reads"), whole);
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
                .starts_with("unknown resource borer://nope; the resources are borer://info, "),
            "{}",
            refused.message
        );
        assert!(
            refused.message.contains("borer://scenarios/{spec}"),
            "{}",
            refused.message
        );
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
            LiveWatchParams, Parameters, SearchParams, StringsParams, SymbolsParams, XrefsParams,
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
                limit: Some(0),
            })),
            server.live_instances(Parameters(LiveInstancesParams {
                class: "Player".to_owned(),
                limit: Some(0),
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
}
