//! The one door for engine work: background requests, their list and each view's slot,
//! the UI-thread call counter, and the engine calls the app makes.

use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::Poll;

use borer_engine::analysis::decompile::replay::{Grade, TextCheck};
use borer_engine::analysis::decompile::text_check;
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::edit::{self, Edit, Force};
use borer_engine::analysis::find::{Found, Query, everywhere};
use borer_engine::analysis::project::{self, PROJECT_MAX, Project};
use borer_engine::analysis::render::{
    Bytes, Cell as BandCell, Cfg, Children, Dir, FunctionOrder, FunctionRows, Level, LinearPage,
    SymbolRows, Triage, Via, XREF_ROWS_MAX, XrefRows, XrefView, answered_flagged, band,
    call_children, cfg, disasm_view, function_rows, linear, symbol_rows, triage, xref_rows,
    xref_rows_of_import,
};
use borer_engine::analysis::utypes::{
    TypeDetail, TypeKind, TypeRows, TypeSource, type_detail, type_rows,
};
use borer_engine::analysis::{
    Analysis, EnumSource, Overlay, decompile, name_of, no_function_at, resolve_suggesting,
};
use borer_engine::cancel::Cancel;
use borer_engine::hexdump::{HexRows, hex_rows};
use borer_engine::pack::Packs;
use borer_engine::program::{Feature, Program, SymbolKind, read_regular};
use borer_engine::session::{self, Open, Pdb};
use borer_engine::strings::walk::{StringEncoding, StringRows, WALK_MIN, string_rows};
use borer_engine::view::View;
use borer_front::project_file::{self, Existing};
use gpui::{App, Context, Global, SharedString, Task, Window};

use crate::call_tree::Search;
use crate::decompile_item::Form;
use crate::places::Place;

thread_local! {
    /// Marks the foreground UI thread so engine calls there are counted.
    static IS_UI_THREAD: Cell<bool> = const { Cell::new(false) };
}

/// Total engine calls executed on the foreground UI thread; must remain zero.
static UI_ENGINE_CALLS: AtomicU64 = AtomicU64::new(0);

/// Marks the calling thread as the UI thread for [`ui_engine_calls`] accounting.
pub fn mark_ui_thread() {
    IS_UI_THREAD.with(|flag| flag.set(true));
}

/// Returns how many engine calls routed through [`run_engine`] ran on the UI thread.
///
/// A call that bypasses [`run_engine`] is not counted here; the test
/// `only_the_worker_names_engine_compute_calls` keeps every other module of the
/// app from naming the engine's load, analysis, decompile and listing calls, so
/// every call the app makes is routed.
///
/// # Returns
///
/// Count of routed engine calls made on the UI thread since startup; zero when
/// each ran through [`spawn_engine`].
#[must_use]
pub fn ui_engine_calls() -> u64 {
    UI_ENGINE_CALLS.load(Ordering::Relaxed)
}

/// Runs synchronous engine work `f`, counting a violation if called on the UI thread.
///
/// # Arguments
///
/// * `f` - Synchronous engine closure to run.
///
/// # Returns
///
/// Whatever `f` returns.
pub fn run_engine<R>(f: impl FnOnce() -> R) -> R {
    if IS_UI_THREAD.with(Cell::get) {
        UI_ENGINE_CALLS.fetch_add(1, Ordering::Relaxed);
    }
    f()
}

/// A background engine request, whose answer is `None` once its flag was raised.
///
/// Awaiting it gives the answer, or `None` when its flag was raised while the work ran, so
/// a stopped request's answer is never used; dropping it, answered or not, raises the
/// request's own [`Cancel`] and takes it off [`Jobs`].
///
/// Raising the flag asks the engine to stop at its next check; work that reads no flag runs
/// on to its end unlisted, and its answer is dropped.
#[derive(Debug)]
#[must_use = "dropping the request cancels it"]
pub struct EngineTask<R> {
    /// The background run of the work, `None` when the flag was raised before it returned.
    task: Task<Option<R>>,
    /// The flag in force while the work runs.
    cancel: Cancel,
}

impl<R: Unpin + 'static> Future for EngineTask<R> {
    type Output = Option<R>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Option<R>> {
        Pin::new(&mut self.task).poll(cx)
    }
}

impl<R> EngineTask<R> {
    /// Returns the request's flag: raising it drops the answer and asks the engine to stop.
    #[must_use]
    pub fn flag(&self) -> Cancel {
        self.cancel.clone()
    }
}

impl<R> Drop for EngineTask<R> {
    fn drop(&mut self) {
        self.cancel.raise();
    }
}

/// Lists the engine requests running in the app, oldest first.
///
/// Each entry is an id, a label naming the request's subject and its [`Cancel`]; a raised
/// flag marks an answered or dropped request, which readers skip and the next request
/// prunes. It holds no time, and no answer reads it.
#[derive(Debug, Default)]
pub struct Jobs {
    /// Id of the newest request.
    newest: u64,
    /// Every request since the last prune: id, label and flag.
    live: Vec<(u64, SharedString, Cancel)>,
}

impl Global for Jobs {}

impl Jobs {
    /// Returns the requests still running, oldest first.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context holding the list.
    ///
    /// # Returns
    ///
    /// Each running request's id, label and flag; raising the flag drops its answer and asks
    /// the engine to stop at its next check.
    #[must_use]
    pub fn running(cx: &App) -> Vec<(u64, SharedString, Cancel)> {
        cx.try_global::<Self>().map_or_else(Vec::new, |jobs| {
            let live = jobs.live.iter().filter(|(_, _, flag)| !flag.is_raised());
            live.cloned().collect()
        })
    }
}

/// Spawns synchronous engine work onto GPUI's background executor, under a fresh
/// [`Cancel`], and lists it in [`Jobs`] while it runs.
///
/// # Arguments
///
/// * `label` - What the request does to which subject (`Reading notepad.exe`), from data
///   the caller already holds.
/// * `cx` - Application context providing the background thread pool and the list.
/// * `work` - Synchronous engine closure to execute off the UI thread.
///
/// # Returns
///
/// The request; dropping it raises its flag.
pub fn spawn_engine<R: Send + Unpin + 'static>(
    label: impl Into<SharedString>,
    cx: &mut App,
    work: impl FnOnce() -> R + Send + 'static,
) -> EngineTask<R> {
    let cancel = Cancel::new();
    let jobs = cx.default_global::<Jobs>();
    jobs.live.retain(|(_, _, flag)| !flag.is_raised());
    jobs.newest = jobs.newest.saturating_add(1);
    jobs.live.push((jobs.newest, label.into(), cancel.clone()));
    let flag = cancel.clone();
    let task = cx.background_executor().spawn(async move {
        flag.within(|| {
            let answer = run_engine(work);
            (!Cancel::raised()).then_some(answer)
        })
    });
    EngineTask { task, cancel }
}

/// Holds one view's newest engine request.
///
/// A new run raises the flag of the one before and drops it, so its answer is never
/// applied; dropping the view drops the slot, which raises its request's flag. Tickets let
/// tests and the measure harness wait for one request.
///
/// The slot raises the flag itself, at once, because dropping a gpui [`Task`] drops its
/// future only when the executor next polls it, so the [`EngineTask`] inside would raise
/// its flag one turn of the UI thread late.
#[derive(Debug, Default)]
pub struct Job {
    /// Ticket of the newest request or stop.
    issued: u64,
    /// Ticket of the newest request whose answer was applied, or of the newest stop.
    settled: Rc<Cell<u64>>,
    /// The applying of the newest request's answer, and that request's flag.
    running: Option<(Task<()>, Cancel)>,
}

impl Drop for Job {
    fn drop(&mut self) {
        self.halt();
    }
}

impl Job {
    /// Drops the request before and starts `work` under a new ticket.
    ///
    /// # Arguments
    ///
    /// * `label` - What [`Jobs`] lists the request as.
    /// * `cx` - Application context.
    /// * `work` - Synchronous engine closure.
    ///
    /// # Returns
    ///
    /// The ticket, the request and the cell its applying settles.
    fn start<R: Send + Unpin + 'static>(
        &mut self,
        label: impl Into<SharedString>,
        cx: &mut App,
        work: impl FnOnce() -> R + Send + 'static,
    ) -> (u64, EngineTask<R>, Rc<Cell<u64>>) {
        self.halt();
        self.issued = self.issued.saturating_add(1);
        (
            self.issued,
            spawn_engine(label, cx, work),
            self.settled.clone(),
        )
    }

    /// Runs `work` in the background and hands its answer to `done` on the UI thread,
    /// unless a newer run, a stop, the view's drop or a raise of its flag came first; a
    /// raised request settles its ticket without `done`.
    ///
    /// # Arguments
    ///
    /// * `label` - What [`Jobs`] lists the request as.
    /// * `cx` - Context of the view holding the slot.
    /// * `work` - Synchronous engine closure.
    /// * `done` - Applies the answer to the view.
    ///
    /// # Returns
    ///
    /// The request's ticket.
    pub fn run<V: 'static, R: Send + Unpin + 'static>(
        &mut self,
        label: impl Into<SharedString>,
        cx: &mut Context<'_, V>,
        work: impl FnOnce() -> R + Send + 'static,
        done: impl FnOnce(&mut V, R, &mut Context<'_, V>) + 'static,
    ) -> u64 {
        let (ticket, request, settled) = self.start(label, cx, work);
        let flag = request.cancel.clone();
        let task = cx.spawn(async move |view, cx| {
            let answer = request.await;
            if let Some(view) = view.upgrade() {
                view.update(cx, |view, cx| {
                    settled.set(ticket);
                    if let Some(answer) = answer {
                        done(view, answer, cx);
                    }
                });
            }
        });
        self.running = Some((task, flag));
        ticket
    }

    /// Runs `work` in the background and hands its answer to `done` on the UI thread with
    /// the view's window, unless a newer run, a stop, the view's drop, the window's close or
    /// a raise of its flag came first; a raised request settles its ticket without `done`.
    ///
    /// # Arguments
    ///
    /// * `label` - What [`Jobs`] lists the request as.
    /// * `window` - Window the view is in.
    /// * `cx` - Context of the view holding the slot.
    /// * `work` - Synchronous engine closure.
    /// * `done` - Applies the answer to the view.
    ///
    /// # Returns
    ///
    /// The request's ticket.
    pub fn run_in<V: 'static, R: Send + Unpin + 'static>(
        &mut self,
        label: impl Into<SharedString>,
        window: &Window,
        cx: &mut Context<'_, V>,
        work: impl FnOnce() -> R + Send + 'static,
        done: impl FnOnce(&mut V, R, &mut Window, &mut Context<'_, V>) + 'static,
    ) -> u64 {
        let (ticket, request, settled) = self.start(label, cx, work);
        let flag = request.cancel.clone();
        let task = cx.spawn_in(window, async move |view, cx| {
            let answer = request.await;
            let applied = view.update_in(cx, |view, window, cx| {
                settled.set(ticket);
                if let Some(answer) = answer {
                    done(view, answer, window, cx);
                }
            });
            applied.unwrap_or(());
        });
        self.running = Some((task, flag));
        ticket
    }

    /// Raises the newest request's flag and drops it.
    fn halt(&mut self) {
        if let Some((_, flag)) = self.running.take() {
            flag.raise();
        }
    }

    /// Drops the running request, raising its flag, and settles every ticket.
    pub fn stop(&mut self) {
        self.halt();
        self.issued = self.issued.saturating_add(1);
        self.settled.set(self.issued);
    }

    /// Returns whether the newest request's answer is not applied yet.
    #[must_use]
    pub fn is_running(&self) -> bool {
        self.settled.get() < self.issued
    }

    /// Returns the ticket of the newest request or stop.
    #[must_use]
    pub const fn ticket(&self) -> u64 {
        self.issued
    }

    /// Returns whether request `ticket` is applied, stopped or superseded.
    ///
    /// # Arguments
    ///
    /// * `ticket` - A [`Self::ticket`] value.
    #[must_use]
    pub fn settled(&self, ticket: u64) -> bool {
        ticket < self.issued || self.settled.get() >= ticket
    }
}

/// Where a load finds a binary's companions: its PDB and its packs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Sources {
    /// Root of the symbol-server cache searched for the binary's PDB after the places the
    /// binary names; `None` searches only beside the binary and at its recorded path.
    pub symbol_cache: Option<PathBuf>,
    /// Pack files the person listed, which load for every binary, in load order.
    pub packs: Vec<PathBuf>,
    /// Pack directories, in search order, whose packs load for a binary their `[match]`
    /// lines fit.
    pub pack_dirs: Vec<PathBuf>,
}

/// Immutable engine state for one opened binary.
#[derive(Debug)]
pub struct LoadedBinary {
    /// File path opened by the user or command line.
    pub path: PathBuf,
    /// Parsed binary image.
    pub program: Arc<Program>,
    /// Computed whole-program code and cross-reference analysis, run with the binary's packs.
    pub analysis: Arc<Analysis>,
    /// Overlay matching the server's binary-enum configuration.
    pub overlay: Arc<Overlay>,
    /// Unfiltered function table fetched once during load, shared with the
    /// view that shows it rather than copied.
    pub initial_rows: Arc<FunctionRows>,
    /// The engine's notes on the open, in its words: the pack files and directories
    /// skipped, the packs that fit and the PDB applied or skipped.
    pub notes: Vec<String>,
    /// The binary's SHA-256 as a project file records it ([`project::program_identity`]).
    pub identity: String,
    /// [`Overlay::fingerprint`] of [`Self::overlay`].
    pub fingerprint: u64,
}

impl LoadedBinary {
    /// Returns the state with `overlay` in place of this one's, with its rows and its
    /// fingerprint.
    ///
    /// # Arguments
    ///
    /// * `overlay` - The overlay an edit or a project left.
    pub(crate) fn with_overlay(&self, overlay: Overlay) -> Arc<Self> {
        let initial_rows = Arc::new(all_rows(&self.analysis, &overlay));
        Arc::new(Self {
            path: self.path.clone(),
            program: self.program.clone(),
            analysis: self.analysis.clone(),
            fingerprint: overlay.fingerprint(),
            overlay: Arc::new(overlay),
            initial_rows,
            notes: self.notes.clone(),
            identity: self.identity.clone(),
        })
    }
}

/// Returns every function's row, in address order.
///
/// # Arguments
///
/// * `analysis` - The binary's analysis.
/// * `overlay` - The names over it.
fn all_rows(analysis: &Analysis, overlay: &Overlay) -> FunctionRows {
    function_rows(
        analysis,
        overlay,
        None,
        FunctionOrder::Address,
        0,
        usize::MAX,
    )
}

/// Opens `path` as [`session::open`] does for the server and builds the initial function rows.
///
/// Its PDB and packs are looked for where `sources` says, the server's size cap held, and
/// the analysis runs with the packs that fit.
///
/// A listed pack file that does not read is a note, as a pack directory's is.
///
/// Must be called inside [`spawn_engine`] (or [`run_engine`] in `--headless` mode).
///
/// # Arguments
///
/// * `path` - File path of the untrusted binary to inspect.
/// * `sources` - Where its PDB and packs are looked for.
/// * `notes` - The notes on where they are looked for ([`crate::stored::sources`]), which
///   the engine's notes follow.
///
/// # Returns
///
/// Shared [`LoadedBinary`] holding the program, analysis, overlay, unfiltered rows and
/// the notes on the open.
///
/// # Errors
///
/// Returns an error when [`session::open`] refuses or fails to read `path`.
pub fn load_binary_blocking(
    path: PathBuf,
    sources: &Sources,
    mut notes: Vec<String>,
) -> anyhow::Result<Arc<LoadedBinary>> {
    let mut named = Vec::with_capacity(sources.packs.len());
    for file in &sources.packs {
        match session::read_pack(file) {
            Ok(pack) => named.push(pack),
            Err(why) => notes.push(format!("skipped pack {}: {why}", file.display())),
        }
    }
    let how = Open {
        max_file: session::MAX_FILE,
        form: session::Form::Headers(sources.symbol_cache.clone().map_or(Pdb::Beside, Pdb::Cache)),
        named: Arc::new(Packs { packs: named }),
        dirs: sources.pack_dirs.clone(),
    };
    let opened = session::open(&path, &how)?;
    notes.extend(opened.notes);
    if let Some(pdb) = &opened.program.pdb {
        notes.push(format!("pdb {}", pdb.render()));
    }
    let program = Arc::new(opened.program);
    let analysis = Arc::new(Analysis::compute_with(&program, opened.packs));
    let overlay = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let initial_rows = Arc::new(all_rows(&analysis, &overlay));
    Ok(Arc::new(LoadedBinary {
        path,
        identity: project::program_identity(&program),
        program,
        analysis,
        fingerprint: overlay.fingerprint(),
        overlay: Arc::new(overlay),
        initial_rows,
        notes,
    }))
}

/// Plans `edits` over `loaded`'s overlay through the engine's edit path and commits them,
/// as the server's annotating tools do.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The state the edits are made over.
/// * `edits` - The edits, in order.
///
/// # Returns
///
/// The state they leave, and how many overlay entries they wrote.
///
/// # Errors
///
/// Returns the engine's refusal when it refuses an edit or the overlay would pass a cap;
/// nothing was written.
pub fn edit_blocking(
    loaded: &LoadedBinary,
    edits: &[Edit],
) -> anyhow::Result<(Arc<LoadedBinary>, usize)> {
    let (program, analysis) = (&loaded.program, &loaded.analysis);
    let plan = edit::plan(program, analysis, &loaded.overlay, edits, Force::Refuse)?;
    let mut overlay = (*loaded.overlay).clone();
    edit::commit(program, analysis, &mut overlay, &plan)?;
    Ok((loaded.with_overlay(overlay), plan.changes().len()))
}

/// Reads and parses the project file at `path` ([`Project::from_json`]).
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `path` - The project file.
///
/// # Errors
///
/// Returns an error when the path is refused, the file is past [`PROJECT_MAX`] bytes or
/// does not read, or it is not a project file.
pub fn read_project_blocking(path: &Path) -> anyhow::Result<Project> {
    let bytes = read_regular(path, PROJECT_MAX)?;
    Project::from_json(&bytes).map_err(|why| anyhow::anyhow!("parse {}: {why}", path.display()))
}

/// Puts `file`'s annotations in place of `loaded`'s overlay as the engine admits them
/// ([`project::admit`]), through the edit path.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The state the project replaces the annotations of.
/// * `file` - The project, as read ([`read_project_blocking`]).
/// * `force` - Whether a project saved for another binary is admitted.
///
/// # Returns
///
/// The state it leaves, and what the engine said of what it loaded and skipped.
///
/// # Errors
///
/// Returns the engine's refusal: a [`project::Foreign`] when the file was saved for another
/// binary and `force` is not set.
pub fn open_project_blocking(
    loaded: &LoadedBinary,
    file: &Project,
    force: bool,
) -> anyhow::Result<(Arc<LoadedBinary>, String)> {
    let (program, analysis) = (&loaded.program, &loaded.analysis);
    let admitted = project::admit(
        program,
        || Ok(analysis.clone()),
        &loaded.overlay,
        file,
        force,
    )?;
    let (plan, _, said) = admitted.into_parts();
    let mut overlay = (*loaded.overlay).clone();
    edit::commit(program, analysis, &mut overlay, &plan)?;
    Ok((loaded.with_overlay(overlay), said))
}

/// Writes `loaded`'s annotations to a project file at `path` as the engine spells one,
/// keyed by the binary's SHA-256, replacing a regular file there whole
/// ([`borer_front::project_file::write`]).
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The state whose overlay is saved.
/// * `path` - The project file.
///
/// # Errors
///
/// Returns an error when the path names a share or a device, a link or another non-file is
/// there, the engine refuses to spell the file (it would pass a project's caps), or the
/// write fails; nothing at `path` changed.
pub fn save_project_blocking(loaded: &LoadedBinary, path: &Path) -> anyhow::Result<()> {
    let program = loaded.program.path.display().to_string();
    let file = Project::from_overlay(&program, Some(loaded.identity.clone()), &loaded.overlay);
    project_file::write(path, &file, Existing::Replace).map_err(anyhow::Error::msg)
}

/// Computes filtered [`FunctionRows`] for `loaded` matching `filter`.
/// Computes the first `limit` [`FunctionRows`] of `loaded` matching `filter`.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `filter` - Substring or `0x`-hex query; empty selects every non-thunk function.
/// * `limit` - Most rows.
///
/// # Returns
///
/// Matching [`FunctionRows`] in ascending entry-address order.
#[must_use]
pub fn filter_rows_blocking(loaded: &LoadedBinary, filter: &str, limit: usize) -> FunctionRows {
    let query = (!filter.is_empty()).then_some(filter);
    function_rows(
        &loaded.analysis,
        &loaded.overlay,
        query,
        FunctionOrder::Address,
        0,
        limit,
    )
}

/// What the engine's check of one function's answer found, counted as the answer's header
/// line counts it ([`TextCheck::header`]).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GradeCounts {
    /// Blocks whose every claim the check proved against the lift.
    pub proved: usize,
    /// Blocks compared but not proved, those with a disagreement among them.
    pub tested: usize,
    /// Blocks not compared.
    pub unknown: usize,
    /// Instructions whose statements the machine does not bear out.
    pub disagree: usize,
}

impl GradeCounts {
    /// Returns the counts of `check`, as its header line gives them.
    ///
    /// # Arguments
    ///
    /// * `check` - The engine's check of one answer.
    #[must_use]
    pub fn of(check: &TextCheck) -> Self {
        let blocks = check.blocks.len();
        let unknown = check.count(Grade::Unchecked);
        let proved = check.count(Grade::Proved);
        Self {
            proved,
            tested: blocks.saturating_sub(unknown).saturating_sub(proved),
            unknown,
            disagree: check.disagree.len(),
        }
    }

    /// Returns the count shown under `grade`.
    ///
    /// # Arguments
    ///
    /// * `grade` - The engine's grade.
    #[must_use]
    pub const fn count(&self, grade: Grade) -> usize {
        match grade {
            Grade::Proved => self.proved,
            Grade::Tested => self.tested,
            Grade::Unchecked => self.unknown,
            Grade::Wrong => self.disagree,
        }
    }
}

/// Returns what the engine's check found of the answer the function at `entry` is drawn as.
///
/// That is the check under the names [`answered_flagged`] gives, the ones the answer is
/// drawn under, so the counts are those of the answer's own header line.
///
/// Must be called inside [`spawn_engine`]; the check and the repair search are memoized by
/// the engine, so a second call for the same function and names is a lookup.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Returns
///
/// The counts, or `None` when the function does not decompile or the image has no
/// emulator to check against.
#[must_use]
pub fn grade_counts_blocking(loaded: &LoadedBinary, entry: u64) -> Option<GradeCounts> {
    (*check_blocking(loaded, entry))
        .as_ref()
        .map(GradeCounts::of)
}

/// Builds the decompile view of the function at `entry` in `loaded`.
///
/// Must be called inside [`spawn_engine`] (or [`run_engine`] in `--headless` mode).
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Returns
///
/// The tokenized view, or `None` when no function starts at `entry`.
#[must_use]
pub fn decompile_blocking(loaded: &LoadedBinary, entry: u64) -> Option<Arc<View>> {
    view(&loaded.program, &loaded.analysis, &loaded.overlay, entry)
}

/// Lists one level of the call tree under or over `node` of `loaded`, and says whether
/// the engine looked for the node's virtual calls.
///
/// The engine lists no virtual call of a function that does not decompile, so a level
/// asking for them that lists none asks the decompiler whether the function decompiles;
/// that decompilation is the one finding them made, memoized.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `node` - A function entry or import slot of the tree.
/// * `level` - Whether the level lists what the node calls, with or without its resolved
///   virtual calls, or what calls it.
///
/// # Returns
///
/// The engine's edges of the level and how many there are, and whether its virtual calls
/// were looked for.
#[must_use]
pub fn call_level_blocking(loaded: &LoadedBinary, node: u64, level: Level) -> (Children, Search) {
    let (p, a, o) = (&loaded.program, &loaded.analysis, &loaded.overlay);
    let children = call_children(p, a, o, node, level);
    let search = match level {
        Level::Callees | Level::Callers => Search::NotAsked,
        Level::CalleesAndVirtuals => {
            let found = children
                .rows
                .iter()
                .any(|e| matches!(e.via, Via::Virtual { .. }));
            if found || decompile::decompile(p, a, o, node).is_some() {
                Search::Searched
            } else {
                Search::Failed
            }
        }
    };
    (children, search)
}

/// Returns the name listings give the function at `entry` of `loaded`.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
#[must_use]
pub fn function_name_blocking(loaded: &LoadedBinary, entry: u64) -> String {
    name_of(&loaded.analysis, &loaded.overlay, entry)
}

/// Most instructions a listing shows; a cut listing ends with the engine's
/// `# instruction cap` line.
pub const LISTING_MAX: usize = 65_536;

/// Returns what a tab says when no function starts at `entry`.
///
/// # Arguments
///
/// * `entry` - The address asked for.
#[must_use]
pub fn no_function(entry: u64) -> String {
    format!("No function starts at {entry:#x}.")
}

/// Builds the decompile view of the function at `entry` in `loaded`, or says why none.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Errors
///
/// Returns that no function starts at `entry`, or that the engine built no decompile view
/// of it.
pub fn decompile_or_why(loaded: &LoadedBinary, entry: u64) -> Result<Arc<View>, String> {
    decompile_blocking(loaded, entry).ok_or_else(|| match loaded.analysis.function(entry) {
        None => no_function(entry),
        Some(_) => format!("The engine built no decompile view of the function at {entry:#x}."),
    })
}

/// Builds the listing view of the function at `entry` in `loaded`, raw bytes shown, or
/// says why none.
///
/// Must be called inside [`spawn_engine`] (or [`run_engine`] in `--headless` mode).
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Errors
///
/// Returns the engine's words when the architecture has no disassembler, else that no
/// function starts at `entry`, else that the listing outgrew what a view holds.
pub fn listing_blocking(loaded: &LoadedBinary, entry: u64) -> Result<Arc<View>, String> {
    let (p, a) = (&*loaded.program, &*loaded.analysis);
    let built = disasm_view(p, a, &loaded.overlay, entry, LISTING_MAX, Bytes::Shown);
    built
        .map(Arc::new)
        .ok_or_else(|| match (p.isa_for(Feature::Disasm), a.function(entry)) {
            (Err(why), _) => why,
            (Ok(_), None) => no_function(entry),
            (Ok(_), Some(_)) => {
                format!("The listing at {entry:#x} outgrew the 4 GiB a view holds.")
            }
        })
}

/// Lists the first `limit` types of `loaded` whose name holds `filter`.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `filter` - Case-insensitive substring of a name; empty selects every type.
/// * `limit` - Most rows.
#[must_use]
pub fn type_rows_blocking(loaded: &LoadedBinary, filter: &str, limit: usize) -> TypeRows {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    let query = (!filter.is_empty()).then_some(filter);
    type_rows(p, a, o, query, 0, limit)
}

/// Opens the type of `loaded` named `name` from `source` of kind `kind`.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `name` - The type's name, as its row spells it.
/// * `source` - Where the type comes from.
/// * `kind` - What the type is.
///
/// # Returns
///
/// Its fields, holes and overlaps; `None` when no such type is listed or it is a
/// recovered class.
#[must_use]
pub fn type_detail_blocking(
    loaded: &LoadedBinary,
    name: &str,
    source: TypeSource,
    kind: TypeKind,
) -> Option<TypeDetail> {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    type_detail(p, a, o, name, source, kind)
}

/// Most function rows a go-to query lists.
pub const GOTO_ROWS: usize = 200;

/// What a go-to query finds: the function its text names, and the functions it filters.
#[derive(Debug)]
pub struct GoToAnswer {
    /// The entry of the function holding the address the text resolves to, and that
    /// address, else the engine's words for the miss (nearest names, or what holds no
    /// function).
    pub target: Result<(u64, u64), String>,
    /// The function rows the text filters, at most [`GOTO_ROWS`].
    pub rows: FunctionRows,
}

/// Resolves `query` as an address or a name, and filters the function rows by it.
/// Builds the control-flow graph of the function at `entry` in `loaded`, laid out once
/// with it, or says why none.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Errors
///
/// Returns the engine's words when it builds no graph there.
pub fn graph_blocking(loaded: &LoadedBinary, entry: u64) -> Result<Arc<Cfg>, String> {
    cfg(&loaded.program, &loaded.analysis, &loaded.overlay, entry).map_err(|e| format!("{e:#}"))
}

/// Checks the decompiled text of the function at `entry` in `loaded` against the machine,
/// block by block, under the names [`answered_flagged`] gives, the ones the answer is drawn
/// under.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `entry` - Entry virtual address of the function.
///
/// # Returns
///
/// The check, `None` inside when the function does not decompile or the image has no
/// emulator.
#[must_use]
pub fn check_blocking(loaded: &LoadedBinary, entry: u64) -> Arc<Option<TextCheck>> {
    let (program, analysis) = (&loaded.program, &loaded.analysis);
    let (answered, _) = answered_flagged(program, analysis, &loaded.overlay, entry);
    text_check(program, analysis, &answered, entry)
}

/// Builds one page of the linear listing of `loaded`, or says why none.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `at` - Address the page runs from; one outside the image moves to its nearer end.
/// * `dir` - Which way the page runs from `at`.
/// * `rows` - Rows the page holds.
///
/// # Errors
///
/// Returns the engine's words when the architecture has no disassembler, else that the
/// image maps no section.
pub fn linear_page(
    loaded: &LoadedBinary,
    at: u64,
    dir: Dir,
    rows: usize,
) -> Result<LinearPage, String> {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    linear(p, a, o, at, dir, rows).ok_or_else(|| match p.isa_for(Feature::Disasm) {
        Err(why) => why,
        Ok(_) => "The image maps no section.".to_owned(),
    })
}

/// Returns the overview band of `loaded` in `cells` equal address buckets.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `cells` - Buckets wanted; the engine holds them between 1 and its cap.
#[must_use]
pub fn band_cells(loaded: &LoadedBinary, cells: usize) -> Vec<BandCell> {
    band(&loaded.program, &loaded.analysis, &loaded.overlay, cells)
}

/// Returns the engine's triage of `loaded`: what the file is, how it is protected, what it
/// can do and the functions to read first.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
#[must_use]
pub fn triage_blocking(loaded: &LoadedBinary) -> Arc<Triage> {
    triage(&loaded.program, &loaded.analysis, &loaded.overlay)
}

/// Returns what an address opens: the decompile of the function starting there, else the
/// listing of the function holding it, at its instruction.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `va` - The address.
///
/// # Returns
///
/// The place, or `None` when no function holds `va`.
#[must_use]
pub fn place_at(loaded: &LoadedBinary, va: u64) -> Option<Place> {
    let entry = loaded.analysis.function_at(va)?.entry;
    Some(if entry == va {
        Place::decompile(va)
    } else {
        Place::Code {
            entry,
            form: Form::Listing,
            at: Some(va),
        }
    })
}

/// Most hits a find lists.
pub const FIND_HITS: usize = 200;

/// What a find query found: the engine's ranked hits, where each one's function starts,
/// and the engine's words when nothing matched.
#[derive(Debug)]
pub struct FindAnswer {
    /// The hits, best first, at most [`FIND_HITS`], with every kind's true count.
    pub found: Found,
    /// The entry of the function holding each hit's address, in the order of the hits;
    /// `None` for a hit with no address or one in no function.
    pub entries: Vec<Option<u64>>,
    /// The query's needle, lowered as the engine matched it.
    pub needle: String,
    /// The engine's words for a text nothing matched (nearest names, or what holds no
    /// function); `None` when something matched or the text is empty.
    pub miss: Option<String>,
}

/// Finds `query` in every name table the engine holds, ranked into one list.
///
/// Must be called inside [`spawn_engine`]. It runs under a flag of its own that nothing
/// raises: the name index and the string walk it builds are kept for the next query only
/// when no raised flag cut them short, and a query typed over would otherwise throw each
/// build away.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `query` - What the person typed: an address form, a name, or a kind prefix (`@`
///   functions, `"` strings, `t:` types, `#` names and comments) and a needle.
#[must_use]
pub fn find_blocking(loaded: &LoadedBinary, query: &str) -> FindAnswer {
    Cancel::new().within(|| find_answer(loaded, query))
}

/// Answers a find query, as [`find_blocking`] does, under whatever flag is in force.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `query` - What the person typed.
fn find_answer(loaded: &LoadedBinary, query: &str) -> FindAnswer {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    let q = Query::parse(query);
    let found = everywhere(p, a, o, &q, FIND_HITS);
    let entries = found
        .hits
        .iter()
        .map(|hit| hit.addr.and_then(|va| a.function_at(va)).map(|f| f.entry))
        .collect();
    let miss = (found.hits.is_empty() && !query.is_empty())
        .then(|| match resolve_suggesting(p, a, o, query) {
            Err(words) => Some(words),
            Ok(va) => a
                .function_at(va)
                .is_none()
                .then(|| no_function_at(p, a, va)),
        })
        .flatten();
    let needle = q.needle.as_str().to_owned();
    FindAnswer {
        found,
        entries,
        needle,
        miss,
    }
}

/// Returns the first `limit` strings of `loaded` that `filter` keeps, both encodings, at the
/// engine's walked minimum length, as the `strings` tool reads them by default.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `filter` - Case-insensitive substring of the whole text; empty keeps every string.
/// * `limit` - Most rows.
#[must_use]
pub fn strings_blocking(loaded: &LoadedBinary, filter: &str, limit: usize) -> StringRows {
    let (p, a) = (&*loaded.program, &*loaded.analysis);
    let filter = (!filter.is_empty()).then_some(filter);
    string_rows(p, a, StringEncoding::Both, WALK_MIN, filter, 0, limit)
}

/// Returns the first `limit` symbols of `kind` in `loaded` that `filter` keeps.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `kind` - The one kind of symbol listed.
/// * `filter` - Case-insensitive substring of the name; empty keeps every symbol.
/// * `limit` - Most rows.
#[must_use]
pub fn symbols_blocking(
    loaded: &LoadedBinary,
    kind: SymbolKind,
    filter: &str,
    limit: usize,
) -> SymbolRows {
    let filter = (!filter.is_empty()).then_some(filter);
    symbol_rows(
        &loaded.program,
        &loaded.analysis,
        Some(kind),
        filter,
        0,
        limit,
    )
}

/// What a cross-reference listing lists the references to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Referent {
    /// One address.
    Address(u64),
    /// An import, by one of its slots: every slot of it and every stub jumping through one.
    Import(u64),
}

impl Referent {
    /// Returns the address the referent is named by: the address, or the import's slot.
    #[must_use]
    pub const fn va(self) -> u64 {
        match self {
            Self::Address(va) | Self::Import(va) => va,
        }
    }
}

/// Returns the first `limit` groups of the references to `referent` in `loaded`, read a
/// page of [`XREF_ROWS_MAX`] groups at a time; an import no symbol has a slot at is read
/// as its one address.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `referent` - What the references are to.
/// * `limit` - Most groups.
#[must_use]
pub fn xrefs_blocking(loaded: &LoadedBinary, referent: Referent, limit: usize) -> XrefRows {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    let page = |offset| {
        let view = XrefView::Page {
            offset,
            limit: XREF_ROWS_MAX,
        };
        match referent {
            Referent::Import(va) => xref_rows_of_import(p, a, o, va, view)
                .unwrap_or_else(|| xref_rows(p, a, o, va, view)),
            Referent::Address(va) => xref_rows(p, a, o, va, view),
        }
    };
    let mut rows = page(0);
    while rows.rows.len() < limit.min(rows.groups) && !Cancel::raised() {
        let next = page(rows.rows.len());
        if next.rows.is_empty() {
            break;
        }
        rows.rows.extend(next.rows);
    }
    rows.rows.truncate(limit);
    rows
}

/// Returns the runs backing `len` addresses of `loaded` from `va`, as the `hexdump` tool
/// reads them.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `va` - Address of the first byte.
/// * `len` - Bytes asked for, at most [`borer_engine::hexdump::HEXDUMP_MAX`].
#[must_use]
pub fn hex_blocking(loaded: &LoadedBinary, va: u64, len: usize) -> HexRows {
    hex_rows(&loaded.program, va, len)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::path::{Path, PathBuf};

    use borer_engine::cancel::Cancel;
    use gpui::{AppContext as _, Entity, SharedString, TestAppContext};

    use super::{Job, Jobs, Sources, find_blocking, load_binary_blocking, spawn_engine};

    /// A view with one request slot, keeping the answers applied to it.
    #[derive(Default)]
    struct Probe {
        /// The slot.
        job: Job,
        /// Answers applied, oldest first: the request's label and whether its flag was
        /// raised while its work ran.
        answers: Vec<(&'static str, bool)>,
    }

    /// Runs a request labelled `label` in `probe`'s slot.
    fn ask(probe: &Entity<Probe>, label: &'static str, cx: &mut TestAppContext) {
        probe.update(cx, |probe, cx| {
            let work = move || (label, Cancel::raised());
            probe.job.run(label, cx, work, |probe, answer, _| {
                probe.answers.push(answer);
            });
        });
    }

    /// Returns the label and flag of every running request.
    fn running(cx: &mut TestAppContext) -> Vec<(SharedString, Cancel)> {
        let jobs = cx.read(Jobs::running);
        jobs.into_iter()
            .map(|(_, label, flag)| (label, flag))
            .collect()
    }

    /// A second request in one slot raises the first's flag at once and only the second's
    /// answer is applied, from work that ran under a flag not raised.
    ///
    /// # Panics
    ///
    /// Panics if the first flag stays low, its answer is applied, or the tickets disagree.
    #[gpui::test]
    fn a_new_request_raises_the_cancel_of_the_one_before_and_drops_its_answer(
        cx: &mut TestAppContext,
    ) {
        let probe = cx.new(|_| Probe::default());
        ask(&probe, "first", cx);
        let first = running(cx);
        assert_eq!(first.len(), 1);
        ask(&probe, "second", cx);
        assert!(first[0].1.is_raised());
        let job = |cx: &mut TestAppContext| {
            probe.read_with(cx, |p, _| {
                (p.job.ticket(), p.job.settled(1), p.job.settled(2))
            })
        };
        assert_eq!(job(cx), (2, true, false));
        cx.run_until_parked();
        assert_eq!(job(cx), (2, true, true));
        let answers = probe.read_with(cx, |probe, _| probe.answers.clone());
        assert_eq!(answers, [("second", false)]);
    }

    /// A request whose flag is raised while it runs settles its ticket and is never applied.
    ///
    /// # Panics
    ///
    /// Panics if the answer is applied or the ticket stays open.
    #[gpui::test]
    fn a_raised_request_settles_without_its_answer(cx: &mut TestAppContext) {
        let probe = cx.new(|_| Probe::default());
        ask(&probe, "raised", cx);
        running(cx).remove(0).1.raise();
        cx.run_until_parked();
        let (answers, settled) = probe.read_with(cx, |p, _| (p.answers.clone(), p.job.settled(1)));
        assert!(answers.is_empty());
        assert!(settled);
    }

    /// Dropping a request before it is answered raises its flag at once.
    ///
    /// # Panics
    ///
    /// Panics if the flag stays low.
    #[gpui::test]
    fn dropping_an_engine_task_raises_its_flag(cx: &mut TestAppContext) {
        let request = cx.update(|cx| spawn_engine("dropped", cx, || ()));
        let flag = running(cx).remove(0).1;
        drop(request);
        assert!(flag.is_raised());
    }

    /// A find runs under a flag of its own, so a raised request flag keeps the name index
    /// its miss builds for the next query.
    ///
    /// # Panics
    ///
    /// Panics if the index is not kept.
    #[test]
    fn a_find_keeps_its_name_index_under_a_raised_flag() {
        let loaded = crate::app_view::tests::sample();
        let raised = Cancel::new();
        raised.raise();
        raised.within(|| find_blocking(&loaded, "zzqx"));
        assert_eq!(loaded.analysis.derived.held("name_index"), 1);
    }

    /// Dropping the view holding a slot raises its request's flag, and the list keeps no
    /// running entry.
    ///
    /// # Panics
    ///
    /// Panics if the flag stays low or the list still names the request.
    #[gpui::test]
    fn dropping_a_view_stops_its_job(cx: &mut TestAppContext) {
        let probe = cx.new(|_| Probe::default());
        ask(&probe, "dropped", cx);
        let flag = running(cx).remove(0).1;
        drop(probe);
        cx.update(|_| ());
        assert!(flag.is_raised());
        cx.run_until_parked();
        assert!(running(cx).is_empty());
    }

    /// The list names each running request by its label, oldest first, and forgets each
    /// once it is answered.
    ///
    /// # Panics
    ///
    /// Panics if the labels differ or an answered request stays listed.
    #[gpui::test]
    fn the_jobs_list_names_each_running_request_and_forgets_it(cx: &mut TestAppContext) {
        let (one, two) = (cx.new(|_| Probe::default()), cx.new(|_| Probe::default()));
        ask(&one, "Reading a.exe", cx);
        ask(&two, "Filtering functions", cx);
        let labels: Vec<_> = running(cx).into_iter().map(|(label, _)| label).collect();
        assert_eq!(labels, ["Reading a.exe", "Filtering functions"]);
        cx.run_until_parked();
        assert!(running(cx).is_empty());
    }

    /// Returns every module of the crate but this one, by path under `src`, with its text.
    fn sources() -> [(&'static str, &'static str); 50] {
        [
            ("actions.rs", include_str!("actions.rs")),
            ("app_assets.rs", include_str!("app_assets.rs")),
            ("app_dirs.rs", include_str!("app_dirs.rs")),
            ("app_settings.rs", include_str!("app_settings.rs")),
            ("app_view.rs", include_str!("app_view.rs")),
            ("binary.rs", include_str!("binary.rs")),
            ("call_tree.rs", include_str!("call_tree.rs")),
            ("call_tree_panel.rs", include_str!("call_tree_panel.rs")),
            ("card.rs", include_str!("card.rs")),
            ("code_semantics.rs", include_str!("code_semantics.rs")),
            ("code_view.rs", include_str!("code_view.rs")),
            ("commands.rs", include_str!("commands.rs")),
            ("commands/tests.rs", include_str!("commands/tests.rs")),
            ("conformance.rs", include_str!("conformance.rs")),
            ("decompile_item.rs", include_str!("decompile_item.rs")),
            ("features.rs", include_str!("features.rs")),
            ("function_columns.rs", include_str!("function_columns.rs")),
            ("functions_panel.rs", include_str!("functions_panel.rs")),
            ("goto.rs", include_str!("goto.rs")),
            ("graph_item.rs", include_str!("graph_item.rs")),
            ("hex_item.rs", include_str!("hex_item.rs")),
            ("lib.rs", include_str!("lib.rs")),
            ("linear_item.rs", include_str!("linear_item.rs")),
            ("main.rs", include_str!("main.rs")),
            ("measure.rs", include_str!("measure.rs")),
            ("measure/drop.rs", include_str!("measure/drop.rs")),
            ("measure/input.rs", include_str!("measure/input.rs")),
            ("measure/scroll.rs", include_str!("measure/scroll.rs")),
            ("measure/tree.rs", include_str!("measure/tree.rs")),
            ("menus.rs", include_str!("menus.rs")),
            ("overview.rs", include_str!("overview.rs")),
            ("panels.rs", include_str!("panels.rs")),
            ("places.rs", include_str!("places.rs")),
            ("rail.rs", include_str!("rail.rs")),
            ("recent.rs", include_str!("recent.rs")),
            ("rows_panel.rs", include_str!("rows_panel.rs")),
            ("shell.rs", include_str!("shell.rs")),
            ("start_item.rs", include_str!("start_item.rs")),
            ("status.rs", include_str!("status.rs")),
            ("stored.rs", include_str!("stored.rs")),
            ("table.rs", include_str!("table.rs")),
            ("theme_contract.rs", include_str!("theme_contract.rs")),
            ("theme_import.rs", include_str!("theme_import.rs")),
            ("theme_picker.rs", include_str!("theme_picker.rs")),
            ("title_bar.rs", include_str!("title_bar.rs")),
            ("tables.rs", include_str!("tables.rs")),
            ("types.rs", include_str!("types.rs")),
            ("xrefs.rs", include_str!("xrefs.rs")),
            ("user_themes.rs", include_str!("user_themes.rs")),
            ("zed_import.rs", include_str!("zed_import.rs")),
        ]
    }

    /// Returns the code of a module the scan reads: its text before its tests module.
    fn kept(text: &str) -> &str {
        text.find("mod tests {").map_or(text, |at| &text[..at])
    }

    /// The scan reads a module up to its tests, past any test-only import above them.
    #[test]
    fn the_scan_keeps_code_before_the_tests_module() {
        assert!(kept(include_str!("functions_panel.rs")).contains("fn fetch"));
        assert!(!kept(include_str!("functions_panel.rs")).contains("fn panel_of"));
    }

    /// Nothing outside the tests reaches the window's binary through a view or the status
    /// line: every view is handed it.
    #[test]
    fn no_view_reaches_the_binary_through_another_view() {
        for (name, text) in sources() {
            let code = kept(text);
            assert!(!code.contains("binary_of("), "{name} looks the binary up");
            assert!(
                !code.contains(".binary()"),
                "{name} reaches the binary through a view"
            );
        }
    }

    /// Entry of [`tiny_pe`]'s helper function, which its entry calls.
    pub(crate) const HELPER: u64 = 0x1_4000_1010;

    /// The first bytes of [`tiny_pe`]'s helper as a pack's `[names]` signature.
    const HELPER_SIG: &str = "b844332211058877665531c9c3";

    /// Returns a fresh directory of the tests named for `what`, emptied if a run left it.
    ///
    /// # Panics
    ///
    /// Panics if the directory cannot be made.
    pub(crate) fn scratch(what: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer-app-{what}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Returns a PE32+ at image base `0x140000000` whose `.text` at RVA `0x1000` holds its
    /// entry, which calls a helper at [`HELPER`] and returns.
    pub(crate) fn tiny_pe() -> Vec<u8> {
        /// File offset of the optional header, after the signature and COFF header at `0x80`.
        const OPT: usize = 0x98;
        /// File offset of the one section row, after a PE32+ optional header.
        const ROW: usize = OPT + 0xf0;
        // ASM: call 0x140001010 ; ret
        let entry = [0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3];
        // ASM: mov eax, 0x11223344 ; add eax, 0x55667788 ; xor ecx, ecx ; ret
        let helper = [
            0xb8, 0x44, 0x33, 0x22, 0x11, 0x05, 0x88, 0x77, 0x66, 0x55, 0x31, 0xc9, 0xc3,
        ];
        let fields: [(usize, Vec<u8>); 25] = [
            (0, b"MZ".to_vec()),
            (0x3c, 0x80u32.to_le_bytes().to_vec()),
            (0x80, b"PE\0\0".to_vec()),
            (0x84, 0x8664u16.to_le_bytes().to_vec()),
            (0x86, 1u16.to_le_bytes().to_vec()),
            (0x94, 0xf0u16.to_le_bytes().to_vec()),
            (0x96, 0x22u16.to_le_bytes().to_vec()),
            (OPT, 0x20bu16.to_le_bytes().to_vec()),
            (OPT + 16, 0x1000u32.to_le_bytes().to_vec()),
            (OPT + 24, 0x1_4000_0000u64.to_le_bytes().to_vec()),
            (OPT + 32, 0x1000u32.to_le_bytes().to_vec()),
            (OPT + 36, 0x200u32.to_le_bytes().to_vec()),
            (OPT + 48, 6u16.to_le_bytes().to_vec()),
            (OPT + 56, 0x2000u32.to_le_bytes().to_vec()),
            (OPT + 60, 0x200u32.to_le_bytes().to_vec()),
            (OPT + 68, 3u16.to_le_bytes().to_vec()),
            (OPT + 108, 16u32.to_le_bytes().to_vec()),
            (ROW, b".text".to_vec()),
            (ROW + 8, 0x200u32.to_le_bytes().to_vec()),
            (ROW + 12, 0x1000u32.to_le_bytes().to_vec()),
            (ROW + 16, 0x200u32.to_le_bytes().to_vec()),
            (ROW + 20, 0x200u32.to_le_bytes().to_vec()),
            (ROW + 36, 0x6000_0020u32.to_le_bytes().to_vec()),
            (0x200, entry.to_vec()),
            (0x210, helper.to_vec()),
        ];
        let mut bytes = vec![0u8; 0x200];
        bytes.resize(0x400, 0xcc);
        for (at, field) in fields {
            bytes[at..at + field.len()].copy_from_slice(&field);
        }
        bytes
    }

    /// Writes a pack naming [`tiny_pe`]'s helper `name` into `dir`.
    ///
    /// # Panics
    ///
    /// Panics if the file cannot be written.
    pub(crate) fn naming_pack(dir: &Path, name: &str) -> PathBuf {
        let pack = dir.join("named.borer");
        let text = format!("pack named 1\n[names]\nfn {HELPER_SIG} {name}\n");
        std::fs::write(&pack, text).unwrap();
        pack
    }

    /// A pack file the person listed names a function of a hand-built PE opened through the
    /// engine's session, and the function rows show that name.
    ///
    /// # Panics
    ///
    /// Panics if the load fails or the helper's row has another name.
    #[test]
    fn a_listed_pack_names_a_function_in_the_rows() {
        let dir = scratch("pack");
        let exe = dir.join("tiny.exe");
        std::fs::write(&exe, tiny_pe()).unwrap();
        let sources = Sources {
            packs: vec![naming_pack(&dir, "packed_helper")],
            ..Sources::default()
        };
        let loaded = load_binary_blocking(exe, &sources, Vec::new()).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        let row = loaded
            .initial_rows
            .rows
            .iter()
            .find(|row| row.entry == HELPER);
        assert_eq!(row.map(|row| row.name.as_str()), Some("packed_helper"));
    }

    /// No module of the app but this one names the engine's compute calls outside its tests.
    ///
    /// Those are its load, session, analysis, decompile, listing, project and edit calls, so
    /// each such call goes through [`super::run_engine`] and is counted.
    ///
    /// # Panics
    ///
    /// Panics if another module names one of them.
    #[test]
    fn only_the_worker_names_engine_compute_calls() {
        let calls = [
            "Program::load",
            "Analysis::compute",
            "decompile::view",
            "disasm_view(",
            "linear(&",
            "band(&",
            "resolve_suggesting(",
            "function_rows(",
            "text_check(",
            "answered_flagged(",
            "triage(",
            "everywhere(",
            "render::cfg",
            "string_rows(",
            "symbol_rows(",
            "xref_rows",
            "hex_rows(",
            "call_children(",
            "decompile::decompile(",
            "borer_engine::session",
            "session::open",
            "read_pack",
            "project::admit",
            "Project::from_json",
            "Project::from_overlay",
            ".to_json(",
            "edit::plan",
            "edit::commit",
            "project_file::",
            "type_rows(",
            "type_detail(",
        ];
        for (name, text) in sources() {
            let code = kept(text);
            for call in calls {
                assert!(!code.contains(call), "{name} names {call}");
            }
        }
    }

    /// Returns the module a line declares in a file of its own (`mod x;` with any
    /// visibility), `None` for any other line.
    fn declared_module(line: &str) -> Option<&str> {
        let line = line.trim_start();
        let line = match line.strip_prefix("pub") {
            Some(rest) if rest.starts_with('(') => rest.split_once(") ")?.1,
            Some(rest) => rest.strip_prefix(' ')?,
            None => line,
        };
        line.strip_prefix("mod ")?.strip_suffix(';')
    }

    /// A module line of any visibility names its module, and no other line names one.
    #[test]
    fn a_module_line_of_any_visibility_names_its_module() {
        for (line, want) in [
            ("pub(super) mod report;", Some("report")),
            ("    pub(crate) mod a;", Some("a")),
            ("pub mod b;", Some("b")),
            ("mod c;", Some("c")),
            ("mod tests {", None),
            ("let x = 1;", None),
        ] {
            assert_eq!(declared_module(line), want, "{line}");
        }
    }

    /// The app asks the system file dialog for a file in one place outside tests, so every
    /// file it opens is picked the same way.
    #[test]
    fn the_app_has_one_file_dialog_helper() {
        let asks: usize = sources()
            .iter()
            .map(|(_, text)| text.split("#[cfg(test)]").next().unwrap_or(text))
            .map(|code| code.matches("prompt_for_paths(").count())
            .sum();
        assert_eq!(asks, 1);
    }

    /// The engine-call scan reads every module the crate declares: each `mod` line of a
    /// scanned file names a scanned file, so a new module cannot slip past it.
    #[test]
    fn the_engine_call_scan_covers_every_module() {
        let scanned: Vec<_> = sources().iter().map(|(name, _)| *name).collect();
        for (name, text) in sources() {
            let dir = match name {
                "lib.rs" | "main.rs" => String::new(),
                _ => format!("{}/", name.trim_end_matches(".rs")),
            };
            for module in text.lines().filter_map(declared_module) {
                let file = format!("{dir}{module}.rs");
                assert!(
                    file == "worker.rs" || scanned.contains(&file.as_str()),
                    "{name} declares {file}, which the scan skips"
                );
            }
        }
    }
}
