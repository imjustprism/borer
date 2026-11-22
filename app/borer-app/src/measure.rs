//! Measurement modes over the app.
//!
//! A harness entity holds the app's workspace window as its only child and drives
//! scripted scrolls, input-latency marks, call tree expansions and the startup and memory
//! reports from outside it.
//!
//! The workspace carries none of this: only the measurement command-line flags build a
//! [`Harness`], and a plain `borer-app [binary]` window has none.

mod actions;
mod annotate_demo;
mod chat_demo;
mod claude_code_demo;
mod drop;
mod input;
mod scroll;
mod stage;
mod start_demo;
mod tree;
mod watch;

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ffi::OsString;
use std::io::{BufRead as _, Write as _};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use borer_engine::analysis::render::FunctionRows;
use borer_engine::cancel::Cancel;
use borer_engine::num::{as_f64, from_usize};
use borer_engine::program::checked_metadata;
use gpui::{
    App, AppContext as _, Context, Entity, EntityId, InteractiveElement as _, IntoElement,
    MouseButton, MouseDownEvent, MouseUpEvent, ParentElement as _, Render, Styled as _,
    Subscription, Task, Window, div,
};
use workspace::dock::DockPosition;
use workspace::{AppState, Workspace};

use self::input::pick_function_with_callees;
use crate::app_view::{AppWindow, add_functions_panel, new_workspace};
use crate::binary::Binary;
use crate::code_view::CodeLines;
use crate::decompile_item::DecompileItem;
use crate::functions_panel::FunctionsPanel;
use crate::panels::add_panels;
use crate::shell::Shell;
use crate::stored::FixedSources;
use crate::worker::{
    Job, LoadedBinary, Sources, decompile_blocking, load_binary_blocking, run_engine,
    ui_engine_calls,
};

/// Shared error slot transferring non-interactive CLI failures out of `Application::run`.
pub type CliExitSlot = Rc<RefCell<Option<anyhow::Error>>>;

/// Shared state matching controller `MARK <id>` / `SENT <id> <delta_ns>` lines to GPUI input.
#[derive(Debug, Default)]
pub struct InjectTracker {
    /// Most recently armed `(event_id, mark_instant)` awaiting GPUI event arrival.
    armed: Mutex<Option<(u64, Instant)>>,
    /// Per-event controller delay (`t_send - t_ack` in nanoseconds) recorded after `SendInput`.
    sent_offsets_ns: Mutex<BTreeMap<u64, u64>>,
}

impl InjectTracker {
    /// Arms `(id, at)` right before acknowledging `MARK_OK` on stdout.
    ///
    /// # Arguments
    ///
    /// * `id` - Monotonic controller event identifier (`0` when unnumbered).
    /// * `at` - Monotonic [`Instant`] captured when `MARK` arrived.
    pub fn arm(&self, id: u64, at: Instant) {
        if let Ok(mut guard) = self.armed.lock() {
            *guard = Some((id, at));
        }
    }

    /// Takes the currently armed `(id, mark_instant)` pair on GPUI input arrival.
    ///
    /// # Returns
    ///
    /// `Some((id, mark_instant))` when a marked event was armed, or `None`.
    #[must_use]
    pub fn take_armed(&self) -> Option<(u64, Instant)> {
        self.armed.lock().ok().and_then(|mut g| g.take())
    }

    /// Records the post-`MARK_OK` controller offset (`t_send - t_ack`) for event `id`.
    ///
    /// # Arguments
    ///
    /// * `id` - Event identifier previously armed with [`Self::arm`].
    /// * `delta_ns` - Elapsed nanoseconds between reading `MARK_OK` and calling `SendInput`.
    pub fn record_sent_offset(&self, id: u64, delta_ns: u64) {
        if id != 0
            && let Ok(mut guard) = self.sent_offsets_ns.lock()
        {
            guard.insert(id, delta_ns);
        }
    }

    /// Consumes any recorded post-`MARK_OK` controller offset for event `id`.
    ///
    /// # Arguments
    ///
    /// * `id` - Event identifier being retired.
    ///
    /// # Returns
    ///
    /// Elapsed nanoseconds between `MARK_OK` and `SendInput`, or `None` when absent.
    #[must_use]
    pub fn take_sent_offset(&self, id: u64) -> Option<u64> {
        if id == 0 {
            return None;
        }
        self.sent_offsets_ns
            .lock()
            .ok()
            .and_then(|mut g| g.remove(&id))
    }
}

/// Shared handle to [`InjectTracker`].
pub type InjectMark = Arc<InjectTracker>;

/// Background work a [`PendingInputMark`] waits on before it is ready to present.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MarkWait {
    /// No background task needed; visible on the next drawn frame.
    Immediate,
    /// Visible only once [`FunctionsPanel::filter_settled`] holds for this filter ticket.
    Filter(u64),
    /// Visible only once [`DecompileItem::decompile_settled`] holds for this ticket of the
    /// tab with this id, or another tab is active.
    Decompile(EntityId, u64),
}

/// Tickets of the latest background work the app was asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tickets {
    /// Latest filter request of the functions panel ([`FunctionsPanel::filter_ticket`]).
    pub filter: u64,
    /// The active decompile tab and its decompile generation ([`DecompileItem::ticket`]).
    pub decompile: Option<(EntityId, u64)>,
}

/// Timestamps and completion gate for one marked input event through GPUI presentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PendingInputMark {
    /// Monotonic event identifier (`0` when unnumbered).
    pub id: u64,
    /// Timestamp recorded at `MARK` prior to post-`MARK_OK` controller offset adjustment.
    pub injected_at: Instant,
    /// Timestamp recorded when GPUI dispatched the input event on the UI thread.
    pub arrived_at: Instant,
    /// Timestamp when the resulting UI state became ready to draw, or `None` while pending.
    pub ready_at: Option<Instant>,
    /// Background work condition gating [`Self::ready_at`].
    pub wait: MarkWait,
}

/// Rows the function-table scroll shows: the large DLL's rows repeated by index.
pub const TARGET_LIST_ROWS: usize = 100_000;

/// Lines the code-view scroll shows: notepad's decompile lines repeated by index.
pub const TARGET_CODE_LINES: usize = 1_000_000;

/// Maximum wall-clock time allowed for analyzing `edgehtml.dll` or `mshtml.dll`.
const LARGE_DLL_BUDGET: Duration = Duration::from_secs(120);

/// Filter keystrokes the input script sends before it clicks.
const FILTER_KEYS: u64 = 200;

/// Call-token clicks the input script sends.
const CALL_CLICKS: u64 = 100;

/// Default system `notepad.exe` path used by code, input, and open benchmarks.
const SYSTEM_NOTEPAD: &str = r"C:\Windows\System32\notepad.exe";

/// Creates an empty [`CliExitSlot`].
///
/// # Returns
///
/// Shared [`CliExitSlot`] initialized to `None`.
#[must_use]
pub fn new_cli_exit_slot() -> CliExitSlot {
    Rc::new(RefCell::new(None))
}

/// Sub-phase selection for `--measure`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MeasurePhase {
    /// Runs the 100k-row list scroll followed by the 1M-line code scroll in sequence.
    BothScrolls,
    /// Runs only the 100k-row function-table scroll for 10 seconds and exits.
    ListScroll,
    /// Runs only the 1M-line decompile-view scroll for 10 seconds and exits.
    CodeScroll,
    /// Runs the interactive Win32 `SendInput` filter + call-click benchmark and exits.
    InputLatency,
    /// Opens 200 nodes of notepad's call tree, timing each expand to its painted rows.
    CallTree,
    /// Times a script of actions on notepad and the large DLL, each to its first visible
    /// change and to settled views, and graph pans and zooms frame by frame.
    Actions,
}

impl MeasurePhase {
    /// Returns what a failure of this phase's preparation says.
    const fn failure(self) -> &'static str {
        match self {
            Self::BothScrolls | Self::ListScroll => "list scroll load failed",
            Self::CodeScroll => "code scroll load failed",
            Self::InputLatency => "input latency load failed",
            Self::CallTree => "call tree load failed",
            Self::Actions => "actions load failed",
        }
    }

    /// Returns what the running work list calls this phase's preparation.
    const fn label(self) -> &'static str {
        match self {
            Self::BothScrolls | Self::ListScroll => "Preparing the list scroll",
            Self::CodeScroll => "Preparing the code scroll",
            Self::InputLatency => "Preparing the input run",
            Self::CallTree => "Preparing the call tree run",
            Self::Actions => "Preparing the action run",
        }
    }
}

/// Parsed command-line execution mode for `borer-app`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CliMode {
    /// Normal interactive desktop window, optionally opening a binary at launch.
    Interactive(Option<PathBuf>),
    /// Prints `FIRST_FRAME_READY` on the first presented frame and exits.
    FirstFrame,
    /// Opens `<path>`, prints `OPEN_LIST_READY` once loaded, and exits.
    ReportOpen(PathBuf),
    /// Runs engine load + first decompile view without GPUI, waits on stdin, and exits.
    Headless(PathBuf),
    /// Opens `<path>` + first decompile view in GPUI, prints `MEMORY_READY`, waits on stdin.
    MeasureMemory(PathBuf),
    /// Runs automated scroll or input-latency profiling.
    Measure(MeasurePhase),
    /// Drops the folder `<path>` on the start tab and on a tab of the binary `<binary>`
    /// (default notepad), prints `DROP_DONE` with the project's folder count, and exits.
    MeasureDrop(PathBuf, PathBuf),
    /// Opens `<path>` (default notepad) and replays a canned conversation of a scripted model
    /// in the chat panel, printing `CHAT_STAGE <name>` at each state worth a screenshot.
    ChatDemo(PathBuf),
    /// Opens `<path>` (default notepad), picks Claude Code in the chat, which must be on
    /// `PATH`, and sends it one short message, printing `CHAT_STAGE picker` and
    /// `CHAT_STAGE turn`, then `CHAT_DONE`: the one demo that sends a message off the machine.
    ClaudeCodeDemo(PathBuf),
    /// Opens `<path>` (default notepad) and opens each inline editor over it, printing
    /// `ANNOTATE_STAGE <name>` at each state worth a screenshot, then `ANNOTATE_DONE`.
    AnnotateDemo(PathBuf),
    /// Opens a few system binaries one after another so the recent list holds them, closes
    /// the last, and shows the start page, printing `START_STAGE start`, then `START_DONE`.
    StartDemo,
}

impl CliMode {
    /// Returns whether the run is a person's window rather than a measurement.
    #[must_use]
    pub const fn is_interactive(&self) -> bool {
        match self {
            Self::Interactive(_) => true,
            Self::FirstFrame
            | Self::ReportOpen(_)
            | Self::Headless(_)
            | Self::MeasureMemory(_)
            | Self::Measure(_)
            | Self::MeasureDrop(..)
            | Self::ChatDemo(_)
            | Self::ClaudeCodeDemo(_)
            | Self::AnnotateDemo(_)
            | Self::StartDemo => false,
        }
    }
}

/// One-shot startup transition decided from the current [`CliMode`] and load state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OneShotAction {
    /// Keep waiting for the startup mode's readiness condition.
    Wait,
    /// Emit `FIRST_FRAME_READY` on the next presented frame and quit.
    FirstFrameReady,
    /// Emit `OPEN_LIST_READY` on the next presented frame and quit.
    OpenListReady,
    /// Emit `MEMORY_READY` on the next presented frame and wait on stdin before quitting.
    MemoryReady,
    /// Fail the non-interactive startup mode with the given message and exit non-zero.
    Fail(String),
}

/// Evaluates whether a one-shot CLI startup mode should wait, report readiness, or fail.
///
/// # Arguments
///
/// * `mode` - Active [`CliMode`].
/// * `mode_reported` - `true` once the one-shot notification has already been scheduled.
/// * `load_error` - Error text if loading the requested binary failed.
/// * `has_loaded` - `true` once the functions panel lists the loaded binary's rows.
/// * `decompiling` - `true` while an initial function decompilation is still running.
///
/// # Returns
///
/// Next [`OneShotAction`] for the [`Harness`] to execute during render.
#[must_use]
pub fn evaluate_one_shot(
    mode: &CliMode,
    mode_reported: bool,
    load_error: Option<&str>,
    has_loaded: bool,
    decompiling: bool,
) -> OneShotAction {
    if mode_reported {
        return OneShotAction::Wait;
    }
    match mode {
        CliMode::FirstFrame => OneShotAction::FirstFrameReady,
        CliMode::ReportOpen(_) => {
            if let Some(err) = load_error {
                OneShotAction::Fail(format!("report-open failed: {err}"))
            } else if has_loaded {
                OneShotAction::OpenListReady
            } else {
                OneShotAction::Wait
            }
        }
        CliMode::MeasureMemory(_) => {
            if let Some(err) = load_error {
                OneShotAction::Fail(format!("measure-memory failed: {err}"))
            } else if has_loaded && !decompiling {
                OneShotAction::MemoryReady
            } else {
                OneShotAction::Wait
            }
        }
        CliMode::Interactive(_)
        | CliMode::Headless(_)
        | CliMode::Measure(_)
        | CliMode::MeasureDrop(..)
        | CliMode::ChatDemo(_)
        | CliMode::ClaudeCodeDemo(_)
        | CliMode::AnnotateDemo(_)
        | CliMode::StartDemo => OneShotAction::Wait,
    }
}

/// Every function's decompile lines of a binary, repeated to [`TARGET_CODE_LINES`].
#[derive(Debug)]
pub struct CodeCorpus {
    /// The analyzed binary the views were built from.
    pub loaded: Arc<LoadedBinary>,
    /// The lines, repeated by index.
    pub code: Arc<CodeLines>,
    /// Lines before repetition (`N`).
    pub base_lines: usize,
}

/// Loaded large-DLL function list prepared for the 100,000-row scroll benchmark.
#[derive(Debug)]
pub struct LargeListReady {
    /// Underlying loaded binary state.
    pub loaded: Arc<LoadedBinary>,
    /// Its rows repeated by index to [`TARGET_LIST_ROWS`].
    pub rows: Arc<FunctionRows>,
    /// Elapsed wall-clock seconds spent loading and analyzing the DLL.
    pub analyze_secs: f64,
    /// Base function row count before index repetition to [`TARGET_LIST_ROWS`].
    pub base_rows: usize,
}

/// Reads the monotonic clock for benchmark duration and present-interval accounting.
///
/// # Returns
///
/// Current monotonic [`Instant`].
#[must_use]
#[expect(
    clippy::disallowed_methods,
    reason = "UI benchmark harness measures real wall-clock frame intervals and analysis budgets"
)]
pub fn now_instant() -> Instant {
    Instant::now()
}

/// Keeps gpui's frame tracing on while it lives; dropped, it turns tracing off only if it
/// was the one to turn it on.
#[derive(Debug)]
pub(super) struct Tracing {
    /// Whether tracing was off before, so this guard turned it on.
    turned_on: bool,
}

impl Tracing {
    /// Turns gpui's frame tracing on and returns the guard that puts it back.
    pub(super) fn on() -> Self {
        Self {
            turned_on: gpui::profiler::set_trace_enabled(true),
        }
    }
}

impl Drop for Tracing {
    fn drop(&mut self) {
        if self.turned_on {
            gpui::profiler::set_trace_enabled(false);
        }
    }
}

/// Returns `d` in nanoseconds, saturating at [`u64::MAX`].
///
/// # Arguments
///
/// * `d` - A measured duration.
fn nanos(d: Duration) -> u64 {
    u64::try_from(d.as_nanos()).unwrap_or(u64::MAX)
}

/// Writes `line` and a newline to stdout, the measurement script's protocol, and flushes.
///
/// # Arguments
///
/// * `line` - One protocol line.
///
/// # Errors
///
/// Returns an error when stdout cannot be written.
fn say(line: &str) -> anyhow::Result<()> {
    let mut out = std::io::stdout().lock();
    writeln!(out, "{line}")?;
    out.flush()?;
    Ok(())
}

/// Parses `std::env::args_os` into a [`CliMode`], the data directory a leading
/// `--data-dir <dir>` names and whether `--park` follows it, without panicking on
/// non-Unicode paths.
///
/// `--park` opens a measurement or demo window off-screen without taking focus, so a
/// capture does not take a keystroke from the person at the machine as it opens; the scroll
/// measurements still activate their window.
///
/// # Returns
///
/// The parsed [`CliMode`], the data directory (`None` when none is named) and whether to
/// park the window.
///
/// # Errors
///
/// Returns an error when a flag requiring a `<path>` or `--phase` value omits it, or
/// `--park` is given for the interactive window.
pub fn parse_cli_args() -> anyhow::Result<(CliMode, Option<PathBuf>, bool)> {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let (data_dir, rest) = split_data_dir(&args)?;
    let park = rest.first().and_then(|first| first.to_str()) == Some("--park");
    let mode = parse_cli_args_os(rest.get(usize::from(park)..).unwrap_or_default())?;
    if park && mode.is_interactive() {
        anyhow::bail!("--park is for the measure and demo modes, not the interactive window");
    }
    Ok((mode, data_dir, park))
}

/// Splits a leading `--data-dir <dir>` off `args`.
///
/// # Arguments
///
/// * `args` - Command-line arguments excluding `argv[0]`.
///
/// # Returns
///
/// The named directory, `None` without the flag, and the arguments after it.
///
/// # Errors
///
/// Returns an error when `--data-dir` has no directory after it.
pub fn split_data_dir(args: &[OsString]) -> anyhow::Result<(Option<PathBuf>, &[OsString])> {
    if args.first().and_then(|first| first.to_str()) != Some("--data-dir") {
        return Ok((None, args));
    }
    let dir = args
        .get(1)
        .ok_or_else(|| anyhow::anyhow!("--data-dir requires a <dir> path"))?;
    Ok((Some(PathBuf::from(dir)), args.get(2..).unwrap_or_default()))
}

/// Parses an explicit slice of OS arguments into a [`CliMode`].
///
/// # Arguments
///
/// * `args` - Command-line arguments excluding `argv[0]`.
///
/// # Returns
///
/// Parsed [`CliMode`].
///
/// # Errors
///
/// Returns an error when an unknown `--` flag is supplied or a required argument is missing.
pub fn parse_cli_args_os(args: &[OsString]) -> anyhow::Result<CliMode> {
    let Some(first) = args.first() else {
        return Ok(CliMode::Interactive(None));
    };
    let path_or_notepad = || {
        args.get(1)
            .map_or_else(|| PathBuf::from(SYSTEM_NOTEPAD), PathBuf::from)
    };
    match first.to_str() {
        Some("--first-frame") => Ok(CliMode::FirstFrame),
        Some("--report-open") => {
            let p = args
                .get(1)
                .ok_or_else(|| anyhow::anyhow!("--report-open requires a <binary> path"))?;
            Ok(CliMode::ReportOpen(PathBuf::from(p)))
        }
        Some("--headless") => Ok(CliMode::Headless(path_or_notepad())),
        Some("--chat-demo") => Ok(CliMode::ChatDemo(path_or_notepad())),
        Some("--claude-code-demo") => Ok(CliMode::ClaudeCodeDemo(path_or_notepad())),
        Some("--measure-memory") => Ok(CliMode::MeasureMemory(path_or_notepad())),
        Some("--annotate-demo") => Ok(CliMode::AnnotateDemo(path_or_notepad())),
        Some("--start-demo") => Ok(CliMode::StartDemo),
        Some("--measure-drop") => {
            let p = args
                .get(1)
                .ok_or_else(|| anyhow::anyhow!("--measure-drop requires a <folder> path"))?;
            let binary = args
                .get(2)
                .map_or_else(|| PathBuf::from(SYSTEM_NOTEPAD), PathBuf::from);
            Ok(CliMode::MeasureDrop(PathBuf::from(p), binary))
        }
        Some("--measure") => {
            let phase = match args.get(1) {
                None => MeasurePhase::BothScrolls,
                Some(opt) if opt.to_str() == Some("--phase") => match args.get(2) {
                    Some(v) if v.to_str() == Some("list") => MeasurePhase::ListScroll,
                    Some(v) if v.to_str() == Some("code") => MeasurePhase::CodeScroll,
                    Some(v) if v.to_str() == Some("input") => MeasurePhase::InputLatency,
                    Some(v) if v.to_str() == Some("tree") => MeasurePhase::CallTree,
                    Some(v) if v.to_str() == Some("actions") => MeasurePhase::Actions,
                    Some(v) => anyhow::bail!("unknown --measure --phase {}", v.display()),
                    None => {
                        anyhow::bail!(
                            "--measure --phase requires list, code, input, tree or actions"
                        )
                    }
                },
                Some(other) => {
                    anyhow::bail!("unexpected argument after --measure: {}", other.display())
                }
            };
            Ok(CliMode::Measure(phase))
        }
        _ if first.as_encoded_bytes().starts_with(b"--") => {
            anyhow::bail!("unknown option {}", first.display())
        }
        _ => Ok(CliMode::Interactive(Some(PathBuf::from(first)))),
    }
}

/// Runs the `--headless` baseline (load + initial rows + first decompile view, no window).
///
/// # Arguments
///
/// * `path` - Binary path to load and decompile.
///
/// # Errors
///
/// Returns an error if loading `path` or reading/writing the headless readiness protocol fails.
pub fn run_headless(path: PathBuf) -> anyhow::Result<()> {
    let (loaded, first_view) = run_engine(move || -> anyhow::Result<_> {
        let loaded = load_binary_blocking(path, &Sources::default(), Vec::new())?;
        let first_view = loaded
            .initial_rows
            .rows
            .first()
            .and_then(|r| decompile_blocking(&loaded, r.entry));
        Ok((loaded, first_view))
    })?;
    let rows = loaded.initial_rows.rows.len();
    let lines = first_view.as_ref().map_or(0, |v| v.lines());
    say(&format!(
        "HEADLESS_READY pid={} rows={rows} lines={lines} ui_engine_calls={}",
        std::process::id(),
        ui_engine_calls()
    ))?;
    let mut line = String::new();
    std::io::stdin().lock().read_line(&mut line)?;
    drop((loaded, first_view));
    Ok(())
}

/// Loads `path` unless `nav_cancel` is raised or it outlasts [`LARGE_DLL_BUDGET`].
///
/// # Arguments
///
/// * `path` - Binary to load.
/// * `nav_cancel` - Cooperative [`Cancel`] flag raised when the user navigates away.
///
/// # Returns
///
/// The loaded binary and its seconds, or `None` when it ran out of budget.
///
/// # Errors
///
/// Returns an error if the load fails or the watchdog thread cannot start.
fn load_within_budget(
    path: &Path,
    nav_cancel: &Cancel,
) -> anyhow::Result<Option<(Arc<LoadedBinary>, f64)>> {
    let attempt = Cancel::new();
    let watchdog = attempt.clone();
    let nav = nav_cancel.clone();
    let started = now_instant();
    let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
    std::thread::Builder::new()
        .name("borer-app-budget".to_owned())
        .spawn(move || {
            while matches!(
                done_rx.recv_timeout(Duration::from_millis(50)),
                Err(std::sync::mpsc::RecvTimeoutError::Timeout)
            ) {
                if nav.is_raised() || started.elapsed() >= LARGE_DLL_BUDGET {
                    watchdog.raise();
                    break;
                }
            }
        })?;
    let outcome = attempt
        .within(|| load_binary_blocking(path.to_path_buf(), &Sources::default(), Vec::new()));
    drop(done_tx);
    let elapsed = started.elapsed();
    let loaded = outcome?;
    Ok((!attempt.is_raised() && elapsed <= LARGE_DLL_BUDGET)
        .then_some((loaded, elapsed.as_secs_f64())))
}

/// Loads the larger of `edgehtml.dll` and `mshtml.dll` that analyzes within 120 seconds.
///
/// # Arguments
///
/// * `nav_cancel` - Cooperative [`Cancel`] flag raised when the user navigates away.
///
/// # Returns
///
/// [`LargeListReady`] containing the analyzed binary, its repeated rows, seconds, and base count.
///
/// # Errors
///
/// Returns an error if `nav_cancel` is raised, no candidate binary exists, or none completes
/// within 120 seconds.
pub fn load_large_dll_blocking(nav_cancel: &Cancel) -> anyhow::Result<LargeListReady> {
    if nav_cancel.is_raised() {
        anyhow::bail!("cancelled");
    }
    let candidates = [
        PathBuf::from(r"C:\Windows\System32\edgehtml.dll"),
        PathBuf::from(r"C:\Windows\System32\mshtml.dll"),
        PathBuf::from(SYSTEM_NOTEPAD),
    ];
    let mut sized: Vec<(u64, PathBuf)> = candidates
        .into_iter()
        .filter_map(|p| checked_metadata(&p).ok().flatten().map(|m| (m.len(), p)))
        .collect();
    sized.sort_by_key(|a| std::cmp::Reverse(a.0));

    let mut last_err = String::from("no candidate DLL found");
    for (_, path) in sized {
        let outcome = load_within_budget(&path, nav_cancel);
        if nav_cancel.is_raised() {
            anyhow::bail!("cancelled");
        }
        match outcome {
            Ok(Some((loaded, analyze_secs))) => {
                let base = &loaded.initial_rows;
                let base_rows = base.rows.len().max(1);
                let rows = Arc::new(FunctionRows {
                    total: TARGET_LIST_ROWS,
                    noun: base.noun,
                    order: base.order,
                    left_out: base.left_out,
                    incomplete: base.incomplete,
                    rows: base
                        .rows
                        .iter()
                        .cycle()
                        .take(TARGET_LIST_ROWS)
                        .cloned()
                        .collect(),
                });
                return Ok(LargeListReady {
                    loaded,
                    rows,
                    analyze_secs,
                    base_rows,
                });
            }
            Ok(None) => last_err = format!("{} exceeded 120s analysis budget", path.display()),
            Err(err) => last_err = format!("{}: {err:#}", path.display()),
        }
    }
    anyhow::bail!("{last_err}")
}

/// Loads `path` and builds every function's decompile view for the 1M-line scroll.
///
/// # Arguments
///
/// * `path` - Binary path (typically `notepad.exe`).
/// * `nav_cancel` - Cooperative [`Cancel`] flag raised when the user navigates away.
///
/// # Returns
///
/// The [`CodeCorpus`] of the binary.
///
/// # Errors
///
/// Returns an error if `nav_cancel` is raised, loading `path` fails, or zero lines are produced.
pub fn build_corpus_code_blocking(path: &Path, nav_cancel: &Cancel) -> anyhow::Result<CodeCorpus> {
    if nav_cancel.is_raised() {
        anyhow::bail!("cancelled");
    }
    let loaded = nav_cancel
        .within(|| load_binary_blocking(path.to_path_buf(), &Sources::default(), Vec::new()))?;
    let mut views = Vec::with_capacity(loaded.initial_rows.rows.len());
    for row in &loaded.initial_rows.rows {
        if nav_cancel.is_raised() {
            anyhow::bail!("cancelled");
        }
        views.extend(nav_cancel.within(|| decompile_blocking(&loaded, row.entry)));
    }
    if nav_cancel.is_raised() {
        anyhow::bail!("cancelled");
    }
    let code = CodeLines::new(views);
    let base_lines = code.len();
    if base_lines == 0 {
        anyhow::bail!("{} produced zero decompiled lines", path.display());
    }
    Ok(CodeCorpus {
        loaded,
        code: Arc::new(code.cycled(TARGET_CODE_LINES)),
        base_lines,
    })
}

/// Converts nanoseconds to milliseconds with microsecond precision.
///
/// # Arguments
///
/// * `ns` - Duration in nanoseconds.
///
/// # Returns
///
/// Duration in milliseconds as `f64`.
fn ns_to_ms(ns: u64) -> f64 {
    as_f64(ns) / 1_000_000.0
}

/// Computes `(p50_ms, p95_ms, p99_ms, max_ms, count)` from nanosecond samples.
///
/// # Arguments
///
/// * `samples_ns` - Mutable slice sorted in place to extract order statistics.
///
/// # Returns
///
/// Tuple `(p50_ms, p95_ms, p99_ms, max_ms, sample_count)`.
fn sorted_quantiles_ms(samples_ns: &mut [u64]) -> (f64, f64, f64, f64, u64) {
    if samples_ns.is_empty() {
        return (0.0, 0.0, 0.0, 0.0, 0);
    }
    samples_ns.sort_unstable();
    let n = samples_ns.len();
    let pick = |num: usize, den: usize| -> u64 {
        let idx = n.saturating_mul(num).saturating_sub(1) / den;
        samples_ns.get(idx.min(n - 1)).copied().unwrap_or(0)
    };
    (
        ns_to_ms(pick(50, 100)),
        ns_to_ms(pick(95, 100)),
        ns_to_ms(pick(99, 100)),
        ns_to_ms(samples_ns.last().copied().unwrap_or(0)),
        from_usize(n),
    )
}

/// What a phase's background preparation hands the harness to start on.
#[derive(Debug)]
enum Prepared {
    /// The large DLL's rows, and whether the code scroll follows.
    List(LargeListReady, bool),
    /// Notepad's decompile lines.
    Code(CodeCorpus),
    /// Notepad, and a function with a call token near its top.
    Input(Arc<LoadedBinary>, u64),
    /// Notepad, and the root of its call tree.
    Tree(Arc<LoadedBinary>, u64),
    /// Notepad, and the functions the actions phase runs on.
    Actions(actions::Prep),
}

/// The window root in measurement modes: the app's workspace window as its only child,
/// with the scripted runs, the input marks and the one-shot reports kept here.
pub struct Harness {
    /// The app's window root under measurement, rendered as the harness's child.
    root: Entity<Shell>,
    /// The workspace the functions panel and the decompile tabs live in.
    workspace: Entity<Workspace>,
    /// The window's binary.
    binary: Entity<Binary>,
    /// Whether the functions panel is observed, which it is from when it is docked.
    panel_observed: bool,
    /// The measurement mode this run was started in.
    mode: CliMode,
    /// Where a failure is left for [`crate::run`] to return.
    exit: CliExitSlot,
    /// Whether the one-shot report of [`Self::mode`] has been scheduled.
    reported: bool,
    /// Flag of the running phase, raised when the next phase begins.
    phase: Cancel,
    /// The running background preparation.
    prep: Job,
    /// The running stdin wait.
    task: Option<Task<()>>,
    /// The stdin `MARK` reader of the input phase.
    inject: Option<InjectMark>,
    /// Marked input events not yet presented, in arrival order.
    marks: VecDeque<PendingInputMark>,
    /// The app's tickets when the latest marked event arrived, and whether a left button
    /// release followed it, until the next frame binds the event to its work.
    before: Option<(Tickets, bool)>,
    /// Key presses the window received, seen before any key binding or text input takes them.
    keys: u64,
    /// Clicks that opened a function.
    clicks: u64,
    /// Mouse button presses and releases the window received, armed or not, so a stall
    /// tells a click that never arrived from one that opened nothing.
    buttons: (u64, u64),
    /// When the functions panel last changed.
    panel_changed: Option<Instant>,
    /// When the watched decompile tab last changed.
    item_changed: Option<Instant>,
    /// The active decompile tab and the observer settling marks when it changes.
    watched: Option<(EntityId, Subscription)>,
    /// The call tree phase, once its root's read is asked for.
    tree_run: Option<tree::TreeRun>,
    /// What each draw showed while a step of the actions phase is watched, read as it
    /// drew: when, and the read; `None` otherwise, so a sweep's timed draws read nothing.
    draws: Option<Vec<(Instant, watch::Seen)>>,
    /// Observers of the pane, the panel and the binary, which settle input marks and
    /// re-render the harness, so it checks its one-shot report, whenever they change.
    observers: Vec<Subscription>,
}

impl std::fmt::Debug for Harness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Harness")
            .field("mode", &self.mode)
            .field("keys", &self.keys)
            .field("clicks", &self.clicks)
            .finish_non_exhaustive()
    }
}

impl Harness {
    /// Creates the harness for `mode`, its workspace window, and starts the mode's phase.
    ///
    /// Every load it makes uses [`Sources::default`] ([`FixedSources`]), so a measurement
    /// reads no packs or symbol cache of the machine's.
    ///
    /// # Arguments
    ///
    /// * `mode` - A measurement [`CliMode`].
    /// * `exit` - Shared error slot populated when the run fails.
    /// * `app_state` - The app state the workspace is built from.
    /// * `window` - Window hosting the harness.
    /// * `cx` - Harness context.
    #[must_use]
    pub fn new(
        mode: CliMode,
        exit: CliExitSlot,
        app_state: &Arc<AppState>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let path = match &mode {
            CliMode::ReportOpen(p)
            | CliMode::MeasureMemory(p)
            | CliMode::ChatDemo(p)
            | CliMode::ClaudeCodeDemo(p)
            | CliMode::AnnotateDemo(p) => Some(p.clone()),
            CliMode::Interactive(p) => p.clone(),
            CliMode::FirstFrame
            | CliMode::Headless(_)
            | CliMode::Measure(_)
            | CliMode::MeasureDrop(..)
            | CliMode::StartDemo => None,
        };
        cx.set_global(FixedSources::default());
        let app = new_workspace(app_state, path, window, cx);
        let AppWindow { workspace, binary } = app.clone();
        let root = cx.new(|cx| Shell::new(app, window, cx));
        let pane = workspace.read(cx).active_pane().clone();
        let harness = cx.weak_entity();
        let mut observe = vec![
            cx.observe(&pane, |harness: &mut Self, _, cx| {
                harness.watch_active_item(cx);
                harness.settle_marks(cx);
                cx.notify();
            }),
            cx.intercept_keystrokes(move |_, _, cx| {
                if let Some(harness) = harness.upgrade() {
                    harness.update(cx, |harness, cx| {
                        harness.keys = harness.keys.saturating_add(1);
                        harness.arrive(cx);
                    });
                }
            }),
        ];
        observe.push(cx.observe(&binary, |harness: &mut Self, _, cx| {
            harness.observe_panel(cx);
            cx.notify();
        }));
        let phase = match mode {
            CliMode::Measure(phase) => Some(phase),
            CliMode::Interactive(_)
            | CliMode::FirstFrame
            | CliMode::ReportOpen(_)
            | CliMode::Headless(_)
            | CliMode::MeasureMemory(_)
            | CliMode::MeasureDrop(..)
            | CliMode::ChatDemo(_)
            | CliMode::ClaudeCodeDemo(_)
            | CliMode::AnnotateDemo(_)
            | CliMode::StartDemo => None,
        };
        let mut harness = Self {
            root,
            workspace,
            binary,
            panel_observed: false,
            mode,
            exit,
            reported: false,
            phase: Cancel::new(),
            prep: Job::default(),
            task: None,
            inject: None,
            marks: VecDeque::new(),
            before: None,
            keys: 0,
            clicks: 0,
            buttons: (0, 0),
            panel_changed: None,
            item_changed: None,
            watched: None,
            tree_run: None,
            draws: None,
            observers: observe,
        };
        if let Some(phase) = phase {
            harness.begin(phase, window, cx);
        }
        harness.start_scripted(window, cx);
        harness
    }

    /// Starts the scripted run the mode names on the next frame: a demo, or the folder drop;
    /// nothing for the other modes.
    ///
    /// # Arguments
    ///
    /// * `window` - The harness's window.
    /// * `cx` - Harness context.
    fn start_scripted(&self, window: &mut Window, cx: &mut Context<'_, Self>) {
        match &self.mode {
            CliMode::ChatDemo(_) => cx.on_next_frame(window, |this, window, cx| {
                this.run_demo("chat demo", chat_demo::demo, window, cx);
            }),
            CliMode::ClaudeCodeDemo(_) => cx.on_next_frame(window, |this, window, cx| {
                this.run_demo("Claude Code demo", claude_code_demo::demo, window, cx);
            }),
            CliMode::StartDemo => cx.on_next_frame(window, |this, window, cx| {
                this.run_demo("start demo", start_demo::demo, window, cx);
            }),
            CliMode::AnnotateDemo(_) => cx.on_next_frame(window, |this, window, cx| {
                this.run_demo("annotate demo", annotate_demo::demo, window, cx);
            }),
            CliMode::MeasureDrop(dir, binary) => {
                let (dir, binary) = (dir.clone(), binary.clone());
                cx.on_next_frame(window, move |this, _, cx| this.drop_folder(dir, binary, cx));
            }
            CliMode::Interactive(_)
            | CliMode::FirstFrame
            | CliMode::ReportOpen(_)
            | CliMode::Headless(_)
            | CliMode::MeasureMemory(_)
            | CliMode::Measure(_) => {}
        }
    }

    /// Observes the functions panel once it is docked, so a change of its rows settles the
    /// input marks.
    ///
    /// # Arguments
    ///
    /// * `cx` - Harness context.
    fn observe_panel(&mut self, cx: &mut Context<'_, Self>) {
        let Some(panel) = self.panel(cx).filter(|_| !self.panel_observed) else {
            return;
        };
        self.panel_observed = true;
        self.observers
            .push(cx.observe(&panel, |harness: &mut Self, _, cx| {
                harness.panel_changed = Some(now_instant());
                harness.settle_marks(cx);
                cx.notify();
            }));
    }

    /// Returns the functions panel of the measured workspace, docking every panel the app
    /// docks first when there is none, as a load does ([`add_panels`]); a phase shows its
    /// rows in it without a load through the binary, and its xrefs and other panels are
    /// there as in the app.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the workspace is in.
    /// * `cx` - Harness context.
    fn docked_panel(
        &mut self,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Entity<FunctionsPanel> {
        if self.panel(cx).is_none() {
            let binary = self.binary.clone();
            self.workspace.update(cx, |workspace, cx| {
                add_panels(workspace, &binary, None, window, cx);
            });
        }
        let panel = self.panel(cx).unwrap_or_else(|| {
            add_functions_panel(
                &self.workspace,
                &self.binary,
                DockPosition::Left,
                window,
                cx,
            )
        });
        self.observe_panel(cx);
        panel
    }

    /// Returns the functions panel of the measured workspace.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn panel(&self, cx: &App) -> Option<Entity<FunctionsPanel>> {
        self.workspace.read(cx).panel::<FunctionsPanel>(cx)
    }

    /// Returns the active decompile tab of the measured workspace.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn item(&self, cx: &App) -> Option<Entity<DecompileItem>> {
        self.workspace.read(cx).active_item_as::<DecompileItem>(cx)
    }

    /// Returns the tickets of the latest filter request and of the active tab's decompile.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn tickets(&self, cx: &App) -> Tickets {
        Tickets {
            filter: self
                .panel(cx)
                .map_or(0, |panel| panel.read(cx).filter_ticket()),
            decompile: self
                .item(cx)
                .map(|item| (item.entity_id(), item.read(cx).ticket())),
        }
    }

    /// Observes the active decompile tab, once it is a different one, so its decompile
    /// settles marks the moment it lands.
    ///
    /// # Arguments
    ///
    /// * `cx` - Harness context.
    fn watch_active_item(&mut self, cx: &mut Context<'_, Self>) {
        let Some(item) = self.item(cx) else {
            self.watched = None;
            return;
        };
        if self
            .watched
            .as_ref()
            .is_some_and(|(id, _)| *id == item.entity_id())
        {
            return;
        }
        let observe = cx.observe(&item, |harness: &mut Self, _, cx| {
            harness.item_changed = Some(now_instant());
            harness.settle_marks(cx);
            cx.notify();
        });
        self.watched = Some((item.entity_id(), observe));
    }

    /// Leaves `err` for [`crate::run`] to return and quits.
    ///
    /// # Arguments
    ///
    /// * `err` - Why the run failed.
    /// * `cx` - Harness context.
    fn fail(&self, err: anyhow::Error, cx: &mut Context<'_, Self>) {
        *self.exit.borrow_mut() = Some(err);
        cx.quit();
    }

    /// Prepares `phase` on the background executor, then starts it; the phase before ends.
    ///
    /// # Arguments
    ///
    /// * `phase` - The phase to run.
    /// * `window` - Window the phase runs in.
    /// * `cx` - Harness context.
    fn begin(&mut self, phase: MeasurePhase, window: &Window, cx: &mut Context<'_, Self>) {
        self.phase.raise();
        self.phase = Cancel::new();
        let cancel = self.phase.clone();
        let worker = cancel.clone();
        let work: Box<dyn FnOnce() -> anyhow::Result<Prepared> + Send> = match phase {
            MeasurePhase::BothScrolls | MeasurePhase::ListScroll => {
                let then_code = phase == MeasurePhase::BothScrolls;
                Box::new(move || {
                    load_large_dll_blocking(&worker).map(|ready| Prepared::List(ready, then_code))
                })
            }
            MeasurePhase::CodeScroll => Box::new(move || {
                build_corpus_code_blocking(Path::new(SYSTEM_NOTEPAD), &worker).map(Prepared::Code)
            }),
            MeasurePhase::InputLatency => {
                match spawn_inject_marker(cancel.clone()) {
                    Ok(mark) => self.inject = Some(mark),
                    Err(err) => {
                        self.fail(err, cx);
                        return;
                    }
                }
                Box::new(move || prepare_input(&worker))
            }
            MeasurePhase::CallTree => Box::new(move || tree::prepare_tree(&worker)),
            MeasurePhase::Actions => Box::new(move || actions::prepare_actions(&worker)),
        };
        self.prep.run_in(
            phase.label(),
            window,
            cx,
            work,
            move |harness, ready, window, cx| match ready {
                Ok(prepared) => harness.start(cancel, prepared, window, cx),
                Err(err) => harness.fail(err.context(phase.failure()), cx),
            },
        );
    }

    /// Schedules the one-shot report of [`Self::mode`] once the app is ready for it.
    ///
    /// # Arguments
    ///
    /// * `window` - Window registering the post-present callback.
    /// * `cx` - Harness context.
    fn check_one_shot(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let (action, rows, lines) = {
            let panel_entity = self.panel(cx);
            let panel = panel_entity.as_ref().map(|panel| panel.read(cx));
            let item_entity = self.item(cx);
            let item = item_entity.as_ref().map(|item| item.read(cx));
            let error = self.binary.read(cx).load_error();
            let rows = panel.and_then(|panel| panel.rows()).map(|r| r.rows.len());
            (
                evaluate_one_shot(
                    &self.mode,
                    self.reported,
                    error,
                    rows.is_some(),
                    item.is_some_and(DecompileItem::is_decompiling),
                ),
                rows.unwrap_or(0),
                item.and_then(DecompileItem::code).map_or(0, |c| c.len()),
            )
        };
        let (line, quit) = match action {
            OneShotAction::Wait => return,
            OneShotAction::Fail(msg) => {
                self.reported = true;
                self.fail(anyhow::anyhow!(msg), cx);
                return;
            }
            OneShotAction::FirstFrameReady => (String::from("FIRST_FRAME_READY"), true),
            OneShotAction::OpenListReady => (format!("OPEN_LIST_READY rows={rows}"), true),
            OneShotAction::MemoryReady => {
                self.wait_stdin(cx);
                let pid = std::process::id();
                (
                    format!("MEMORY_READY pid={pid} rows={rows} lines={lines}"),
                    false,
                )
            }
        };
        self.reported = true;
        cx.on_next_frame(window, move |this, _, cx| {
            match say(&format!("{line} ui_engine_calls={}", ui_engine_calls())) {
                Err(err) => this.fail(err, cx),
                Ok(()) if quit => cx.quit(),
                Ok(()) => {}
            }
        });
    }

    /// Quits once a line arrives on stdin, as the memory script asks.
    ///
    /// # Arguments
    ///
    /// * `cx` - Harness context.
    fn wait_stdin(&mut self, cx: &mut Context<'_, Self>) {
        let read = cx.background_executor().spawn(async {
            let mut buf = String::new();
            std::io::stdin().lock().read_line(&mut buf).map(drop)
        });
        let exit = self.exit.clone();
        self.task = Some(cx.spawn(async move |_, cx| {
            if let Err(err) = read.await {
                *exit.borrow_mut() = Some(anyhow::Error::new(err).context("reading stdin"));
            }
            cx.update(|cx| cx.quit());
        }));
    }

    /// Records the arrival of a marked input event, before the app handles it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Harness context scheduling a frame so the mark can be bound and retire.
    fn arrive(&mut self, cx: &mut Context<'_, Self>) {
        let Some((id, injected_at)) = self.inject.as_ref().and_then(|t| t.take_armed()) else {
            return;
        };
        let arrived_at = now_instant();
        self.marks.push_back(PendingInputMark {
            id,
            injected_at,
            arrived_at,
            ready_at: Some(arrived_at),
            wait: MarkWait::Immediate,
        });
        self.before = Some((self.tickets(cx), false));
        cx.notify();
    }

    /// Binds the latest mark to the background work its event started.
    ///
    /// Runs when the next frame renders the harness: the app's editor takes typed text as
    /// a separate platform event and defers its edit, and a link opens its tab once the
    /// click's update ends, so the work is known only after every effect of the event ran.
    /// Work that already landed counts as ready when its panel or tab last changed.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn bind(&mut self, cx: &App) {
        let Some((before, click)) = self.before.take() else {
            return;
        };
        let after = self.tickets(cx);
        let (wait, changed) = if after.decompile != before.decompile {
            let Some((id, ticket)) = after.decompile else {
                return;
            };
            if click {
                self.clicks = self.clicks.saturating_add(1);
            }
            (MarkWait::Decompile(id, ticket), self.item_changed)
        } else if after.filter != before.filter {
            (MarkWait::Filter(after.filter), self.panel_changed)
        } else {
            return;
        };
        let settled = self.settled(wait, cx);
        if let Some(last) = self.marks.back_mut() {
            if settled {
                let landed = changed.map_or(last.arrived_at, |at| at.max(last.arrived_at));
                last.ready_at = Some(landed);
            } else {
                last.ready_at = None;
                last.wait = wait;
            }
        }
    }
}

impl Render for Harness {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        self.bind(cx);
        self.check_one_shot(window, cx);
        if let Some(draws) = self.draws.as_mut() {
            draws.push((
                now_instant(),
                watch::seen(&self.workspace, &self.binary, cx),
            ));
        }
        div()
            .size_full()
            .capture_any_mouse_down(cx.listener(|this, _: &MouseDownEvent, _, cx| {
                this.buttons.0 = this.buttons.0.saturating_add(1);
                this.arrive(cx);
            }))
            .capture_any_mouse_up(cx.listener(|this, event: &MouseUpEvent, _, cx| {
                this.buttons.1 = this.buttons.1.saturating_add(1);
                this.arrive(cx);
                if event.button == MouseButton::Left
                    && let Some((_, click)) = this.before.as_mut()
                {
                    *click = true;
                }
            }))
            .child(self.root.clone())
    }
}

/// Loads notepad and picks a function with a call token near its top, for the input phase.
///
/// # Arguments
///
/// * `cancel` - Cooperative cancel flag of the phase.
///
/// # Errors
///
/// Returns an error when notepad does not load or has no such function.
fn prepare_input(cancel: &Cancel) -> anyhow::Result<Prepared> {
    cancel.within(|| {
        let loaded = load_binary_blocking(
            PathBuf::from(SYSTEM_NOTEPAD),
            &Sources::default(),
            Vec::new(),
        )?;
        let entry = pick_function_with_callees(&loaded).ok_or_else(|| {
            anyhow::anyhow!("{SYSTEM_NOTEPAD} has no function with a visible call token")
        })?;
        Ok(Prepared::Input(loaded, entry))
    })
}

/// Reads one controller line: arms a `MARK [<id>]` and returns its acknowledgement, or
/// records a `SENT <id> <delta_ns>` offset.
///
/// # Arguments
///
/// * `line` - One trimmed stdin line.
/// * `tracker` - The marks the line updates.
///
/// # Returns
///
/// The line to acknowledge with, or `None` when there is none.
fn read_mark(line: &str, tracker: &InjectTracker) -> Option<String> {
    if line == "MARK" {
        tracker.arm(0, now_instant());
        return Some(String::from("MARK_OK"));
    }
    if let Some(rest) = line.strip_prefix("MARK ") {
        let id = rest.trim().parse::<u64>().ok()?;
        tracker.arm(id, now_instant());
        return Some(format!("MARK_OK {id}"));
    }
    let mut parts = line.strip_prefix("SENT ")?.split_whitespace();
    let id = parts.next()?.parse().ok()?;
    let delta_ns = parts.next()?.parse().ok()?;
    tracker.record_sent_offset(id, delta_ns);
    None
}

/// Spawns a stdin reader coordinating `MARK [<id>]` and `SENT <id> <delta_ns>` controller lines.
///
/// # Arguments
///
/// * `cancel` - Cooperative cancellation flag terminating the reader when the benchmark ends.
///
/// # Returns
///
/// Shared [`InjectMark`] tracking armed event marks and post-`MARK_OK` `SendInput` offsets.
///
/// # Errors
///
/// Returns an error when the reader thread cannot start.
fn spawn_inject_marker(cancel: Cancel) -> anyhow::Result<InjectMark> {
    let mark: InjectMark = Arc::new(InjectTracker::default());
    let shared = mark.clone();
    std::thread::Builder::new()
        .name("borer-app-marks".to_owned())
        .spawn(move || {
            let stdin = std::io::stdin();
            let mut line = String::new();
            while !cancel.is_raised() {
                line.clear();
                if !matches!(stdin.lock().read_line(&mut line), Ok(n) if n > 0) {
                    break;
                }
                if let Some(ack) = read_mark(line.trim(), &shared)
                    && say(&ack).is_err()
                {
                    break;
                }
            }
        })?;
    Ok(mark)
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};

    use borer_engine::cancel::Cancel;

    use super::scroll::scroll_report;
    use super::{
        CliMode, OneShotAction, Tracing, build_corpus_code_blocking, evaluate_one_shot,
        load_large_dll_blocking, parse_cli_args_os,
    };

    /// A tracing guard turns tracing off when dropped only if it turned it on: with tracing
    /// already on, it stays on.
    ///
    /// # Panics
    ///
    /// Panics if the guard leaves tracing other than it found it.
    #[test]
    fn a_tracing_guard_puts_tracing_back_as_it_found_it() {
        let was = gpui::profiler::trace_enabled();
        for before in [true, false] {
            gpui::profiler::set_trace_enabled(before);
            let guard = Tracing::on();
            assert!(gpui::profiler::trace_enabled());
            drop(guard);
            assert_eq!(gpui::profiler::trace_enabled(), before);
        }
        gpui::profiler::set_trace_enabled(was);
    }

    /// Returns a frame snapshot whose three histograms each hold `n` one-millisecond samples.
    ///
    /// # Panics
    ///
    /// Panics if a histogram cannot be built or record a sample.
    fn snapshot(n: u64) -> gpui::profiler::FrameDurationSnapshot {
        let hist = || {
            let mut h = hdrhistogram::Histogram::<u64>::new(3).unwrap();
            for _ in 0..n {
                h.record(1_000_000).unwrap();
            }
            h
        };
        gpui::profiler::FrameDurationSnapshot {
            dirty_to_present_histogram: hist(),
            draw_duration_histogram: hist(),
            present_interval_histogram: hist(),
            by_refresh_interval: Vec::new(),
        }
    }

    /// A scroll report whose histograms do not subtract fails instead of dropping samples.
    ///
    /// # Panics
    ///
    /// Panics if a later snapshot holding fewer samples than the earlier one still reports.
    #[test]
    fn a_histogram_that_does_not_subtract_fails_the_scroll_report() {
        assert!(scroll_report("list", "x", 1, 1, &snapshot(1), &snapshot(2), &mut []).is_ok());
        assert!(scroll_report("list", "x", 1, 1, &snapshot(2), &snapshot(1), &mut []).is_err());
    }

    /// Raised navigation [`Cancel`] flags immediately abort interactive benchmark preparation.
    ///
    /// # Panics
    ///
    /// Panics if either blocking preparation helper proceeds after cancellation is raised.
    #[test]
    fn benchmark_preparation_honors_raised_navigation_cancel() {
        let cancel = Cancel::new();
        cancel.raise();
        let dll_err = load_large_dll_blocking(&cancel).unwrap_err().to_string();
        assert!(dll_err.contains("cancelled"), "got {dll_err}");
        let code_err = build_corpus_code_blocking(Path::new("nonexistent.bin"), &cancel)
            .unwrap_err()
            .to_string();
        assert!(code_err.contains("cancelled"), "got {code_err}");
    }

    /// `--report-open` and `--measure-memory` fail cleanly on load errors and settle on zero-row binaries.
    ///
    /// # Panics
    ///
    /// Panics if either CLI mode hangs (`Wait`) after a load failure or a zero-function binary settles.
    #[test]
    fn one_shot_modes_fail_on_corrupt_load_and_settle_on_zero_function_binary() {
        let report_mode = CliMode::ReportOpen(PathBuf::from("corrupt.bin"));
        assert_eq!(
            evaluate_one_shot(&report_mode, false, None, false, false),
            OneShotAction::Wait
        );
        assert_eq!(
            evaluate_one_shot(&report_mode, false, Some("bad header"), false, false),
            OneShotAction::Fail(String::from("report-open failed: bad header"))
        );
        assert_eq!(
            evaluate_one_shot(&report_mode, false, None, true, false),
            OneShotAction::OpenListReady
        );
        assert_eq!(
            evaluate_one_shot(&report_mode, true, None, true, false),
            OneShotAction::Wait
        );

        let mem_mode = CliMode::MeasureMemory(PathBuf::from("tzres.dll"));
        assert_eq!(
            evaluate_one_shot(&mem_mode, false, Some("io error"), false, false),
            OneShotAction::Fail(String::from("measure-memory failed: io error"))
        );
        assert_eq!(
            evaluate_one_shot(&mem_mode, false, None, true, true),
            OneShotAction::Wait
        );
        assert_eq!(
            evaluate_one_shot(&mem_mode, false, None, true, false),
            OneShotAction::MemoryReady
        );
    }

    /// `parse_cli_args_os` preserves non-Unicode OS paths without panicking.
    ///
    /// # Panics
    ///
    /// Panics if `parse_cli_args_os` rejects or alters an unpaired UTF-16 path on Windows.
    #[test]
    #[cfg(windows)]
    fn parse_cli_args_preserves_non_unicode_paths() {
        use std::os::windows::ffi::OsStringExt as _;

        let raw = OsString::from_wide(&[0x0066, 0x006F, 0xD800, 0x002E, 0x0065, 0x0078, 0x0065]);
        assert_eq!(
            parse_cli_args_os(std::slice::from_ref(&raw)).unwrap(),
            CliMode::Interactive(Some(PathBuf::from(&raw)))
        );
        assert_eq!(
            parse_cli_args_os(&[OsString::from("--report-open"), raw.clone()]).unwrap(),
            CliMode::ReportOpen(PathBuf::from(&raw))
        );
    }

    /// A window and a headless run take the same path from the command line, whether it is
    /// spelled with backslashes, forward slashes or spaces.
    ///
    /// # Panics
    ///
    /// Panics if the two modes read a path differently.
    #[test]
    fn a_window_and_a_headless_run_take_the_same_path() {
        let spellings = [
            r"C:\Windows\System32\notepad.exe",
            "C:/Windows/System32/notepad.exe",
            r"C:\Program Files\some tool\a b.exe",
        ];
        for spelled in spellings {
            let path = OsString::from(spelled);
            let window = parse_cli_args_os(std::slice::from_ref(&path)).unwrap();
            let headless = parse_cli_args_os(&[OsString::from("--headless"), path]).unwrap();
            assert_eq!(window, CliMode::Interactive(Some(PathBuf::from(spelled))));
            assert_eq!(headless, CliMode::Headless(PathBuf::from(spelled)));
        }
    }
}
