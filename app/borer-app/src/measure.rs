//! Measurement modes over the app: a harness entity that holds the [`AppView`] as
//! its only child and drives scripted scrolls, input-latency marks and the startup
//! and memory reports from outside it.
//!
//! The app view carries none of this: only the measurement command-line flags
//! build a [`Harness`], and a plain `borer-app [binary]` window has none.

mod input;

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
    AppContext as _, Context, Entity, InteractiveElement as _, IntoElement, KeyDownEvent,
    MouseButton, MouseDownEvent, MouseUpEvent, ParentElement as _, Render, ScrollStrategy,
    Styled as _, Subscription, Task, Window, div,
};

use self::input::pick_function_with_callees;
use crate::app_view::{AppView, Tickets};
use crate::code_view::CodeLines;
use crate::worker::{
    LoadedBinary, TaskEpoch, decompile_blocking, load_binary_blocking, run_engine, spawn_engine,
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
    /// Visible only once [`AppView::filter_settled`] holds for this filter ticket.
    Filter(u64),
    /// Visible only once [`AppView::decompile_settled`] holds for this decompile ticket.
    Decompile(u64),
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

/// Number of rows or lines advanced on each animation frame during scroll benchmarks.
const SCROLL_STEP_PER_FRAME: usize = 7;

/// Frames drawn before a scroll run starts recording.
const WARMUP_FRAMES: u8 = 8;

/// Duration of each scripted scroll benchmark run.
const SCROLL_DURATION: Duration = Duration::from_secs(10);

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
}

impl MeasurePhase {
    /// Returns what a failure of this phase's preparation says.
    const fn failure(self) -> &'static str {
        match self {
            Self::BothScrolls | Self::ListScroll => "list scroll load failed",
            Self::CodeScroll => "code scroll load failed",
            Self::InputLatency => "input latency load failed",
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
/// * `has_loaded` - `true` once [`LoadedBinary`] has finished installing on [`AppView`].
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
        CliMode::Interactive(_) | CliMode::Headless(_) | CliMode::Measure(_) => OneShotAction::Wait,
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

/// Parses `std::env::args_os` into a [`CliMode`] without panicking on non-Unicode paths.
///
/// # Returns
///
/// Parsed [`CliMode`] describing how `borer-app` should run.
///
/// # Errors
///
/// Returns an error when a flag requiring a `<path>` or `--phase` value omits it.
pub fn parse_cli_args() -> anyhow::Result<CliMode> {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    parse_cli_args_os(&args)
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
        Some("--measure-memory") => Ok(CliMode::MeasureMemory(path_or_notepad())),
        Some("--measure") => {
            let phase = match args.get(1) {
                None => MeasurePhase::BothScrolls,
                Some(opt) if opt.to_str() == Some("--phase") => match args.get(2) {
                    Some(v) if v.to_str() == Some("list") => MeasurePhase::ListScroll,
                    Some(v) if v.to_str() == Some("code") => MeasurePhase::CodeScroll,
                    Some(v) if v.to_str() == Some("input") => MeasurePhase::InputLatency,
                    Some(v) => anyhow::bail!("unknown --measure --phase {}", v.display()),
                    None => anyhow::bail!("--measure --phase requires list, code, or input"),
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
        let loaded = load_binary_blocking(path)?;
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
    let outcome = attempt.within(|| load_binary_blocking(path.to_path_buf()));
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
    let loaded = nav_cancel.within(|| load_binary_blocking(path.to_path_buf()))?;
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

/// Summarizes frame work recorded between two snapshots, across refresh intervals.
///
/// # Arguments
///
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
///
/// # Returns
///
/// `(work_n, work_p50_ms, work_p95_ms, work_p99_ms, work_max_ms, refresh_ms)`.
///
/// # Errors
///
/// Returns an error when the profiler's histograms cannot be subtracted or added, so a
/// failed step never drops samples silently.
fn frame_work(
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
) -> anyhow::Result<(u64, f64, f64, f64, f64, f64)> {
    let mut combined = None;
    let mut max_refresh_ns: u64 = 0;
    for post in &after.by_refresh_interval {
        let pre = before
            .by_refresh_interval
            .iter()
            .find(|pre| pre.refresh_interval == post.refresh_interval);
        let mut work = post.work.clone();
        if let Some(pre) = pre {
            work.subtract(&pre.work)?;
        }
        let drawn = post
            .frames_drawn
            .saturating_sub(pre.map_or(0, |p| p.frames_drawn));
        if drawn == 0 && work.is_empty() {
            continue;
        }
        if let Some(interval) = post.refresh_interval {
            max_refresh_ns = max_refresh_ns.max(nanos(interval));
        }
        match &mut combined {
            None => combined = Some(work),
            Some(acc) => acc.add(&work)?,
        }
    }
    let refresh_ms = ns_to_ms(max_refresh_ns);
    let Some(acc) = combined else {
        return Ok((0, 0.0, 0.0, 0.0, 0.0, refresh_ms));
    };
    Ok((
        acc.len(),
        ns_to_ms(acc.value_at_quantile(0.50)),
        ns_to_ms(acc.value_at_quantile(0.95)),
        ns_to_ms(acc.value_at_quantile(0.99)),
        ns_to_ms(acc.max()),
        refresh_ms,
    ))
}

/// Formats frame-duration and interval snapshots into one `MEASURE_SCROLL` protocol line.
///
/// # Arguments
///
/// * `kind` - `"list"` or `"code"`.
/// * `source` - Label naming the loaded binary.
/// * `base_items` - Unreplicated item count.
/// * `virtual_items` - Item count the scrolled list shows.
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
/// * `manual_intervals_ns` - Frame-to-frame durations collected via [`now_instant`].
///
/// # Errors
///
/// Returns an error when a histogram subtraction or addition fails.
fn scroll_report(
    kind: &str,
    source: &str,
    base_items: usize,
    virtual_items: usize,
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
    manual_intervals_ns: &mut [u64],
) -> anyhow::Result<String> {
    let mut draw = after.draw_duration_histogram.clone();
    draw.subtract(&before.draw_duration_histogram)?;
    let mut dirty = after.dirty_to_present_histogram.clone();
    dirty.subtract(&before.dirty_to_present_histogram)?;
    let mut present = after.present_interval_histogram.clone();
    present.subtract(&before.present_interval_histogram)?;
    let (wn, wp50, wp95, wp99, wmax, refresh_ms) = frame_work(before, after)?;
    let (mp50, mp95, mp99, mmax, mcount) = sorted_quantiles_ms(manual_intervals_ns);
    let replicated = base_items < virtual_items;
    Ok(format!(
        "MEASURE_SCROLL kind={kind} source={source:?} base_items={base_items} virtual_items={virtual_items} replicated={replicated} \
draw_n={} draw_p50_ms={:.3} draw_p95_ms={:.3} draw_p99_ms={:.3} draw_max_ms={:.3} \
work_n={wn} work_p50_ms={wp50:.3} work_p95_ms={wp95:.3} work_p99_ms={wp99:.3} work_max_ms={wmax:.3} refresh_ms={refresh_ms:.3} \
dirty_n={} dirty_p50_ms={:.3} dirty_p95_ms={:.3} dirty_p99_ms={:.3} dirty_max_ms={:.3} \
present_n={} present_p50_ms={:.3} present_p95_ms={:.3} present_p99_ms={:.3} present_max_ms={:.3} \
manual_n={mcount} manual_p50_ms={mp50:.3} manual_p95_ms={mp95:.3} manual_p99_ms={mp99:.3} manual_max_ms={mmax:.3} \
ui_engine_calls={}",
        draw.len(),
        ns_to_ms(draw.value_at_quantile(0.50)),
        ns_to_ms(draw.value_at_quantile(0.95)),
        ns_to_ms(draw.value_at_quantile(0.99)),
        ns_to_ms(draw.max()),
        dirty.len(),
        ns_to_ms(dirty.value_at_quantile(0.50)),
        ns_to_ms(dirty.value_at_quantile(0.95)),
        ns_to_ms(dirty.value_at_quantile(0.99)),
        ns_to_ms(dirty.max()),
        present.len(),
        ns_to_ms(present.value_at_quantile(0.50)),
        ns_to_ms(present.value_at_quantile(0.95)),
        ns_to_ms(present.value_at_quantile(0.99)),
        ns_to_ms(present.max()),
        ui_engine_calls(),
    ))
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
}

/// State of one 10-second scripted scroll, carried from frame to frame.
struct ScrollRun {
    /// Measurement generation owning this run.
    ticket: u64,
    /// Cooperative cancel flag owning this run.
    cancel: Cancel,
    /// `true` to scroll the code view, `false` the function table.
    code: bool,
    /// Label naming the loaded binary for the report.
    source: String,
    /// Items before repetition.
    base: usize,
    /// Items the scrolled list shows.
    items: usize,
    /// Whether the code scroll follows this one.
    then_code: bool,
    /// Warmup frames remaining before recording begins.
    warmup: u8,
    /// Snapshot captured immediately after warmup.
    before: Option<gpui::profiler::FrameDurationSnapshot>,
    /// Start of the recorded window.
    started: Option<Instant>,
    /// Timestamp of the previous frame.
    prev: Option<Instant>,
    /// Current scroll target index.
    ix: usize,
    /// Recorded frame-to-frame durations in nanoseconds.
    intervals: Vec<u64>,
}

/// The window root in measurement modes: the [`AppView`] as its only child, with the
/// scripted runs, the input marks and the one-shot reports kept here.
pub struct Harness {
    /// The app view under measurement.
    app: Entity<AppView>,
    /// The measurement mode this run was started in.
    mode: CliMode,
    /// Where a failure is left for [`crate::run`] to return.
    exit: CliExitSlot,
    /// Whether the one-shot report of [`Self::mode`] has been scheduled.
    reported: bool,
    /// Generation and cancel flag of the running phase.
    epoch: TaskEpoch,
    /// The running background preparation or stdin wait.
    task: Option<Task<()>>,
    /// The stdin `MARK` reader of the input phase.
    inject: Option<InjectMark>,
    /// Marked input events not yet presented, in arrival order.
    marks: VecDeque<PendingInputMark>,
    /// The app's tickets when the latest marked event arrived, while its dispatch runs.
    before: Option<Tickets>,
    /// Key presses that reached the window root.
    keys: u64,
    /// Clicks that opened a function.
    clicks: u64,
    /// Settles input marks and re-renders the harness, so it checks its one-shot report,
    /// whenever the app changes.
    _observe: Subscription,
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
    /// Creates the harness for `mode`, its app view, and starts the mode's phase.
    ///
    /// # Arguments
    ///
    /// * `mode` - A measurement [`CliMode`].
    /// * `exit` - Shared error slot populated when the run fails.
    /// * `window` - Window hosting the harness.
    /// * `cx` - Harness context.
    #[must_use]
    pub fn new(
        mode: CliMode,
        exit: CliExitSlot,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let path = match &mode {
            CliMode::ReportOpen(p) | CliMode::MeasureMemory(p) => Some(p.clone()),
            CliMode::Interactive(p) => p.clone(),
            CliMode::FirstFrame | CliMode::Headless(_) | CliMode::Measure(_) => None,
        };
        let app = cx.new(|cx| AppView::new(path, window, cx));
        let observe = cx.observe(&app, |harness: &mut Self, _, cx| {
            harness.settle_marks(cx);
            cx.notify();
        });
        let phase = match mode {
            CliMode::Measure(phase) => Some(phase),
            CliMode::Interactive(_)
            | CliMode::FirstFrame
            | CliMode::ReportOpen(_)
            | CliMode::Headless(_)
            | CliMode::MeasureMemory(_) => None,
        };
        let mut harness = Self {
            app,
            mode,
            exit,
            reported: false,
            epoch: TaskEpoch::new(),
            task: None,
            inject: None,
            marks: VecDeque::new(),
            before: None,
            keys: 0,
            clicks: 0,
            _observe: observe,
        };
        if let Some(phase) = phase {
            harness.begin(phase, cx);
        }
        harness
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

    /// Prepares `phase` on the background executor, then starts it.
    ///
    /// # Arguments
    ///
    /// * `phase` - The phase to run.
    /// * `cx` - Harness context.
    fn begin(&mut self, phase: MeasurePhase, cx: &mut Context<'_, Self>) {
        let (ticket, cancel) = self.epoch.begin();
        let worker = cancel.clone();
        let bg = match phase {
            MeasurePhase::BothScrolls | MeasurePhase::ListScroll => {
                let then_code = phase == MeasurePhase::BothScrolls;
                spawn_engine(cx, move || {
                    load_large_dll_blocking(&worker).map(|ready| Prepared::List(ready, then_code))
                })
            }
            MeasurePhase::CodeScroll => spawn_engine(cx, move || {
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
                spawn_engine(cx, move || prepare_input(&worker))
            }
        };
        let exit = self.exit.clone();
        self.task = Some(cx.spawn(async move |this, cx| {
            let ready = bg.await;
            let started = this.update_in(cx, |harness, window, cx| {
                if !harness.epoch.is_current(ticket, &cancel) {
                    return;
                }
                match ready {
                    Ok(prepared) => harness.start(ticket, cancel, prepared, window, cx),
                    Err(err) => harness.fail(err.context(phase.failure()), cx),
                }
            });
            if let Err(err) = started {
                *exit.borrow_mut() = Some(err.context("the measured window is gone"));
                cx.update(|cx| cx.quit());
            }
        }));
    }

    /// Shows what `prepared` holds in the app and starts its run on the next frame.
    ///
    /// # Arguments
    ///
    /// * `ticket` - Generation of the phase.
    /// * `cancel` - Cancel flag of the phase.
    /// * `prepared` - The phase's background preparation.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn start(
        &mut self,
        ticket: u64,
        cancel: Cancel,
        prepared: Prepared,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        cx.activate(true);
        window.activate_window();
        let (code, source, base, items, then_code) = match prepared {
            Prepared::List(ready, then_code) => {
                let source = format!(
                    "{} ({:.2}s)",
                    ready.loaded.path.display(),
                    ready.analyze_secs
                );
                self.app
                    .update(cx, |app, cx| app.show(ready.loaded, ready.rows, cx));
                (false, source, ready.base_rows, TARGET_LIST_ROWS, then_code)
            }
            Prepared::Code(corpus) => {
                let source = corpus.loaded.path.display().to_string();
                let rows = corpus.loaded.initial_rows.clone();
                self.app.update(cx, |app, cx| {
                    app.show(corpus.loaded, rows, cx);
                    app.show_code(corpus.code, cx);
                });
                (true, source, corpus.base_lines, TARGET_CODE_LINES, false)
            }
            Prepared::Input(loaded, entry) => {
                self.start_input(ticket, cancel, loaded, entry, window, cx);
                return;
            }
        };
        let run = ScrollRun {
            ticket,
            cancel,
            code,
            source,
            base,
            items,
            then_code,
            warmup: WARMUP_FRAMES,
            before: None,
            started: None,
            prev: None,
            ix: 0,
            intervals: Vec::with_capacity(2048),
        };
        cx.on_next_frame(window, move |this, window, cx| {
            this.scroll_step(run, window, cx);
        });
    }

    /// Scrolls one step of `run`, recording frame intervals, until 10 seconds pass.
    ///
    /// # Arguments
    ///
    /// * `run` - The scroll's state.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn scroll_step(&mut self, mut run: ScrollRun, window: &mut Window, cx: &mut Context<'_, Self>) {
        if !self.epoch.is_current(run.ticket, &run.cancel) {
            return;
        }
        let now = now_instant();
        if run.warmup > 0 {
            run.warmup -= 1;
            if run.warmup == 0 {
                run.before = Some(window.frame_duration_snapshot());
                run.started = Some(now);
                run.prev = Some(now);
            }
        } else {
            if let Some(prev) = run.prev.replace(now) {
                run.intervals.push(nanos(now.duration_since(prev)));
            }
            if run
                .started
                .is_some_and(|t0| now.duration_since(t0) >= SCROLL_DURATION)
            {
                self.finish_scroll(run, window, cx);
                return;
            }
        }
        run.ix = run.ix.saturating_add(SCROLL_STEP_PER_FRAME) % run.items.max(1);
        let (ix, code) = (run.ix, run.code);
        self.app.update(cx, |app, cx| {
            if code {
                app.scroll_code_to(ix, ScrollStrategy::Top);
            } else {
                app.scroll_table_to(ix, ScrollStrategy::Top, cx);
            }
            cx.notify();
        });
        cx.on_next_frame(window, move |this, window, cx| {
            this.scroll_step(run, window, cx);
        });
    }

    /// Prints the report of a finished scroll, then runs the code scroll or quits.
    ///
    /// # Arguments
    ///
    /// * `run` - The finished scroll.
    /// * `window` - Window providing the closing snapshot.
    /// * `cx` - Harness context.
    fn finish_scroll(
        &mut self,
        mut run: ScrollRun,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let Some(before) = run.before.take() else {
            self.fail(anyhow::anyhow!("scroll run ended before its warmup"), cx);
            return;
        };
        let after = window.frame_duration_snapshot();
        let kind = if run.code { "code" } else { "list" };
        let report = scroll_report(
            kind,
            &run.source,
            run.base,
            run.items,
            &before,
            &after,
            &mut run.intervals,
        )
        .and_then(|line| say(&line));
        match report {
            Err(err) => self.fail(err, cx),
            Ok(()) if run.then_code => self.begin(MeasurePhase::CodeScroll, cx),
            Ok(()) => cx.quit(),
        }
    }

    /// Schedules the one-shot report of [`Self::mode`] once the app is ready for it.
    ///
    /// # Arguments
    ///
    /// * `window` - Window registering the post-present callback.
    /// * `cx` - Harness context.
    fn check_one_shot(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let (action, rows, lines) = {
            let app = self.app.read(cx);
            (
                evaluate_one_shot(
                    &self.mode,
                    self.reported,
                    app.load_error(),
                    app.loaded().is_some(),
                    app.is_decompiling(),
                ),
                app.rows().map_or(0, |r| r.rows.len()),
                app.code().map_or(0, |c| c.len()),
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
    /// * `cx` - Harness context scheduling a frame so the mark can retire.
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
        self.before = Some(self.app.read(cx).tickets());
        cx.notify();
    }

    /// Binds the latest mark to the background work its event started, once the app
    /// has handled the event.
    ///
    /// # Arguments
    ///
    /// * `click` - Whether the event was a mouse release, counted when it opened a function.
    /// * `cx` - Harness context.
    fn bind(&mut self, click: bool, cx: &Context<'_, Self>) {
        let Some(before) = self.before.take() else {
            return;
        };
        let after = self.app.read(cx).tickets();
        let wait = if after.decompile != before.decompile {
            if click {
                self.clicks = self.clicks.saturating_add(1);
            }
            MarkWait::Decompile(after.decompile)
        } else if after.filter != before.filter {
            MarkWait::Filter(after.filter)
        } else {
            return;
        };
        if let Some(last) = self.marks.back_mut() {
            last.ready_at = None;
            last.wait = wait;
        }
    }
}

impl Render for Harness {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        self.check_one_shot(window, cx);
        div()
            .size_full()
            .capture_key_down(cx.listener(|this, _: &KeyDownEvent, _, cx| this.arrive(cx)))
            .on_key_down(cx.listener(|this, _: &KeyDownEvent, _, cx| {
                this.keys = this.keys.saturating_add(1);
                this.bind(false, cx);
            }))
            .capture_any_mouse_down(cx.listener(|this, _: &MouseDownEvent, _, cx| this.arrive(cx)))
            .capture_any_mouse_up(cx.listener(|this, _: &MouseUpEvent, _, cx| this.arrive(cx)))
            .on_mouse_up(
                MouseButton::Left,
                cx.listener(|this, _: &MouseUpEvent, _, cx| this.bind(true, cx)),
            )
            .child(self.app.clone())
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
        let loaded = load_binary_blocking(PathBuf::from(SYSTEM_NOTEPAD))?;
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

    use super::{
        CliMode, OneShotAction, build_corpus_code_blocking, evaluate_one_shot,
        load_large_dll_blocking, parse_cli_args_os, scroll_report,
    };

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
}
