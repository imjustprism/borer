//! Automated frame-pacing, input-latency, startup, memory, and headless measurement modes.

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ffi::OsString;
use std::io::{BufRead as _, Write as _};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use borer_engine::analysis::decompile::view::view as build_decompile_view;
use borer_engine::cancel::Cancel;
use borer_engine::num::{as_f64, from_usize};
use borer_engine::program::checked_metadata;
use borer_engine::view::{Ref, View};
use gpui::{App, Context, ScrollStrategy, Window};

use crate::app_view::AppView;
use crate::worker::{
    LoadedBinary, load_binary_blocking, run_engine, spawn_engine, ui_engine_calls,
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

/// Asynchronous completion condition required before a [`PendingInputMark`] becomes visible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MarkWait {
    /// No background task needed; visible on the next drawn frame.
    Immediate,
    /// Visible only after [`crate::worker::FilterLatest`] sequence `seq` is installed.
    Filter(u64),
    /// Visible only after decompile generation `ticket` finishes installing `active_view`.
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

/// Virtual row count used for the 100,000-row function-table scroll benchmark.
pub const TARGET_LIST_ROWS: usize = 100_000;

/// Virtual line count used for the 1,000,000-line decompile-view scroll benchmark.
pub const TARGET_CODE_LINES: usize = 1_000_000;

/// Number of rows or lines advanced on each animation frame during scroll benchmarks.
const SCROLL_STEP_PER_FRAME: usize = 7;

/// Duration of each scripted scroll benchmark run.
const SCROLL_DURATION: Duration = Duration::from_secs(10);

/// Maximum wall-clock time allowed for analyzing `edgehtml.dll` or `mshtml.dll`.
const LARGE_DLL_BUDGET: Duration = Duration::from_secs(120);

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
/// Next [`OneShotAction`] for [`AppView`] to execute during render.
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

/// Prebuilt corpus of every function's decompile [`View`] in `notepad.exe` for 1M-line scrolling.
#[derive(Debug)]
pub struct CorpusCode {
    /// Binary path from which the views were built.
    pub source_path: PathBuf,
    /// Decompile views indexed by the first element of [`Self::lines`].
    pub views: Vec<Arc<View>>,
    /// Flattened `(view_index, line_index)` pairs across all functions (`N` base lines).
    pub lines: Vec<(usize, usize)>,
}

/// Loaded large-DLL function list prepared for the 100,000-row scroll benchmark.
#[derive(Debug)]
pub struct LargeListReady {
    /// Underlying loaded binary state.
    pub loaded: Arc<LoadedBinary>,
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
    match first.to_str() {
        Some("--first-frame") => Ok(CliMode::FirstFrame),
        Some("--report-open") => {
            let p = args
                .get(1)
                .ok_or_else(|| anyhow::anyhow!("--report-open requires a <binary> path"))?;
            Ok(CliMode::ReportOpen(PathBuf::from(p)))
        }
        Some("--headless") => {
            let p = args
                .get(1)
                .map_or_else(|| PathBuf::from(SYSTEM_NOTEPAD), PathBuf::from);
            Ok(CliMode::Headless(p))
        }
        Some("--measure-memory") => {
            let p = args
                .get(1)
                .map_or_else(|| PathBuf::from(SYSTEM_NOTEPAD), PathBuf::from);
            Ok(CliMode::MeasureMemory(p))
        }
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
        let first_view = loaded.initial_rows.rows.first().and_then(|r| {
            build_decompile_view(&loaded.program, &loaded.analysis, &loaded.overlay, r.entry)
        });
        Ok((loaded, first_view))
    })?;
    let rows = loaded.initial_rows.rows.len();
    let lines = first_view.as_ref().map_or(0, |v| v.lines());
    let pid = std::process::id();
    {
        let mut out = std::io::stdout().lock();
        writeln!(
            out,
            "HEADLESS_READY pid={pid} rows={rows} lines={lines} ui_engine_calls={}",
            ui_engine_calls()
        )?;
        out.flush()?;
    }
    let mut line = String::new();
    std::io::stdin().lock().read_line(&mut line)?;
    drop((loaded, first_view));
    Ok(())
}

/// Loads the larger of `edgehtml.dll` and `mshtml.dll` that analyzes within 120 seconds.
///
/// # Arguments
///
/// * `nav_cancel` - Cooperative [`Cancel`] flag raised when the user navigates away.
///
/// # Returns
///
/// [`LargeListReady`] containing the analyzed binary, elapsed seconds, and base row count.
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
        if nav_cancel.is_raised() {
            anyhow::bail!("cancelled");
        }
        let attempt_cancel = Cancel::new();
        let watchdog_flag = attempt_cancel.clone();
        let nav_flag = nav_cancel.clone();
        let started = now_instant();
        let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
        std::thread::spawn(move || {
            let poll = Duration::from_millis(50);
            while done_rx.recv_timeout(poll).is_err() {
                if nav_flag.is_raised() || started.elapsed() >= LARGE_DLL_BUDGET {
                    watchdog_flag.raise();
                    break;
                }
            }
        });
        let outcome = attempt_cancel.within(|| load_binary_blocking(path.clone()));
        let _ = done_tx.send(());
        if nav_cancel.is_raised() {
            anyhow::bail!("cancelled");
        }
        let elapsed = started.elapsed();
        match outcome {
            Ok(loaded) if !attempt_cancel.is_raised() && elapsed <= LARGE_DLL_BUDGET => {
                let base_rows = loaded.initial_rows.rows.len().max(1);
                return Ok(LargeListReady {
                    loaded,
                    analyze_secs: elapsed.as_secs_f64(),
                    base_rows,
                });
            }
            Ok(_) => {
                last_err = format!("{} exceeded 120s analysis budget", path.display());
            }
            Err(err) => {
                last_err = format!("{}: {err:#}", path.display());
            }
        }
    }
    anyhow::bail!("{last_err}")
}

/// Loads `path` and builds every function's decompile [`View`] for 1M-line scrolling.
///
/// # Arguments
///
/// * `path` - Binary path (typically `notepad.exe`).
/// * `nav_cancel` - Cooperative [`Cancel`] flag raised when the user navigates away.
///
/// # Returns
///
/// Loaded binary state paired with the flattened [`CorpusCode`] line table.
///
/// # Errors
///
/// Returns an error if `nav_cancel` is raised, loading `path` fails, or zero lines are produced.
pub fn build_corpus_code_blocking(
    path: &Path,
    nav_cancel: &Cancel,
) -> anyhow::Result<(Arc<LoadedBinary>, Arc<CorpusCode>)> {
    if nav_cancel.is_raised() {
        anyhow::bail!("cancelled");
    }
    let loaded = nav_cancel.within(|| load_binary_blocking(path.to_path_buf()))?;
    let mut views = Vec::with_capacity(loaded.initial_rows.rows.len());
    let mut lines = Vec::new();
    for row in &loaded.initial_rows.rows {
        if nav_cancel.is_raised() {
            anyhow::bail!("cancelled");
        }
        if let Some(built) = nav_cancel.within(|| {
            build_decompile_view(
                &loaded.program,
                &loaded.analysis,
                &loaded.overlay,
                row.entry,
            )
        }) {
            let v_ix = views.len();
            let count = built.lines();
            views.push(built);
            for l_ix in 0..count {
                lines.push((v_ix, l_ix));
            }
        }
    }
    if nav_cancel.is_raised() {
        anyhow::bail!("cancelled");
    }
    if lines.is_empty() {
        anyhow::bail!("{} produced zero decompiled lines", path.display());
    }
    Ok((
        loaded,
        Arc::new(CorpusCode {
            source_path: path.to_path_buf(),
            views,
            lines,
        }),
    ))
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

/// Summarizes per-refresh-interval frame work (`work_n`, `p50`, `p95`, `p99`, `max`, `refresh_ms`).
///
/// # Arguments
///
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
///
/// # Returns
///
/// `(work_n, work_p50_ms, work_p95_ms, work_p99_ms, work_max_ms, refresh_ms)` across displays.
fn summarize_frame_work(
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
) -> (u64, f64, f64, f64, f64, f64) {
    let mut combined: Option<gpui::profiler::RefreshIntervalFrames> = None;
    let mut max_refresh_ns: u64 = 0;
    for post in &after.by_refresh_interval {
        let delta = before
            .by_refresh_interval
            .iter()
            .find(|pre| pre.refresh_interval == post.refresh_interval)
            .map_or_else(|| post.clone(), |pre| post.since(pre));
        if delta.frames_drawn == 0 && delta.work.is_empty() {
            continue;
        }
        if let Some(interval) = delta.refresh_interval {
            let ns = u64::try_from(interval.as_nanos()).unwrap_or(u64::MAX);
            max_refresh_ns = max_refresh_ns.max(ns);
        }
        match &mut combined {
            None => combined = Some(delta),
            Some(acc) => {
                let _ = acc.work.add(&delta.work);
            }
        }
    }
    let Some(acc) = combined else {
        return (0, 0.0, 0.0, 0.0, 0.0, ns_to_ms(max_refresh_ns));
    };
    (
        acc.work.len(),
        ns_to_ms(acc.work.value_at_quantile(0.50)),
        ns_to_ms(acc.work.value_at_quantile(0.95)),
        ns_to_ms(acc.work.value_at_quantile(0.99)),
        ns_to_ms(acc.work.max()),
        ns_to_ms(max_refresh_ns),
    )
}

/// Formats frame-duration and interval snapshots into one `MEASURE_SCROLL` stdout line.
///
/// # Arguments
///
/// * `kind` - `"list"` or `"code"`.
/// * `source` - Label naming the loaded binary.
/// * `base_items` - Unreplicated item count.
/// * `virtual_items` - Virtualized item count scrolled by `uniform_list`.
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
/// * `manual_intervals_ns` - Frame-to-frame durations collected via [`now_instant`].
fn print_scroll_report(
    kind: &str,
    source: &str,
    base_items: usize,
    virtual_items: usize,
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
    manual_intervals_ns: &mut [u64],
) {
    let mut draw = after.draw_duration_histogram.clone();
    let _ = draw.subtract(&before.draw_duration_histogram);
    let mut dirty = after.dirty_to_present_histogram.clone();
    let _ = dirty.subtract(&before.dirty_to_present_histogram);
    let mut present = after.present_interval_histogram.clone();
    let _ = present.subtract(&before.present_interval_histogram);
    let (wn, wp50, wp95, wp99, wmax, refresh_ms) = summarize_frame_work(before, after);

    let (mp50, mp95, mp99, mmax, mcount) = sorted_quantiles_ms(manual_intervals_ns);
    let replicated = base_items < virtual_items;
    let mut out = std::io::stdout().lock();
    let _ = writeln!(
        out,
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
    );
    let _ = out.flush();
}

/// Shared mutable state driving one 10-second `on_next_frame` scroll loop.
struct ScrollLoopState {
    /// Warmup frames remaining before recording begins.
    warmup_left: u8,
    /// Snapshot captured immediately after warmup.
    before_snap: Option<gpui::profiler::FrameDurationSnapshot>,
    /// Start instant of the 10-second scroll window.
    started_at: Option<Instant>,
    /// Timestamp of the previous presented frame.
    prev_frame: Option<Instant>,
    /// Current scroll target index.
    scroll_ix: usize,
    /// Recorded frame-to-frame durations in nanoseconds.
    intervals_ns: Vec<u64>,
}

/// Parameters describing one 10-second scripted scroll benchmark run.
#[derive(Debug, Clone)]
pub struct ScrollRunSpec {
    /// Target `AppView` entity whose list or code pane is scrolled.
    pub view_entity: gpui::Entity<AppView>,
    /// Generation counter from [`AppView::begin_measure`].
    pub ticket: u64,
    /// Cooperative [`Cancel`] flag from [`AppView::begin_measure`].
    pub cancel: Cancel,
    /// `true` to scroll the decompile code view, `false` to scroll the function table.
    pub is_code: bool,
    /// Label naming the loaded binary and analysis time for the stdout report.
    pub source_label: String,
    /// Unreplicated base item count before index modulo repetition.
    pub base_items: usize,
    /// Virtual item count exposed to `uniform_list`.
    pub virtual_items: usize,
    /// Optional next phase to chain immediately when this run finishes.
    pub next_after: Option<MeasurePhase>,
    /// `true` to call `cx.quit()` after the final phase finishes (`--measure` CLI).
    pub quit_on_finish: bool,
}

/// Starts a 10-second `on_next_frame` scroll benchmark over either the list or code pane.
///
/// # Arguments
///
/// * `spec` - Scroll target, item counts, chaining, and completion behavior.
/// * `window` - Window driving frame callbacks.
/// * `cx` - Application context activated for foreground vsync pacing.
pub fn start_scroll_run(spec: ScrollRunSpec, window: &mut Window, cx: &mut App) {
    cx.activate(true);
    window.activate_window();
    let state = Rc::new(RefCell::new(ScrollLoopState {
        warmup_left: 8,
        before_snap: None,
        started_at: None,
        prev_frame: None,
        scroll_ix: 0,
        intervals_ns: Vec::with_capacity(2048),
    }));
    schedule_scroll_step(spec, state, window);
}

/// Schedules one frame step of [`start_scroll_run`] and recurses until 10 seconds elapse.
///
/// # Arguments
///
/// * `spec` - Active [`ScrollRunSpec`].
/// * `state` - Shared [`ScrollLoopState`] across frames.
/// * `window` - Window registering the next-frame callback.
fn schedule_scroll_step(
    spec: ScrollRunSpec,
    state: Rc<RefCell<ScrollLoopState>>,
    window: &mut Window,
) {
    window.on_next_frame(move |window, cx| {
        if !spec
            .view_entity
            .read(cx)
            .is_measure_current(spec.ticket, &spec.cancel)
        {
            return;
        }
        let now = now_instant();
        let mut finished_before = None;
        let mut finished_intervals = Vec::new();
        {
            let mut st = state.borrow_mut();
            if st.warmup_left > 0 {
                st.warmup_left -= 1;
                if st.warmup_left == 0 {
                    st.before_snap = Some(window.frame_duration_snapshot());
                    st.started_at = Some(now);
                    st.prev_frame = Some(now);
                }
            } else {
                if let Some(prev) = st.prev_frame.replace(now) {
                    let ns = u64::try_from(now.duration_since(prev).as_nanos()).unwrap_or(u64::MAX);
                    st.intervals_ns.push(ns);
                }
                if st
                    .started_at
                    .is_some_and(|t0| now.duration_since(t0) >= SCROLL_DURATION)
                {
                    finished_before = st.before_snap.take();
                    finished_intervals = std::mem::take(&mut st.intervals_ns);
                }
            }
            st.scroll_ix = (st.scroll_ix + SCROLL_STEP_PER_FRAME) % spec.virtual_items.max(1);
            let target = st.scroll_ix;
            let is_code = spec.is_code;
            spec.view_entity.update(cx, |view, cx| {
                if is_code {
                    view.scroll_code_to(target, ScrollStrategy::Top);
                } else {
                    view.scroll_table_to(target, ScrollStrategy::Top, cx);
                }
                cx.notify();
            });
        }

        if let Some(before) = finished_before {
            let after = window.frame_duration_snapshot();
            let kind = if spec.is_code { "code" } else { "list" };
            print_scroll_report(
                kind,
                &spec.source_label,
                spec.base_items,
                spec.virtual_items,
                &before,
                &after,
                &mut finished_intervals,
            );
            if spec.next_after == Some(MeasurePhase::CodeScroll) {
                let quit_on_finish = spec.quit_on_finish;
                spec.view_entity.update(cx, |view, cx| {
                    begin_code_scroll_phase(view, quit_on_finish, window, cx);
                });
            } else if spec.quit_on_finish {
                cx.quit();
            } else {
                spec.view_entity.update(cx, |view, cx| {
                    view.cancel_measure();
                    cx.notify();
                });
            }
            return;
        }
        schedule_scroll_step(spec, state, window);
    });
}

/// Spawns background preparation for the 100k-row list scroll phase and starts scrolling.
///
/// # Arguments
///
/// * `view` - Root [`AppView`] hosting the benchmark.
/// * `chain_code` - `true` to chain the 1M-line code scroll immediately afterward.
/// * `quit_on_finish` - `true` when invoked from `--measure` CLI, `false` for interactive action.
/// * `window` - Window driving frame callbacks.
/// * `cx` - View context.
pub fn begin_list_scroll_phase(
    view: &mut AppView,
    chain_code: bool,
    quit_on_finish: bool,
    window: &mut Window,
    cx: &mut Context<'_, AppView>,
) {
    let (ticket, worker_cancel) = view.begin_measure();
    let check_cancel = worker_cancel.clone();
    let bg = spawn_engine(cx, move || load_large_dll_blocking(&worker_cancel));
    let next_phase = chain_code.then_some(MeasurePhase::CodeScroll);
    let task = cx.spawn_in(window, async move |this, cx| {
        let ready = bg.await;
        let _ = this.update_in(cx, |view, window, cx| {
            if !view.is_measure_current(ticket, &check_cancel) {
                return;
            }
            match ready {
                Ok(info) => {
                    let source =
                        format!("{} ({:.2}s)", info.loaded.path.display(), info.analyze_secs);
                    let base_rows = info.base_rows;
                    view.install_virtual_list(info.loaded, TARGET_LIST_ROWS, cx);
                    let entity = cx.entity();
                    start_scroll_run(
                        ScrollRunSpec {
                            view_entity: entity,
                            ticket,
                            cancel: check_cancel,
                            is_code: false,
                            source_label: source,
                            base_items: base_rows,
                            virtual_items: TARGET_LIST_ROWS,
                            next_after: next_phase,
                            quit_on_finish,
                        },
                        window,
                        cx,
                    );
                }
                Err(err) => {
                    if quit_on_finish {
                        view.fail_cli(err.context("list scroll load failed"), cx);
                    } else {
                        view.finish_interactive_measure_error(
                            format!("list scroll load failed: {err:#}"),
                            cx,
                        );
                    }
                }
            }
        });
    });
    view.set_measure_task(task);
}

/// Spawns background preparation for the 1M-line code scroll phase and starts scrolling.
///
/// # Arguments
///
/// * `view` - Root [`AppView`] hosting the benchmark.
/// * `quit_on_finish` - `true` when invoked from `--measure` CLI, `false` for interactive action.
/// * `window` - Window driving frame callbacks.
/// * `cx` - View context.
pub fn begin_code_scroll_phase(
    view: &mut AppView,
    quit_on_finish: bool,
    window: &mut Window,
    cx: &mut Context<'_, AppView>,
) {
    let (ticket, worker_cancel) = view.begin_measure();
    let check_cancel = worker_cancel.clone();
    let bg = spawn_engine(cx, move || {
        build_corpus_code_blocking(Path::new(SYSTEM_NOTEPAD), &worker_cancel)
    });
    let task = cx.spawn_in(window, async move |this, cx| {
        let ready = bg.await;
        let _ = this.update_in(cx, |view, window, cx| {
            if !view.is_measure_current(ticket, &check_cancel) {
                return;
            }
            match ready {
                Ok((loaded, corpus)) => {
                    let base_lines = corpus.lines.len();
                    let source = corpus.source_path.display().to_string();
                    view.install_corpus_code(loaded, corpus, cx);
                    let entity = cx.entity();
                    start_scroll_run(
                        ScrollRunSpec {
                            view_entity: entity,
                            ticket,
                            cancel: check_cancel,
                            is_code: true,
                            source_label: source,
                            base_items: base_lines,
                            virtual_items: TARGET_CODE_LINES,
                            next_after: None,
                            quit_on_finish,
                        },
                        window,
                        cx,
                    );
                }
                Err(err) => {
                    if quit_on_finish {
                        view.fail_cli(err.context("code scroll load failed"), cx);
                    } else {
                        view.finish_interactive_measure_error(
                            format!("code scroll load failed: {err:#}"),
                            cx,
                        );
                    }
                }
            }
        });
    });
    view.set_measure_task(task);
}

/// Runs the `--measure --phase input` Win32 `SendInput` coordination loop inside GPUI.
///
/// # Arguments
///
/// * `view` - Root [`AppView`] hosting the benchmark.
/// * `window` - Window receiving real OS keyboard and mouse events.
/// * `cx` - View context.
pub fn begin_input_latency_phase(
    view: &mut AppView,
    window: &mut Window,
    cx: &mut Context<'_, AppView>,
) {
    let (ticket, worker_cancel) = view.begin_measure();
    let check_cancel = worker_cancel.clone();
    let inject_mark = spawn_inject_marker(worker_cancel.clone());
    view.set_inject_mark(Some(inject_mark));
    cx.activate(true);
    window.activate_window();
    let bg = spawn_engine(cx, move || -> anyhow::Result<_> {
        worker_cancel.within(|| {
            let loaded = load_binary_blocking(PathBuf::from(SYSTEM_NOTEPAD))?;
            let preferred = pick_function_with_callees(&loaded).ok_or_else(|| {
                anyhow::anyhow!("{SYSTEM_NOTEPAD} has no function with a visible call token")
            })?;
            Ok((loaded, preferred))
        })
    });
    let task = cx.spawn_in(window, async move |this, cx| {
        let outcome = bg.await;
        let _ = this.update_in(cx, |view, window, cx| {
            if !view.is_measure_current(ticket, &check_cancel) {
                return;
            }
            match outcome {
                Ok((loaded, preferred)) => {
                    view.install_for_input_bench(loaded, preferred, window, cx);
                    let entity = cx.entity();
                    let was_trace_enabled = gpui::profiler::set_trace_enabled(true);
                    let collector = gpui::profiler::FrameTimingCollector::new();
                    let before = window.input_latency_snapshot();
                    let state = Rc::new(RefCell::new(InputBenchState {
                        ticket,
                        cancel: check_cancel,
                        window_id: window.window_handle().window_id(),
                        was_trace_enabled,
                        collector,
                        pending_draw_start: None,
                        before,
                        retired_samples: Vec::with_capacity(512),
                        filter_announced: false,
                        targets: CallTargetTracker::new(),
                        empty_frames: 0,
                        settle_frames: 0,
                    }));
                    poll_input_bench_step(entity, state, window);
                }
                Err(err) => {
                    view.fail_cli(err.context("input latency load failed"), cx);
                }
            }
        });
    });
    view.set_measure_task(task);
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
fn spawn_inject_marker(cancel: Cancel) -> InjectMark {
    let mark: InjectMark = Arc::new(InjectTracker::default());
    let shared = mark.clone();
    std::thread::spawn(move || {
        let stdin = std::io::stdin();
        let mut line = String::new();
        while !cancel.is_raised() {
            line.clear();
            let Ok(n) = stdin.lock().read_line(&mut line) else {
                break;
            };
            if n == 0 {
                break;
            }
            let trimmed = line.trim();
            if trimmed == "MARK" {
                shared.arm(0, now_instant());
                let mut out = std::io::stdout().lock();
                let _ = writeln!(out, "MARK_OK");
                let _ = out.flush();
            } else if let Some(rest) = trimmed.strip_prefix("MARK ") {
                if let Ok(id) = rest.trim().parse::<u64>() {
                    shared.arm(id, now_instant());
                    let mut out = std::io::stdout().lock();
                    let _ = writeln!(out, "MARK_OK {id}");
                    let _ = out.flush();
                }
            } else if let Some(rest) = trimmed.strip_prefix("SENT ") {
                let mut parts = rest.split_whitespace();
                if let (Some(id_str), Some(delta_str)) = (parts.next(), parts.next())
                    && let (Ok(id), Ok(delta_ns)) =
                        (id_str.parse::<u64>(), delta_str.parse::<u64>())
                {
                    shared.record_sent_offset(id, delta_ns);
                }
            }
        }
    });
    mark
}

/// Action selected for a frame where a clickable call token is visible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TargetDecision {
    /// Print `CALL_TARGET` so the controller injects the next click.
    Emit,
    /// Keep waiting for an already-announced click to complete.
    Wait,
    /// Abort cleanly after exhausting bounded re-announcements without click progress.
    Abort,
}

/// Tracks `CALL_TARGET` announcements, recovery re-announcements, and bounded click retries.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CallTargetTracker {
    /// Click count most recently announced on `CALL_TARGET`, if any.
    last_reported_clicks: Option<u64>,
    /// Timestamp when [`Self::last_reported_clicks`] was last announced.
    last_reported_at: Option<Instant>,
    /// Whether `navigate_back` recovery requires re-announcing a visible target at the same count.
    reannounce_after_back: bool,
    /// Consecutive re-announcements emitted without `clicks` advancing.
    retries_at_count: u8,
    /// Consecutive `navigate_back` recoveries without `clicks` advancing.
    stalled_backs: u8,
}

impl CallTargetTracker {
    /// Creates an idle [`CallTargetTracker`] prior to the first `CALL_TARGET` emission.
    ///
    /// # Returns
    ///
    /// Initialized [`CallTargetTracker`].
    const fn new() -> Self {
        Self {
            last_reported_clicks: None,
            last_reported_at: None,
            reannounce_after_back: false,
            retries_at_count: 0,
            stalled_backs: 0,
        }
    }

    /// Decides whether to emit `CALL_TARGET`, wait, or abort when a call token is visible.
    ///
    /// # Arguments
    ///
    /// * `clicks` - Current [`AppView::call_clicks`] count.
    /// * `now` - Current [`Instant`].
    ///
    /// # Returns
    ///
    /// [`TargetDecision`] governing the current frame.
    fn decide_visible(&mut self, clicks: u64, now: Instant) -> TargetDecision {
        if self.last_reported_clicks != Some(clicks) {
            self.last_reported_clicks = Some(clicks);
            self.last_reported_at = Some(now);
            self.reannounce_after_back = false;
            self.retries_at_count = 0;
            self.stalled_backs = 0;
            return TargetDecision::Emit;
        }
        let timed_out = self
            .last_reported_at
            .is_some_and(|t| now.saturating_duration_since(t) >= Duration::from_secs(1));
        if !self.reannounce_after_back && !timed_out {
            return TargetDecision::Wait;
        }
        if self.retries_at_count >= 8 {
            return TargetDecision::Abort;
        }
        self.retries_at_count = self.retries_at_count.saturating_add(1);
        self.reannounce_after_back = false;
        self.last_reported_at = Some(now);
        TargetDecision::Emit
    }

    /// Records a `navigate_back` recovery step when a callee view lacks visible call tokens.
    ///
    /// # Arguments
    ///
    /// * `can_go_back` - Whether [`AppView::can_go_back`] permits stepping back.
    ///
    /// # Returns
    ///
    /// `true` when recovery may call `navigate_back`, `false` when recovery attempts are exhausted.
    fn note_back(&mut self, can_go_back: bool) -> bool {
        if !can_go_back || self.stalled_backs >= 8 {
            return false;
        }
        self.stalled_backs = self.stalled_backs.saturating_add(1);
        self.reannounce_after_back = true;
        true
    }
}

/// Unadjusted latency durations captured when a [`PendingInputMark`] is presented.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RetiredInputSample {
    /// Monotonic controller event identifier (`0` when unnumbered).
    id: u64,
    /// Elapsed nanoseconds from `MARK` to GPUI event arrival (`arrived_at - injected_at`).
    raw_queue_ns: u64,
    /// Elapsed nanoseconds from `MARK` to frame presentation (`present_end - injected_at`).
    raw_e2e_ns: u64,
}

/// Mutable state shared across `on_next_frame` callbacks in `--measure --phase input`.
struct InputBenchState {
    /// Measurement generation ticket owning this input benchmark.
    ticket: u64,
    /// Cooperative [`Cancel`] flag owning this input benchmark.
    cancel: Cancel,
    /// Target [`gpui::WindowId`] filtering profiler [`gpui::profiler::FrameEvent`] entries.
    window_id: gpui::WindowId,
    /// Whether GPUI profiler tracing was already enabled before this run started.
    was_trace_enabled: bool,
    /// Cursor draining newly recorded [`gpui::profiler::FrameEvent`] entries.
    collector: gpui::profiler::FrameTimingCollector,
    /// Start timestamp of the latest `Window::draw` awaiting presentation.
    pending_draw_start: Option<Instant>,
    /// Baseline snapshot captured before input injection started.
    before: gpui::profiler::InputLatencySnapshot,
    /// Presented input samples awaiting final `SENT <id> <delta_ns>` adjustment.
    retired_samples: Vec<RetiredInputSample>,
    /// `true` once `INPUT_FILTER_READY` has been printed.
    filter_announced: bool,
    /// `CALL_TARGET` emission and recovery state machine.
    targets: CallTargetTracker,
    /// Consecutive frames where the opened callee lacked a visible call token.
    empty_frames: u8,
    /// Post-completion frames awaited so the 100th click's presentation is captured.
    settle_frames: u8,
}

impl Drop for InputBenchState {
    fn drop(&mut self) {
        if !self.was_trace_enabled {
            gpui::profiler::set_trace_enabled(false);
        }
    }
}

/// Retires every ready [`PendingInputMark`] included in newly presented frames for `window_id`.
///
/// A mark retires only when [`PendingInputMark::ready_at`] is `Some(ready)` with
/// `ready <= draw_start`, so loading frames never retire marks awaiting background filter or
/// decompile completion.
///
/// # Arguments
///
/// * `pending_marks` - Queue of unpresented [`PendingInputMark`] entries.
/// * `pending_draw_start` - Latest `draw_start` observed for `window_id` prior to `Present`.
/// * `window_id` - Window whose draw/present events are being retired.
/// * `events` - Newly drained [`gpui::profiler::FrameEvent`] slice.
/// * `retired_out` - Destination buffer receiving unadjusted [`RetiredInputSample`] records.
fn retire_presented_marks(
    pending_marks: &mut VecDeque<PendingInputMark>,
    pending_draw_start: &mut Option<Instant>,
    window_id: gpui::WindowId,
    events: &[gpui::profiler::FrameEvent],
    retired_out: &mut Vec<RetiredInputSample>,
) {
    for event in events {
        match event {
            gpui::profiler::FrameEvent::Draw(draw) if draw.window_id == window_id => {
                *pending_draw_start = Some(draw.draw_start);
            }
            gpui::profiler::FrameEvent::Present(present) if present.window_id == window_id => {
                let cutoff = pending_draw_start.take().unwrap_or(present.present_start);
                pending_marks.retain(|mark| {
                    let Some(ready) = mark.ready_at else {
                        return true;
                    };
                    if ready > cutoff {
                        return true;
                    }
                    let raw_queue_ns = u64::try_from(
                        mark.arrived_at
                            .saturating_duration_since(mark.injected_at)
                            .as_nanos(),
                    )
                    .unwrap_or(u64::MAX);
                    let raw_e2e_ns = u64::try_from(
                        present
                            .present_end
                            .saturating_duration_since(mark.injected_at)
                            .as_nanos(),
                    )
                    .unwrap_or(u64::MAX);
                    retired_out.push(RetiredInputSample {
                        id: mark.id,
                        raw_queue_ns,
                        raw_e2e_ns,
                    });
                    false
                });
            }
            gpui::profiler::FrameEvent::Draw(_) | gpui::profiler::FrameEvent::Present(_) => {}
        }
    }
}

/// Adjusts retired input samples by subtracting each event's post-`MARK_OK` `SendInput` offset.
///
/// # Arguments
///
/// * `samples` - Retired `(id, raw_queue_ns, raw_e2e_ns)` records in presentation order.
/// * `tracker` - Optional [`InjectTracker`] holding `SENT <id> <delta_ns>` controller offsets.
///
/// # Returns
///
/// `(queue_samples_ns, e2e_samples_ns)` anchored to `SendInput` and clamped at `arrived_at`.
fn apply_sent_offsets(
    samples: &[RetiredInputSample],
    tracker: Option<&InjectTracker>,
) -> (Vec<u64>, Vec<u64>) {
    let mut queue_out = Vec::with_capacity(samples.len());
    let mut e2e_out = Vec::with_capacity(samples.len());
    for sample in samples {
        let delta_ns = tracker
            .and_then(|t| t.take_sent_offset(sample.id))
            .unwrap_or(0)
            .min(sample.raw_queue_ns);
        queue_out.push(sample.raw_queue_ns.saturating_sub(delta_ns));
        e2e_out.push(sample.raw_e2e_ns.saturating_sub(delta_ns));
    }
    (queue_out, e2e_out)
}

/// Drains newly presented [`gpui::profiler::FrameEvent`] records and retires matched input marks.
///
/// # Arguments
///
/// * `st` - Active [`InputBenchState`].
/// * `entity` - Root [`AppView`] holding [`PendingInputMark`] records.
/// * `cx` - Application context updating `entity`.
fn record_frame_input_samples(
    st: &mut InputBenchState,
    entity: &gpui::Entity<AppView>,
    cx: &mut App,
) {
    let events = st.collector.collect_unseen();
    if events.is_empty() {
        return;
    }
    let window_id = st.window_id;
    let pending_draw_start = &mut st.pending_draw_start;
    let retired_out = &mut st.retired_samples;
    entity.update(cx, |view, _| {
        retire_presented_marks(
            view.pending_marks_mut(),
            pending_draw_start,
            window_id,
            &events,
            retired_out,
        );
    });
}

/// Selects a function entry in `loaded` whose top lines contain a clickable `Ref::Function` call.
///
/// Must be called on the background engine executor before installing the input benchmark.
///
/// # Arguments
///
/// * `loaded` - Analyzed binary state.
///
/// # Returns
///
/// Entry address of a function with a visible `Ref::Function` token near line 0, or `None` when
/// no function in `loaded` exposes one.
fn pick_function_with_callees(loaded: &LoadedBinary) -> Option<u64> {
    for f in &loaded.analysis.functions {
        if f.thunk.is_some() || f.callees.is_empty() || f.blocks.len() < 2 {
            continue;
        }
        let Some(v) =
            build_decompile_view(&loaded.program, &loaded.analysis, &loaded.overlay, f.entry)
        else {
            continue;
        };
        let top = v.lines().min(15);
        let has_top_call = (0..top).any(|line_ix| {
            v.tokens(line_ix)
                .any(|(_, _, r)| matches!(r, Some(Ref::Function(t)) if *t != f.entry))
        });
        if has_top_call {
            return Some(f.entry);
        }
    }
    None
}

/// Polls progress of the 200 filter keystrokes and 100 call-token clicks across frames.
///
/// # Arguments
///
/// * `entity` - Target [`AppView`] entity.
/// * `state` - Shared [`InputBenchState`] tracking progress and latency samples.
/// * `window` - Window scheduling the next-frame callback.
fn poll_input_bench_step(
    entity: gpui::Entity<AppView>,
    state: Rc<RefCell<InputBenchState>>,
    window: &mut Window,
) {
    window.on_next_frame(move |window, cx| {
        {
            let st = state.borrow();
            if !entity.read(cx).is_measure_current(st.ticket, &st.cancel) {
                return;
            }
        }
        {
            let mut st = state.borrow_mut();
            record_frame_input_samples(&mut st, &entity, cx);
        }
        let mut done = false;
        let mut aborted = false;

        entity.update(cx, |view, cx| {
            if !view.has_active_view() {
                cx.notify();
                return;
            }
            let mut st = state.borrow_mut();
            if !st.filter_announced {
                st.filter_announced = true;
                let pid = std::process::id();
                let mut out = std::io::stdout().lock();
                let _ = writeln!(out, "INPUT_FILTER_READY pid={pid}");
                let _ = out.flush();
                return;
            }
            if view.filter_keys_handled() < 200 {
                return;
            }
            if view.decompile_in_flight() {
                st.empty_frames = 0;
                cx.notify();
                return;
            }
            let clicks = view.call_clicks();
            if clicks >= 100 {
                st.settle_frames = st.settle_frames.saturating_add(1);
                if (!view.has_pending_marks() && st.settle_frames >= 2) || st.settle_frames >= 10 {
                    done = true;
                } else {
                    cx.notify();
                }
                return;
            }
            if let Some((lx, ly)) = view.call_token_client_xy() {
                st.empty_frames = 0;
                match st.targets.decide_visible(clicks, now_instant()) {
                    TargetDecision::Emit => {
                        let mut out = std::io::stdout().lock();
                        let _ = writeln!(out, "CALL_TARGET x={lx:.2} y={ly:.2} clicks={clicks}");
                        let _ = out.flush();
                    }
                    TargetDecision::Wait => {
                        cx.notify();
                    }
                    TargetDecision::Abort => {
                        aborted = true;
                        view.fail_cli(
                            anyhow::anyhow!(
                                "input latency benchmark stalled at click {clicks} after 8 retries"
                            ),
                            cx,
                        );
                    }
                }
            } else {
                st.empty_frames = st.empty_frames.saturating_add(1);
                if st.empty_frames >= 3 {
                    st.empty_frames = 0;
                    if st.targets.note_back(view.can_go_back()) {
                        view.clear_dispatch_mark();
                        view.navigate_back(cx);
                    } else {
                        aborted = true;
                        view.fail_cli(
                            anyhow::anyhow!(
                                "input latency benchmark lost visible call target after {clicks} clicks"
                            ),
                            cx,
                        );
                    }
                } else {
                    cx.notify();
                }
            }
        });

        if aborted {
            return;
        }
        if done {
            print_input_report(&state.borrow(), &entity, window, cx);
            cx.quit();
            return;
        }
        poll_input_bench_step(entity, state, window);
    });
}

/// Prints the `MEASURE_INPUT` quantile summary line once 100 clicks complete.
///
/// # Arguments
///
/// * `st` - Completed [`InputBenchState`] holding end-to-end and queue-delay samples.
/// * `entity` - Target [`AppView`] entity holding keystroke and click counters.
/// * `window` - Window providing the post-run input-latency snapshot.
/// * `cx` - Application context reading `entity`.
fn print_input_report(
    st: &InputBenchState,
    entity: &gpui::Entity<AppView>,
    window: &Window,
    cx: &App,
) {
    let after = window.input_latency_snapshot();
    let mut lat = after.latency_histogram.clone();
    let _ = lat.subtract(&st.before.latency_histogram);
    let v = entity.read(cx);
    let (mut queue_samples_ns, mut e2e_samples_ns) =
        apply_sent_offsets(&st.retired_samples, v.inject_tracker().map(Arc::as_ref));
    let (ep50, ep95, ep99, emax, ecount) = if e2e_samples_ns.is_empty() {
        (
            ns_to_ms(lat.value_at_quantile(0.50)),
            ns_to_ms(lat.value_at_quantile(0.95)),
            ns_to_ms(lat.value_at_quantile(0.99)),
            ns_to_ms(lat.max()),
            lat.len(),
        )
    } else {
        sorted_quantiles_ms(&mut e2e_samples_ns)
    };
    let (qp50, qp95, qp99, qmax, qcount) = sorted_quantiles_ms(&mut queue_samples_ns);
    let (keys, clicks) = (v.filter_keys_handled(), v.call_clicks());
    let mut out = std::io::stdout().lock();
    let _ = writeln!(
        out,
        "MEASURE_INPUT samples={ecount} p50_ms={ep50:.3} p95_ms={ep95:.3} p99_ms={ep99:.3} max_ms={emax:.3} \
queue_samples={qcount} queue_p50_ms={qp50:.3} queue_p95_ms={qp95:.3} queue_p99_ms={qp99:.3} queue_max_ms={qmax:.3} \
gpui_samples={} gpui_p50_ms={:.3} gpui_p95_ms={:.3} gpui_p99_ms={:.3} gpui_max_ms={:.3} \
filter_keys={keys} call_clicks={clicks} mid_draw_dropped={} ui_engine_calls={}",
        lat.len(),
        ns_to_ms(lat.value_at_quantile(0.50)),
        ns_to_ms(lat.value_at_quantile(0.95)),
        ns_to_ms(lat.value_at_quantile(0.99)),
        ns_to_ms(lat.max()),
        after
            .mid_draw_events_dropped
            .saturating_sub(st.before.mid_draw_events_dropped),
        ui_engine_calls(),
    );
    let _ = out.flush();
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    use borer_engine::cancel::Cancel;

    use super::{
        CallTargetTracker, CliMode, InjectTracker, MarkWait, OneShotAction, PendingInputMark,
        TargetDecision, apply_sent_offsets, build_corpus_code_blocking, evaluate_one_shot,
        load_large_dll_blocking, now_instant, parse_cli_args_os, retire_presented_marks,
    };

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

    /// Event-associated retirement preserves exact per-event totals across multi-frame batches.
    ///
    /// # Panics
    ///
    /// Panics if `(queue=1ms, gpui=100ms)` and `(queue=100ms, gpui=1ms)` are mispaired as `2ms`
    /// and `200ms` instead of `101ms` each, or if a post-draw arrival is retired early.
    #[test]
    fn event_associated_retirement_preserves_exact_per_event_totals() {
        let win = gpui::WindowId::from(7);
        let t0 = now_instant();
        let ms = |n: u64| t0 + Duration::from_millis(n);
        let mut pending = VecDeque::from([
            PendingInputMark {
                id: 1,
                injected_at: ms(0),
                arrived_at: ms(1),
                ready_at: Some(ms(1)),
                wait: MarkWait::Immediate,
            },
            PendingInputMark {
                id: 2,
                injected_at: ms(200),
                arrived_at: ms(300),
                ready_at: Some(ms(300)),
                wait: MarkWait::Immediate,
            },
            PendingInputMark {
                id: 3,
                injected_at: ms(301),
                arrived_at: ms(302),
                ready_at: Some(ms(302)),
                wait: MarkWait::Immediate,
            },
        ]);
        let events = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(1)),
                invalidations: 1,
                draw_start: ms(2),
                draw_end: ms(50),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(50),
                present_end: ms(101),
                animation_interval: None,
            }),
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(300)),
                invalidations: 1,
                draw_start: ms(300),
                draw_end: ms(301),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(301),
                present_end: ms(301),
                animation_interval: None,
            }),
        ];
        let mut draw_start = None;
        let mut retired = Vec::new();
        retire_presented_marks(&mut pending, &mut draw_start, win, &events, &mut retired);
        let (queue_out, e2e_out) = apply_sent_offsets(&retired, None);
        assert_eq!(queue_out, vec![1_000_000, 100_000_000]);
        assert_eq!(e2e_out, vec![101_000_000, 101_000_000]);
        assert_eq!(pending.len(), 1);
    }

    /// Loading frames never retire marks awaiting background filter/decompile completion, and
    /// `SENT` offsets anchor latency at `SendInput` rather than `MARK`.
    ///
    /// # Panics
    ///
    /// Panics if an unready mark (`ready_at: None`) retires on an intermediate loading frame or if
    /// `InjectTracker` fails to subtract and clamp the post-`MARK_OK` `SendInput` offset.
    #[test]
    fn loading_frames_hold_async_marks_and_sent_offsets_anchor_to_sendinput() {
        let win = gpui::WindowId::from(9);
        let t0 = now_instant();
        let ms = |n: u64| t0 + Duration::from_millis(n);
        let mut pending = VecDeque::from([PendingInputMark {
            id: 42,
            injected_at: ms(0),
            arrived_at: ms(5),
            ready_at: None,
            wait: MarkWait::Decompile(1),
        }]);
        let loading_frame = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(5)),
                invalidations: 1,
                draw_start: ms(6),
                draw_end: ms(7),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(7),
                present_end: ms(8),
                animation_interval: None,
            }),
        ];
        let mut draw_start = None;
        let mut retired = Vec::new();
        retire_presented_marks(
            &mut pending,
            &mut draw_start,
            win,
            &loading_frame,
            &mut retired,
        );
        assert!(retired.is_empty());
        assert_eq!(pending.len(), 1);

        pending[0].ready_at = Some(ms(15));
        pending[0].wait = MarkWait::Immediate;
        let final_frame = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(15)),
                invalidations: 1,
                draw_start: ms(16),
                draw_end: ms(18),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(18),
                present_end: ms(20),
                animation_interval: None,
            }),
        ];
        retire_presented_marks(
            &mut pending,
            &mut draw_start,
            win,
            &final_frame,
            &mut retired,
        );
        assert!(pending.is_empty());
        let tracker = InjectTracker::default();
        tracker.record_sent_offset(42, 3_000_000);
        let (queue_out, e2e_out) = apply_sent_offsets(&retired, Some(&tracker));
        assert_eq!(queue_out, vec![2_000_000]);
        assert_eq!(e2e_out, vec![17_000_000]);
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

    /// `CallTargetTracker` re-announces targets after `navigate_back` or missed clicks and caps retries.
    ///
    /// # Panics
    ///
    /// Panics if recovery suppresses `CALL_TARGET` at an unchanged click count or retries unboundedly.
    #[test]
    fn call_target_tracker_reannounces_after_recovery_and_caps_retries() {
        let t0 = now_instant();
        let mut tracker = CallTargetTracker::new();
        assert_eq!(tracker.decide_visible(0, t0), TargetDecision::Emit);
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(20)),
            TargetDecision::Wait
        );
        assert!(tracker.note_back(true));
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(30)),
            TargetDecision::Emit
        );
        for step in 1..8_u64 {
            assert_eq!(
                tracker.decide_visible(0, t0 + Duration::from_millis(1100 * step)),
                TargetDecision::Emit
            );
        }
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(9000)),
            TargetDecision::Abort
        );
        assert_eq!(
            tracker.decide_visible(1, t0 + Duration::from_millis(9010)),
            TargetDecision::Emit
        );
    }
}
