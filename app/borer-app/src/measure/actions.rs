//! The actions phase: a fixed script of actions on notepad, then on the large DLL.
//!
//! Each action is dispatched through the path its key takes and timed to its first
//! visible change (ack) and to settled views (settle); then a pan and a zoom sweep run
//! over large graphs, timed frame by frame.
//!
//! Every run starts from a cleared window, sets its action up through the same paths and
//! waits for it to settle, untimed; only its last step is timed. The targets are the
//! engine's: the first functions by address that call others, and the first call token of
//! each, never picked by time or chance. A large DLL that is missing or too slow to analyze
//! is reported as skipped.

use std::collections::{BTreeMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};

use borer_engine::analysis::render::FunctionRow;
use borer_engine::cancel::Cancel;
use borer_engine::num::as_f64;
use borer_engine::view::Ref;
use editor::SelectionEffects;
use gpui::{
    Action, Context, Keystroke, Modifiers, PlatformInput, ScrollDelta, ScrollEvent, Window,
    WindowId, point, px,
};
use language::Point;
use picker::Picker;

use super::tree::quantiles;
use super::watch::{Seen, Watch, seen};
use super::{
    Harness, Prepared, SYSTEM_NOTEPAD, Tracing, load_large_dll_blocking, nanos, now_instant, say,
    sorted_quantiles_ms,
};
use crate::actions::{FocusFilter, Overview, ShowGraph, ToggleListing, Xrefs, ZoomIn, ZoomOut};
use crate::code_view::CodeLines;
use crate::decompile_item::Form;
use crate::goto::{FindEverywhere, GoTo, GoToDelegate};
use crate::graph_item::GraphItem;
use crate::places::{PERMANENT, Place, open};
use crate::worker::{LoadedBinary, Sources, load_binary_blocking, ui_engine_calls};

/// Timed runs of each action on each binary.
const RUNS: usize = 50;

/// Most a timed step may take to settle; one slower is counted late at this time.
const LATE: Duration = Duration::from_secs(10);

/// Most a run's untimed setup may take to settle before the run is skipped.
const SETUP_LIMIT: Duration = Duration::from_secs(60);

/// How long each pan or zoom sweep runs on one graph.
const SWEEP: Duration = Duration::from_secs(2);

/// Notepad's largest functions the graph sweeps run on; the large DLL's largest only.
const NOTEPAD_GRAPHS: usize = 20;

/// Frames each pan or zoom direction lasts before the sweep turns.
const TURN_FRAMES: u32 = 30;

/// Pixels each frame of a pan sweep moves the graph.
const PAN_STEP: f32 = 40.0;

/// One action the phase times.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Act {
    /// Go to a function by name: the go-to picker's confirm.
    GoTo,
    /// One keystroke typed into Find Everywhere.
    Find,
    /// Xrefs (`x`) on a call token.
    Xrefs,
    /// Toggle a code tab to its listing, both built before.
    Listing,
    /// Open the graph of a code tab's function, built before.
    Graph,
    /// One keystroke typed into the functions filter.
    Filter,
    /// Open the overview.
    Overview,
    /// Go back to the function before.
    Back,
}

impl Act {
    /// Every action, in the order the script runs them.
    pub(super) const ALL: [Self; 8] = [
        Self::GoTo,
        Self::Find,
        Self::Xrefs,
        Self::Listing,
        Self::Graph,
        Self::Filter,
        Self::Overview,
        Self::Back,
    ];

    /// Returns the action's name in the report.
    pub(super) const fn word(self) -> &'static str {
        match self {
            Self::GoTo => "goto",
            Self::Find => "find",
            Self::Xrefs => "xrefs",
            Self::Listing => "listing",
            Self::Graph => "graph",
            Self::Filter => "filter",
            Self::Overview => "overview",
            Self::Back => "back",
        }
    }
}

/// One graph sweep the phase times frame by frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Sweep {
    /// Scroll-wheel pans, turning every [`TURN_FRAMES`].
    Pan,
    /// Zoom in and out, turning every [`TURN_FRAMES`].
    Zoom,
}

impl Sweep {
    /// Returns the sweep's name in the report.
    pub(super) const fn word(self) -> &'static str {
        match self {
            Self::Pan => "pan",
            Self::Zoom => "zoom",
        }
    }
}

/// Which binary a run is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Bench {
    /// The system's `notepad.exe`.
    Notepad,
    /// The large DLL the list scroll loads.
    Large,
}

impl Bench {
    /// Returns the binary's name in the report.
    pub(super) const fn word(self) -> &'static str {
        match self {
            Self::Notepad => "notepad",
            Self::Large => "large",
        }
    }
}

/// A function an action runs on: its entry and the name the engine gives it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Target {
    /// Entry virtual address.
    entry: u64,
    /// The name in force.
    name: String,
}

/// A binary the phase runs on, and what the engine's order picks in it.
#[derive(Debug)]
pub(super) struct Prep {
    /// Which binary it is.
    bench: Bench,
    /// The binary, analyzed.
    pub(super) loaded: Arc<LoadedBinary>,
    /// The functions the actions run on, one more than [`RUNS`] when there are so many.
    targets: Vec<Target>,
    /// The functions the graph sweeps run on.
    largest: Vec<u64>,
}

/// Returns the first `n` rows that call another function, in the rows' order, which is the
/// engine's address order.
///
/// # Arguments
///
/// * `rows` - The function table's rows.
/// * `n` - Most targets.
pub(super) fn pick_targets(rows: &[FunctionRow], n: usize) -> Vec<Target> {
    rows.iter()
        .filter(|row| row.callees > 0)
        .take(n)
        .map(|row| Target {
            entry: row.entry,
            name: row.name.clone(),
        })
        .collect()
}

/// Returns the entries of the `n` largest functions, the lowest entry first among equals.
///
/// # Arguments
///
/// * `rows` - The function table's rows.
/// * `n` - Most functions.
pub(super) fn largest(rows: &[FunctionRow], n: usize) -> Vec<u64> {
    let mut sized: Vec<(u64, u64)> = rows.iter().map(|row| (row.size, row.entry)).collect();
    sized.sort_by_key(|&(size, entry)| (std::cmp::Reverse(size), entry));
    sized.into_iter().take(n).map(|(_, entry)| entry).collect()
}

/// Returns the shown line and byte of the first token of `code` calling a function other
/// than `entry`.
///
/// # Arguments
///
/// * `code` - The lines a code tab shows.
/// * `entry` - The function the tab shows.
pub(super) fn first_call(code: &CodeLines, entry: u64) -> Option<(usize, usize)> {
    (0..code.len()).find_map(|row| {
        let (view, line) = code.get(row)?;
        view.tokens(line).find_map(|(span, _, link)| {
            matches!(link, Some(Ref::Function(to)) if *to != entry).then_some((row, span.start))
        })
    })
}

/// Returns `loaded` with the functions its actions and sweeps run on.
///
/// # Arguments
///
/// * `bench` - Which binary it is.
/// * `loaded` - The binary, analyzed.
fn prep_of(bench: Bench, loaded: Arc<LoadedBinary>) -> Prep {
    let rows = &loaded.initial_rows.rows;
    let graphs = match bench {
        Bench::Notepad => NOTEPAD_GRAPHS,
        Bench::Large => 1,
    };
    Prep {
        bench,
        targets: pick_targets(rows, RUNS.saturating_add(1)),
        largest: largest(rows, graphs),
        loaded,
    }
}

/// Loads notepad and picks its targets, for the actions phase.
///
/// # Arguments
///
/// * `cancel` - Cooperative cancel flag of the phase.
///
/// # Errors
///
/// Returns an error when notepad does not load or no function of it calls another.
pub(super) fn prepare_actions(cancel: &Cancel) -> anyhow::Result<Prepared> {
    cancel.within(|| {
        let loaded = load_binary_blocking(
            std::path::PathBuf::from(SYSTEM_NOTEPAD),
            &Sources::default(),
            Vec::new(),
        )?;
        let prep = prep_of(Bench::Notepad, loaded);
        anyhow::ensure!(
            !prep.targets.is_empty(),
            "{SYSTEM_NOTEPAD} has no function that calls another"
        );
        Ok(Prepared::Actions(prep))
    })
}

/// Loads the large DLL and picks its targets.
///
/// # Arguments
///
/// * `cancel` - Cooperative cancel flag of the phase.
///
/// # Errors
///
/// Returns why the DLL is skipped: missing, too slow to analyze, or calling nothing.
fn prepare_large(cancel: &Cancel) -> Result<Prep, String> {
    let ready = load_large_dll_blocking(cancel).map_err(|err| format!("{err:#}"))?;
    if ready.loaded.path.as_path() == std::path::Path::new(SYSTEM_NOTEPAD) {
        return Err("no large DLL analyzed within the budget".to_owned());
    }
    let prep = prep_of(Bench::Large, ready.loaded);
    if prep.targets.is_empty() {
        return Err("no function calls another".to_owned());
    }
    Ok(prep)
}

/// One step of a run.
#[derive(Debug)]
enum Move {
    /// Closes the modal and every tab and empties the functions filter.
    Clear,
    /// Opens a place, focused, as a permanent tab.
    Open(Place),
    /// Dispatches an action on the focused element.
    Dispatch(Box<dyn Action>),
    /// Puts text in the go-to picker's query.
    Query(String),
    /// Types one key into the focused element, once the harness's update ends.
    Key(String),
    /// Puts the active code tab's cursor on its first call token.
    Cursor,
    /// Runs a sweep for [`SWEEP`].
    Sweep(Sweep),
}

/// What a run times: an action, or a sweep's frames.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum What {
    /// An action's ack and settle.
    Act(Act),
    /// A sweep's frame times.
    Sweep(Sweep),
}

/// One run of the script: what it times and its steps, the last one timed.
#[derive(Debug)]
struct Run {
    /// What the run times.
    what: What,
    /// Its steps.
    moves: VecDeque<Move>,
}

/// Returns the key typed for `c`: itself when it is a lowercase letter or a digit, its
/// lowercase when an uppercase letter, else `a`.
///
/// # Arguments
///
/// * `c` - A character of a function's name.
fn key_of(c: Option<char>) -> String {
    c.filter(char::is_ascii_alphanumeric)
        .map_or('a', |c| c.to_ascii_lowercase())
        .to_string()
}

/// Returns the steps of one run of `act` on `t`, with `next` the target after it.
///
/// # Arguments
///
/// * `act` - The action.
/// * `t` - The target.
/// * `next` - The target after it, which go to starts from and back leaves.
fn moves(act: Act, t: &Target, next: &Target) -> VecDeque<Move> {
    let code = |entry| Move::Open(Place::decompile(entry));
    let mut chars = t.name.chars();
    let last = chars.next_back();
    let steps = match act {
        Act::GoTo => vec![
            code(next.entry),
            Move::Dispatch(Box::new(GoTo)),
            Move::Query(t.name.clone()),
            Move::Dispatch(Box::new(menu::Confirm)),
        ],
        Act::Find => vec![
            code(t.entry),
            Move::Dispatch(Box::new(FindEverywhere)),
            Move::Query(chars.as_str().to_owned()),
            Move::Key(key_of(last)),
        ],
        Act::Xrefs => vec![code(t.entry), Move::Cursor, Move::Dispatch(Box::new(Xrefs))],
        Act::Listing => vec![
            Move::Open(Place::Code {
                entry: t.entry,
                form: Form::Listing,
                at: None,
            }),
            code(t.entry),
            Move::Dispatch(Box::new(ToggleListing)),
        ],
        Act::Graph => vec![
            Move::Open(Place::Graph {
                entry: t.entry,
                at: None,
            }),
            code(t.entry),
            Move::Dispatch(Box::new(ShowGraph)),
        ],
        Act::Filter => vec![
            code(t.entry),
            Move::Dispatch(Box::new(FocusFilter)),
            Move::Key(key_of(t.name.chars().next())),
        ],
        Act::Overview => vec![code(t.entry), Move::Dispatch(Box::new(Overview))],
        Act::Back => vec![
            code(t.entry),
            code(next.entry),
            Move::Dispatch(Box::new(workspace::pane::GoBack)),
        ],
    };
    std::iter::once(Move::Clear).chain(steps).collect()
}

/// Returns every run on `prep`: each action on each target, then each sweep on each of
/// the largest functions.
///
/// # Arguments
///
/// * `prep` - The binary and its targets.
fn script(prep: &Prep) -> VecDeque<Run> {
    let mut runs = VecDeque::new();
    for act in Act::ALL {
        for (i, t) in prep.targets.iter().take(RUNS).enumerate() {
            let next = prep.targets.get(i.saturating_add(1)).unwrap_or(t);
            runs.push_back(Run {
                what: What::Act(act),
                moves: moves(act, t, next),
            });
        }
    }
    for &entry in &prep.largest {
        for sweep in [Sweep::Pan, Sweep::Zoom] {
            let graph = Place::Graph { entry, at: None };
            runs.push_back(Run {
                what: What::Sweep(sweep),
                moves: VecDeque::from([Move::Clear, Move::Open(graph), Move::Sweep(sweep)]),
            });
        }
    }
    runs
}

/// One action's times on one binary, in nanoseconds.
#[derive(Debug, Default)]
pub(super) struct Times {
    /// Dispatch to the first presented frame showing a change.
    pub(super) ack: Vec<u64>,
    /// Dispatch to the presented frame the app settled on.
    pub(super) settle: Vec<u64>,
    /// Runs that settled with nothing changed, which time no ack.
    still: usize,
    /// Runs that did not settle within [`LATE`], timed at it.
    late: usize,
    /// Runs whose setup could not be done or did not settle.
    skipped: usize,
}

/// The step being watched.
#[derive(Debug)]
enum Going {
    /// A step waiting to settle: its watch, when it was dispatched, and whether it is timed.
    Watching(Box<Watch>, Instant, bool),
    /// A sweep, until when it runs, and its frame count.
    Sweeping(Sweep, Instant, u32),
}

/// State of the actions phase, carried from frame to frame.
pub(super) struct ActionsRun {
    /// Flag of the phase.
    cancel: Cancel,
    /// The measured window.
    window_id: WindowId,
    /// Keeps gpui's frame tracing on while the phase lives.
    _tracing: Tracing,
    /// The frame events not read yet.
    collector: gpui::profiler::FrameTimingCollector,
    /// The binary the runs are on.
    bench: Bench,
    /// The runs left on it.
    script: VecDeque<Run>,
    /// What the run going times.
    what: What,
    /// The steps left of the run going.
    moves: VecDeque<Move>,
    /// The step being watched.
    going: Option<Going>,
    /// Each frame drawn since that step began: when it finished drawing, when it was
    /// presented.
    drawn: Vec<(Instant, Option<Instant>)>,
    /// Each action's times, by binary.
    times: BTreeMap<(Bench, Act), Times>,
    /// Each sweep's frame draw times in nanoseconds, by binary.
    frames: BTreeMap<(Bench, Sweep), Vec<u64>>,
}

impl ActionsRun {
    /// Returns the times of the action the run going times, `None` for a sweep.
    fn times(&mut self) -> Option<&mut Times> {
        let What::Act(act) = self.what else {
            return None;
        };
        Some(self.times.entry((self.bench, act)).or_default())
    }

    /// Returns when the frame showing what was read at `ready` was presented: the draw it
    /// was read in, else the first after it; `ready` when none was presented.
    ///
    /// # Arguments
    ///
    /// * `ready` - When the change was first read.
    fn shown(&self, ready: Instant) -> Instant {
        let drawn = self.drawn.iter().find(|(end, _)| *end >= ready);
        drawn.and_then(|&(_, presented)| presented).unwrap_or(ready)
    }

    /// Reads the frame events since the last frame: each draw of the window, its
    /// presentation, and a sweep's draw times.
    fn take_frames(&mut self) {
        for event in self.collector.collect_unseen() {
            match event {
                gpui::profiler::FrameEvent::Draw(draw) if draw.window_id == self.window_id => {
                    self.drawn.push((draw.draw_end, None));
                    if let Some(Going::Sweeping(sweep, ..)) = self.going {
                        let ns = nanos(draw.draw_end.saturating_duration_since(draw.draw_start));
                        self.frames.entry((self.bench, sweep)).or_default().push(ns);
                    }
                }
                gpui::profiler::FrameEvent::Present(present)
                    if present.window_id == self.window_id =>
                {
                    if let Some(last) = self.drawn.last_mut() {
                        last.1.get_or_insert(present.present_end);
                    }
                }
                gpui::profiler::FrameEvent::Draw(_) | gpui::profiler::FrameEvent::Present(_) => {}
            }
        }
    }

    /// Records a timed step that settled, or ran late, as `watch` saw it.
    ///
    /// # Arguments
    ///
    /// * `watch` - The step's watch.
    /// * `at` - When the step was dispatched.
    /// * `now` - Start of this frame, the time a late step is timed at.
    fn record(&mut self, watch: &Watch, at: Instant, now: Instant) {
        let ack = watch.ack().map(|ready| self.shown(ready));
        let settle = watch.settle().map(|ready| self.shown(ready));
        let since = |t: Instant| nanos(t.saturating_duration_since(at));
        let Some(times) = self.times() else {
            return;
        };
        match (ack, settle) {
            (_, None) => {
                times.late = times.late.saturating_add(1);
                times.ack.push(since(ack.unwrap_or(now)));
                times.settle.push(since(now));
            }
            (None, Some(settle)) => {
                times.still = times.still.saturating_add(1);
                times.settle.push(since(settle));
            }
            (Some(ack), Some(settle)) => {
                times.ack.push(since(ack));
                times.settle.push(since(settle));
            }
        }
    }

    /// Drops the rest of the run going and counts it skipped.
    fn skip(&mut self) {
        self.moves.clear();
        if let Some(times) = self.times() {
            times.skipped = times.skipped.saturating_add(1);
        }
    }

    /// Returns the protocol lines of the times on the binary the runs were on.
    fn report(&mut self) -> Vec<String> {
        let bench = self.bench;
        let mut lines = Vec::new();
        for (&(on, act), times) in &mut self.times {
            if on != bench {
                continue;
            }
            lines.push(format!(
                "MEASURE_ACTION bench={} action={} {} {} still={} late={} skipped={}",
                bench.word(),
                act.word(),
                quantiles("ack_", &mut times.ack),
                quantiles("settle_", &mut times.settle),
                times.still,
                times.late,
                times.skipped
            ));
        }
        for (&(on, sweep), frames) in &mut self.frames {
            if on == bench {
                let (word, frames) = (sweep.word(), quantiles("", frames));
                lines.push(format!(
                    "MEASURE_FRAMES bench={} sweep={word} {frames}",
                    bench.word()
                ));
            }
        }
        lines
    }
}

/// Feeds `watch` the reads of the draws since the last frame, then this frame's read.
///
/// A draw's read is taken as it draws, so a change is credited to the draw that showed it;
/// this frame's read, taken before it draws, catches what no draw has shown yet.
///
/// # Arguments
///
/// * `watch` - The step's watch.
/// * `draws` - Each draw since the last frame: when it was read, and the read.
/// * `now` - Start of this frame.
/// * `read` - What the window shows now.
///
/// # Returns
///
/// Whether the step has settled.
fn feed(watch: &mut Watch, draws: Vec<(Instant, Seen)>, now: Instant, read: Seen) -> bool {
    draws
        .into_iter()
        .chain([(now, read)])
        .fold(false, |_, (at, seen)| watch.frame(at, seen))
}

/// What a bar holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Held {
    /// An action's dispatch to its first presented change, at the 99th percentile.
    Ack,
    /// An action's dispatch to its settled views, at the 95th percentile.
    Settle,
    /// A sweep's frame draw time, at the 99th percentile.
    Frame,
}

impl Held {
    /// Returns what the report calls it.
    const fn word(self) -> &'static str {
        match self {
            Self::Ack => "ack",
            Self::Settle => "settle",
            Self::Frame => "frame",
        }
    }

    /// Returns the percentile the bar holds.
    const fn percentile(self) -> usize {
        match self {
            Self::Ack | Self::Frame => 99,
            Self::Settle => 95,
        }
    }
}

/// One bar of the phase: what it times, what it holds, and its limit in microseconds on
/// notepad and on the large DLL, `None` where the plan only reports the time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Bar {
    /// The action's or the sweep's name ([`Act::word`], [`Sweep::word`]).
    what: &'static str,
    /// What it holds.
    held: Held,
    /// Limit on notepad, microseconds.
    notepad: Option<u64>,
    /// Limit on the large DLL, microseconds.
    large: Option<u64>,
}

/// Returns the bar on `what`'s `held` time of `notepad` and `large` microseconds.
const fn bar(what: &'static str, held: Held, notepad: Option<u64>, large: Option<u64>) -> Bar {
    Bar {
        what,
        held,
        notepad,
        large,
    }
}

/// The phase's bars: ack 16 ms at p99 for every action, settle at p95 per action and
/// binary, frames 8.3 ms at p99 for both sweeps. A later action adds its rows here.
pub(super) const BARS: &[Bar] = &[
    bar("goto", Held::Ack, Some(16_000), Some(16_000)),
    bar("find", Held::Ack, Some(16_000), Some(16_000)),
    bar("xrefs", Held::Ack, Some(16_000), Some(16_000)),
    bar("listing", Held::Ack, Some(16_000), Some(16_000)),
    bar("graph", Held::Ack, Some(16_000), Some(16_000)),
    bar("filter", Held::Ack, Some(16_000), Some(16_000)),
    bar("overview", Held::Ack, Some(16_000), Some(16_000)),
    bar("back", Held::Ack, Some(16_000), Some(16_000)),
    bar("goto", Held::Settle, Some(50_000), Some(100_000)),
    bar("find", Held::Settle, Some(16_000), Some(50_000)),
    bar("xrefs", Held::Settle, Some(16_000), Some(33_000)),
    bar("listing", Held::Settle, Some(16_000), Some(16_000)),
    bar("graph", Held::Settle, Some(50_000), Some(100_000)),
    bar("filter", Held::Settle, Some(16_000), Some(50_000)),
    bar("overview", Held::Settle, Some(500_000), None),
    bar("pan", Held::Frame, Some(8_300), Some(8_300)),
    bar("zoom", Held::Frame, Some(8_300), Some(8_300)),
];

/// Returns every bar the times miss, one line each.
///
/// A line names the binary, the action or sweep, what is held, the percentile, the time
/// and the bar; a bar on a binary the phase ran with no time to hold misses too.
///
/// # Arguments
///
/// * `times` - Each action's times, by binary.
/// * `frames` - Each sweep's frame times, by binary.
pub(super) fn misses(
    times: &BTreeMap<(Bench, Act), Times>,
    frames: &BTreeMap<(Bench, Sweep), Vec<u64>>,
) -> Vec<String> {
    let mut out = Vec::new();
    for bench in [Bench::Notepad, Bench::Large] {
        if !times.keys().any(|&(on, _)| on == bench) {
            continue;
        }
        for bar in BARS {
            let limit = match bench {
                Bench::Notepad => bar.notepad,
                Bench::Large => bar.large,
            };
            let Some(limit) = limit else {
                continue;
            };
            let samples = match bar.held {
                Held::Ack | Held::Settle => Act::ALL
                    .into_iter()
                    .find(|act| act.word() == bar.what)
                    .and_then(|act| times.get(&(bench, act)))
                    .map(|t| {
                        if bar.held == Held::Ack {
                            &t.ack
                        } else {
                            &t.settle
                        }
                    }),
                Held::Frame => [Sweep::Pan, Sweep::Zoom]
                    .into_iter()
                    .find(|sweep| sweep.word() == bar.what)
                    .and_then(|sweep| frames.get(&(bench, sweep))),
            };
            let mut samples = samples.cloned().unwrap_or_default();
            let (_, p95, p99, _, n) = sorted_quantiles_ms(&mut samples);
            let pct = bar.held.percentile();
            let at = if pct == 95 { p95 } else { p99 };
            let limit_ms = as_f64(limit) / 1000.0;
            if n == 0 || at > limit_ms {
                out.push(format!(
                    "MEASURE_MISS bench={} what={} held={} p{pct}_ms={at:.3} bar_ms={limit_ms:.3} n={n}",
                    bench.word(),
                    bar.what,
                    bar.held.word(),
                ));
            }
        }
    }
    out
}

impl Harness {
    /// Shows `prep`'s binary in the measured window and runs its script, frame by frame.
    ///
    /// # Arguments
    ///
    /// * `cancel` - Flag of the phase.
    /// * `prep` - The binary and its targets.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    pub(super) fn start_actions(
        &mut self,
        cancel: Cancel,
        prep: Prep,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.draws = Some(Vec::new());
        let run = ActionsRun {
            cancel,
            window_id: window.window_handle().window_id(),
            _tracing: Tracing::on(),
            collector: gpui::profiler::FrameTimingCollector::new(),
            bench: prep.bench,
            script: VecDeque::new(),
            what: What::Act(Act::GoTo),
            moves: VecDeque::new(),
            going: None,
            drawn: Vec::new(),
            times: BTreeMap::new(),
            frames: BTreeMap::new(),
        };
        self.next_bench(run, prep, window, cx);
    }

    /// Shows `prep`'s binary and runs its script from the next frame.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `prep` - The binary and its targets.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn next_bench(
        &mut self,
        mut run: ActionsRun,
        prep: Prep,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        run.bench = prep.bench;
        run.script = script(&prep);
        self.binary
            .update(cx, |binary, cx| binary.show_loaded(prep.loaded, cx));
        cx.on_next_frame(window, move |this, window, cx| {
            this.actions_step(run, window, cx);
        });
    }

    /// Feeds this frame to the step being watched, starts the next step once it is done,
    /// and asks for the next frame.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn actions_step(
        &mut self,
        mut run: ActionsRun,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        if run.cancel.is_raised() {
            return;
        }
        let now = now_instant();
        run.take_frames();
        let draws = self.draws.as_mut().map(std::mem::take).unwrap_or_default();
        let read = seen(&self.workspace, &self.binary, cx);
        match run.going.take() {
            Some(Going::Watching(mut watch, at, timed)) => {
                let settled = feed(&mut watch, draws, now, read.clone());
                let limit = if timed { LATE } else { SETUP_LIMIT };
                if settled || now.saturating_duration_since(at) > limit {
                    if timed {
                        run.record(&watch, at, now);
                    } else if !settled {
                        run.skip();
                    }
                } else {
                    run.going = Some(Going::Watching(watch, at, timed));
                }
            }
            Some(Going::Sweeping(sweep, until, frames)) if now < until => {
                self.sweep_step(sweep, frames, window, cx);
                run.going = Some(Going::Sweeping(sweep, until, frames.saturating_add(1)));
            }
            Some(Going::Sweeping(..)) | None => {}
        }
        if run.going.is_none() && !self.next_move(&mut run, read.stamp, now, window, cx) {
            self.bench_done(run, window, cx);
            return;
        }
        cx.on_next_frame(window, move |this, window, cx| {
            this.actions_step(run, window, cx);
        });
    }

    /// Starts the next step of the script, skipping runs whose steps cannot be done.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `before` - What the window shows now.
    /// * `now` - Start of this frame.
    /// * `window` - Window the steps act in.
    /// * `cx` - Harness context.
    ///
    /// # Returns
    ///
    /// Whether a step started; `false` once the script is done.
    fn next_move(
        &mut self,
        run: &mut ActionsRun,
        before: super::watch::Stamp,
        now: Instant,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> bool {
        loop {
            let Some(step) = run.moves.pop_front() else {
                let Some(next) = run.script.pop_front() else {
                    return false;
                };
                if say(&format!("MEASURE_RUN what={:?}", next.what)).is_err() {
                    return false;
                }
                run.what = next.what;
                run.moves = next.moves;
                continue;
            };
            run.drawn.clear();
            if let Move::Sweep(sweep) = step {
                run.going = Some(Going::Sweeping(sweep, now + SWEEP, 0));
                return true;
            }
            let timed = run.moves.is_empty();
            let at = now_instant();
            if self.perform(step, window, cx).is_some() {
                run.going = Some(Going::Watching(Box::new(Watch::new(before)), at, timed));
                return true;
            }
            run.skip();
        }
    }

    /// Does one step; a key is dispatched once the harness update ends, as a key dispatch
    /// draws the window and the harness is its root view.
    ///
    /// # Arguments
    ///
    /// * `step` - The step; a sweep is run frame by frame instead.
    /// * `window` - Window the step acts in.
    /// * `cx` - Harness context.
    ///
    /// # Returns
    ///
    /// `None` when the step cannot be done: no binary, no picker, no call token, a key
    /// that does not parse.
    fn perform(&self, step: Move, window: &mut Window, cx: &mut Context<'_, Self>) -> Option<()> {
        match step {
            Move::Clear => self.clear(window, cx),
            Move::Open(place) => {
                let loaded = self.binary.read(cx).loaded()?.clone();
                let binary = self.binary.clone();
                self.workspace.update(cx, |workspace, cx| {
                    open(workspace, &binary, &loaded, place, PERMANENT, window, cx);
                });
            }
            Move::Dispatch(action) => window.dispatch_action(action, cx),
            Move::Query(text) => {
                let picker = self
                    .workspace
                    .read(cx)
                    .active_modal::<Picker<GoToDelegate>>(cx)?;
                picker.update(cx, |picker, cx| picker.set_query(&text, window, cx));
            }
            Move::Key(key) => {
                let keystroke = Keystroke {
                    modifiers: Modifiers::default(),
                    key: key.clone(),
                    key_char: Some(key),
                };
                window.defer(cx, move |window, cx| {
                    window.dispatch_keystroke(keystroke, cx);
                });
            }
            Move::Cursor => {
                let tab = self.item(cx)?;
                let (row, col) = {
                    let tab = tab.read(cx);
                    first_call(tab.code()?, tab.entry()?)?
                };
                let at = Point::new(u32::try_from(row).ok()?, u32::try_from(col).ok()?);
                let editor = tab.read(cx).editor().clone();
                editor.update(cx, |editor, cx| {
                    editor.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
                        s.select_ranges([at..at]);
                    });
                });
            }
            Move::Sweep(_) => return None,
        }
        Some(())
    }

    /// Closes the modal and every tab, and empties the functions filter.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the workspace is in.
    /// * `cx` - Harness context.
    fn clear(&self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.workspace.update(cx, |workspace, cx| {
            workspace.hide_modal(window, cx);
            for pane in workspace.panes().to_vec() {
                pane.update(cx, |pane, cx| {
                    let tabs: Vec<_> = pane.items().map(|item| item.item_id()).collect();
                    for tab in tabs {
                        pane.remove_item(tab, false, false, window, cx);
                    }
                });
            }
        });
        if let Some(panel) = self.panel(cx) {
            panel.update(cx, |panel, cx| panel.set_filter("", window, cx));
        }
    }

    /// Takes one frame's step of a sweep on the active graph tab.
    ///
    /// # Arguments
    ///
    /// * `sweep` - The sweep.
    /// * `frames` - Frames of it so far.
    /// * `window` - Window the graph is in.
    /// * `cx` - Harness context.
    fn sweep_step(
        &self,
        sweep: Sweep,
        frames: u32,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let forward = (frames / TURN_FRAMES).is_multiple_of(2);
        match sweep {
            Sweep::Pan => {
                let workspace = self.workspace.read(cx);
                let Some(graph) = workspace.active_item_as::<GraphItem>(cx) else {
                    return;
                };
                let position = graph.read(cx).painted().bounds.center();
                let step = if forward { PAN_STEP } else { -PAN_STEP };
                let event = ScrollEvent {
                    position,
                    delta: ScrollDelta::Pixels(point(px(step), px(step / 2.0))),
                    ..ScrollEvent::default()
                };
                window.dispatch_event(PlatformInput::Scroll(event), cx);
            }
            Sweep::Zoom => {
                let zoom: Box<dyn Action> = if forward {
                    Box::new(ZoomIn)
                } else {
                    Box::new(ZoomOut)
                };
                window.dispatch_action(zoom, cx);
            }
        }
    }

    /// Reports the binary the runs were on, then loads the large DLL after notepad, or
    /// ends the phase.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn bench_done(&mut self, mut run: ActionsRun, window: &mut Window, cx: &mut Context<'_, Self>) {
        for line in run.report() {
            if let Err(err) = say(&line) {
                self.fail(err, cx);
                return;
            }
        }
        if run.bench == Bench::Large {
            self.actions_end(&run, cx);
            return;
        }
        let worker = run.cancel.clone();
        self.prep.run_in(
            "Preparing the large DLL",
            window,
            cx,
            move || prepare_large(&worker),
            move |this, ready, window, cx| match ready {
                Ok(prep) => this.next_bench(run, prep, window, cx),
                Err(why) => match say(&format!(
                    "MEASURE_ACTIONS_SKIPPED bench=large reason={why:?}"
                )) {
                    Ok(()) => this.actions_end(&run, cx),
                    Err(err) => this.fail(err, cx),
                },
            },
        );
    }

    /// Ends the phase with each bar it missed and its closing line.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `cx` - Harness context.
    fn actions_end(&mut self, run: &ActionsRun, cx: &mut Context<'_, Self>) {
        self.draws = None;
        let missed = misses(&run.times, &run.frames);
        let end = format!(
            "MEASURE_ACTIONS misses={} ui_engine_calls={}",
            missed.len(),
            ui_engine_calls()
        );
        match missed.iter().chain([&end]).try_for_each(|line| say(line)) {
            Ok(()) => cx.quit(),
            Err(err) => self.fail(err, cx),
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::collections::{BTreeMap, VecDeque};
    use std::time::Duration;

    use borer_engine::analysis::render::{FunctionRow, RowSource};
    use borer_engine::cancel::Cancel;
    use gpui::{Entity, TestAppContext, VisualTestContext, WindowId};

    use super::{
        Act, ActionsRun, Bench, Move, Sweep, Times, What, feed, first_call, largest, misses,
        pick_targets,
    };
    use crate::app_view::tests::{CALLEE, CALLER, init, sample};
    use crate::code_view::CodeLines;
    use crate::functions_panel::FunctionsPanel;
    use crate::measure::watch::{Seen, Stamp, Watch, seen};
    use crate::measure::{CliMode, Harness, Tracing, now_instant};
    use crate::worker::decompile_blocking;

    /// Returns a hand-built row at `entry` calling `callees` functions, `size` bytes long.
    fn row(entry: u64, callees: usize, size: u64) -> FunctionRow {
        FunctionRow {
            entry,
            size,
            blocks: 1,
            instrs: 1,
            callers: 0,
            callees,
            src: RowSource::User,
            name: format!("f{entry:x}"),
        }
    }

    /// Two runs pick the same targets: the first rows by address that call another, the
    /// largest functions by size then address, and the first call token of a function.
    ///
    /// # Panics
    ///
    /// Panics if a pick differs between runs or from the engine's order.
    #[test]
    fn targets_are_chosen_by_the_engine_order() {
        let rows: Vec<FunctionRow> = (0..40u64)
            .map(|i| row(0x1000 + i * 0x10, usize::from(i % 3 == 0), 0x40 - (i % 7)))
            .collect();
        let entries = |n| -> Vec<u64> { pick_targets(&rows, n).iter().map(|t| t.entry).collect() };
        let want: Vec<u64> = (0..8u64).map(|i| 0x1000 + i * 0x30).collect();
        assert_eq!(entries(8), want);
        assert_eq!(entries(8), entries(8));
        assert_eq!(largest(&rows, 3), vec![0x1000, 0x1070, 0x10e0]);
        let loaded = sample();
        let again = sample();
        let picked = pick_targets(&loaded.initial_rows.rows, 51);
        assert_eq!(picked, pick_targets(&again.initial_rows.rows, 51));
        assert_eq!(picked.first().map(|t| t.entry), Some(CALLER));
        let code = |loaded| CodeLines::new(vec![decompile_blocking(loaded, CALLER).unwrap()]);
        let call = first_call(&code(&loaded), CALLER);
        assert!(call.is_some());
        assert_eq!(call, first_call(&code(&again), CALLER));
        let (row, col) = call.unwrap();
        let shown = code(&loaded);
        let (view, line) = shown.get(row).unwrap();
        let (_, _, link) = view.token_at(line, col).unwrap();
        assert_eq!(link, Some(&borer_engine::view::Ref::Function(CALLEE)));
    }

    /// Opens an interactive harness window over the sample and returns it and its context.
    fn harness(cx: &mut TestAppContext) -> (Entity<Harness>, &mut VisualTestContext) {
        let app_state = init(cx);
        let (harness, cx) = cx.add_window_view(|window, cx| {
            let mode = CliMode::Interactive(None);
            Harness::new(mode, std::rc::Rc::default(), &app_state, window, cx)
        });
        let binary = harness.read_with(cx, |harness, _| harness.binary.clone());
        binary.update(cx, |binary, cx| binary.show_loaded(sample(), cx));
        cx.run_until_parked();
        (harness, cx)
    }

    /// While the actions phase runs, each draw of the harness reads what it shows.
    ///
    /// # Panics
    ///
    /// Panics if a draw is not read, or its read is not what the window shows.
    #[gpui::test]
    fn each_draw_of_the_actions_phase_reads_what_it_shows(cx: &mut TestAppContext) {
        let (harness, cx) = harness(cx);
        harness.update(cx, |harness, _| harness.draws = Some(Vec::new()));
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let (draws, now) = harness.read_with(cx, |harness, cx| {
            let now = seen(&harness.workspace, &harness.binary, cx);
            (harness.draws.clone().unwrap_or_default(), now)
        });
        assert_eq!(draws.len(), 1, "{draws:?}");
        assert_eq!(draws.first().map(|(_, read)| read), Some(&now));
    }

    /// A change read as a frame drew is credited to that frame's presentation, not to the
    /// next frame's start.
    ///
    /// # Panics
    ///
    /// Panics if the ack or the settle is credited to another frame.
    #[test]
    fn a_change_is_credited_to_the_frame_that_drew_it() {
        let at = now_instant();
        let ms = |n| at + Duration::from_millis(n);
        let mut run = ActionsRun {
            cancel: Cancel::new(),
            window_id: WindowId::from(1),
            _tracing: Tracing { turned_on: false },
            collector: gpui::profiler::FrameTimingCollector::new(),
            bench: Bench::Notepad,
            script: VecDeque::new(),
            what: What::Act(Act::Find),
            moves: VecDeque::new(),
            going: None,
            drawn: vec![(ms(1), Some(ms(3)))],
            times: BTreeMap::new(),
            frames: BTreeMap::new(),
        };
        let shows = |status: &str| Seen {
            stamp: Stamp {
                status: status.to_owned(),
                ..Stamp::default()
            },
            quiet: true,
        };
        let mut watch = Watch::new(shows("").stamp);
        let drawn = vec![(ms(1), shows("changed"))];
        assert!(feed(&mut watch, drawn, ms(17), shows("changed")));
        run.record(&watch, at, ms(17));
        let times = run.times.get(&(Bench::Notepad, Act::Find));
        let three = 3_000_000;
        assert_eq!(
            times.map(|t| (t.ack.clone(), t.settle.clone())),
            Some((vec![three], vec![three]))
        );
    }

    /// A key step types into the focused filter once the harness's update ends, so the
    /// harness's own keystroke count never updates it twice.
    ///
    /// # Panics
    ///
    /// Panics if the step fails or the filter does not read the key.
    #[gpui::test]
    fn a_key_step_types_into_the_focused_filter(cx: &mut TestAppContext) {
        let (harness, cx) = harness(cx);
        let workspace = harness.read_with(cx, |harness, _| harness.workspace.clone());
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        let done = harness.update_in(cx, |harness, window, cx| {
            harness.perform(Move::Key("a".to_owned()), window, cx)
        });
        assert_eq!(done, Some(()));
        cx.run_until_parked();
        let filter = harness.read_with(cx, |harness, cx| {
            harness
                .panel(cx)
                .map(|panel| panel.read(cx).filter_text(cx))
        });
        assert_eq!(filter.as_deref(), Some("a"));
    }

    /// Returns times of `n` samples of `ns` nanoseconds each.
    fn of(n: usize, ns: u64) -> Vec<u64> {
        vec![ns; n]
    }

    /// Every action's ack, every settle with a bar and every sweep's frames, made slower
    /// than its bar, fail the run with a line naming the action and the percentile, and
    /// times within every bar fail nothing.
    ///
    /// # Panics
    ///
    /// Panics if a slow time passes or a fast run fails.
    #[test]
    fn a_missed_bar_fails_the_run() {
        let fast = || -> BTreeMap<(Bench, Act), Times> {
            let times = |_| Times {
                ack: of(50, 1_000),
                settle: of(50, 1_000),
                ..Times::default()
            };
            Act::ALL
                .into_iter()
                .map(|act| ((Bench::Notepad, act), times(act)))
                .collect()
        };
        let frames: BTreeMap<_, _> = [Sweep::Pan, Sweep::Zoom]
            .into_iter()
            .map(|sweep| ((Bench::Notepad, sweep), of(100, 1_000)))
            .collect();
        assert_eq!(misses(&fast(), &frames), Vec::<String>::new());
        for act in Act::ALL {
            for (held, pct) in [("ack", 99), ("settle", 95)] {
                if (act, held) == (Act::Back, "settle") {
                    continue;
                }
                let mut slow = fast();
                let times = slow.get_mut(&(Bench::Notepad, act)).unwrap();
                let held_times = if held == "ack" {
                    &mut times.ack
                } else {
                    &mut times.settle
                };
                *held_times = of(50, 10_000_000_000);
                let missed = misses(&slow, &frames);
                let want = format!("what={} held={held} p{pct}_ms=", act.word());
                assert!(
                    missed.iter().any(|m| m.contains(&want)),
                    "{want}: {missed:?}"
                );
            }
        }
        for sweep in [Sweep::Pan, Sweep::Zoom] {
            let mut slow = frames.clone();
            slow.insert((Bench::Notepad, sweep), of(100, 9_000_000));
            let missed = misses(&fast(), &slow);
            let want = format!("what={} held=frame p99_ms=", sweep.word());
            assert!(
                missed.iter().any(|m| m.contains(&want)),
                "{want}: {missed:?}"
            );
        }
    }
}
