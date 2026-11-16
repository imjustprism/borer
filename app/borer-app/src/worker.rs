//! Background engine execution guard, UI-thread call counter, and filter sequencer.

use std::cell::Cell;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use borer_engine::analysis::decompile::replay::{Grade, TextCheck};
use borer_engine::analysis::decompile::text_check;
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::render::{
    Bytes, FunctionOrder, FunctionRows, answered_flagged, disasm_view, function_rows,
};
use borer_engine::analysis::{Analysis, EnumSource, Overlay, no_function_at, resolve_suggesting};
use borer_engine::cancel::Cancel;
use borer_engine::program::{Feature, Program};
use borer_engine::view::View;
use gpui::{App, Task};

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

/// Spawns synchronous engine work `f` onto GPUI's background executor.
///
/// # Arguments
///
/// * `cx` - Application context providing the background thread pool.
/// * `f` - Synchronous engine closure to execute off the UI thread.
///
/// # Returns
///
/// A [`Task`] yielding the result of `f`.
pub fn spawn_engine<R: Send + 'static>(
    cx: &App,
    f: impl FnOnce() -> R + Send + 'static,
) -> Task<R> {
    cx.background_executor().spawn(async move { run_engine(f) })
}

/// Immutable engine state for one opened binary.
#[derive(Debug)]
pub struct LoadedBinary {
    /// File path opened by the user or command line.
    pub path: PathBuf,
    /// Parsed binary image.
    pub program: Arc<Program>,
    /// Computed whole-program code and cross-reference analysis.
    pub analysis: Arc<Analysis>,
    /// Overlay matching the server's binary-enum configuration (packs left out).
    pub overlay: Arc<Overlay>,
    /// Unfiltered function table fetched once during load, shared with the
    /// view that shows it rather than copied.
    pub initial_rows: Arc<FunctionRows>,
}

/// Loads `path`, runs [`Analysis::compute`], and builds the initial function rows.
///
/// Must be called inside [`spawn_engine`] (or [`run_engine`] in `--headless` mode).
///
/// # Arguments
///
/// * `path` - File path of the untrusted binary to inspect.
///
/// # Returns
///
/// Shared [`LoadedBinary`] holding the program, analysis, overlay, and unfiltered rows.
///
/// # Errors
///
/// Returns an error when [`Program::load`] rejects or fails to read `path`.
pub fn load_binary_blocking(path: PathBuf) -> anyhow::Result<Arc<LoadedBinary>> {
    let program = Arc::new(Program::load(&path)?);
    let analysis = Arc::new(Analysis::compute(&program));
    let overlay = Arc::new(Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    });
    let initial_rows = Arc::new(function_rows(
        &analysis,
        &overlay,
        None,
        FunctionOrder::Address,
        0,
        usize::MAX,
    ));
    Ok(Arc::new(LoadedBinary {
        path,
        program,
        analysis,
        overlay,
        initial_rows,
    }))
}

/// Computes filtered [`FunctionRows`] for `loaded` matching `filter`.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `filter` - Substring or `0x`-hex query; empty selects every non-thunk function.
///
/// # Returns
///
/// Matching [`FunctionRows`] in ascending entry-address order.
#[must_use]
pub fn filter_rows_blocking(loaded: &LoadedBinary, filter: &str) -> FunctionRows {
    let query = (!filter.is_empty()).then_some(filter);
    function_rows(
        &loaded.analysis,
        &loaded.overlay,
        query,
        FunctionOrder::Address,
        0,
        usize::MAX,
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
    let (program, analysis) = (&loaded.program, &loaded.analysis);
    let (answered, _) = answered_flagged(program, analysis, &loaded.overlay, entry);
    let check = text_check(program, analysis, &answered, entry);
    (*check).as_ref().map(GradeCounts::of)
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
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
/// * `query` - What the person typed: `0x`-hex, decimal or a name.
#[must_use]
pub fn goto_blocking(loaded: &LoadedBinary, query: &str) -> GoToAnswer {
    let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
    let target = resolve_suggesting(p, a, o, query).and_then(|va| {
        a.function_at(va)
            .map(|f| (f.entry, va))
            .ok_or_else(|| no_function_at(p, a, va))
    });
    let filter = (!query.is_empty()).then_some(query);
    let rows = function_rows(a, o, filter, FunctionOrder::Address, 0, GOTO_ROWS);
    GoToAnswer { target, rows }
}

/// Monotonic request sequencer ensuring a late older background answer never
/// overwrites a newer filter result.
#[derive(Debug, Clone)]
pub struct FilterLatest<T> {
    /// Sequence number of the latest issued request.
    issued: u64,
    /// Sequence number of the latest accepted answer.
    accepted: u64,
    /// Value held for `accepted`, if any answer has arrived.
    value: Option<T>,
}

impl<T> Default for FilterLatest<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> FilterLatest<T> {
    /// Creates an empty sequencer with no issued requests.
    ///
    /// # Returns
    ///
    /// A new [`FilterLatest`] state.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            issued: 0,
            accepted: 0,
            value: None,
        }
    }

    /// Replaces the current value immediately and invalidates all earlier in-flight requests.
    ///
    /// # Arguments
    ///
    /// * `value` - New baseline value (such as the unfiltered rows of a freshly opened binary).
    pub fn reset(&mut self, value: T) {
        self.issued = self.issued.saturating_add(1);
        self.accepted = self.issued;
        self.value = Some(value);
    }

    /// Clears the current value immediately and invalidates all earlier in-flight requests.
    pub fn clear(&mut self) {
        self.issued = self.issued.saturating_add(1);
        self.accepted = self.issued;
        self.value = None;
    }

    /// Issues a new request ticket higher than every previous ticket.
    ///
    /// # Returns
    ///
    /// Sequence ticket to pass to [`FilterLatest::accept`] when the background task finishes.
    pub fn issue(&mut self) -> u64 {
        self.issued = self.issued.saturating_add(1);
        self.issued
    }

    /// Accepts `value` only when `seq` is strictly newer than the already accepted answer
    /// and matches the latest issued request (or supersedes older ones).
    ///
    /// # Arguments
    ///
    /// * `seq` - Ticket returned by [`FilterLatest::issue`].
    /// * `value` - Answer produced for `seq`.
    ///
    /// # Returns
    ///
    /// `true` when `value` became the active answer, `false` when discarded as stale.
    pub fn accept(&mut self, seq: u64, value: T) -> bool {
        if seq < self.issued || seq <= self.accepted {
            return false;
        }
        self.accepted = seq;
        self.value = Some(value);
        true
    }

    /// Returns the ticket of the latest issued request.
    #[must_use]
    pub const fn issued(&self) -> u64 {
        self.issued
    }

    /// Returns the ticket of the latest accepted answer; every request up to it is
    /// answered or superseded.
    #[must_use]
    pub const fn accepted(&self) -> u64 {
        self.accepted
    }

    /// Returns the most recent accepted answer.
    ///
    /// # Returns
    ///
    /// Active value, or `None` before any reset or accepted answer.
    #[must_use]
    pub const fn current(&self) -> Option<&T> {
        self.value.as_ref()
    }
}

/// Monotonic ticket and cooperative [`Cancel`] pair invalidating superseded background work.
#[derive(Debug, Default)]
pub struct TaskEpoch {
    /// Current generation counter; incremented on every start or invalidation.
    seq: u64,
    /// Active cancellation flag for the current generation, if any task is running.
    cancel: Option<Cancel>,
}

impl TaskEpoch {
    /// Creates an idle [`TaskEpoch`] at generation `0`.
    ///
    /// # Returns
    ///
    /// A new idle [`TaskEpoch`].
    #[must_use]
    pub const fn new() -> Self {
        Self {
            seq: 0,
            cancel: None,
        }
    }

    /// Raises any active [`Cancel`] flag and advances the generation so in-flight tickets expire.
    pub fn invalidate(&mut self) {
        if let Some(prev) = self.cancel.take() {
            prev.raise();
        }
        self.seq = self.seq.saturating_add(1);
    }

    /// Invalidates any prior generation and starts a fresh one with a new [`Cancel`] token.
    ///
    /// # Returns
    ///
    /// `(ticket, cancel)` to pass into the background task and check on completion.
    #[must_use]
    pub fn begin(&mut self) -> (u64, Cancel) {
        self.invalidate();
        let cancel = Cancel::new();
        self.cancel = Some(cancel.clone());
        (self.seq, cancel)
    }

    /// Returns the current generation counter.
    #[must_use]
    pub const fn seq(&self) -> u64 {
        self.seq
    }

    /// Reports whether `ticket` and `cancel` still belong to the active, uncancelled generation.
    ///
    /// # Arguments
    ///
    /// * `ticket` - Generation counter returned by [`Self::begin`].
    /// * `cancel` - Cooperative [`Cancel`] flag returned by [`Self::begin`].
    ///
    /// # Returns
    ///
    /// `true` when `ticket` matches the current generation and `cancel` was not raised.
    #[must_use]
    pub fn is_current(&self, ticket: u64, cancel: &Cancel) -> bool {
        ticket == self.seq && !cancel.is_raised()
    }
}

#[cfg(test)]
mod tests {
    use super::{FilterLatest, TaskEpoch};

    /// No module of the app but this one names the engine's compute calls outside its
    /// tests, so each such call goes through [`super::run_engine`] and is counted.
    ///
    /// # Panics
    ///
    /// Panics if another module names `Program::load`, `Analysis::compute`, a decompile
    /// or listing view, the resolver, the function listing or the check of an answer.
    #[test]
    fn only_the_worker_names_engine_compute_calls() {
        let sources = [
            ("actions.rs", include_str!("actions.rs")),
            ("app_assets.rs", include_str!("app_assets.rs")),
            ("app_view.rs", include_str!("app_view.rs")),
            ("binary.rs", include_str!("binary.rs")),
            ("code_semantics.rs", include_str!("code_semantics.rs")),
            ("code_view.rs", include_str!("code_view.rs")),
            ("decompile_item.rs", include_str!("decompile_item.rs")),
            ("functions_panel.rs", include_str!("functions_panel.rs")),
            ("goto.rs", include_str!("goto.rs")),
            ("lib.rs", include_str!("lib.rs")),
            ("main.rs", include_str!("main.rs")),
            ("measure.rs", include_str!("measure.rs")),
            ("measure/drop.rs", include_str!("measure/drop.rs")),
            ("measure/input.rs", include_str!("measure/input.rs")),
            ("measure/scroll.rs", include_str!("measure/scroll.rs")),
            ("menus.rs", include_str!("menus.rs")),
            ("rail.rs", include_str!("rail.rs")),
            ("recent.rs", include_str!("recent.rs")),
            ("shell.rs", include_str!("shell.rs")),
            ("start_item.rs", include_str!("start_item.rs")),
            ("status.rs", include_str!("status.rs")),
            ("title_bar.rs", include_str!("title_bar.rs")),
        ];
        let calls = [
            "Program::load",
            "Analysis::compute",
            "decompile::view",
            "disasm_view(",
            "resolve_suggesting(",
            "function_rows(",
            "text_check(",
            "answered_flagged(",
        ];
        for (name, text) in sources {
            let code = text.split("#[cfg(test)]").next().unwrap_or(text);
            for call in calls {
                assert!(!code.contains(call), "{name} names {call}");
            }
        }
    }

    /// Older filter requests finishing after a newer one are discarded.
    ///
    /// # Panics
    ///
    /// Panics if a stale answer overwrites the newest request's answer.
    #[test]
    fn newest_filter_request_wins_over_late_older_answer() {
        let mut seq = FilterLatest::new();
        seq.reset("all");
        assert_eq!(seq.current().copied(), Some("all"));

        let older = seq.issue();
        let newer = seq.issue();

        assert!(seq.accept(newer, "new-rows"));
        assert_eq!(seq.current().copied(), Some("new-rows"));

        assert!(!seq.accept(older, "stale-rows"));
        assert_eq!(seq.current().copied(), Some("new-rows"));
    }

    /// Clearing or resetting rows permanently rejects in-flight filter tickets from an earlier binary.
    ///
    /// # Panics
    ///
    /// Panics if a prior binary's ticket is accepted after [`FilterLatest::clear`] or [`FilterLatest::reset`].
    #[test]
    fn reset_and_clear_permanently_reject_prior_binary_filter_tickets() {
        let mut seq = FilterLatest::new();
        seq.reset("binary-a-all");
        let ticket_a = seq.issue();

        seq.clear();
        assert_eq!(seq.current().copied(), None);
        assert!(!seq.accept(ticket_a, "binary-a-filtered"));

        seq.reset("binary-b-all");
        assert_eq!(seq.current().copied(), Some("binary-b-all"));
        assert!(!seq.accept(ticket_a, "binary-a-filtered"));

        let ticket_b = seq.issue();
        assert!(!seq.accept(ticket_a, "binary-a-filtered"));
        assert!(seq.accept(ticket_b, "binary-b-filtered"));
        assert_eq!(seq.current().copied(), Some("binary-b-filtered"));
    }

    /// Invalidating an epoch when switching binaries cancels and rejects an in-flight decompile.
    ///
    /// # Panics
    ///
    /// Panics if a superseded generation stays current or fails to raise its cancel flag.
    #[test]
    fn task_epoch_invalidation_cancels_and_rejects_prior_binary_ticket() {
        let mut decompile_epoch = TaskEpoch::new();
        let (ticket_a, cancel_a) = decompile_epoch.begin();
        assert!(decompile_epoch.is_current(ticket_a, &cancel_a));
        assert!(!cancel_a.is_raised());

        decompile_epoch.invalidate();
        assert!(cancel_a.is_raised());
        assert!(!decompile_epoch.is_current(ticket_a, &cancel_a));

        let (ticket_b, cancel_b) = decompile_epoch.begin();
        assert!(ticket_b > ticket_a);
        assert!(decompile_epoch.is_current(ticket_b, &cancel_b));
        assert!(!decompile_epoch.is_current(ticket_a, &cancel_b));
    }
}
