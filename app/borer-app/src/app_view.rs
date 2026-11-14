//! Main window view hosting the function table, filter bar, and clickable decompile pane.

use std::collections::VecDeque;
use std::io::{BufRead as _, Write as _};
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::decompile::view::view as build_decompile_view;
use borer_engine::analysis::render::{FunctionRow, FunctionRows};
use borer_engine::cancel::Cancel;
use borer_engine::view::{Ref, View};
use gpui::{
    AnyElement, AppContext as _, Context, Entity, FocusHandle, InteractiveElement as _,
    InteractiveText, IntoElement, KeyDownEvent, ParentElement as _, PathPromptOptions, Render,
    ScrollStrategy, SharedString, StatefulInteractiveElement as _, Styled as _, StyledText, Task,
    TextLayout, UniformListScrollHandle, Window, div, px, uniform_list,
};
use theme::ActiveTheme as _;
use ui::{Label, Table, TableInteractionState};

use crate::actions::{
    ActionId, FocusFilter, GoBack, GoForward, Measure, NextRow, Open, OpenSelected, PageDown,
    PageUp, PreviousRow, TogglePalette,
};
use crate::code_view::{ClickOutcome, CodePalette, resolve_ref_click, style_view_line};
use crate::history::NavHistory;
use crate::measure::{
    CliExitSlot, CliMode, CorpusCode, InjectMark, MarkWait, MeasurePhase, OneShotAction,
    PendingInputMark, TARGET_CODE_LINES, begin_code_scroll_phase, begin_input_latency_phase,
    begin_list_scroll_phase, evaluate_one_shot, new_cli_exit_slot, now_instant,
};
use crate::palette::{CommandPalette, handle_palette_key_down, render_palette_overlay};
use crate::worker::{
    FilterLatest, LoadedBinary, TaskEpoch, filter_rows_blocking, load_binary_blocking,
    spawn_engine, ui_engine_calls,
};

/// Note appended to status messages explaining what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// Number of columns in the function table.
const TABLE_COLS: usize = 8;

/// Uniform height in logical pixels of each line row in the decompile pane.
const CODE_ROW_HEIGHT_PX: f32 = 20.0;

/// Root view managing the loaded binary, filter bar, function table, and decompile view.
pub struct AppView {
    /// Active CLI startup or benchmark mode.
    mode: CliMode,
    /// Shared exit error slot for non-interactive CLI failure propagation.
    exit_slot: CliExitSlot,
    /// Whether the one-shot startup hook (`--first-frame`, `--report-open`, etc.) has fired.
    mode_reported: bool,
    /// Whether a benchmark run is currently active (prevents re-entrant `Ctrl+Shift+M`).
    measuring: bool,
    /// Root focus handle for keyboard shortcuts outside the filter bar.
    focus_handle: FocusHandle,
    /// Focus handle for the keystroke filter field.
    filter_focus: FocusHandle,
    /// Focus handle for the command palette overlay input.
    palette_focus: FocusHandle,
    /// Keyboard command palette listing [`crate::actions::ACTION_REGISTRY`].
    palette: CommandPalette,
    /// Scroll and focus state for the [`Table`] component.
    table_state: Entity<TableInteractionState>,
    /// Scroll handle driving the virtualized decompile line list.
    code_scroll: UniformListScrollHandle,
    /// Currently loaded binary and analysis, if one has finished loading.
    loaded: Option<Arc<LoadedBinary>>,
    /// Error text from the most recent failed load, if any.
    load_error: Option<String>,
    /// Sequenced function-table rows matching [`Self::filter_text`].
    rows_seq: FilterLatest<Arc<FunctionRows>>,
    /// Optional virtual row count repeating [`Self::rows_seq`] by index (`100_000` in `--measure`).
    virtual_row_count: Option<usize>,
    /// Optional 1,000,000-line corpus code table used during the code scroll benchmark.
    corpus_code: Option<Arc<CorpusCode>>,
    /// Index of the highlighted row within the active [`FunctionRows`].
    selected_row: usize,
    /// Plain keystroke filter query.
    filter_text: String,
    /// Back/forward navigation stack of opened function entries.
    history: NavHistory,
    /// Active tokenized decompile [`View`] displayed in the right pane.
    active_view: Option<Arc<View>>,
    /// Generation and cooperative [`Cancel`] state for in-flight binary loads.
    load_epoch: TaskEpoch,
    /// Generation and cooperative [`Cancel`] state for in-flight decompilations.
    decompile_epoch: TaskEpoch,
    /// Generation and cooperative [`Cancel`] state for interactive or CLI measurement runs.
    measure_epoch: TaskEpoch,
    /// Whether a background decompilation is currently awaiting completion.
    decompiling: bool,
    /// Count of character/backspace/escape keystrokes handled in the filter input.
    filter_keys_count: u64,
    /// Count of `Ref::Function` call-token clicks handled in `InteractiveText`.
    call_clicks_count: u64,
    /// Painted [`TextLayout`] and byte index of the first visible `Ref::Function` token.
    call_token_layout: Option<(TextLayout, usize)>,
    /// Pre-`SendInput` timestamp slot active during `--measure --phase input`.
    inject_mark: Option<InjectMark>,
    /// FIFO queue of unpresented [`PendingInputMark`] timestamps in arrival order.
    pending_marks: VecDeque<PendingInputMark>,
    /// Whether the back entry of [`Self::pending_marks`] belongs to the currently dispatching event.
    active_dispatch_pending: bool,
    /// Status message displayed at the bottom of the window.
    status: String,
    /// In-flight binary load task.
    load_task: Option<Task<()>>,
    /// In-flight background filter task.
    filter_task: Option<Task<()>>,
    /// In-flight background decompile task.
    decompile_task: Option<Task<()>>,
    /// In-flight native file-picker prompt task.
    prompt_task: Option<Task<()>>,
    /// In-flight automated measurement orchestration task.
    measure_task: Option<Task<()>>,
}

impl std::fmt::Debug for AppView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppView")
            .field("mode", &self.mode)
            .field("measuring", &self.measuring)
            .field("selected_row", &self.selected_row)
            .field("filter_text", &self.filter_text)
            .field("current_entry", &self.history.current())
            .field("status", &self.status)
            .finish_non_exhaustive()
    }
}

impl AppView {
    /// Creates an [`AppView`] configured for `mode` and bound to `exit_slot`.
    ///
    /// # Arguments
    ///
    /// * `mode` - Startup or benchmark [`CliMode`].
    /// * `exit_slot` - Shared error slot populated when a non-interactive CLI mode fails.
    /// * `window` - Window hosting the view.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// The initialized [`AppView`].
    #[must_use]
    pub fn new_with_mode(
        mode: CliMode,
        exit_slot: CliExitSlot,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let focus_handle = cx.focus_handle();
        let filter_focus = cx.focus_handle();
        let palette_focus = cx.focus_handle();
        window.focus(&focus_handle, cx);
        let table_state = cx.new(|cx| TableInteractionState::new(cx));
        let mut view = Self {
            mode: mode.clone(),
            exit_slot,
            mode_reported: false,
            measuring: false,
            focus_handle,
            filter_focus,
            palette_focus,
            palette: CommandPalette::new(),
            table_state,
            code_scroll: UniformListScrollHandle::new(),
            loaded: None,
            load_error: None,
            rows_seq: FilterLatest::new(),
            virtual_row_count: None,
            corpus_code: None,
            selected_row: 0,
            filter_text: String::new(),
            history: NavHistory::new(),
            active_view: None,
            load_epoch: TaskEpoch::new(),
            decompile_epoch: TaskEpoch::new(),
            measure_epoch: TaskEpoch::new(),
            decompiling: false,
            filter_keys_count: 0,
            call_clicks_count: 0,
            call_token_layout: None,
            inject_mark: None,
            pending_marks: VecDeque::new(),
            active_dispatch_pending: false,
            status: format!("Press Ctrl+O to open a binary ({LOAD_SCOPE_NOTE})"),
            load_task: None,
            filter_task: None,
            decompile_task: None,
            prompt_task: None,
            measure_task: None,
        };
        view.start_mode(mode, window, cx);
        view
    }

    /// Creates an interactive [`AppView`], optionally starting a background load of `initial_path`.
    ///
    /// # Arguments
    ///
    /// * `initial_path` - Optional binary file path to open at launch.
    /// * `window` - Window hosting the view.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// The initialized interactive [`AppView`].
    #[must_use]
    pub fn new(
        initial_path: Option<PathBuf>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        Self::new_with_mode(
            CliMode::Interactive(initial_path),
            new_cli_exit_slot(),
            window,
            cx,
        )
    }

    /// Dispatches startup behavior requested by `mode`.
    ///
    /// # Arguments
    ///
    /// * `mode` - Requested [`CliMode`].
    /// * `window` - Window hosting the view.
    /// * `cx` - View context.
    fn start_mode(&mut self, mode: CliMode, window: &mut Window, cx: &mut Context<'_, Self>) {
        match mode {
            CliMode::Interactive(Some(path))
            | CliMode::ReportOpen(path)
            | CliMode::MeasureMemory(path) => {
                self.open_path(path, cx);
            }
            CliMode::Interactive(None) | CliMode::FirstFrame | CliMode::Headless(_) => {}
            CliMode::Measure(MeasurePhase::BothScrolls) => {
                begin_list_scroll_phase(self, true, true, window, cx);
            }
            CliMode::Measure(MeasurePhase::ListScroll) => {
                begin_list_scroll_phase(self, false, true, window, cx);
            }
            CliMode::Measure(MeasurePhase::CodeScroll) => {
                begin_code_scroll_phase(self, true, window, cx);
            }
            CliMode::Measure(MeasurePhase::InputLatency) => {
                begin_input_latency_phase(self, window, cx);
            }
        }
    }

    /// Cancels and invalidates any in-flight binary load task.
    fn cancel_load(&mut self) {
        self.load_epoch.invalidate();
        self.load_task = None;
        self.load_error = None;
    }

    /// Cancels and invalidates any in-flight function decompilation task.
    fn cancel_decompile(&mut self) {
        self.decompile_epoch.invalidate();
        self.decompiling = false;
        self.decompile_task = None;
        self.call_token_layout = None;
        let ready = now_instant();
        for mark in &mut self.pending_marks {
            if matches!(mark.wait, MarkWait::Decompile(_)) {
                mark.ready_at = Some(ready);
                mark.wait = MarkWait::Immediate;
            }
        }
    }

    /// Cancels and invalidates any running or preparing benchmark task.
    pub fn cancel_measure(&mut self) {
        self.measure_epoch.invalidate();
        self.measure_task = None;
        self.inject_mark = None;
        self.pending_marks.clear();
        self.active_dispatch_pending = false;
        self.measuring = false;
    }

    /// Attaches or clears the pre-`SendInput` [`InjectMark`] slot for input-latency profiling.
    ///
    /// # Arguments
    ///
    /// * `mark` - Shared [`InjectMark`] populated right before `SendInput`.
    pub fn set_inject_mark(&mut self, mark: Option<InjectMark>) {
        self.inject_mark = mark;
        self.pending_marks.clear();
        self.active_dispatch_pending = false;
    }

    /// Captures the arrival timestamp of a marked input event and schedules presentation.
    ///
    /// # Arguments
    ///
    /// * `track_async` - `true` when target/bubble handlers may bind background work to this mark.
    /// * `cx` - View context scheduling a frame draw when an armed mark arrives.
    pub fn record_inject_arrival(&mut self, track_async: bool, cx: &mut Context<'_, Self>) {
        self.active_dispatch_pending = false;
        let Some(tracker) = &self.inject_mark else {
            return;
        };
        if let Some((id, injected_at)) = tracker.take_armed() {
            let arrived_at = now_instant();
            self.pending_marks.push_back(PendingInputMark {
                id,
                injected_at,
                arrived_at,
                ready_at: Some(arrived_at),
                wait: MarkWait::Immediate,
            });
            self.active_dispatch_pending = track_async;
            cx.notify();
        }
    }

    /// Clears the synchronous event-dispatch mark guard before programmatic navigation.
    pub fn clear_dispatch_mark(&mut self) {
        self.active_dispatch_pending = false;
    }

    /// Binds `wait` to the [`PendingInputMark`] pushed during the current event dispatch, if any.
    ///
    /// # Arguments
    ///
    /// * `wait` - Background completion condition required before the mark may retire.
    fn bind_dispatch_mark(&mut self, wait: MarkWait) {
        if std::mem::replace(&mut self.active_dispatch_pending, false)
            && let Some(last) = self.pending_marks.back_mut()
        {
            last.ready_at = None;
            last.wait = wait;
        }
    }

    /// Marks every pending [`MarkWait::Filter`] entry up to `accepted_seq` ready to present.
    ///
    /// # Arguments
    ///
    /// * `accepted_seq` - Installed [`FilterLatest`] sequence number.
    fn complete_filter_marks(&mut self, accepted_seq: u64) {
        let ready = now_instant();
        for mark in &mut self.pending_marks {
            if let MarkWait::Filter(seq) = mark.wait
                && seq <= accepted_seq
            {
                mark.ready_at = Some(ready);
                mark.wait = MarkWait::Immediate;
            }
        }
    }

    /// Marks every pending [`MarkWait::Decompile`] entry up to `completed_ticket` ready to present.
    ///
    /// # Arguments
    ///
    /// * `completed_ticket` - Installed [`TaskEpoch`] decompile generation counter.
    fn complete_decompile_marks(&mut self, completed_ticket: u64) {
        let ready = now_instant();
        for mark in &mut self.pending_marks {
            if let MarkWait::Decompile(ticket) = mark.wait
                && ticket <= completed_ticket
            {
                mark.ready_at = Some(ready);
                mark.wait = MarkWait::Immediate;
            }
        }
    }

    /// Borrows the active [`InjectMark`] tracker, if input-latency profiling is armed.
    ///
    /// # Returns
    ///
    /// Shared [`InjectMark`] handle, or `None` outside `--measure --phase input`.
    #[must_use]
    pub const fn inject_tracker(&self) -> Option<&InjectMark> {
        self.inject_mark.as_ref()
    }

    /// Reports whether any [`PendingInputMark`] entries are still awaiting presentation.
    ///
    /// # Returns
    ///
    /// `true` when [`Self::pending_marks`] is non-empty.
    #[must_use]
    pub fn has_pending_marks(&self) -> bool {
        !self.pending_marks.is_empty()
    }

    /// Borrows the FIFO queue of unpresented [`PendingInputMark`] records.
    ///
    /// # Returns
    ///
    /// Mutable reference to [`Self::pending_marks`].
    #[must_use]
    pub fn pending_marks_mut(&mut self) -> &mut VecDeque<PendingInputMark> {
        &mut self.pending_marks
    }

    /// Starts a new measurement generation, cancelling any prior measurement task.
    ///
    /// # Returns
    ///
    /// `(ticket, cancel)` guarding background preparation and foreground installation.
    #[must_use]
    pub fn begin_measure(&mut self) -> (u64, Cancel) {
        self.cancel_measure();
        self.measuring = true;
        self.measure_epoch.begin()
    }

    /// Reports whether `ticket` and `cancel` still belong to the active measurement run.
    ///
    /// # Arguments
    ///
    /// * `ticket` - Generation counter returned by [`Self::begin_measure`].
    /// * `cancel` - Cooperative [`Cancel`] flag returned by [`Self::begin_measure`].
    ///
    /// # Returns
    ///
    /// `true` while measurement remains active and uncancelled for `ticket`.
    #[must_use]
    pub fn is_measure_current(&self, ticket: u64, cancel: &Cancel) -> bool {
        self.measuring && self.measure_epoch.is_current(ticket, cancel)
    }

    /// Reports whether [`NavHistory`] holds an earlier function entry to return to.
    ///
    /// # Returns
    ///
    /// `true` when [`Self::navigate_back`] can step to a prior entry.
    #[must_use]
    pub fn can_go_back(&self) -> bool {
        self.history.can_go_back()
    }

    /// Records a fatal non-interactive CLI error and quits the GPUI run loop.
    ///
    /// # Arguments
    ///
    /// * `err` - Error to return from [`crate::run`].
    /// * `cx` - View context used to quit the application.
    pub fn fail_cli(&mut self, err: anyhow::Error, cx: &mut Context<'_, Self>) {
        *self.exit_slot.borrow_mut() = Some(err);
        cx.quit();
    }

    /// Clears the interactive measurement guard and reports an error in the status bar.
    ///
    /// # Arguments
    ///
    /// * `message` - Human-readable error status text.
    /// * `cx` - View context used to schedule a repaint.
    pub fn finish_interactive_measure_error(
        &mut self,
        message: String,
        cx: &mut Context<'_, Self>,
    ) {
        self.measuring = false;
        self.status = message;
        cx.notify();
    }

    /// Reports whether an interactive or CLI benchmark phase is currently active.
    ///
    /// # Returns
    ///
    /// `true` while a scroll or input benchmark is running.
    #[must_use]
    pub const fn is_measuring(&self) -> bool {
        self.measuring
    }

    /// Updates whether a benchmark phase is currently active.
    ///
    /// # Arguments
    ///
    /// * `active` - `true` when starting a benchmark phase, `false` when it settles.
    pub fn set_measuring(&mut self, active: bool) {
        self.measuring = active;
    }

    /// Stores the active measurement task handle on [`AppView`].
    ///
    /// # Arguments
    ///
    /// * `task` - Background orchestration [`Task`] to retain until completion.
    pub fn set_measure_task(&mut self, task: Task<()>) {
        self.measure_task = Some(task);
    }

    /// Installs `loaded` with `virtual_rows` index-repeated rows for the 100k-row list benchmark.
    ///
    /// # Arguments
    ///
    /// * `loaded` - Analyzed binary whose rows are repeated by index.
    /// * `virtual_rows` - Virtual row count exposed to `uniform_list`.
    /// * `cx` - View context.
    pub fn install_virtual_list(
        &mut self,
        loaded: Arc<LoadedBinary>,
        virtual_rows: usize,
        cx: &mut Context<'_, Self>,
    ) {
        self.cancel_load();
        self.cancel_decompile();
        let rows = Arc::new(loaded.initial_rows.clone());
        self.corpus_code = None;
        self.active_view = None;
        self.history.clear();
        self.virtual_row_count = Some(virtual_rows);
        self.rows_seq.reset(rows);
        self.loaded = Some(loaded);
        cx.notify();
    }

    /// Installs `corpus` for the 1,000,000-line decompile-view scroll benchmark.
    ///
    /// # Arguments
    ///
    /// * `loaded` - Analyzed binary backing `corpus`.
    /// * `corpus` - Flattened decompile views across every discovered function.
    /// * `cx` - View context.
    pub fn install_corpus_code(
        &mut self,
        loaded: Arc<LoadedBinary>,
        corpus: Arc<CorpusCode>,
        cx: &mut Context<'_, Self>,
    ) {
        self.cancel_load();
        self.cancel_decompile();
        let rows = Arc::new(loaded.initial_rows.clone());
        self.virtual_row_count = None;
        self.active_view = None;
        self.history.clear();
        self.rows_seq.reset(rows);
        self.loaded = Some(loaded);
        self.corpus_code = Some(corpus);
        cx.notify();
    }

    /// Installs `loaded`, focuses the filter input, and opens `entry` for `--measure --phase input`.
    ///
    /// # Arguments
    ///
    /// * `loaded` - Analyzed binary under test.
    /// * `entry` - Function entry address containing a visible `Ref::Function` call token.
    /// * `window` - Window receiving keyboard focus in the filter box.
    /// * `cx` - View context.
    pub fn install_for_input_bench(
        &mut self,
        loaded: Arc<LoadedBinary>,
        entry: u64,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.cancel_load();
        self.cancel_decompile();
        let rows = Arc::new(loaded.initial_rows.clone());
        self.virtual_row_count = None;
        self.corpus_code = None;
        self.active_view = None;
        self.history.clear();
        self.filter_keys_count = 0;
        self.call_clicks_count = 0;
        self.rows_seq.reset(rows);
        self.loaded = Some(loaded);
        window.focus(&self.filter_focus, cx);
        self.clear_dispatch_mark();
        self.open_function(entry, true, cx);
    }

    /// Scrolls the function table to `item_ix` using `strategy`.
    ///
    /// # Arguments
    ///
    /// * `item_ix` - Zero-based row index to bring into view.
    /// * `strategy` - GPUI [`ScrollStrategy`] governing placement.
    /// * `cx` - View context reading the [`TableInteractionState`] entity.
    pub fn scroll_table_to(
        &self,
        item_ix: usize,
        strategy: ScrollStrategy,
        cx: &Context<'_, Self>,
    ) {
        self.table_state
            .read(cx)
            .scroll_handle
            .scroll_to_item(item_ix, strategy);
    }

    /// Scrolls the decompile code view to `line_ix` using `strategy`.
    ///
    /// # Arguments
    ///
    /// * `line_ix` - Zero-based virtual line index.
    /// * `strategy` - GPUI [`ScrollStrategy`] governing placement.
    pub fn scroll_code_to(&self, line_ix: usize, strategy: ScrollStrategy) {
        self.code_scroll.scroll_to_item(line_ix, strategy);
    }

    /// Reports whether [`Self::active_view`] is populated.
    ///
    /// # Returns
    ///
    /// `true` when a decompiled [`View`] is ready in the code pane.
    #[must_use]
    pub const fn has_active_view(&self) -> bool {
        self.active_view.is_some()
    }

    /// Reports whether a background decompilation is still running.
    ///
    /// # Returns
    ///
    /// `true` while awaiting an [`Self::open_function`] task.
    #[must_use]
    pub const fn decompile_in_flight(&self) -> bool {
        self.decompiling
    }

    /// Returns how many filter keystrokes have been processed.
    ///
    /// # Returns
    ///
    /// Total character, backspace, and escape keystrokes handled in the filter bar.
    #[must_use]
    pub const fn filter_keys_handled(&self) -> u64 {
        self.filter_keys_count
    }

    /// Returns how many `Ref::Function` call-token clicks have fired.
    ///
    /// # Returns
    ///
    /// Total function-call token clicks dispatched through [`InteractiveText`].
    #[must_use]
    pub const fn call_clicks(&self) -> u64 {
        self.call_clicks_count
    }

    /// Resolves the logical client `(x, y)` center of the first visible `Ref::Function` token.
    ///
    /// # Returns
    ///
    /// Logical `(x, y)` client coordinates, or `None` when no call token is visible yet.
    #[must_use]
    pub fn call_token_client_xy(&self) -> Option<(f32, f32)> {
        let (layout, byte_ix) = self.call_token_layout.as_ref()?;
        let pt = layout.position_for_index(*byte_ix)?;
        Some((f32::from(pt.x) + 3.0, f32::from(pt.y) + 7.0))
    }

    /// Opens a native file dialog and loads the chosen binary in the background.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context spawning the dialog receiver task.
    pub fn prompt_open(&mut self, cx: &mut Context<'_, Self>) {
        self.palette.close();
        cx.notify();
        let receiver = cx.prompt_for_paths(PathPromptOptions {
            files: true,
            directories: false,
            multiple: false,
            prompt: None,
        });
        self.prompt_task = Some(cx.spawn(async move |this, cx| {
            let Ok(outcome) = receiver.await else {
                return;
            };
            let _ = this.update(cx, |view, cx| match outcome {
                Ok(Some(mut paths)) => {
                    if let Some(path) = paths.pop() {
                        view.open_path(path, cx);
                    }
                }
                Ok(None) => {}
                Err(err) => {
                    view.status = format!("open dialog failed: {err:#}");
                    cx.notify();
                }
            });
        }));
    }

    /// Starts loading and analyzing `path` on the background executor.
    ///
    /// # Arguments
    ///
    /// * `path` - File path of the binary to load.
    /// * `cx` - View context spawning the background task.
    pub fn open_path(&mut self, path: PathBuf, cx: &mut Context<'_, Self>) {
        self.palette.close();
        self.cancel_measure();
        self.cancel_decompile();
        self.load_error = None;
        self.loaded = None;
        self.active_view = None;
        self.rows_seq.clear();
        self.filter_task = None;
        self.virtual_row_count = None;
        self.corpus_code = None;
        self.selected_row = 0;
        self.history.clear();
        let (ticket, worker_cancel) = self.load_epoch.begin();
        let check_cancel = worker_cancel.clone();
        self.status = format!("loading {} ({LOAD_SCOPE_NOTE})", path.display());
        cx.notify();
        let bg = spawn_engine(cx, move || {
            worker_cancel.within(|| load_binary_blocking(path))
        });
        self.load_task = Some(cx.spawn(async move |this, cx| {
            let result = bg.await;
            let _ = this.update(cx, |view, cx| {
                if !view.load_epoch.is_current(ticket, &check_cancel) {
                    return;
                }
                view.finish_load(result, cx);
            });
        }));
    }

    /// Applies the result of a background load, showing errors in the status bar.
    ///
    /// # Arguments
    ///
    /// * `result` - Outcome of [`load_binary_blocking`].
    /// * `cx` - View context scheduling a repaint.
    fn finish_load(
        &mut self,
        result: anyhow::Result<Arc<LoadedBinary>>,
        cx: &mut Context<'_, Self>,
    ) {
        self.cancel_decompile();
        match result {
            Ok(loaded) => {
                let rows = Arc::new(loaded.initial_rows.clone());
                let count = rows.rows.len();
                let left_out = rows.left_out.clone();
                let first_entry = rows.rows.first().map(|r| r.entry);
                let display = loaded.path.display().to_string();
                self.load_error = None;
                self.filter_text.clear();
                self.virtual_row_count = None;
                self.corpus_code = None;
                self.selected_row = 0;
                self.history.clear();
                self.active_view = None;
                self.rows_seq.reset(rows);
                self.loaded = Some(loaded);
                self.status = format!("{display}: {count} functions{left_out} ({LOAD_SCOPE_NOTE})");
                self.scroll_to_selected(cx);
                let skip_initial_decompile = matches!(self.mode, CliMode::ReportOpen(_));
                if !skip_initial_decompile && let Some(entry) = first_entry {
                    self.clear_dispatch_mark();
                    self.open_function(entry, true, cx);
                }
            }
            Err(err) => {
                let msg = format!("{err:#}");
                self.loaded = None;
                self.active_view = None;
                self.rows_seq.clear();
                self.history.clear();
                self.virtual_row_count = None;
                self.corpus_code = None;
                self.load_error = Some(msg.clone());
                self.status = format!("load failed: {msg}");
            }
        }
        cx.notify();
    }

    /// Decompiles `entry` in the background under a fresh [`TaskEpoch`] generation.
    ///
    /// # Arguments
    ///
    /// * `entry` - Function entry address to decompile.
    /// * `record_history` - `true` when opening a new history entry, `false` on Back/Forward.
    /// * `cx` - View context spawning the background decompile task.
    pub fn open_function(&mut self, entry: u64, record_history: bool, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.loaded.clone() else {
            return;
        };
        if record_history {
            let _ = self.history.open(entry);
        }
        if let Some(rows) = self.rows_seq.current()
            && let Some(pos) = rows.rows.iter().position(|r| r.entry == entry)
        {
            self.selected_row = pos;
            self.scroll_to_selected(cx);
        }
        let (ticket, worker_cancel) = self.decompile_epoch.begin();
        let check_cancel = worker_cancel.clone();
        self.bind_dispatch_mark(MarkWait::Decompile(ticket));
        self.active_view = None;
        self.decompiling = true;
        self.call_token_layout = None;
        self.status = format!("decompiling {entry:#x} ({LOAD_SCOPE_NOTE})");
        cx.notify();

        let bg = spawn_engine(cx, move || {
            worker_cancel.within(|| {
                build_decompile_view(&loaded.program, &loaded.analysis, &loaded.overlay, entry)
            })
        });
        self.decompile_task = Some(cx.spawn(async move |this, cx| {
            let built = bg.await;
            let _ = this.update(cx, |view, cx| {
                if !view.decompile_epoch.is_current(ticket, &check_cancel) {
                    return;
                }
                view.decompiling = false;
                match built {
                    Some(v) => {
                        let lines = v.lines();
                        view.active_view = Some(v);
                        view.code_scroll.scroll_to_item(0, ScrollStrategy::Top);
                        view.status =
                            format!("opened {entry:#x}: {lines} lines ({LOAD_SCOPE_NOTE})");
                    }
                    None => {
                        view.active_view = None;
                        view.status = format!("no function at {entry:#x} ({LOAD_SCOPE_NOTE})");
                    }
                }
                view.complete_decompile_marks(ticket);
                cx.notify();
            });
        }));
    }

    /// Steps backward in [`NavHistory`] and opens the previous function.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    pub fn navigate_back(&mut self, cx: &mut Context<'_, Self>) {
        let was_open = self.palette.is_open();
        self.palette.close();
        if let Some(prev) = self.history.go_back() {
            self.open_function(prev, false, cx);
        } else if was_open {
            cx.notify();
        }
    }

    /// Steps forward in [`NavHistory`] and opens the next function.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    pub fn navigate_forward(&mut self, cx: &mut Context<'_, Self>) {
        let was_open = self.palette.is_open();
        self.palette.close();
        if let Some(next) = self.history.go_forward() {
            self.open_function(next, false, cx);
        } else if was_open {
            cx.notify();
        }
    }

    /// Issues a sequenced background filter query for [`Self::filter_text`].
    ///
    /// # Arguments
    ///
    /// * `cx` - View context spawning the background filter task.
    fn request_filter(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.loaded.clone() else {
            self.active_dispatch_pending = false;
            return;
        };
        let seq = self.rows_seq.issue();
        self.bind_dispatch_mark(MarkWait::Filter(seq));
        let query = self.filter_text.clone();
        let bg = spawn_engine(cx, move || Arc::new(filter_rows_blocking(&loaded, &query)));
        self.filter_task = Some(cx.spawn(async move |this, cx| {
            let rows = bg.await;
            let _ = this.update(cx, |view, cx| {
                if view.rows_seq.accept(seq, rows) {
                    view.selected_row = 0;
                    view.update_filter_status();
                    view.scroll_to_selected(cx);
                    view.complete_filter_marks(seq);
                    cx.notify();
                }
            });
        }));
    }

    /// Refreshes the status bar counts after a filter completes.
    fn update_filter_status(&mut self) {
        let (Some(loaded), Some(rows)) = (&self.loaded, self.rows_seq.current()) else {
            return;
        };
        let count = rows.rows.len();
        let display = loaded.path.display();
        if self.filter_text.is_empty() {
            self.status = format!(
                "{display}: {count} {}{} ({LOAD_SCOPE_NOTE})",
                rows.noun, rows.left_out
            );
        } else {
            self.status = format!(
                "{display}: {count} {} matching {:?}{} ({LOAD_SCOPE_NOTE})",
                rows.noun, self.filter_text, rows.left_out
            );
        }
    }

    /// Scrolls the function table so [`Self::selected_row`] stays visible.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context reading the table scroll handle.
    fn scroll_to_selected(&self, cx: &Context<'_, Self>) {
        let row = self.selected_row;
        self.table_state
            .read(cx)
            .scroll_handle
            .scroll_to_item(row, ScrollStrategy::Nearest);
    }

    /// Opens or closes the keyboard command palette overlay.
    ///
    /// # Arguments
    ///
    /// * `window` - Window managing keyboard focus.
    /// * `cx` - View context.
    pub fn toggle_palette(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        if self.palette.is_open() {
            self.dismiss_palette(window, cx);
        } else {
            self.palette.open();
            window.focus(&self.palette_focus, cx);
            cx.notify();
        }
    }

    /// Closes the command palette overlay and restores focus to the root view.
    ///
    /// # Arguments
    ///
    /// * `window` - Window managing keyboard focus.
    /// * `cx` - View context.
    pub fn dismiss_palette(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.palette.close();
        window.focus(&self.focus_handle, cx);
        cx.notify();
    }

    /// Closes the command palette if open and moves focus to the function-filter input.
    ///
    /// # Arguments
    ///
    /// * `window` - Window managing keyboard focus.
    /// * `cx` - View context.
    pub fn focus_filter(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.palette.close();
        window.focus(&self.filter_focus, cx);
        cx.notify();
    }

    /// Handles keyboard events delivered to the open command palette overlay.
    ///
    /// # Arguments
    ///
    /// * `event` - GPUI [`KeyDownEvent`].
    /// * `window` - Window managing focus and action dispatch.
    /// * `cx` - View context.
    pub fn on_palette_key_down(
        &mut self,
        event: &KeyDownEvent,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let root_focus = self.focus_handle.clone();
        handle_palette_key_down(&mut self.palette, &root_focus, event, window, cx);
    }

    /// Confirms and dispatches command palette match `ix` when clicked.
    ///
    /// # Arguments
    ///
    /// * `ix` - Clicked match index inside the open palette.
    /// * `window` - Window managing focus and action dispatch.
    /// * `cx` - View context.
    pub fn execute_palette_index(
        &mut self,
        ix: usize,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let chosen = self.palette.confirm_index(ix);
        window.focus(&self.focus_handle, cx);
        if let Some(id) = chosen
            && id != ActionId::TogglePalette
        {
            window.dispatch_action(id.boxed_action(), cx);
        }
        cx.notify();
    }

    /// Handles character, backspace, escape, and enter keystrokes inside the filter field.
    ///
    /// # Arguments
    ///
    /// * `event` - GPUI [`KeyDownEvent`] delivered to the focused filter input.
    /// * `window` - Window managing keyboard focus.
    /// * `cx` - View context.
    fn on_filter_key_down(
        &mut self,
        event: &KeyDownEvent,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let mods = event.keystroke.modifiers;
        if mods.control || mods.alt || mods.platform {
            self.active_dispatch_pending = false;
            return;
        }
        match event.keystroke.key.as_str() {
            "backspace" => {
                self.filter_keys_count = self.filter_keys_count.saturating_add(1);
                if self.filter_text.pop().is_some() {
                    self.request_filter(cx);
                }
                cx.notify();
            }
            "escape" => {
                self.filter_keys_count = self.filter_keys_count.saturating_add(1);
                if self.filter_text.is_empty() {
                    window.focus(&self.focus_handle, cx);
                } else {
                    self.filter_text.clear();
                    self.request_filter(cx);
                }
                cx.notify();
            }
            "enter" => {
                self.activate_row(self.selected_row, cx);
                window.focus(&self.focus_handle, cx);
            }
            "down" => self.step_row(1, cx),
            "up" => self.step_row(-1, cx),
            _ => {
                if let Some(ch) = &event.keystroke.key_char
                    && ch.chars().all(|c| !c.is_control())
                    && !ch.is_empty()
                {
                    self.filter_keys_count = self.filter_keys_count.saturating_add(1);
                    self.filter_text.push_str(ch);
                    self.request_filter(cx);
                    cx.notify();
                }
            }
        }
        self.active_dispatch_pending = false;
    }

    /// Moves [`Self::selected_row`] by `delta` within the active row list.
    ///
    /// # Arguments
    ///
    /// * `delta` - Signed row step (`1`, `-1`, `25`, `-25`).
    /// * `cx` - View context.
    fn step_row(&mut self, delta: isize, cx: &mut Context<'_, Self>) {
        let base_len = self.rows_seq.current().map_or(0, |r| r.rows.len());
        let len = self.virtual_row_count.unwrap_or(base_len);
        if len == 0 {
            return;
        }
        self.selected_row = self
            .selected_row
            .saturating_add_signed(delta)
            .min(len.saturating_sub(1));
        self.scroll_to_selected(cx);
        cx.notify();
    }

    /// Selects `row_ix` and opens that function's decompile view.
    ///
    /// # Arguments
    ///
    /// * `row_ix` - Highlighted row index in the function table.
    /// * `cx` - View context.
    fn activate_row(&mut self, row_ix: usize, cx: &mut Context<'_, Self>) {
        let Some(rows) = self.rows_seq.current() else {
            return;
        };
        if rows.rows.is_empty() {
            return;
        }
        let Some(entry) = rows.rows.get(row_ix % rows.rows.len()).map(|r| r.entry) else {
            return;
        };
        self.selected_row = row_ix;
        self.open_function(entry, true, cx);
    }

    /// Schedules one-shot stdout notifications for `--first-frame`, `--report-open`, and `--measure-memory`.
    ///
    /// # Arguments
    ///
    /// * `window` - Window registering the post-present callback.
    /// * `cx` - View context.
    fn check_one_shot_modes(&mut self, window: &Window, cx: &mut Context<'_, Self>) {
        let action = evaluate_one_shot(
            &self.mode,
            self.mode_reported,
            self.load_error.as_deref(),
            self.loaded.is_some(),
            self.decompiling,
        );
        match action {
            OneShotAction::Wait => {}
            OneShotAction::Fail(msg) => {
                self.mode_reported = true;
                self.fail_cli(anyhow::anyhow!(msg), cx);
            }
            OneShotAction::FirstFrameReady => {
                self.mode_reported = true;
                window.on_next_frame(|_, cx| {
                    let mut out = std::io::stdout().lock();
                    let _ = writeln!(out, "FIRST_FRAME_READY");
                    let _ = out.flush();
                    cx.quit();
                });
            }
            OneShotAction::OpenListReady => {
                let count = self.rows_seq.current().map_or(0, |r| r.rows.len());
                self.mode_reported = true;
                window.on_next_frame(move |_, cx| {
                    let mut out = std::io::stdout().lock();
                    let _ = writeln!(
                        out,
                        "OPEN_LIST_READY rows={count} ui_engine_calls={}",
                        ui_engine_calls()
                    );
                    let _ = out.flush();
                    cx.quit();
                });
            }
            OneShotAction::MemoryReady => {
                let rows = self.rows_seq.current().map_or(0, |r| r.rows.len());
                let lines = self.active_view.as_ref().map_or(0, |v| v.lines());
                self.mode_reported = true;
                let wait_stdin = cx.background_executor().spawn(async move {
                    let mut buf = String::new();
                    let _ = std::io::stdin().lock().read_line(&mut buf);
                });
                self.measure_task = Some(cx.spawn(async move |_, cx| {
                    wait_stdin.await;
                    cx.update(|cx| cx.quit());
                }));
                window.on_next_frame(move |_, _| {
                    let pid = std::process::id();
                    let mut out = std::io::stdout().lock();
                    let _ = writeln!(
                        out,
                        "MEMORY_READY pid={pid} rows={rows} lines={lines} ui_engine_calls={}",
                        ui_engine_calls()
                    );
                    let _ = out.flush();
                });
            }
        }
    }

    /// Renders the top toolbar with Open, Back, Forward, and the keystroke filter box.
    ///
    /// # Arguments
    ///
    /// * `window` - Window queried for focus state.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Toolbar [`AnyElement`].
    fn render_toolbar(&self, window: &Window, cx: &mut Context<'_, Self>) -> AnyElement {
        let (surface_bg, bg, border_col, border_focused) = {
            let colors = cx.theme().colors();
            (
                colors.surface_background,
                colors.background,
                colors.border,
                colors.border_focused,
            )
        };
        let focused = self.filter_focus.is_focused(window);
        let filter_label = if self.filter_text.is_empty() {
            if focused {
                SharedString::from("|")
            } else {
                SharedString::from("Filter functions (/ or Ctrl+F)...")
            }
        } else if focused {
            SharedString::from(format!("{}|", self.filter_text))
        } else {
            SharedString::from(self.filter_text.clone())
        };
        let border = if focused { border_focused } else { border_col };
        div()
            .flex()
            .flex_row()
            .items_center()
            .gap(px(8.0))
            .px(px(8.0))
            .py(px(6.0))
            .bg(surface_bg)
            .border_b_1()
            .border_color(border_col)
            .child(toolbar_button(
                "open-btn",
                "Open (Ctrl+O)",
                true,
                border_col,
                cx.listener(|this, _, _, cx| this.prompt_open(cx)),
            ))
            .child(toolbar_button(
                "cmd-btn",
                "Commands (Ctrl+Shift+P)",
                true,
                border_col,
                cx.listener(|this, _, window, cx| this.toggle_palette(window, cx)),
            ))
            .child(toolbar_button(
                "back-btn",
                "Back",
                self.history.can_go_back(),
                border_col,
                cx.listener(|this, _, _, cx| this.navigate_back(cx)),
            ))
            .child(toolbar_button(
                "fwd-btn",
                "Forward",
                self.history.can_go_forward(),
                border_col,
                cx.listener(|this, _, _, cx| this.navigate_forward(cx)),
            ))
            .child(
                div()
                    .id("filter-box")
                    .track_focus(&self.filter_focus)
                    .on_key_down(cx.listener(Self::on_filter_key_down))
                    .on_click(cx.listener(|this, _, window, cx| {
                        this.focus_filter(window, cx);
                    }))
                    .flex_1()
                    .px(px(8.0))
                    .py(px(3.0))
                    .bg(bg)
                    .border_1()
                    .border_color(border)
                    .cursor_text()
                    .child(filter_label),
            )
            .into_any_element()
    }

    /// Renders the virtualized [`Table`] of [`FunctionRow`] entries.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Virtualized table [`AnyElement`].
    fn render_table(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let rows = self.rows_seq.current().cloned();
        let base_count = rows.as_ref().map_or(0, |r| r.rows.len());
        let count = if base_count == 0 {
            0
        } else {
            self.virtual_row_count.unwrap_or(base_count)
        };
        let selected = self.selected_row;
        let selected_bg = cx.theme().colors().element_selected;
        let view = cx.entity().downgrade();
        let headers = vec![
            "entry", "size", "blocks", "instrs", "callers", "callees", "src", "name",
        ];
        Table::new(TABLE_COLS)
            .striped()
            .no_ui_font()
            .interactable(&self.table_state)
            .header(headers)
            .map_row(move |(ix, row_div), _window, _cx| {
                let view = view.clone();
                let styled = if ix == selected {
                    row_div.bg(selected_bg)
                } else {
                    row_div
                };
                styled
                    .cursor_pointer()
                    .on_click(move |_, window, cx| {
                        let _ = view.update(cx, |this, cx| {
                            window.focus(&this.focus_handle, cx);
                            this.activate_row(ix, cx);
                        });
                    })
                    .into_any_element()
            })
            .uniform_list("function-table", count, move |range, _window, _cx| {
                let Some(rows) = &rows else {
                    return Vec::new();
                };
                let n = rows.rows.len();
                if n == 0 {
                    return Vec::new();
                }
                range
                    .filter_map(|ix| rows.rows.get(ix % n).map(format_row_cells))
                    .collect()
            })
            .into_any_element()
    }

    /// Renders the right-hand decompile pane with virtualized [`InteractiveText`] lines.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Code pane [`AnyElement`].
    fn render_code_pane(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let (surface_bg, border_col, text_muted) = {
            let colors = cx.theme().colors();
            (colors.surface_background, colors.border, colors.text_muted)
        };
        let line_count = if self.corpus_code.is_some() {
            TARGET_CODE_LINES
        } else {
            self.active_view.as_ref().map_or(0, |v| v.lines())
        };
        let header = if let Some(corpus) = &self.corpus_code {
            SharedString::from(format!(
                "Decompile benchmark ({} base lines replicated to {TARGET_CODE_LINES})",
                corpus.lines.len()
            ))
        } else if let Some(entry) = self.history.current() {
            SharedString::from(format!("Decompile {entry:#x}"))
        } else {
            SharedString::from("Decompile (select a function)")
        };
        let body = if line_count == 0 {
            div()
                .flex_1()
                .p(px(12.0))
                .text_color(text_muted)
                .child("Open a binary and select a function to view decompiled code.")
                .into_any_element()
        } else {
            uniform_list(
                "code-view",
                line_count,
                cx.processor(Self::render_code_rows),
            )
            .track_scroll(&self.code_scroll)
            .size_full()
            .into_any_element()
        };
        div()
            .flex_1()
            .min_w(px(0.0))
            .h_full()
            .flex()
            .flex_col()
            .overflow_hidden()
            .child(
                div()
                    .px(px(8.0))
                    .py(px(4.0))
                    .bg(surface_bg)
                    .border_b_1()
                    .border_color(border_col)
                    .text_color(text_muted)
                    .child(header),
            )
            .child(div().flex_1().overflow_hidden().child(body))
            .into_any_element()
    }

    /// Builds visible [`InteractiveText`] rows for `range` in the decompile `uniform_list`.
    ///
    /// # Arguments
    ///
    /// * `range` - Visible virtual line index range requested by `uniform_list`.
    /// * `_window` - Window painting the rows.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Styled line elements covering `range`.
    fn render_code_rows(
        &mut self,
        range: Range<usize>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Vec<AnyElement> {
        let font = theme::theme_settings(cx).buffer_font(cx).clone();
        let palette = CodePalette::from_theme(cx);
        let weak = cx.entity().downgrade();
        let current_entry = self.history.current();
        let record_layout = range.len() > 1;
        let mut out = Vec::with_capacity(range.len());
        let mut fallback_layout = None;
        if record_layout {
            self.call_token_layout = None;
        }

        for ix in range {
            let Some((view_arc, line_ix)) = self.resolve_line_source(ix) else {
                continue;
            };
            let styled = style_view_line(&view_arc, line_ix, &font, &palette);
            let styled_text = StyledText::new(styled.text).with_runs(styled.runs);
            if record_layout && self.call_token_layout.is_none() {
                if let Some((pos, _)) = styled
                    .click_refs
                    .iter()
                    .enumerate()
                    .find(|(_, r)| matches!(r, Ref::Function(t) if Some(*t) != current_entry))
                    && let Some(span) = styled.click_ranges.get(pos)
                {
                    self.call_token_layout = Some((styled_text.layout().clone(), span.start));
                } else if fallback_layout.is_none()
                    && let Some((pos, _)) = styled
                        .click_refs
                        .iter()
                        .enumerate()
                        .find(|(_, r)| matches!(r, Ref::Function(_)))
                    && let Some(span) = styled.click_ranges.get(pos)
                {
                    fallback_layout = Some((styled_text.layout().clone(), span.start));
                }
            }
            let text_el = build_interactive_line(
                ix,
                styled_text,
                styled.click_ranges,
                styled.click_refs,
                view_arc,
                weak.clone(),
            );
            out.push(
                div()
                    .h(px(CODE_ROW_HEIGHT_PX))
                    .px(px(8.0))
                    .flex()
                    .items_center()
                    .whitespace_nowrap()
                    .child(text_el)
                    .into_any_element(),
            );
        }
        if record_layout && self.call_token_layout.is_none() {
            self.call_token_layout = fallback_layout;
        }
        out
    }

    /// Maps virtual line index `ix` to its `(Arc<View>, line_index)` source.
    ///
    /// # Arguments
    ///
    /// * `ix` - Virtual line index in the code pane.
    ///
    /// # Returns
    ///
    /// Backing `(view, line_index)` pair, or `None` if out of bounds.
    fn resolve_line_source(&self, ix: usize) -> Option<(Arc<View>, usize)> {
        if let Some(corpus) = &self.corpus_code {
            let n = corpus.lines.len();
            if n == 0 {
                return None;
            }
            let &(v_ix, l_ix) = corpus.lines.get(ix % n)?;
            let v = corpus.views.get(v_ix)?.clone();
            Some((v, l_ix))
        } else {
            let v = self.active_view.clone()?;
            (ix < v.lines()).then_some((v, ix))
        }
    }
}

/// Wraps one [`StyledText`] row in an [`InteractiveText`] dispatching link clicks.
///
/// # Arguments
///
/// * `row_ix` - Virtual row index providing a stable element identifier.
/// * `styled_text` - Highlighted line text and runs.
/// * `click_ranges` - UTF-8 byte ranges of clickable tokens.
/// * `click_refs` - Corroborated [`Ref`] targets matching `click_ranges`.
/// * `view_for_click` - Owning [`View`] used to resolve `Ref::Block` targets.
/// * `entity` - Weak handle to [`AppView`].
///
/// # Returns
///
/// [`InteractiveText`] element wired to open functions or scroll to blocks.
fn build_interactive_line(
    row_ix: usize,
    styled_text: StyledText,
    click_ranges: Vec<Range<usize>>,
    click_refs: Vec<Ref>,
    view_for_click: Arc<View>,
    entity: gpui::WeakEntity<AppView>,
) -> InteractiveText {
    if click_ranges.is_empty() {
        return InteractiveText::new(("code-line", row_ix), styled_text);
    }
    InteractiveText::new(("code-line", row_ix), styled_text).on_click(
        click_ranges,
        move |range_ix, _window, cx| {
            let Some(target) = click_refs.get(range_ix) else {
                return;
            };
            let outcome = resolve_ref_click(&view_for_click, target);
            let _ = entity.update(cx, |this, cx| match outcome {
                ClickOutcome::OpenFunction(callee) => {
                    this.call_clicks_count = this.call_clicks_count.saturating_add(1);
                    this.open_function(callee, true, cx);
                }
                ClickOutcome::ScrollToLine(line_ix) => {
                    this.code_scroll
                        .scroll_to_item(line_ix, ScrollStrategy::Top);
                    cx.notify();
                }
                ClickOutcome::None => {}
            });
        },
    )
}

/// Builds a small clickable toolbar button element.
///
/// # Arguments
///
/// * `id` - Static element ID.
/// * `label` - Button caption.
/// * `enabled` - Whether click events are attached and full opacity is used.
/// * `border` - Border color from the active theme.
/// * `on_click` - Click callback invoked when `enabled` is `true`.
///
/// # Returns
///
/// Toolbar button [`AnyElement`].
fn toolbar_button(
    id: &'static str,
    label: &'static str,
    enabled: bool,
    border: gpui::Hsla,
    on_click: impl Fn(&gpui::ClickEvent, &mut Window, &mut gpui::App) + 'static,
) -> AnyElement {
    let base = div()
        .id(id)
        .px(px(8.0))
        .py(px(3.0))
        .border_1()
        .border_color(border)
        .child(Label::new(label));
    if enabled {
        base.cursor_pointer().on_click(on_click).into_any_element()
    } else {
        base.opacity(0.45).into_any_element()
    }
}

/// Formats one [`FunctionRow`] into eight cell elements without deriving new facts.
///
/// # Arguments
///
/// * `row` - Engine [`FunctionRow`] to format.
///
/// # Returns
///
/// Eight cell elements in column order.
fn format_row_cells(row: &FunctionRow) -> Vec<AnyElement> {
    vec![
        SharedString::from(format!("{:#x}", row.entry)).into_any_element(),
        SharedString::from(row.size.to_string()).into_any_element(),
        SharedString::from(row.blocks.to_string()).into_any_element(),
        SharedString::from(row.instrs.to_string()).into_any_element(),
        SharedString::from(row.callers.to_string()).into_any_element(),
        SharedString::from(row.callees.to_string()).into_any_element(),
        SharedString::from(row.src).into_any_element(),
        SharedString::from(row.name.clone()).into_any_element(),
    ]
}

impl Render for AppView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        self.active_dispatch_pending = false;
        self.check_one_shot_modes(window, cx);
        if self.palette.is_open() && !self.palette_focus.is_focused(window) {
            window.focus(&self.palette_focus, cx);
        }
        let key_ctx = if self.filter_focus.is_focused(window) || self.palette.is_open() {
            "AppRoot"
        } else {
            "AppRoot AppBrowse"
        };
        let toolbar = self.render_toolbar(window, cx);
        let table = self.render_table(cx);
        let code_pane = self.render_code_pane(cx);
        let palette_el = self
            .palette
            .is_open()
            .then(|| render_palette_overlay(&self.palette, &self.palette_focus, cx));
        let status = SharedString::from(self.status.clone());
        let (bg, text_col, border_col, surface_bg, text_muted) = {
            let colors = cx.theme().colors();
            (
                colors.background,
                colors.text,
                colors.border,
                colors.surface_background,
                colors.text_muted,
            )
        };
        let buffer_font = theme::theme_settings(cx).buffer_font(cx).clone();
        let split_body = render_split_body(table, code_pane, border_col);
        let status_bar = render_status_bar(status, surface_bg, border_col, text_muted);

        div()
            .id("app-root")
            .relative()
            .key_context(key_ctx)
            .track_focus(&self.focus_handle)
            .capture_key_down(cx.listener(|this, _, _, cx| this.record_inject_arrival(true, cx)))
            .capture_any_mouse_down(
                cx.listener(|this, _, _, cx| this.record_inject_arrival(false, cx)),
            )
            .capture_any_mouse_up(
                cx.listener(|this, _, _, cx| this.record_inject_arrival(true, cx)),
            )
            .on_action(cx.listener(|this, _: &TogglePalette, window, cx| {
                this.toggle_palette(window, cx);
            }))
            .on_action(cx.listener(|this, _: &Open, _, cx| this.prompt_open(cx)))
            .on_action(cx.listener(|this, _: &FocusFilter, window, cx| {
                this.focus_filter(window, cx);
            }))
            .on_action(cx.listener(|this, _: &OpenSelected, _, cx| {
                this.activate_row(this.selected_row, cx);
            }))
            .on_action(cx.listener(|this, _: &NextRow, _, cx| this.step_row(1, cx)))
            .on_action(cx.listener(|this, _: &PreviousRow, _, cx| this.step_row(-1, cx)))
            .on_action(cx.listener(|this, _: &PageDown, _, cx| this.step_row(25, cx)))
            .on_action(cx.listener(|this, _: &PageUp, _, cx| this.step_row(-25, cx)))
            .on_action(cx.listener(|this, _: &GoBack, _, cx| this.navigate_back(cx)))
            .on_action(cx.listener(|this, _: &GoForward, _, cx| this.navigate_forward(cx)))
            .on_action(cx.listener(|this, _: &Measure, window, cx| {
                this.palette.close();
                if this.is_measuring() {
                    cx.notify();
                } else {
                    begin_list_scroll_phase(this, true, false, window, cx);
                }
            }))
            .size_full()
            .flex()
            .flex_col()
            .bg(bg)
            .text_color(text_col)
            .font(buffer_font)
            .text_size(px(crate::theme_provider::FONT_SIZE_PX))
            .child(toolbar)
            .child(split_body)
            .child(status_bar)
            .children(palette_el)
    }
}

/// Renders the two-column split container holding the function table and decompile pane.
///
/// # Arguments
///
/// * `table` - Rendered function table element.
/// * `code_pane` - Rendered decompile code pane element.
/// * `border_col` - Divider border color from the active theme.
///
/// # Returns
///
/// Split body [`AnyElement`].
fn render_split_body(
    table: AnyElement,
    code_pane: AnyElement,
    border_col: gpui::Hsla,
) -> AnyElement {
    div()
        .flex_1()
        .min_h(px(0.0))
        .flex()
        .flex_row()
        .overflow_hidden()
        .child(
            div()
                .flex_1()
                .min_w(px(0.0))
                .h_full()
                .border_r_1()
                .border_color(border_col)
                .overflow_hidden()
                .child(table),
        )
        .child(code_pane)
        .into_any_element()
}

/// Renders the bottom status bar row.
///
/// # Arguments
///
/// * `status` - Status string to display.
/// * `surface_bg` - Background color from the active theme.
/// * `border_col` - Top border color from the active theme.
/// * `text_muted` - Muted foreground color from the active theme.
///
/// # Returns
///
/// Status bar [`AnyElement`].
fn render_status_bar(
    status: SharedString,
    surface_bg: gpui::Hsla,
    border_col: gpui::Hsla,
    text_muted: gpui::Hsla,
) -> AnyElement {
    div()
        .px(px(8.0))
        .py(px(4.0))
        .bg(surface_bg)
        .border_t_1()
        .border_color(border_col)
        .text_color(text_muted)
        .child(status)
        .into_any_element()
}
