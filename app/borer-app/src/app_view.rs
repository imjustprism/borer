//! Main window view hosting the function table, filter bar, and clickable decompile pane.

use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::render::{FunctionRow, FunctionRows};
use borer_engine::view::{Ref, View};
use gpui::{
    AnyElement, AppContext as _, Context, Entity, FocusHandle, InteractiveElement as _,
    InteractiveText, IntoElement, KeyDownEvent, ParentElement as _, PathPromptOptions, Render,
    ScrollStrategy, SharedString, StatefulInteractiveElement as _, Styled as _, StyledText, Task,
    UniformListScrollHandle, WeakEntity, Window, div, px, uniform_list,
};
use theme::ActiveTheme as _;
use ui::{Button, Clickable as _, Disableable as _, KeyBinding, Table, TableInteractionState};

use crate::actions::{
    FocusFilter, GoBack, GoForward, NextRow, Open, OpenSelected, PageDown, PageUp, PreviousRow,
};
use crate::code_view::{ClickOutcome, CodeLines, CodePalette, resolve_ref_click, style_view_line};
use crate::history::NavHistory;
use crate::worker::{
    FilterLatest, LoadedBinary, TaskEpoch, decompile_blocking, filter_rows_blocking,
    load_binary_blocking, spawn_engine,
};

/// Note appended to status messages explaining what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// Number of columns in the function table.
const TABLE_COLS: usize = 8;

/// Uniform height in logical pixels of each line row in the decompile pane.
pub const CODE_ROW_HEIGHT_PX: f32 = 20.0;

/// Left padding in logical pixels before the text of each decompile line.
pub const CODE_PAD_PX: f32 = 8.0;

/// Rows one page step moves the function-table selection.
const PAGE_ROWS: isize = 25;

/// Tickets of the latest background work a view asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tickets {
    /// Latest filter request ([`FilterLatest::issue`]).
    pub filter: u64,
    /// Latest decompile generation ([`TaskEpoch::begin`]).
    pub decompile: u64,
}

/// Root view managing the loaded binary, filter bar, function table, and decompile view.
pub struct AppView {
    /// Root focus handle for keyboard shortcuts outside the filter bar.
    focus_handle: FocusHandle,
    /// Focus handle for the keystroke filter field.
    filter_focus: FocusHandle,
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
    /// Index of the highlighted row within the active [`FunctionRows`].
    selected_row: usize,
    /// Plain keystroke filter query.
    filter_text: String,
    /// Back/forward navigation stack of opened function entries.
    history: NavHistory,
    /// Lines shown in the decompile pane, if any.
    code: Option<Arc<CodeLines>>,
    /// Generation and cooperative [`borer_engine::cancel::Cancel`] state for in-flight binary loads.
    load_epoch: TaskEpoch,
    /// Generation and cooperative [`borer_engine::cancel::Cancel`] state for in-flight decompilations.
    decompile_epoch: TaskEpoch,
    /// Whether a background decompilation is currently awaiting completion.
    decompiling: bool,
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
}

impl std::fmt::Debug for AppView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppView")
            .field("selected_row", &self.selected_row)
            .field("filter_text", &self.filter_text)
            .field("current_entry", &self.history.current())
            .field("status", &self.status)
            .finish_non_exhaustive()
    }
}

impl AppView {
    /// Creates an [`AppView`], starting a background load of `initial_path` if given.
    ///
    /// # Arguments
    ///
    /// * `initial_path` - Optional binary file path to open at launch.
    /// * `window` - Window hosting the view.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// The initialized [`AppView`].
    #[must_use]
    pub fn new(
        initial_path: Option<PathBuf>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let focus_handle = cx.focus_handle();
        window.focus(&focus_handle, cx);
        let mut view = Self {
            focus_handle,
            filter_focus: cx.focus_handle(),
            table_state: cx.new(|cx| TableInteractionState::new(cx)),
            code_scroll: UniformListScrollHandle::new(),
            loaded: None,
            load_error: None,
            rows_seq: FilterLatest::new(),
            selected_row: 0,
            filter_text: String::new(),
            history: NavHistory::new(),
            code: None,
            load_epoch: TaskEpoch::new(),
            decompile_epoch: TaskEpoch::new(),
            decompiling: false,
            status: format!("Open a binary ({LOAD_SCOPE_NOTE})"),
            load_task: None,
            filter_task: None,
            decompile_task: None,
            prompt_task: None,
        };
        if let Some(path) = initial_path {
            view.open_path(path, cx);
        }
        view
    }

    /// Returns the loaded binary, once a load has finished.
    #[must_use]
    pub fn loaded(&self) -> Option<&Arc<LoadedBinary>> {
        self.loaded.as_ref()
    }

    /// Returns the error of the most recent failed load, if any.
    #[must_use]
    pub fn load_error(&self) -> Option<&str> {
        self.load_error.as_deref()
    }

    /// Returns the rows the function table shows, if any.
    #[must_use]
    pub fn rows(&self) -> Option<&Arc<FunctionRows>> {
        self.rows_seq.current()
    }

    /// Returns the lines the decompile pane shows, if any.
    #[must_use]
    pub fn code(&self) -> Option<&Arc<CodeLines>> {
        self.code.as_ref()
    }

    /// Returns the scroll handle of the decompile pane's line list.
    #[must_use]
    pub const fn code_scroll(&self) -> &UniformListScrollHandle {
        &self.code_scroll
    }

    /// Returns the entry of the function the decompile pane is for, if any.
    #[must_use]
    pub fn current(&self) -> Option<u64> {
        self.history.current()
    }

    /// Returns whether a background decompilation is still running.
    #[must_use]
    pub const fn is_decompiling(&self) -> bool {
        self.decompiling
    }

    /// Returns whether [`NavHistory`] holds an earlier function entry to return to.
    #[must_use]
    pub fn can_go_back(&self) -> bool {
        self.history.can_go_back()
    }

    /// Returns the tickets of the latest filter request and decompile.
    #[must_use]
    pub const fn tickets(&self) -> Tickets {
        Tickets {
            filter: self.rows_seq.issued(),
            decompile: self.decompile_epoch.seq(),
        }
    }

    /// Returns whether filter request `seq` is answered on screen or superseded.
    ///
    /// # Arguments
    ///
    /// * `seq` - A [`Tickets::filter`] value.
    #[must_use]
    pub const fn filter_settled(&self, seq: u64) -> bool {
        self.rows_seq.accepted() >= seq
    }

    /// Returns whether decompile `ticket` is on screen, cancelled, or superseded.
    ///
    /// # Arguments
    ///
    /// * `ticket` - A [`Tickets::decompile`] value.
    #[must_use]
    pub const fn decompile_settled(&self, ticket: u64) -> bool {
        !self.decompiling || self.decompile_epoch.seq() > ticket
    }

    /// Cancels and invalidates any in-flight function decompilation task.
    fn cancel_decompile(&mut self) {
        self.decompile_epoch.invalidate();
        self.decompiling = false;
        self.decompile_task = None;
    }

    /// Shows `loaded` with `rows` in the table, clearing the filter, the code pane and history.
    ///
    /// # Arguments
    ///
    /// * `loaded` - Analyzed binary to show.
    /// * `rows` - Function rows the table lists.
    /// * `cx` - View context.
    pub fn show(
        &mut self,
        loaded: Arc<LoadedBinary>,
        rows: Arc<FunctionRows>,
        cx: &mut Context<'_, Self>,
    ) {
        self.load_epoch.invalidate();
        self.cancel_decompile();
        self.load_error = None;
        self.filter_text.clear();
        self.selected_row = 0;
        self.history.clear();
        self.code = None;
        self.rows_seq.reset(rows);
        self.loaded = Some(loaded);
        self.scroll_to_selected(cx);
        cx.notify();
    }

    /// Shows `code` in the decompile pane, for no one function.
    ///
    /// # Arguments
    ///
    /// * `code` - Lines to show.
    /// * `cx` - View context.
    pub fn show_code(&mut self, code: Arc<CodeLines>, cx: &mut Context<'_, Self>) {
        self.cancel_decompile();
        self.history.clear();
        self.code = Some(code);
        self.code_scroll.scroll_to_item(0, ScrollStrategy::Top);
        cx.notify();
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
    /// * `line_ix` - Zero-based shown line index.
    /// * `strategy` - GPUI [`ScrollStrategy`] governing placement.
    pub fn scroll_code_to(&self, line_ix: usize, strategy: ScrollStrategy) {
        self.code_scroll.scroll_to_item(line_ix, strategy);
    }

    /// Opens a native file dialog and loads the chosen binary in the background.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context spawning the dialog receiver task.
    pub fn prompt_open(&mut self, cx: &mut Context<'_, Self>) {
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
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |view, cx| match outcome {
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
        self.cancel_decompile();
        self.load_error = None;
        self.loaded = None;
        self.code = None;
        self.rows_seq.clear();
        self.filter_task = None;
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
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |view, cx| {
                if view.load_epoch.is_current(ticket, &check_cancel) {
                    view.finish_load(result, cx);
                }
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
        match result {
            Ok(loaded) => {
                let rows = loaded.initial_rows.clone();
                let first_entry = rows.rows.first().map(|r| r.entry);
                self.status = format!(
                    "{}: {} functions{} ({LOAD_SCOPE_NOTE})",
                    loaded.path.display(),
                    rows.rows.len(),
                    rows.left_out
                );
                self.show(loaded, rows, cx);
                if let Some(entry) = first_entry {
                    self.open_function(entry, true, cx);
                }
            }
            Err(err) => {
                self.cancel_decompile();
                let msg = format!("{err:#}");
                self.loaded = None;
                self.code = None;
                self.rows_seq.clear();
                self.history.clear();
                self.status = format!("load failed: {msg}");
                self.load_error = Some(msg);
                cx.notify();
            }
        }
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
            self.history.open(entry);
        }
        if let Some(rows) = self.rows_seq.current()
            && let Some(pos) = rows.rows.iter().position(|r| r.entry == entry)
        {
            self.selected_row = pos;
            self.scroll_to_selected(cx);
        }
        let (ticket, worker_cancel) = self.decompile_epoch.begin();
        let check_cancel = worker_cancel.clone();
        self.code = None;
        self.decompiling = true;
        self.status = format!("decompiling {entry:#x} ({LOAD_SCOPE_NOTE})");
        cx.notify();

        let bg = spawn_engine(cx, move || {
            worker_cancel.within(|| decompile_blocking(&loaded, entry))
        });
        self.decompile_task = Some(cx.spawn(async move |this, cx| {
            let built = bg.await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |view, cx| {
                if view.decompile_epoch.is_current(ticket, &check_cancel) {
                    view.finish_decompile(entry, built, cx);
                }
            });
        }));
    }

    /// Shows the answer of a background decompile of `entry`.
    ///
    /// # Arguments
    ///
    /// * `entry` - Function entry address that was decompiled.
    /// * `built` - Its view, or `None` when no function starts there.
    /// * `cx` - View context.
    fn finish_decompile(
        &mut self,
        entry: u64,
        built: Option<Arc<View>>,
        cx: &mut Context<'_, Self>,
    ) {
        self.decompiling = false;
        match built {
            Some(v) => {
                let lines = v.lines();
                self.code = Some(Arc::new(CodeLines::new(vec![v])));
                self.code_scroll.scroll_to_item(0, ScrollStrategy::Top);
                self.status = format!("opened {entry:#x}: {lines} lines ({LOAD_SCOPE_NOTE})");
            }
            None => {
                self.code = None;
                self.status = format!("no function at {entry:#x} ({LOAD_SCOPE_NOTE})");
            }
        }
        cx.notify();
    }

    /// Steps backward in [`NavHistory`] and opens the previous function.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    pub fn navigate_back(&mut self, cx: &mut Context<'_, Self>) {
        if let Some(prev) = self.history.go_back() {
            self.open_function(prev, false, cx);
        }
    }

    /// Steps forward in [`NavHistory`] and opens the next function.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
    pub fn navigate_forward(&mut self, cx: &mut Context<'_, Self>) {
        if let Some(next) = self.history.go_forward() {
            self.open_function(next, false, cx);
        }
    }

    /// Issues a sequenced background filter query for [`Self::filter_text`].
    ///
    /// # Arguments
    ///
    /// * `cx` - View context spawning the background filter task.
    fn request_filter(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.loaded.clone() else {
            return;
        };
        let seq = self.rows_seq.issue();
        let query = self.filter_text.clone();
        let bg = spawn_engine(cx, move || Arc::new(filter_rows_blocking(&loaded, &query)));
        self.filter_task = Some(cx.spawn(async move |this, cx| {
            let rows = bg.await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |view, cx| {
                if view.rows_seq.accept(seq, rows) {
                    view.selected_row = 0;
                    view.update_filter_status();
                    view.scroll_to_selected(cx);
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
        self.scroll_table_to(self.selected_row, ScrollStrategy::Nearest, cx);
    }

    /// Moves focus to the function-filter input.
    ///
    /// # Arguments
    ///
    /// * `window` - Window managing keyboard focus.
    /// * `cx` - View context.
    pub fn focus_filter(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        window.focus(&self.filter_focus, cx);
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
            return;
        }
        match event.keystroke.key.as_str() {
            "backspace" => {
                if self.filter_text.pop().is_some() {
                    self.request_filter(cx);
                }
                cx.notify();
            }
            "escape" => {
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
                    self.filter_text.push_str(ch);
                    self.request_filter(cx);
                    cx.notify();
                }
            }
        }
    }

    /// Moves [`Self::selected_row`] by `delta` within the active row list.
    ///
    /// # Arguments
    ///
    /// * `delta` - Signed row step (`1`, `-1`, [`PAGE_ROWS`], `-PAGE_ROWS`).
    /// * `cx` - View context.
    fn step_row(&mut self, delta: isize, cx: &mut Context<'_, Self>) {
        let len = self.rows_seq.current().map_or(0, |r| r.rows.len());
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
        let Some(entry) = self
            .rows_seq
            .current()
            .and_then(|rows| rows.rows.get(row_ix))
            .map(|r| r.entry)
        else {
            return;
        };
        self.selected_row = row_ix;
        self.open_function(entry, true, cx);
    }

    /// Renders the top toolbar: Zed's buttons for Open, Back and Forward, each
    /// with its shortcut as gpui's keymap binds it, and the keystroke filter box.
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
        let filter_label = match (self.filter_text.is_empty(), focused) {
            (true, true) => SharedString::from("|"),
            (true, false) => SharedString::from("Filter functions"),
            (false, true) => SharedString::from(format!("{}|", self.filter_text)),
            (false, false) => SharedString::from(self.filter_text.clone()),
        };
        let border = if focused { border_focused } else { border_col };
        let root = &self.focus_handle;
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
            .child(
                Button::new("open", "Open")
                    .key_binding(KeyBinding::for_action_in(&Open, root, cx))
                    .on_click(|_, window, cx| window.dispatch_action(Box::new(Open), cx)),
            )
            .child(
                Button::new("back", "Back")
                    .key_binding(KeyBinding::for_action_in(&GoBack, root, cx))
                    .disabled(!self.history.can_go_back())
                    .on_click(|_, window, cx| window.dispatch_action(Box::new(GoBack), cx)),
            )
            .child(
                Button::new("forward", "Forward")
                    .key_binding(KeyBinding::for_action_in(&GoForward, root, cx))
                    .disabled(!self.history.can_go_forward())
                    .on_click(|_, window, cx| window.dispatch_action(Box::new(GoForward), cx)),
            )
            .child(
                div()
                    .id("filter-box")
                    .track_focus(&self.filter_focus)
                    .on_key_down(cx.listener(Self::on_filter_key_down))
                    .on_click(cx.listener(|this, _, window, cx| {
                        this.focus_filter(window, cx);
                    }))
                    .flex_1()
                    .flex()
                    .justify_between()
                    .px(px(8.0))
                    .py(px(3.0))
                    .bg(bg)
                    .border_1()
                    .border_color(border)
                    .cursor_text()
                    .child(filter_label)
                    .child(KeyBinding::for_action_in(&FocusFilter, root, cx)),
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
        let count = rows.as_ref().map_or(0, |r| r.rows.len());
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
                        let Some(view) = view.upgrade() else {
                            return;
                        };
                        view.update(cx, |this, cx| {
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
                range
                    .filter_map(|ix| rows.rows.get(ix).map(format_row_cells))
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
        let line_count = self.code.as_ref().map_or(0, |c| c.len());
        let header = match (self.history.current(), &self.code) {
            (Some(entry), _) => SharedString::from(format!("Decompile {entry:#x}")),
            (None, Some(code)) => SharedString::from(format!(
                "Decompile: {} lines from {} functions",
                code.len(),
                code.views()
            )),
            (None, None) => SharedString::from("Decompile (select a function)"),
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
    /// * `range` - Visible shown-line index range requested by `uniform_list`.
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
        let Some(code) = self.code.clone() else {
            return Vec::new();
        };
        let font = theme::theme_settings(cx).buffer_font(cx).clone();
        let palette = CodePalette::from_theme(cx);
        let weak = cx.entity().downgrade();
        range
            .filter_map(|ix| {
                let (view, line_ix) = code.get(ix)?;
                let styled = style_view_line(view, line_ix, &font, &palette);
                let text = StyledText::new(styled.text).with_runs(styled.runs);
                let line = build_interactive_line(
                    (ix, line_ix),
                    text,
                    styled.click_ranges,
                    styled.click_refs,
                    view.clone(),
                    weak.clone(),
                );
                Some(
                    div()
                        .h(px(CODE_ROW_HEIGHT_PX))
                        .px(px(CODE_PAD_PX))
                        .flex()
                        .items_center()
                        .whitespace_nowrap()
                        .child(line)
                        .into_any_element(),
                )
            })
            .collect()
    }
}

/// Wraps one [`StyledText`] row in an [`InteractiveText`] dispatching link clicks.
///
/// # Arguments
///
/// * `(row_ix, line_ix)` - Shown line index (also the element identifier) and its line in `view`.
/// * `styled_text` - Highlighted line text and runs.
/// * `click_ranges` - UTF-8 byte ranges of clickable tokens.
/// * `click_refs` - Corroborated [`Ref`] targets matching `click_ranges`.
/// * `view` - Owning [`View`] used to resolve `Ref::Address` targets.
/// * `entity` - Weak handle to [`AppView`].
///
/// # Returns
///
/// [`InteractiveText`] element wired to open functions or scroll to definitions.
fn build_interactive_line(
    (row_ix, line_ix): (usize, usize),
    styled_text: StyledText,
    click_ranges: Vec<Range<usize>>,
    click_refs: Vec<Ref>,
    view: Arc<View>,
    entity: WeakEntity<AppView>,
) -> InteractiveText {
    let line = InteractiveText::new(("code-line", row_ix), styled_text);
    if click_ranges.is_empty() {
        return line;
    }
    line.on_click(click_ranges, move |range_ix, _window, cx| {
        let Some(target) = click_refs.get(range_ix) else {
            return;
        };
        let outcome = resolve_ref_click(&view, target);
        let Some(entity) = entity.upgrade() else {
            return;
        };
        entity.update(cx, |this, cx| match outcome {
            ClickOutcome::OpenFunction(callee) => this.open_function(callee, true, cx),
            ClickOutcome::ScrollToLine(def) => {
                let shown = row_ix.saturating_sub(line_ix).saturating_add(def);
                this.code_scroll.scroll_to_item(shown, ScrollStrategy::Top);
                cx.notify();
            }
            ClickOutcome::None => {}
        });
    })
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
        SharedString::from(row.src.code()).into_any_element(),
        SharedString::from(row.name.clone()).into_any_element(),
    ]
}

impl Render for AppView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let key_ctx = if self.filter_focus.is_focused(window) {
            "AppRoot"
        } else {
            "AppRoot AppBrowse"
        };
        let toolbar = self.render_toolbar(window, cx);
        let table = self.render_table(cx);
        let code_pane = self.render_code_pane(cx);
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
            .key_context(key_ctx)
            .track_focus(&self.focus_handle)
            .on_action(cx.listener(|this, _: &Open, _, cx| this.prompt_open(cx)))
            .on_action(cx.listener(|this, _: &FocusFilter, window, cx| {
                this.focus_filter(window, cx);
            }))
            .on_action(cx.listener(|this, _: &OpenSelected, _, cx| {
                this.activate_row(this.selected_row, cx);
            }))
            .on_action(cx.listener(|this, _: &NextRow, _, cx| this.step_row(1, cx)))
            .on_action(cx.listener(|this, _: &PreviousRow, _, cx| this.step_row(-1, cx)))
            .on_action(cx.listener(|this, _: &PageDown, _, cx| this.step_row(PAGE_ROWS, cx)))
            .on_action(cx.listener(|this, _: &PageUp, _, cx| this.step_row(-PAGE_ROWS, cx)))
            .on_action(cx.listener(|this, _: &GoBack, _, cx| this.navigate_back(cx)))
            .on_action(cx.listener(|this, _: &GoForward, _, cx| this.navigate_forward(cx)))
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
