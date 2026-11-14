//! Main window view hosting the function table, filter bar, and clickable decompile pane.

use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::decompile::view::view as build_decompile_view;
use borer_engine::analysis::render::{FunctionRow, FunctionRows};
use borer_engine::cancel::Cancel;
use borer_engine::view::View;
use gpui::{
    AnyElement, AppContext as _, Context, Entity, FocusHandle, InteractiveElement as _,
    InteractiveText, IntoElement, KeyDownEvent, ParentElement as _, PathPromptOptions, Render,
    ScrollStrategy, SharedString, StatefulInteractiveElement as _, Styled as _, StyledText, Task,
    UniformListScrollHandle, Window, div, px, uniform_list,
};
use theme::ActiveTheme as _;
use ui::{Label, Table, TableInteractionState};

use crate::actions::{
    ActionId, FocusFilter, GoBack, GoForward, Measure, NextRow, Open, OpenSelected, PageDown,
    PageUp, PreviousRow, TogglePalette,
};
use crate::code_view::{ClickOutcome, CodePalette, resolve_ref_click, style_view_line};
use crate::history::NavHistory;
use crate::palette::{CommandPalette, handle_palette_key_down, render_palette_overlay};
use crate::worker::{
    FilterLatest, LoadedBinary, filter_rows_blocking, load_binary_blocking, spawn_engine,
};

/// Note appended to status messages explaining what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// Number of columns in the function table.
const TABLE_COLS: usize = 8;

/// Uniform height in logical pixels of each line row in the decompile pane.
const CODE_ROW_HEIGHT_PX: f32 = 20.0;

/// Root view managing the loaded binary, filter bar, function table, and decompile view.
pub struct AppView {
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
    /// Sequenced function-table rows matching [`Self::filter_text`].
    rows_seq: FilterLatest<Arc<FunctionRows>>,
    /// Index of the highlighted row within the active [`FunctionRows`].
    selected_row: usize,
    /// Plain keystroke filter query.
    filter_text: String,
    /// Back/forward navigation stack of opened function entries.
    history: NavHistory,
    /// Active tokenized decompile [`View`] displayed in the right pane.
    active_view: Option<Arc<View>>,
    /// Cancellation flag raised when navigating away from an in-flight decompilation.
    decompile_cancel: Option<Cancel>,
    /// Monotonic ticket discarding superseded decompilation completions.
    decompile_seq: u64,
    /// Status message displayed at the bottom of the window.
    status: String,
    /// Monotonic counter discarding superseded binary-open tasks.
    load_seq: u64,
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
    /// Creates an [`AppView`], optionally starting a background load of `initial_path`.
    ///
    /// # Arguments
    ///
    /// * `initial_path` - Optional binary path supplied on the command line.
    /// * `window` - Window hosting the view, used to set initial focus.
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
        let filter_focus = cx.focus_handle();
        let palette_focus = cx.focus_handle();
        window.focus(&focus_handle, cx);
        let table_state = cx.new(|cx| TableInteractionState::new(cx));
        let mut view = Self {
            focus_handle,
            filter_focus,
            palette_focus,
            palette: CommandPalette::new(),
            table_state,
            code_scroll: UniformListScrollHandle::new(),
            loaded: None,
            rows_seq: FilterLatest::new(),
            selected_row: 0,
            filter_text: String::new(),
            history: NavHistory::new(),
            active_view: None,
            decompile_cancel: None,
            decompile_seq: 0,
            status: format!("Press Ctrl+O to open a binary ({LOAD_SCOPE_NOTE})"),
            load_seq: 0,
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

    /// Opens a native file dialog and loads the chosen binary in the background.
    ///
    /// # Arguments
    ///
    /// * `cx` - View context.
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
    /// * `cx` - View context.
    pub fn open_path(&mut self, path: PathBuf, cx: &mut Context<'_, Self>) {
        self.palette.close();
        if let Some(prev) = self.decompile_cancel.take() {
            prev.raise();
        }
        self.loaded = None;
        self.active_view = None;
        self.rows_seq.clear();
        self.filter_task = None;
        self.selected_row = 0;
        self.history.clear();
        self.load_seq = self.load_seq.saturating_add(1);
        let ticket = self.load_seq;
        self.status = format!("loading {} ({LOAD_SCOPE_NOTE})", path.display());
        cx.notify();
        let bg = spawn_engine(cx, move || load_binary_blocking(path));
        self.load_task = Some(cx.spawn(async move |this, cx| {
            let result = bg.await;
            let _ = this.update(cx, |view, cx| {
                if ticket != view.load_seq {
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
    /// * `result` - Outcome from [`load_binary_blocking`].
    /// * `cx` - View context.
    fn finish_load(
        &mut self,
        result: anyhow::Result<Arc<LoadedBinary>>,
        cx: &mut Context<'_, Self>,
    ) {
        match result {
            Ok(loaded) => {
                let rows = Arc::new(loaded.initial_rows.clone());
                let count = rows.rows.len();
                let left_out = rows.left_out.clone();
                let first_entry = rows.rows.first().map(|r| r.entry);
                let display = loaded.path.display().to_string();
                self.filter_text.clear();
                self.selected_row = 0;
                self.history.clear();
                self.active_view = None;
                self.rows_seq.reset(rows);
                self.loaded = Some(loaded);
                self.status = format!("{display}: {count} functions{left_out} ({LOAD_SCOPE_NOTE})");
                self.scroll_to_selected(cx);
                if let Some(entry) = first_entry {
                    self.open_function(entry, true, cx);
                }
            }
            Err(err) => {
                self.loaded = None;
                self.active_view = None;
                self.rows_seq.clear();
                self.history.clear();
                self.status = format!("load failed: {err:#}");
            }
        }
        cx.notify();
    }

    /// Decompiles `entry` in the background under a fresh [`Cancel`] token, cancelling
    /// any previous in-flight decompilation.
    ///
    /// # Arguments
    ///
    /// * `entry` - Function entry virtual address to open.
    /// * `record_history` - Whether to push onto [`NavHistory`].
    /// * `cx` - View context.
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
        if let Some(prev) = self.decompile_cancel.take() {
            prev.raise();
        }
        let cancel = Cancel::new();
        let worker_cancel = cancel.clone();
        let check_cancel = cancel.clone();
        self.decompile_cancel = Some(cancel);
        self.active_view = None;
        self.decompile_seq = self.decompile_seq.saturating_add(1);
        let ticket = self.decompile_seq;
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
                if ticket != view.decompile_seq || check_cancel.is_raised() {
                    return;
                }
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
    /// * `cx` - View context.
    fn request_filter(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.loaded.clone() else {
            return;
        };
        let seq = self.rows_seq.issue();
        let query = self.filter_text.clone();
        let bg = spawn_engine(cx, move || Arc::new(filter_rows_blocking(&loaded, &query)));
        self.filter_task = Some(cx.spawn(async move |this, cx| {
            let rows = bg.await;
            let _ = this.update(cx, |view, cx| {
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
    /// * `cx` - View context.
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
    /// * `event` - Key-down event from GPUI.
    /// * `window` - Active window.
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
                    cx.notify();
                }
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
    /// * `delta` - Signed row offset.
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
    /// * `row_ix` - Index into the active [`FunctionRows`].
    /// * `cx` - View context.
    fn activate_row(&mut self, row_ix: usize, cx: &mut Context<'_, Self>) {
        let Some(entry) = self
            .rows_seq
            .current()
            .and_then(|r| r.rows.get(row_ix))
            .map(|r| r.entry)
        else {
            return;
        };
        self.selected_row = row_ix;
        self.open_function(entry, true, cx);
    }

    /// Renders the top toolbar with Open, Back, Forward, and the keystroke filter box.
    ///
    /// # Arguments
    ///
    /// * `window` - Active window for checking filter focus.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Toolbar element.
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
    /// Table element filling the left pane.
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
    /// Decompile pane element.
    fn render_code_pane(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let (surface_bg, border_col, text_muted) = {
            let colors = cx.theme().colors();
            (colors.surface_background, colors.border, colors.text_muted)
        };
        let line_count = self.active_view.as_ref().map_or(0, |v| v.lines());
        let header = match self.history.current() {
            Some(entry) => SharedString::from(format!("Decompile {entry:#x}")),
            None => SharedString::from("Decompile (select a function)"),
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
    /// * `range` - Visible 0-based line indices requested by `uniform_list`.
    /// * `_window` - Active window.
    /// * `cx` - View context.
    ///
    /// # Returns
    ///
    /// Styled row elements for `range`.
    fn render_code_rows(
        &mut self,
        range: Range<usize>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Vec<AnyElement> {
        let Some(active) = self.active_view.clone() else {
            return Vec::new();
        };
        let font = theme::theme_settings(cx).buffer_font(cx).clone();
        let palette = CodePalette::from_theme(cx);
        let weak = cx.entity().downgrade();
        let mut out = Vec::with_capacity(range.len());

        for ix in range {
            let styled = style_view_line(&active, ix, &font, &palette);
            let styled_text = StyledText::new(styled.text).with_runs(styled.runs);
            let text_el = if styled.click_ranges.is_empty() {
                InteractiveText::new(("code-line", ix), styled_text)
            } else {
                let refs = styled.click_refs;
                let view_for_click = active.clone();
                let entity = weak.clone();
                InteractiveText::new(("code-line", ix), styled_text).on_click(
                    styled.click_ranges,
                    move |range_ix, _window, cx| {
                        let Some(target) = refs.get(range_ix) else {
                            return;
                        };
                        let outcome = resolve_ref_click(&view_for_click, target);
                        let _ = entity.update(cx, |this, cx| match outcome {
                            ClickOutcome::OpenFunction(callee) => {
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
            };
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
        out
    }
}

/// Builds a small clickable toolbar button element.
///
/// # Arguments
///
/// * `id` - Stable element id.
/// * `label` - Button text.
/// * `enabled` - Whether clicking invokes `on_click`.
/// * `border` - Border color from the active theme.
/// * `on_click` - Click callback.
///
/// # Returns
///
/// Toolbar button element.
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
/// * `row` - Engine function row to format.
///
/// # Returns
///
/// Eight cell elements in header column order.
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

        div()
            .id("app-root")
            .relative()
            .key_context(key_ctx)
            .track_focus(&self.focus_handle)
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
            .on_action(cx.listener(|this, _: &Measure, _, cx| {
                this.palette.close();
                this.status =
                    format!("run borer-app --measure for automated profiling ({LOAD_SCOPE_NOTE})");
                cx.notify();
            }))
            .size_full()
            .flex()
            .flex_col()
            .bg(bg)
            .text_color(text_col)
            .font(buffer_font)
            .text_size(px(crate::theme_provider::FONT_SIZE_PX))
            .child(toolbar)
            .child(
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
                    .child(code_pane),
            )
            .child(
                div()
                    .px(px(8.0))
                    .py(px(4.0))
                    .bg(surface_bg)
                    .border_t_1()
                    .border_color(border_col)
                    .text_color(text_muted)
                    .child(status),
            )
            .children(palette_el)
    }
}
