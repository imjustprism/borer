//! Main window view for opening binaries and filtering the function table.

use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::render::{FunctionRow, FunctionRows};
use gpui::{
    AnyElement, AppContext as _, Context, Entity, FocusHandle, InteractiveElement as _,
    IntoElement, KeyDownEvent, ParentElement as _, PathPromptOptions, Render, ScrollStrategy,
    SharedString, StatefulInteractiveElement as _, Styled as _, Task, Window, div, px,
};
use theme::ActiveTheme as _;
use ui::{Label, Table, TableInteractionState};

use crate::worker::{
    FilterLatest, LoadedBinary, filter_rows_blocking, load_binary_blocking, spawn_engine,
};

/// Note appended to status messages explaining what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// Number of columns in the function table.
const TABLE_COLS: usize = 8;

/// Root view managing the loaded binary, filter bar, and function table.
pub struct AppView {
    /// Root focus handle for keyboard shortcuts outside the filter bar.
    focus_handle: FocusHandle,
    /// Focus handle for the keystroke filter field.
    filter_focus: FocusHandle,
    /// Scroll and focus state for the [`Table`] component.
    table_state: Entity<TableInteractionState>,
    /// Currently loaded binary and analysis, if one has finished loading.
    loaded: Option<Arc<LoadedBinary>>,
    /// Sequenced function-table rows matching [`Self::filter_text`].
    rows_seq: FilterLatest<Arc<FunctionRows>>,
    /// Index of the highlighted row within the active [`FunctionRows`].
    selected_row: usize,
    /// Plain keystroke filter query.
    filter_text: String,
    /// Status message displayed at the bottom of the window.
    status: String,
    /// Monotonic counter discarding superseded binary-open tasks.
    load_seq: u64,
    /// In-flight binary load task.
    load_task: Option<Task<()>>,
    /// In-flight background filter task.
    filter_task: Option<Task<()>>,
    /// In-flight native file-picker prompt task.
    prompt_task: Option<Task<()>>,
}

impl std::fmt::Debug for AppView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppView")
            .field("selected_row", &self.selected_row)
            .field("filter_text", &self.filter_text)
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
        window.focus(&focus_handle, cx);
        let table_state = cx.new(|cx| TableInteractionState::new(cx));
        let mut view = Self {
            focus_handle,
            filter_focus,
            table_state,
            loaded: None,
            rows_seq: FilterLatest::new(),
            selected_row: 0,
            filter_text: String::new(),
            status: format!("Press Ctrl+O to open a binary ({LOAD_SCOPE_NOTE})"),
            load_seq: 0,
            load_task: None,
            filter_task: None,
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
        self.loaded = None;
        self.rows_seq.clear();
        self.filter_task = None;
        self.selected_row = 0;
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
                let display = loaded.path.display().to_string();
                self.filter_text.clear();
                self.selected_row = 0;
                self.rows_seq.reset(rows);
                self.loaded = Some(loaded);
                self.status = format!("{display}: {count} functions{left_out} ({LOAD_SCOPE_NOTE})");
                self.scroll_to_selected(cx);
            }
            Err(err) => {
                self.loaded = None;
                self.rows_seq.clear();
                self.status = format!("load failed: {err:#}");
            }
        }
        cx.notify();
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

    /// Handles keystrokes while the filter field holds focus.
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
        if mods.control && event.keystroke.key == "o" {
            self.prompt_open(cx);
            return;
        }
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

    /// Handles keystrokes when the root view (not the filter field) holds focus.
    ///
    /// # Arguments
    ///
    /// * `event` - Key-down event from GPUI.
    /// * `window` - Active window.
    /// * `cx` - View context.
    fn on_root_key_down(
        &mut self,
        event: &KeyDownEvent,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        if self.filter_focus.is_focused(window) {
            return;
        }
        let mods = event.keystroke.modifiers;
        if mods.control && event.keystroke.key == "o" {
            self.prompt_open(cx);
            return;
        }
        if (mods.control && event.keystroke.key == "f")
            || (!mods.control && !mods.alt && event.keystroke.key == "/")
        {
            window.focus(&self.filter_focus, cx);
            cx.notify();
            return;
        }
        match event.keystroke.key.as_str() {
            "down" | "j" => self.step_row(1, cx),
            "up" | "k" => self.step_row(-1, cx),
            "pagedown" => self.step_row(25, cx),
            "pageup" => self.step_row(-25, cx),
            "enter" => self.activate_row(self.selected_row, cx),
            _ => {}
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

    /// Selects `row_ix` and records the chosen function in the status bar.
    ///
    /// # Arguments
    ///
    /// * `row_ix` - Index into the active [`FunctionRows`].
    /// * `cx` - View context.
    fn activate_row(&mut self, row_ix: usize, cx: &mut Context<'_, Self>) {
        let Some(row) = self.rows_seq.current().and_then(|r| r.rows.get(row_ix)) else {
            return;
        };
        let entry = row.entry;
        let name = row.name.clone();
        self.selected_row = row_ix;
        self.status = format!("selected {name} ({entry:#x}) ({LOAD_SCOPE_NOTE})");
        cx.notify();
    }

    /// Renders the top toolbar with the Open button and keystroke filter box.
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
        let colors = cx.theme().colors();
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
        let border = if focused {
            colors.border_focused
        } else {
            colors.border
        };
        div()
            .flex()
            .flex_row()
            .items_center()
            .gap(px(8.0))
            .px(px(8.0))
            .py(px(6.0))
            .bg(colors.surface_background)
            .border_b_1()
            .border_color(colors.border)
            .child(
                div()
                    .id("open-btn")
                    .px(px(8.0))
                    .py(px(3.0))
                    .border_1()
                    .border_color(colors.border)
                    .cursor_pointer()
                    .on_click(cx.listener(|this, _, _, cx| this.prompt_open(cx)))
                    .child(Label::new("Open (Ctrl+O)")),
            )
            .child(
                div()
                    .id("filter-box")
                    .track_focus(&self.filter_focus)
                    .on_key_down(cx.listener(Self::on_filter_key_down))
                    .on_click(cx.listener(|this, _, window, cx| {
                        window.focus(&this.filter_focus, cx);
                        cx.notify();
                    }))
                    .flex_1()
                    .px(px(8.0))
                    .py(px(3.0))
                    .bg(colors.background)
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
    /// Table element filling the main pane.
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
                    .on_click(move |_, _, cx| {
                        let _ = view.update(cx, |this, cx| this.activate_row(ix, cx));
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
        let toolbar = self.render_toolbar(window, cx);
        let table = self.render_table(cx);
        let colors = cx.theme().colors();
        let buffer_font = theme::theme_settings(cx).buffer_font(cx).clone();
        let status = SharedString::from(self.status.clone());
        div()
            .id("app-root")
            .track_focus(&self.focus_handle)
            .on_key_down(cx.listener(Self::on_root_key_down))
            .size_full()
            .flex()
            .flex_col()
            .bg(colors.background)
            .text_color(colors.text)
            .font(buffer_font)
            .text_size(px(crate::theme_provider::FONT_SIZE_PX))
            .child(toolbar)
            .child(div().flex_1().overflow_hidden().child(table))
            .child(
                div()
                    .px(px(8.0))
                    .py(px(4.0))
                    .bg(colors.surface_background)
                    .border_t_1()
                    .border_color(colors.border)
                    .text_color(colors.text_muted)
                    .child(status),
            )
    }
}
