//! The functions panel: the open binary's function table as a panel of Zed's left dock,
//! filtered through a Zed single-line editor, opening a row in a decompile tab.

use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::render::{FunctionRows, INCOMPLETE_NOTE, LeftOut};
use editor::{Editor, EditorEvent};
use gpui::prelude::FluentBuilder as _;
use gpui::{
    Action, AnyElement, App, AppContext as _, BorrowAppContext as _, Context, Div, Entity,
    EventEmitter, FocusHandle, Focusable, FontWeight, InteractiveElement as _, IntoElement,
    ParentElement as _, Pixels, Render, ScrollStrategy, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, Task, WeakEntity, Window, canvas,
    div, px, transparent_black,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};

use theme_settings::ThemeSettings;
use ui::{
    Color, ColumnWidthConfig, IconName, KeyBinding, Label, LabelCommon as _, LabelSize,
    ResizableColumnsState, Table, TableInteractionState, TableResizeBehavior, h_flex, v_flex,
};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

use crate::actions::{FocusFilter, OPEN_HINT, ToggleFunctions, hint_row};
use crate::binary::{Binary, SettingsNotice};
use crate::code_view::CodePalette;
use crate::decompile_item::{TabMode, code_row_height, open_function};
use crate::function_columns::{Align, Columns, Ink, column_widths, row_cells};
use crate::worker::{FilterLatest, LoadedBinary, filter_rows_blocking, spawn_engine};

/// Name Zed saves the panel's dock state and size under.
pub const PANEL_KEY: &str = "Functions";

/// Width in logical pixels of the panel before the person resizes it.
const DEFAULT_WIDTH_PX: f32 = 560.0;

/// Horizontal padding of a cell of Zed's table, both sides together, in rems (`px_1`).
const CELL_PAD_REMS: f32 = 0.5;

/// Width in logical pixels of the bar the selected row paints over its left padding, so no
/// row and no header moves.
const SELECTED_BAR_PX: f32 = 2.0;

/// Debug selector of a table row, whose laid-out bounds the tests read.
const ROW_SELECTOR: &str = "function-row";

/// Debug selector of an entry cell's content, whose laid-out bounds the tests read.
const ENTRY_SELECTOR: &str = "function-entry";

/// Rows the engine selected, with the filter query that selected them.
#[derive(Debug, Clone)]
struct Filtered {
    /// The query, empty for every function.
    query: SharedString,
    /// The engine's rows for it.
    rows: Arc<FunctionRows>,
}

/// Why the panel shows no table, each case from what the binary and the shown rows say.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Empty {
    /// No binary was opened, or the last one was closed.
    NoBinary,
    /// A load reads this file.
    Reading(PathBuf),
    /// The last load failed, for this reason.
    LoadFailed(String),
    /// The engine selected no function of the binary, leaving these out.
    NoFunction(LeftOut),
    /// The engine selected no function for this query.
    NoMatch(SharedString),
}

impl Empty {
    /// Returns what the panel says for the case.
    #[must_use]
    pub fn says(&self) -> SharedString {
        match self {
            Self::NoBinary => SharedString::new_static("No binary loaded"),
            Self::Reading(path) => {
                let name = path.file_name().unwrap_or(path.as_os_str());
                format!("Reading {}", name.to_string_lossy()).into()
            }
            Self::LoadFailed(reason) => format!("Load failed: {reason}").into(),
            Self::NoFunction(left_out) => format!("The engine found no function{left_out}").into(),
            Self::NoMatch(query) => format!("No function matches \"{query}\"").into(),
        }
    }

    /// Returns whether the case offers to open a binary.
    #[must_use]
    pub const fn offers_open(&self) -> bool {
        match self {
            Self::NoBinary | Self::LoadFailed(_) => true,
            Self::Reading(_) | Self::NoFunction(_) | Self::NoMatch(_) => false,
        }
    }
}

/// The open binary's function table, in a dock.
pub struct FunctionsPanel {
    /// Workspace the panel opens decompile tabs in.
    workspace: WeakEntity<Workspace>,
    /// The binary whose functions the panel lists.
    binary: Entity<Binary>,
    /// Focus handle of the panel's root.
    focus_handle: FocusHandle,
    /// Zed's single-line editor holding the filter query.
    filter: Entity<Editor>,
    /// Scroll and focus state of the table.
    table_state: Entity<TableInteractionState>,
    /// The binary the rows come from.
    shown: Option<Arc<LoadedBinary>>,
    /// Sequenced rows matching the filter, each with its query, the newest answer winning.
    rows: FilterLatest<Filtered>,
    /// Index of the highlighted row.
    selected: usize,
    /// Columns the table shows.
    columns: Columns,
    /// Widths of the shown columns, laid out again when the rows, the columns, the
    /// settings or the table's width change.
    widths: Entity<ResizableColumnsState>,
    /// Width of the table as last painted, the panel's default before its first paint.
    table_width: Pixels,
    /// Dock the panel sits in.
    position: DockPosition,
    /// The running background filter.
    filter_task: Option<Task<()>>,
    /// Colors of the engine's token kinds, read again when the theme or the settings change.
    palette: CodePalette,
    /// Reruns the filter on each edit, follows the binary's loads, and lays the table out
    /// again on a settings or theme change.
    _subscriptions: [Subscription; 4],
}

impl std::fmt::Debug for FunctionsPanel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionsPanel")
            .field("selected", &self.selected)
            .finish_non_exhaustive()
    }
}

impl FunctionsPanel {
    /// Returns the panel listing `binary`'s functions.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the panel opens decompile tabs in.
    /// * `binary` - The binary whose functions to list.
    /// * `position` - Dock the panel starts in.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    #[must_use]
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        position: DockPosition,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let filter = cx.new(|cx| {
            let mut editor = Editor::single_line(window, cx);
            editor.set_placeholder_text("Filter by name or address", window, cx);
            editor
        });
        let subscriptions = [
            cx.subscribe(&filter, |this, _, event: &EditorEvent, cx| {
                if matches!(event, EditorEvent::BufferEdited) {
                    this.request_filter(cx);
                }
            }),
            cx.observe_in(&binary, window, |this, binary, window, cx| {
                this.follow_binary(&binary, window, cx);
            }),
            cx.observe_global::<SettingsStore>(Self::relayout),
            cx.observe_global::<GlobalTheme>(Self::relayout),
        ];
        let mut panel = Self {
            workspace,
            binary,
            focus_handle: cx.focus_handle(),
            filter,
            table_state: cx.new(|cx| TableInteractionState::new(cx)),
            shown: None,
            rows: FilterLatest::new(),
            selected: 0,
            columns: Columns::Brief,
            widths: cx.new(|_| ResizableColumnsState::new(0, Vec::<Pixels>::new(), Vec::new())),
            table_width: px(DEFAULT_WIDTH_PX),
            position,
            filter_task: None,
            palette: CodePalette::from_theme(cx.theme()),
            _subscriptions: subscriptions,
        };
        panel.relayout(cx);
        panel
    }

    /// Lays the shown columns out for the shown rows, the buffer font the table draws in and
    /// the table's width, and rereads the theme's token colors; a font the text system cannot
    /// measure is measured by its size instead, and the status line says so.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    fn relayout(&mut self, cx: &mut Context<'_, Self>) {
        self.palette = CodePalette::from_theme(cx.theme());
        let settings = ThemeSettings::get_global(cx);
        let (font, size) = (settings.buffer_font.clone(), settings.buffer_font_size(cx));
        let pad = settings.ui_font_size(cx) * CELL_PAD_REMS;
        let text = cx.text_system();
        let measured = text.ch_advance(text.resolve_font(&font), size);
        let ch = measured.unwrap_or_else(|err| {
            let why = format!("function table measured by font size: {err:#}");
            cx.set_global(SettingsNotice(Some(why.into())));
            size
        });
        let rows = self.rows().map_or(&[][..], |rows| rows.rows.as_slice());
        let widths = column_widths(self.columns, rows, ch, pad, self.table_width);
        let cols = widths.len();
        let resize = vec![TableResizeBehavior::None; cols];
        self.widths = cx.new(|_| ResizableColumnsState::new(cols, widths, resize));
        cx.notify();
    }

    /// Lays the columns out again for a table now `width` wide, when that changed.
    ///
    /// # Arguments
    ///
    /// * `width` - Width the table was painted at.
    /// * `cx` - Panel context.
    fn set_table_width(&mut self, width: Pixels, cx: &mut Context<'_, Self>) {
        if width > Pixels::ZERO && width != self.table_width {
            self.table_width = width;
            self.relayout(cx);
        }
    }

    /// Returns the binary whose functions the panel lists.
    #[must_use]
    pub const fn binary(&self) -> &Entity<Binary> {
        &self.binary
    }

    /// Returns the columns the table shows.
    #[must_use]
    pub const fn columns(&self) -> Columns {
        self.columns
    }

    /// Shows the full columns if the brief ones are shown, else the brief ones.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    pub fn toggle_columns(&mut self, cx: &mut Context<'_, Self>) {
        self.columns = self.columns.toggled();
        self.relayout(cx);
    }

    /// Returns why the panel shows no table, from the binary's load and the shown rows with
    /// the query that selected them, never the filter's text since; `None` while the
    /// table has rows.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the binary.
    #[must_use]
    pub fn empty(&self, cx: &App) -> Option<Empty> {
        let Some(Filtered { query, rows }) = self.rows.current() else {
            let binary = self.binary.read(cx);
            return Some(match (binary.reading(), binary.load_error()) {
                (Some(path), _) => Empty::Reading(path.to_path_buf()),
                (None, Some(reason)) => Empty::LoadFailed(reason.to_owned()),
                (None, None) => Empty::NoBinary,
            });
        };
        if !rows.rows.is_empty() {
            return None;
        }
        Some(if query.is_empty() {
            Empty::NoFunction(rows.left_out)
        } else {
            Empty::NoMatch(query.clone())
        })
    }

    /// Returns the filter's hint: the binding the keymap holds for [`FocusFilter`].
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the keymap.
    #[must_use]
    pub fn filter_hint(cx: &App) -> KeyBinding {
        KeyBinding::for_action(&FocusFilter, cx)
    }

    /// Returns the rows the table shows, if any.
    #[must_use]
    pub fn rows(&self) -> Option<&Arc<FunctionRows>> {
        self.rows.current().map(|filtered| &filtered.rows)
    }

    /// Returns the ticket of the latest filter request.
    #[must_use]
    pub const fn filter_ticket(&self) -> u64 {
        self.rows.issued()
    }

    /// Returns whether filter request `seq` is answered on screen or superseded.
    ///
    /// # Arguments
    ///
    /// * `seq` - A [`Self::filter_ticket`] value.
    #[must_use]
    pub const fn filter_settled(&self, seq: u64) -> bool {
        self.rows.accepted() >= seq
    }

    /// Scrolls the table so row `row` is at its top.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    /// * `cx` - Application context reading the table state.
    pub fn scroll_to(&self, row: usize, cx: &App) {
        self.table_state
            .read(cx)
            .scroll_handle
            .scroll_to_item(row, ScrollStrategy::Top);
    }

    /// Returns the height in logical pixels the table was last painted at, zero before its
    /// first paint.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the table state.
    #[must_use]
    pub fn painted_height(&self, cx: &App) -> Pixels {
        self.table_state
            .read(cx)
            .scroll_handle
            .0
            .borrow()
            .base_handle
            .bounds()
            .size
            .height
    }

    /// Shows `rows` of `loaded`, clearing the filter and the selection.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary the rows come from.
    /// * `rows` - Rows to list.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub fn show(
        &mut self,
        loaded: Arc<LoadedBinary>,
        rows: Arc<FunctionRows>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.shown = Some(loaded);
        self.rows.reset(Filtered {
            query: SharedString::default(),
            rows,
        });
        self.filter_task = None;
        self.selected = 0;
        if !self.filter.read(cx).text(cx).is_empty() {
            self.filter
                .update(cx, |editor, cx| editor.set_text("", window, cx));
        }
        self.scroll_to_selected(cx);
        self.relayout(cx);
    }

    /// Lists the functions of a binary that finished loading and opens its first one, or
    /// empties the table while a load runs.
    ///
    /// # Arguments
    ///
    /// * `binary` - The binary the panel follows.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    fn follow_binary(
        &mut self,
        binary: &Entity<Binary>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let Some(loaded) = binary.read(cx).loaded().cloned() else {
            if self.shown.take().is_some() {
                self.rows.clear();
                self.filter_task = None;
                self.relayout(cx);
            }
            return;
        };
        if self.shown.as_ref().is_some_and(|s| Arc::ptr_eq(s, &loaded)) {
            return;
        }
        let rows = loaded.initial_rows.clone();
        self.show(loaded, rows, window, cx);
        self.open_row(0, TabMode::Preview, window, cx);
    }

    /// Issues a sequenced background filter for the editor's query.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context spawning the background filter.
    fn request_filter(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.shown.clone() else {
            return;
        };
        let seq = self.rows.issue();
        let query = SharedString::from(self.filter.read(cx).text(cx));
        let asked = query.clone();
        let bg = spawn_engine(cx, move || Arc::new(filter_rows_blocking(&loaded, &asked)));
        self.filter_task = Some(cx.spawn(async move |this, cx| {
            let rows = Filtered {
                query,
                rows: bg.await,
            };
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |panel, cx| {
                if panel.rows.accept(seq, rows) {
                    panel.selected = 0;
                    panel.scroll_to_selected(cx);
                    panel.relayout(cx);
                }
            });
        }));
    }

    /// Scrolls the table so the highlighted row stays visible.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the table state.
    fn scroll_to_selected(&self, cx: &App) {
        self.table_state
            .read(cx)
            .scroll_handle
            .scroll_to_item(self.selected, ScrollStrategy::Nearest);
    }

    /// Moves the highlight to row `row`, clamped to the rows shown.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index; past the last row selects the last.
    /// * `cx` - Panel context.
    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        let len = self.rows().map_or(0, |r| r.rows.len());
        if len == 0 {
            return;
        }
        self.selected = row.min(len - 1);
        self.scroll_to_selected(cx);
        cx.notify();
    }

    /// Highlights row `row` and shows its function as `mode` says: a permanent tab takes
    /// keyboard focus, the preview leaves it in the panel.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    /// * `mode` - Whether a new tab is the preview tab or a permanent one.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    fn open_row(
        &mut self,
        row: usize,
        mode: TabMode,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let Some(entry) = self
            .rows()
            .and_then(|rows| rows.rows.get(row))
            .map(|r| r.entry)
        else {
            return;
        };
        let (Some(loaded), Some(workspace)) = (self.shown.clone(), self.workspace.upgrade()) else {
            return;
        };
        self.selected = row;
        cx.notify();
        workspace.update(cx, |workspace, cx| {
            let focus = mode == TabMode::Permanent;
            open_function(workspace, loaded, entry, mode, focus, window, cx);
        });
    }

    /// Renders the virtualized table of the shown rows in the buffer font, its columns as
    /// [`Self::relayout`] laid them out, scrolling sideways when they are wider than it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    ///
    /// # Returns
    ///
    /// The table element.
    fn render_table(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let rows = self.rows().cloned();
        let count = rows.as_ref().map_or(0, |r| r.rows.len());
        let selected = self.selected;
        let colors = cx.theme().colors();
        let (selected_bg, hover_bg) = (colors.element_selected, colors.element_hover);
        let (bar, muted) = (colors.text, colors.text_muted);
        let palette = self.palette;
        let ink = move |ink| match ink {
            Ink::Address => palette.address,
            Ink::Function => palette.function,
            Ink::Muted => muted,
        };
        let ui_font = ThemeSettings::get_global(cx).ui_font.clone();
        let panel = cx.entity().downgrade();
        let columns = self.columns;
        let headers = columns.shown().iter().map(|c| {
            let label = Label::new(c.header)
                .size(LabelSize::Small)
                .color(Color::Muted);
            aligned(c.align, label).font(ui_font.clone())
        });
        Table::new(columns.shown().len())
            .width_config(ColumnWidthConfig::Resizable(self.widths.clone()))
            .no_ui_font()
            .hide_row_borders()
            .hide_row_hover()
            .interactable(&self.table_state)
            .header(headers.collect())
            .map_row(move |(ix, row_div), _window, _cx| {
                let panel = panel.clone();
                let here = ix == selected;
                let mark = div()
                    .absolute()
                    .left_0()
                    .top_0()
                    .bottom_0()
                    .w(px(SELECTED_BAR_PX))
                    .bg(bar);
                row_div
                    .debug_selector(|| ROW_SELECTOR.to_owned())
                    .relative()
                    .bg(if here {
                        selected_bg
                    } else {
                        transparent_black()
                    })
                    .when(here, |row| row.child(mark))
                    .when(!here, |row| row.hover(|style| style.bg(hover_bg)))
                    .cursor_pointer()
                    .on_click(move |_, window, cx| {
                        let Some(panel) = panel.upgrade() else {
                            return;
                        };
                        panel.update(cx, |this, cx| {
                            window.focus(&this.focus_handle, cx);
                            this.open_row(ix, TabMode::Preview, window, cx);
                        });
                    })
                    .into_any_element()
            })
            .uniform_list("function-table", count, move |range, _window, _cx| {
                let Some(rows) = &rows else {
                    return Vec::new();
                };
                range
                    .filter_map(|ix| rows.rows.get(ix))
                    .map(|row| {
                        let cells = row_cells(row, columns).into_iter();
                        let shown = columns.shown().iter();
                        cells
                            .zip(shown)
                            .enumerate()
                            .map(|(col, (cell, c))| {
                                aligned(c.align, cell)
                                    .text_color(ink(c.ink))
                                    .when(col == 0, |d| {
                                        d.debug_selector(|| ENTRY_SELECTOR.to_owned())
                                    })
                                    .into_any_element()
                            })
                            .collect()
                    })
                    .collect()
            })
            .into_any_element()
    }
}

/// Returns `child` as the content of a table cell, filling it and sitting where `align`
/// says.
///
/// # Arguments
///
/// * `align` - Where the content sits in its column.
/// * `child` - The cell's text or label.
fn aligned(align: Align, child: impl IntoElement) -> Div {
    div()
        .w_full()
        .flex()
        .when(align == Align::End, Div::justify_end)
        .child(child)
}

impl Render for FunctionsPanel {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let rows = self.rows();
        let header = h_flex()
            .justify_between()
            .gap_2()
            .px(px(8.0))
            .pt(px(6.0))
            .child(Label::new("Functions").weight(FontWeight::SEMIBOLD))
            .children(rows.map(|rows| {
                Label::new(rows.showing())
                    .size(LabelSize::Small)
                    .color(Color::Muted)
            }));
        let incomplete = rows.filter(|rows| rows.incomplete).map(|_| {
            let note = INCOMPLETE_NOTE.trim_start_matches("# ");
            div().px(px(8.0)).child(
                Label::new(note)
                    .size(LabelSize::Small)
                    .color(Color::Warning),
            )
        });
        let filter = h_flex()
            .gap_2()
            .px(px(8.0))
            .py(px(6.0))
            .child(div().flex_1().child(self.filter.clone()))
            .child(Self::filter_hint(cx));
        let body = match self.empty(cx) {
            Some(empty) => v_flex()
                .size_full()
                .items_center()
                .justify_center()
                .gap_2()
                .font(ThemeSettings::get_global(cx).ui_font.clone())
                .child(Label::new(empty.says()).color(Color::Muted))
                .when(empty.offers_open(), |d| d.child(hint_row(OPEN_HINT, cx)))
                .into_any_element(),
            None => self.render_table(cx),
        };
        let (font, size) = {
            let settings = ThemeSettings::get_global(cx);
            (settings.buffer_font.clone(), settings.buffer_font_size(cx))
        };
        let panel = cx.entity().downgrade();
        let watch_width = canvas(
            move |bounds, _, cx| {
                if let Some(panel) = panel.upgrade() {
                    panel.update(cx, |panel, cx| panel.set_table_width(bounds.size.width, cx));
                }
            },
            |_, (), _, _| {},
        )
        .absolute()
        .size_full();
        div()
            .id("functions-panel")
            .key_context("FunctionsPanel")
            .track_focus(&self.focus_handle)
            .on_action(cx.listener(|this, _: &menu::SelectNext, _, cx| {
                this.select(this.selected.saturating_add(1), cx);
            }))
            .on_action(cx.listener(|this, _: &menu::SelectPrevious, _, cx| {
                this.select(this.selected.saturating_sub(1), cx);
            }))
            .on_action(cx.listener(|this, _: &menu::SelectFirst, _, cx| this.select(0, cx)))
            .on_action(cx.listener(|this, _: &menu::SelectLast, _, cx| {
                this.select(usize::MAX, cx);
            }))
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| {
                this.open_row(this.selected, TabMode::Permanent, window, cx);
            }))
            .size_full()
            .flex()
            .flex_col()
            .child(header)
            .children(incomplete)
            .child(filter)
            .child(
                div()
                    .relative()
                    .flex_1()
                    .min_h(px(0.0))
                    .font(font)
                    .text_size(size)
                    .line_height(code_row_height(cx))
                    .child(body)
                    .child(watch_width),
            )
    }
}

impl EventEmitter<PanelEvent> for FunctionsPanel {}

impl Focusable for FunctionsPanel {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Panel for FunctionsPanel {
    fn persistent_name() -> &'static str {
        PANEL_KEY
    }

    fn panel_key() -> &'static str {
        PANEL_KEY
    }

    fn activation_focus_handle(&self, cx: &App) -> FocusHandle {
        self.filter.focus_handle(cx)
    }

    fn position(&self, _window: &Window, _cx: &App) -> DockPosition {
        self.position
    }

    fn position_is_valid(&self, position: DockPosition) -> bool {
        matches!(position, DockPosition::Left | DockPosition::Right)
    }

    fn set_position(
        &mut self,
        position: DockPosition,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.position = position;
        cx.notify();
        cx.update_global::<SettingsStore, _>(|_, _| {});
    }

    fn default_size(&self, _window: &Window, _cx: &App) -> Pixels {
        px(DEFAULT_WIDTH_PX)
    }

    fn icon(&self, _window: &Window, _cx: &App) -> Option<IconName> {
        Some(IconName::ListTree)
    }

    fn icon_tooltip(&self, _window: &Window, _cx: &App) -> Option<&'static str> {
        Some("Functions")
    }

    fn toggle_action(&self) -> Box<dyn Action> {
        Box::new(ToggleFunctions)
    }

    fn starts_open(&self, _window: &Window, _cx: &App) -> bool {
        true
    }

    fn activation_priority(&self) -> u32 {
        1
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::{
        FunctionOrder, FunctionRow, FunctionRows, LeftOut, RowSource,
    };
    use gpui::{Entity, SharedString, TestAppContext, VisualTestContext, px};
    use workspace::Workspace;

    use super::{ENTRY_SELECTOR, Empty, FunctionsPanel, ROW_SELECTOR};
    use crate::actions::FocusFilter;
    use crate::app_view::tests::{init, open, sample};

    /// Vertical padding of a cell of Zed's table at the pin, both sides together, in rems
    /// (`py_0p5` in `data_table.rs`).
    const CELL_PAD_Y_REMS: f32 = 0.25;

    /// Settles the work in flight and lays the window out twice, the second time at the
    /// table width the first measured.
    fn draw(cx: &mut VisualTestContext) {
        for _ in 0..2 {
            cx.run_until_parked();
            cx.update(|window, cx| window.draw(cx).clear(cx));
        }
    }

    /// Returns `workspace`'s functions panel.
    ///
    /// # Panics
    ///
    /// Panics if the workspace has none.
    fn panel_of(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<FunctionsPanel> {
        workspace
            .read_with(cx, |workspace, cx| workspace.panel::<FunctionsPanel>(cx))
            .unwrap()
    }

    /// Shows `rows` of the sample binary in `workspace`'s functions panel and lays it out.
    fn show_rows(workspace: &Entity<Workspace>, rows: FunctionRows, cx: &mut VisualTestContext) {
        let panel = panel_of(workspace, cx);
        panel.update_in(cx, |panel, window, cx| {
            panel.show(sample(), Arc::new(rows), window, cx);
        });
        draw(cx);
    }

    /// Returns hand-built rows of functions at `entries`, each one byte long.
    fn rows_at(entries: &[u64]) -> FunctionRows {
        let row = |&entry: &u64| FunctionRow {
            entry,
            size: 1,
            blocks: 1,
            instrs: 1,
            callers: 0,
            callees: 0,
            src: RowSource::User,
            name: format!("f{entry:x}"),
        };
        FunctionRows {
            total: entries.len(),
            noun: "functions",
            order: FunctionOrder::Address,
            left_out: LeftOut::default(),
            incomplete: false,
            rows: entries.iter().map(row).collect(),
        }
    }

    /// The function table draws no border under its rows: a row is as tall as its cells'
    /// content and Zed's cell padding, not a pixel more.
    ///
    /// # Panics
    ///
    /// Panics if a row is taller, or no row is laid out.
    #[gpui::test]
    fn the_function_table_draws_no_row_border(cx: &mut TestAppContext) {
        the_function_table_draws_no_row_border_steps(cx);
    }

    /// Runs the steps of [`the_function_table_draws_no_row_border`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_function_table_draws_no_row_border`] says.
    fn the_function_table_draws_no_row_border_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        show_rows(&workspace, rows_at(&[0x1000, 0x2000, 0x3000]), cx);
        let row = cx.debug_bounds(ROW_SELECTOR).unwrap();
        let entry = cx.debug_bounds(ENTRY_SELECTOR).unwrap();
        let pad = cx.update(|window, _| window.rem_size()) * CELL_PAD_Y_REMS;
        let extra = row.size.height - entry.size.height - pad;
        assert!(
            extra.abs() < px(0.5),
            "a row is {extra:?} taller than its cells"
        );
    }

    /// Before a load the panel has no rows and offers to open a binary; while a load reads
    /// a file it names the file; when the load fails it gives the binary's reason and
    /// offers to open another.
    ///
    /// # Panics
    ///
    /// Panics if a step says anything else.
    #[gpui::test]
    fn the_panel_follows_a_failing_load(cx: &mut TestAppContext) {
        the_panel_follows_a_failing_load_steps(cx);
    }

    /// Runs the steps of [`the_panel_follows_a_failing_load`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_panel_follows_a_failing_load`] says.
    fn the_panel_follows_a_failing_load_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let empty = |cx: &mut VisualTestContext| panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(empty(cx), Some(Empty::NoBinary));
        assert!(Empty::NoBinary.offers_open());
        let path = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        let binary = panel.read_with(cx, |panel, _| panel.binary().clone());
        binary.update(cx, |binary, cx| binary.open_path(path.clone(), cx));
        let reading = empty(cx);
        assert_eq!(reading, Some(Empty::Reading(path)));
        assert_eq!(
            reading.map(|empty| empty.says()),
            Some("Reading borer-app-no-such-binary.exe".into())
        );
        cx.run_until_parked();
        let reason = binary.read_with(cx, |binary, _| binary.load_error().map(str::to_owned));
        let failed = empty(cx).unwrap();
        assert_eq!(failed, Empty::LoadFailed(reason.unwrap()));
        assert!(failed.offers_open());
        assert!(failed.says().starts_with("Load failed: "));
    }

    /// A binary whose functions the engine all left out says so in the engine's words, how
    /// many and how to list them, and the count line is the engine's own.
    ///
    /// # Panics
    ///
    /// Panics if the panel words it otherwise.
    #[gpui::test]
    fn no_function_names_what_the_engine_left_out(cx: &mut TestAppContext) {
        no_function_names_what_the_engine_left_out_steps(cx);
    }

    /// Runs the steps of [`no_function_names_what_the_engine_left_out`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`no_function_names_what_the_engine_left_out`] says.
    fn no_function_names_what_the_engine_left_out_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        let left_out = LeftOut {
            thunks: 3,
            funclets: 0,
        };
        show_rows(
            &workspace,
            FunctionRows {
                left_out,
                ..rows_at(&[])
            },
            cx,
        );
        let panel = panel_of(&workspace, cx);
        let (empty, showing) = panel.read_with(cx, |panel, cx| {
            (panel.empty(cx), panel.rows().map(|rows| rows.showing()))
        });
        let empty = empty.unwrap();
        assert_eq!(empty, Empty::NoFunction(left_out));
        assert!(!empty.offers_open());
        let note = "; 3 import thunks left out, filter=thunk lists them";
        assert_eq!(
            empty.says(),
            SharedString::from(format!("The engine found no function{note}"))
        );
        assert_eq!(showing, Some(format!("showing 0 of 0 functions{note}")));
    }

    /// A filter nothing matches is quoted as the query that selected the rows shown, and a
    /// newer query whose answer is not in yet does not change what the panel says.
    ///
    /// # Panics
    ///
    /// Panics if the panel quotes another query.
    #[gpui::test]
    fn no_match_quotes_the_query_of_the_rows_shown(cx: &mut TestAppContext) {
        no_match_quotes_the_query_of_the_rows_shown_steps(cx);
    }

    /// Runs the steps of [`no_match_quotes_the_query_of_the_rows_shown`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`no_match_quotes_the_query_of_the_rows_shown`] says.
    fn no_match_quotes_the_query_of_the_rows_shown_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let set_filter = |text: &'static str, cx: &mut VisualTestContext| {
            panel.update_in(cx, |panel, window, cx| {
                panel
                    .filter
                    .update(cx, |editor, cx| editor.set_text(text, window, cx));
            });
        };
        let loaded = sample();
        panel.update_in(cx, |panel, window, cx| {
            panel.show(loaded.clone(), loaded.initial_rows.clone(), window, cx);
        });
        set_filter("zz", cx);
        draw(cx);
        let zz = Some(Empty::NoMatch("zz".into()));
        let empty = |cx: &mut VisualTestContext| panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(empty(cx), zz);
        assert_eq!(
            zz.map(|empty| empty.says()),
            Some("No function matches \"zz\"".into())
        );
        set_filter("zzz", cx);
        assert_eq!(empty(cx), Some(Empty::NoMatch("zz".into())));
        draw(cx);
        assert_eq!(empty(cx), Some(Empty::NoMatch("zzz".into())));
    }

    /// The filter's hint shows the binding the keymap holds for [`FocusFilter`], and a new
    /// binding replaces it.
    ///
    /// # Panics
    ///
    /// Panics if the hint shows no binding or keeps the old one.
    #[gpui::test]
    fn the_filter_hint_follows_the_keymap(cx: &mut TestAppContext) {
        the_filter_hint_follows_the_keymap_steps(cx);
    }

    /// Runs the steps of [`the_filter_hint_follows_the_keymap`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_filter_hint_follows_the_keymap`] says.
    fn the_filter_hint_follows_the_keymap_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        let hint = |cx: &mut VisualTestContext| {
            cx.update(|window, cx| {
                FunctionsPanel::filter_hint(cx).keyboard_shortcut_text(window, cx)
            })
        };
        let before = hint(cx);
        assert!(before.is_some(), "the hint shows no binding");
        cx.update(|_, cx| {
            let rebound = gpui::KeyBinding::new("ctrl-alt-9", FocusFilter, Some("Workspace"));
            cx.bind_keys([rebound]);
        });
        let after = hint(cx);
        assert_ne!(after, before);
        assert!(
            after.as_ref().is_some_and(|text| text.ends_with('9')),
            "{after:?}"
        );
    }
}
