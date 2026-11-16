//! A panel of the engine's rows of one kind, in a dock of Zed's workspace.
//!
//! The rows are filtered through a Zed single-line editor in the background and drawn as
//! Zed's table in the engine's words; a row opens its place.

use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::render::LeftOut;
use editor::{Editor, EditorEvent};
use gpui::prelude::FluentBuilder as _;
use gpui::{
    Action, AnyElement, App, AppContext as _, BorrowAppContext as _, Context, Div, Entity,
    EventEmitter, FocusHandle, Focusable, FontWeight, InteractiveElement as _, IntoElement,
    ParentElement as _, Pixels, Render, ScrollStrategy, SharedString, Stateful,
    StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity, Window, canvas, div,
    px, transparent_black,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};
use theme_settings::ThemeSettings;
use ui::{
    Color, ColumnWidthConfig, IconName, KeyBinding, Label, LabelCommon as _, LabelSize,
    ResizableColumnsState, Table, TableInteractionState, TableResizeBehavior, h_flex,
};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

use crate::actions::{FocusFilter, Hint, OPEN_HINT};
use crate::binary::{Binary, BinaryEvent, SettingsNotice, reading_label};
use crate::card::{Card, Tone};
use crate::code_view::{CodePalette, Role};
use crate::decompile_item::{TabMode, code_row_height};
use crate::panels::{PanelSpec, priority};
use crate::places::{Opening, Place, open};
use crate::table::{Column, Columns, Ink, aligned, cells, widths};
use crate::worker::{Job, LoadedBinary};

/// One kind of rows a panel lists: its panel's facts, its columns, how the engine selects
/// its rows and what a row opens.
pub trait RowKind: Sized + 'static {
    /// One row of the engine's answer.
    type Row: Send + Sync + 'static;
    /// The engine's whole answer for one filter: its rows and the words counting them.
    type Shown: Send + Sync + 'static;
    /// The panel's row of [`crate::panels::PANELS`].
    const PANEL: &'static PanelSpec;
    /// What the filter's empty editor says.
    const PLACEHOLDER: &'static str;
    /// What the status line calls the table (`function table`).
    const TABLE: &'static str;
    /// What the running work list calls a filter request (`Filtering functions`).
    const FILTERING: &'static str;

    /// Returns the columns of set `columns`, in order.
    fn columns(columns: Columns) -> &'static [Column<Self::Row>];

    /// Returns the rows of an answer.
    fn rows(shown: &Self::Shown) -> &[Self::Row];

    /// Returns the engine's count line of an answer: `showing N of M` and what it left out.
    fn showing(shown: &Self::Shown) -> SharedString;

    /// Returns the engine's warning about an answer, if it gave one.
    fn warning(shown: &Self::Shown) -> Option<&'static str>;

    /// Returns the rows a finished load already built, every row unfiltered; no engine
    /// call, since it runs on the UI thread.
    fn first(loaded: &LoadedBinary) -> Arc<Self::Shown>;

    /// Selects the rows matching `filter`, every row for an empty one; runs in the
    /// background.
    fn fetch(loaded: &LoadedBinary, filter: &str) -> Self::Shown;

    /// Returns why an answer with no rows has none, from the engine's words and `query`.
    fn nothing(shown: &Self::Shown, query: &SharedString) -> Empty;

    /// Returns what Enter on `row` opens, `None` for a row that opens nothing.
    fn place(row: &Self::Row) -> Option<Place>;
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
            Self::Reading(path) => reading_label(path),
            Self::LoadFailed(reason) => format!("Load failed: {reason}").into(),
            Self::NoFunction(left_out) => format!("The engine found no function{left_out}").into(),
            Self::NoMatch(query) => format!("No function matches \"{query}\"").into(),
        }
    }

    /// Returns the case for a binary no rows are shown of: a load reading a file, the last
    /// load's failure, else no binary.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    #[must_use]
    pub fn of_binary(binary: &Binary) -> Self {
        match (binary.reading(), binary.load_error()) {
            (Some(loading), _) => Self::Reading(loading.path.clone()),
            (None, Some(reason)) => Self::LoadFailed(reason.to_owned()),
            (None, None) => Self::NoBinary,
        }
    }

    /// Returns the card the panel draws for the case: its words, an error tone for a
    /// failed load, and the open command where it offers one.
    #[must_use]
    pub fn card(&self) -> Card {
        let tone = match self {
            Self::LoadFailed(_) => Tone::Error,
            Self::NoBinary | Self::Reading(_) | Self::NoFunction(_) | Self::NoMatch(_) => {
                Tone::Quiet
            }
        };
        let offers: &'static [Hint] = if self.offers_open() {
            &[OPEN_HINT]
        } else {
            &[]
        };
        Card {
            says: self.says(),
            tone,
            offers,
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

/// Horizontal padding of a cell of Zed's table, both sides together, in rems (`px_1`).
const CELL_PAD_REMS: f32 = 0.5;

/// Width in logical pixels of the bar the selected row paints over its left padding, so no
/// row and no header moves.
const SELECTED_BAR_PX: f32 = 2.0;

/// Debug selector of a table row, whose laid-out bounds the tests read.
pub(crate) const ROW_SELECTOR: &str = "function-row";

/// Debug selector of a first cell's content, whose laid-out bounds the tests read.
pub(crate) const ENTRY_SELECTOR: &str = "function-entry";

/// Debug selector of a column header, whose presence the tests read.
pub(crate) const HEADER_SELECTOR: &str = "rows-header";

/// Rows the engine selected, with the filter query that selected them.
struct Filtered<K: RowKind> {
    /// The query, empty for every row.
    query: SharedString,
    /// The engine's rows for it.
    rows: Arc<K::Shown>,
}

/// The open binary's rows of kind `K`, in a dock.
pub struct RowsPanel<K: RowKind> {
    /// Workspace the panel opens a row's place in.
    workspace: WeakEntity<Workspace>,
    /// The binary whose rows the panel lists.
    binary: Entity<Binary>,
    /// Focus handle of the panel's root.
    focus_handle: FocusHandle,
    /// Zed's single-line editor holding the filter query.
    pub(crate) filter: Entity<Editor>,
    /// Scroll and focus state of the table.
    table_state: Entity<TableInteractionState>,
    /// The binary the rows come from.
    shown: Option<Arc<LoadedBinary>>,
    /// The rows shown, with the query that selected them.
    rows: Option<Filtered<K>>,
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
    /// The running background filter, the newest answer winning.
    filter_job: Job,
    /// Colors of the engine's token kinds, read again when the theme or the settings change.
    palette: CodePalette,
    /// Reruns the filter on each edit, follows the binary's loads, and lays the table out
    /// again on a settings or theme change.
    _subscriptions: [Subscription; 4],
}

impl<K: RowKind> std::fmt::Debug for RowsPanel<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(K::PANEL.key)
            .field("selected", &self.selected)
            .finish_non_exhaustive()
    }
}

impl<K: RowKind> RowsPanel<K> {
    /// Returns the panel listing `binary`'s rows of kind `K`.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the panel opens a row's place in.
    /// * `binary` - The binary whose rows to list.
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
            editor.set_placeholder_text(K::PLACEHOLDER, window, cx);
            editor
        });
        let subscriptions = [
            cx.subscribe(&filter, |this, _, event: &EditorEvent, cx| {
                if matches!(event, EditorEvent::BufferEdited) {
                    this.request_filter(cx);
                }
            }),
            cx.subscribe_in(&binary, window, |this, _, _: &BinaryEvent, window, cx| {
                this.follow(window, cx);
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
            rows: None,
            selected: 0,
            columns: Columns::Brief,
            widths: cx.new(|_| ResizableColumnsState::new(0, Vec::<Pixels>::new(), Vec::new())),
            table_width: px(K::PANEL.size_px),
            position,
            filter_job: Job::default(),
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
            let why = format!("{} measured by font size: {err:#}", K::TABLE);
            cx.set_global(SettingsNotice(Some(why.into())));
            size
        });
        let rows = self.rows().map_or(&[][..], |rows| K::rows(rows));
        let widths = widths(K::columns(self.columns), rows, ch, pad, self.table_width);
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

    /// Returns the binary whose rows the panel lists.
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
        let Some(Filtered { query, rows }) = &self.rows else {
            return Some(Empty::of_binary(self.binary.read(cx)));
        };
        K::rows(rows).is_empty().then(|| K::nothing(rows, query))
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
    pub fn rows(&self) -> Option<&Arc<K::Shown>> {
        self.rows.as_ref().map(|filtered| &filtered.rows)
    }

    /// Returns the ticket of the latest filter request.
    #[must_use]
    pub const fn filter_ticket(&self) -> u64 {
        self.filter_job.ticket()
    }

    /// Returns whether filter request `seq` is answered on screen or superseded.
    ///
    /// # Arguments
    ///
    /// * `seq` - A [`Self::filter_ticket`] value.
    #[must_use]
    pub fn filter_settled(&self, seq: u64) -> bool {
        self.filter_job.settled(seq)
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
        rows: Arc<K::Shown>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.shown = Some(loaded);
        self.rows = Some(Filtered {
            query: SharedString::default(),
            rows,
        });
        self.filter_job.stop();
        self.selected = 0;
        if !self.filter.read(cx).text(cx).is_empty() {
            self.filter
                .update(cx, |editor, cx| editor.set_text("", window, cx));
        }
        self.scroll_to_selected(cx);
        self.relayout(cx);
    }

    /// Lists the rows the binary open now already holds and opens the first one's place,
    /// or empties the table when none is open; it runs on every [`BinaryEvent`] and reads
    /// the binary, not the event, so a panel added after a load and a load closed in the
    /// same update both show what is open.
    ///
    /// Never call it while the workspace is being updated: opening the first row updates
    /// the workspace.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub fn follow(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        match self.binary.read(cx).loaded().cloned() {
            Some(loaded) => {
                let rows = K::first(&loaded);
                self.show(loaded, rows, window, cx);
                self.open_row(0, TabMode::Preview, window, cx);
            }
            None => {
                if self.shown.take().is_some() {
                    self.rows = None;
                    self.filter_job.stop();
                    self.relayout(cx);
                }
            }
        }
    }

    /// Filters the rows by the editor's query in the background, dropping the filter before.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context spawning the background filter.
    fn request_filter(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.shown.clone() else {
            return;
        };
        let query = SharedString::from(self.filter.read(cx).text(cx));
        let asked = query.clone();
        let work = move || Arc::new(K::fetch(&loaded, &asked));
        self.filter_job
            .run(K::FILTERING, cx, work, |panel, rows, cx| {
                panel.rows = Some(Filtered { query, rows });
                panel.selected = 0;
                panel.scroll_to_selected(cx);
                panel.relayout(cx);
            });
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

    /// Highlights row `row` and shows its place as `mode` says: a permanent tab takes
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
        let Some(place) = self
            .rows()
            .and_then(|rows| K::rows(rows).get(row))
            .and_then(K::place)
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
            let how = Opening { mode, focus };
            open(workspace, &self.binary, &loaded, place, how, window, cx);
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
        let count = rows.as_ref().map_or(0, |r| K::rows(r).len());
        let selected = self.selected;
        let colors = cx.theme().colors();
        let (selected_bg, hover_bg) = (colors.element_selected, colors.element_hover);
        let (bar, muted) = (colors.text, colors.text_muted);
        let palette = self.palette;
        let ink = move |ink| match ink {
            Ink::Address => palette.color(Role::Address),
            Ink::Function => palette.color(Role::Function),
            Ink::Muted => muted,
        };
        let ui_font = ThemeSettings::get_global(cx).ui_font.clone();
        let panel = cx.entity().downgrade();
        let columns = self.columns;
        let shown = K::columns(columns);
        let headers = shown.iter().map(|c| {
            let label = Label::new(c.header)
                .size(LabelSize::Small)
                .color(Color::Muted);
            aligned(c.align, label)
                .font(ui_font.clone())
                .debug_selector(|| HEADER_SELECTOR.to_owned())
        });
        Table::new(shown.len())
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
            .uniform_list(K::PANEL.key, count, move |range, _window, _cx| {
                let Some(rows) = &rows else {
                    return Vec::new();
                };
                range
                    .filter_map(|ix| K::rows(rows).get(ix))
                    .map(|row| {
                        cells(row, shown)
                            .into_iter()
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

impl<K: RowKind> Render for RowsPanel<K> {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let rows = self.rows();
        let header = h_flex()
            .justify_between()
            .gap_2()
            .px(px(8.0))
            .pt(px(6.0))
            .child(Label::new(K::PANEL.title).weight(FontWeight::SEMIBOLD))
            .children(rows.map(|rows| {
                Label::new(K::showing(rows))
                    .size(LabelSize::Small)
                    .color(Color::Muted)
            }));
        let incomplete = rows.and_then(|rows| K::warning(rows)).map(|note| {
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
            Some(empty) => empty.card().render(cx),
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
        let root = div()
            .id(K::PANEL.key)
            .key_context("RowsPanel")
            .track_focus(&self.focus_handle);
        row_keys(root, cx)
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

/// A view with a highlighted row, which the menu's next and previous keys move.
pub(crate) trait Rows: Sized + 'static {
    /// Returns the index of the highlighted row.
    fn selected(&self) -> usize;

    /// Moves the highlight to row `row`, held to the rows shown.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row; past the last selects the last.
    /// * `cx` - View context.
    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>);
}

/// Returns `element` with the menu's next and previous keys moving `T`'s highlight.
///
/// # Arguments
///
/// * `element` - The view's root element.
/// * `cx` - View context.
pub(crate) fn row_keys<T: Rows>(element: Stateful<Div>, cx: &Context<'_, T>) -> Stateful<Div> {
    element
        .on_action(cx.listener(|this: &mut T, _: &menu::SelectNext, _, cx| {
            this.select(this.selected().saturating_add(1), cx);
        }))
        .on_action(
            cx.listener(|this: &mut T, _: &menu::SelectPrevious, _, cx| {
                this.select(this.selected().saturating_sub(1), cx);
            }),
        )
}

impl<K: RowKind> Rows for RowsPanel<K> {
    fn selected(&self) -> usize {
        self.selected
    }

    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        let len = self.rows().map_or(0, |r| K::rows(r).len());
        if len == 0 {
            return;
        }
        self.selected = row.min(len - 1);
        self.scroll_to_selected(cx);
        cx.notify();
    }
}

impl<K: RowKind> EventEmitter<PanelEvent> for RowsPanel<K> {}

impl<K: RowKind> Focusable for RowsPanel<K> {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl<K: RowKind> Panel for RowsPanel<K> {
    fn persistent_name() -> &'static str {
        K::PANEL.key
    }

    fn panel_key() -> &'static str {
        K::PANEL.key
    }

    fn activation_focus_handle(&self, cx: &App) -> FocusHandle {
        self.filter.focus_handle(cx)
    }

    fn position(&self, _window: &Window, _cx: &App) -> DockPosition {
        self.position
    }

    fn position_is_valid(&self, position: DockPosition) -> bool {
        K::PANEL.docks.contains(&position)
    }

    /// Moves the panel to `position`, then pokes the settings store once: Zed's dock moves a
    /// panel only when the store changes (the settings observer `Dock::add_panel` sets), and
    /// the app keeps no dock setting of its own to write.
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
        px(K::PANEL.size_px)
    }

    fn icon(&self, _window: &Window, _cx: &App) -> Option<IconName> {
        Some(K::PANEL.icon)
    }

    fn icon_tooltip(&self, _window: &Window, _cx: &App) -> Option<&'static str> {
        Some(K::PANEL.title)
    }

    fn toggle_action(&self) -> Box<dyn Action> {
        K::PANEL.toggle.boxed_clone()
    }

    fn starts_open(&self, _window: &Window, _cx: &App) -> bool {
        true
    }

    fn activation_priority(&self) -> u32 {
        priority(K::PANEL.key)
    }
}
