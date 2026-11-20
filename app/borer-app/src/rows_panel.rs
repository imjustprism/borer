//! A panel of the engine's rows of one kind, in a dock of Zed's workspace.
//!
//! The rows are filtered through a Zed single-line editor in the background and drawn as
//! Zed's table in the engine's words; a row opens its place. A kind whose rows a load does
//! not build asks the engine for them while its panel is open, [`PAGE_ROWS`] at a time and a
//! page more as the list nears its end; sorted by a column, the panel asks for the first
//! [`SORT_MAX`] rows the filter keeps and sorts them, and says so when it keeps more.

use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use borer_engine::analysis::render::LeftOut;
use borer_engine::view::Ref;
use editor::{Editor, EditorEvent};
use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, AppContext as _, BorrowAppContext as _, Context, Div, Entity, EventEmitter,
    FocusHandle, Focusable, FontWeight, InteractiveElement as _, IntoElement, ParentElement as _,
    Pixels, Render, ScrollStrategy, SharedString, Stateful, StatefulInteractiveElement as _,
    Styled as _, Subscription, WeakEntity, Window, canvas, div, px, transparent_black,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};
use theme_settings::ThemeSettings;
use ui::{
    Color, ColumnWidthConfig, KeyBinding, Label, LabelCommon as _, LabelSize,
    ResizableColumnsState, Table, TableInteractionState, TableResizeBehavior, Tooltip, h_flex,
};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

use crate::actions::{CycleSort, FocusFilter, Hint, OPEN_HINT, ShowHex, Xrefs};
use crate::annotate::{Ask, Strip, answer_asks};
use crate::binary::{Binary, BinaryEvent, Revision, SettingsNotice, reading_label};
use crate::card::{Card, Tone};
use crate::code_view::CodePalette;
use crate::decompile_item::{TabMode, code_row_height};
use crate::panels::{PanelSpec, spec_panel};
use crate::places::{Opening, Place, open_later};
use crate::table::{
    Column, Columns, Fit, Ink, aligned, count_text, fit_width, row_cells, scrollbar_room, widths,
};
use crate::worker::{Job, LoadedBinary, Referent};

/// Rows one page asks the engine for.
pub const PAGE_ROWS: usize = 20_000;

/// Most rows a sorted table asks for and sorts.
pub const SORT_MAX: usize = 100_000;

/// One kind of rows a panel lists: its panel's facts, its columns, how the engine selects
/// its rows and what a row opens.
pub trait RowKind: Sized + 'static {
    /// One row of the engine's answer.
    type Row: Send + Sync + 'static;
    /// The engine's whole answer for one filter: its rows and the words counting them.
    type Shown: Answer<Self::Row>;
    /// What the rows are of beyond the binary, `()` for a whole table; a new binary starts
    /// it over.
    type Target: Clone + Default + Send + 'static;
    /// The panel's row of [`crate::panels::PANELS`].
    const PANEL: &'static PanelSpec;
    /// What the filter's empty editor says.
    const PLACEHOLDER: &'static str;
    /// What the status line calls the table (`function table`).
    const TABLE: &'static str;
    /// What the running work list calls a filter request (`Filtering functions`).
    const FILTERING: &'static str;
    /// Whether a click shows a row's place in the preview tab, a new binary opens its first
    /// row and the panel starts open; else a click only highlights a row.
    const PREVIEWS: bool = false;
    /// Whether the engine filters the rows by text, so the panel shows a filter.
    const FILTERS: bool = true;

    /// Returns the columns of set `columns`, in order.
    fn columns(columns: Columns) -> &'static [Column<Self::Row>];

    /// Returns the engine's warning about an answer, if it gave one.
    fn warning(_shown: &Self::Shown) -> Option<&'static str> {
        None
    }

    /// Returns the rows a finished load already built, every row unfiltered, `None` when
    /// the load builds none and the panel asks the engine in the background; no engine
    /// call, since it runs on the UI thread.
    fn first(_loaded: &LoadedBinary) -> Option<Arc<Self::Shown>> {
        None
    }

    /// Selects the first `limit` rows of `target` matching `filter`, every row for an
    /// empty one; runs in the background.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary.
    /// * `target` - What the rows are of.
    /// * `filter` - The filter's text, empty for every row.
    /// * `limit` - Most rows; a kind whose load builds every row may return them all.
    fn fetch(
        loaded: &LoadedBinary,
        target: &Self::Target,
        filter: &str,
        limit: usize,
    ) -> Self::Shown;

    /// Returns why an answer with no rows has none, from the engine's words and `query`.
    fn nothing(shown: &Self::Shown, query: &SharedString) -> Empty;

    /// Returns what Enter on `row` opens, `None` for a row that opens nothing.
    fn place(row: &Self::Row) -> Option<Place>;

    /// Returns what `row` stands for, whose references Xrefs lists and whose bytes Show
    /// Hex shows; `None` for a row that stands for no address.
    fn referent(_row: &Self::Row) -> Option<Referent> {
        None
    }

    /// Returns what `row` stands for as the engine's edits name it ([`borer_engine::analysis::edit::offer`]): its
    /// referent's address or import; `None` for a row that stands for no address.
    fn subject(row: &Self::Row) -> Option<Ref> {
        Self::referent(row).map(|referent| match referent {
            Referent::Address(va) => Ref::Address(va),
            Referent::Import(slot) => Ref::Import(slot),
        })
    }
}

/// The engine's answer for one filter of a table of rows `R`.
pub trait Answer<R>: Send + Sync + 'static {
    /// Returns the rows of the answer.
    fn rows(&self) -> &[R];

    /// Returns the rows of the answer to reorder.
    fn rows_mut(&mut self) -> &mut [R];

    /// Returns how many rows the filter keeps in all, past the ones the answer holds.
    fn total(&self) -> usize {
        self.rows().len()
    }

    /// Returns the answer's count as a person reads it ([`crate::table::count_text`]).
    fn showing(&self) -> SharedString;

    /// Returns a short count of the rows the engine left out unless the filter asks for
    /// them, and the sentence its tooltip says; `None` when it left none out.
    fn hidden(&self) -> Option<(SharedString, SharedString)> {
        None
    }
}

impl<R: Send + Sync + 'static> Answer<R> for Page<R> {
    fn rows(&self) -> &[R] {
        &self.rows
    }

    fn rows_mut(&mut self) -> &mut [R] {
        &mut self.rows
    }

    fn total(&self) -> usize {
        self.total
    }

    fn showing(&self) -> SharedString {
        self.header.clone()
    }
}

/// One answer of an engine table: its rows, how many the filter keeps and the engine's
/// header counting them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Page<R> {
    /// How many rows show of how many the filter keeps, in the engine's words.
    pub header: SharedString,
    /// Rows the filter keeps, on every page.
    pub total: usize,
    /// The rows shown, in the engine's order.
    pub rows: Vec<R>,
}

impl<R> Page<R> {
    /// Returns `rows` of `total`, counted as `plural` ([`count_text`]).
    ///
    /// # Arguments
    ///
    /// * `rows` - The rows on the page.
    /// * `total` - Rows the filter keeps.
    /// * `plural` - What the rows are, plural.
    #[must_use]
    pub fn counted(rows: Vec<R>, total: usize, plural: &str) -> Self {
        let header = count_text(rows.len(), total, plural);
        Self {
            header: header.into(),
            total,
            rows,
        }
    }

    /// Returns why a page with no rows has none: no `noun` matches `query`, else the
    /// engine's header.
    ///
    /// # Arguments
    ///
    /// * `noun` - What one row is.
    /// * `query` - The filter that selected the page.
    #[must_use]
    pub fn nothing(&self, noun: &str, query: &SharedString) -> Empty {
        if query.is_empty() {
            Empty::Nothing(self.header.clone())
        } else {
            Empty::Nothing(format!("No {noun} matches \"{query}\"").into())
        }
    }
}

/// Which column the rows are sorted by, and which way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sort {
    /// Index of the column among the shown ones.
    pub column: usize,
    /// Whether the largest come first.
    pub descending: bool,
}

/// Returns the sort after `sort` that a click on column `column` asks for: ascending, then
/// descending, then the engine's order again.
///
/// # Arguments
///
/// * `sort` - The sort in force.
/// * `column` - The clicked column.
#[must_use]
pub const fn clicked(sort: Option<Sort>, column: usize) -> Option<Sort> {
    match sort {
        Some(Sort {
            column: c,
            descending,
        }) if c == column => {
            if descending {
                None
            } else {
                Some(Sort {
                    column,
                    descending: true,
                })
            }
        }
        Some(_) | None => Some(Sort {
            column,
            descending: false,
        }),
    }
}

/// Returns the sort after `sort` that [`CycleSort`] asks for: each sortable column of
/// `columns` ascending then descending, in order, then the engine's order again.
///
/// # Arguments
///
/// * `sort` - The sort in force.
/// * `columns` - The shown columns.
#[must_use]
pub fn cycled<R>(sort: Option<Sort>, columns: &[Column<R>]) -> Option<Sort> {
    let next_from = |from: usize| {
        (from..columns.len())
            .find(|&c| columns.get(c).is_some_and(|c| c.sort.is_some()))
            .map(|column| Sort {
                column,
                descending: false,
            })
    };
    match sort {
        None => next_from(0),
        Some(Sort {
            column,
            descending: false,
        }) => Some(Sort {
            column,
            descending: true,
        }),
        Some(Sort {
            column,
            descending: true,
        }) => next_from(column.saturating_add(1)),
    }
}

/// Where a rows panel's highlight goes when the rows it asked for come.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Then {
    /// It stays on the place of the row highlighted then ([`RowsPanel::kept_row`]).
    Kept,
    /// It goes back to the first row, highlighted only if a row was.
    First,
    /// It goes to the first row and highlights it, as the person typed a filter, so Enter
    /// opens the top match; none while no row matches.
    Typed,
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
    /// The engine's words for an answer with no rows of another kind.
    Nothing(SharedString),
}

impl Empty {
    /// Returns what the panel says for the case.
    #[must_use]
    pub fn says(&self) -> SharedString {
        match self {
            Self::NoBinary => SharedString::new_static("No binary loaded"),
            Self::Reading(path) => reading_label(path),
            Self::LoadFailed(reason) => format!("Load failed: {reason}").into(),
            Self::NoFunction(left_out) => match crate::functions_panel::hidden(*left_out) {
                Some((_, tip)) => format!("The engine found no function. {tip}").into(),
                None => SharedString::new_static("The engine found no function"),
            },
            Self::NoMatch(query) => format!("No function matches \"{query}\"").into(),
            Self::Nothing(said) => said.clone(),
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
            Self::NoBinary
            | Self::Reading(_)
            | Self::NoFunction(_)
            | Self::NoMatch(_)
            | Self::Nothing(_) => Tone::Quiet,
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
            Self::Reading(_) | Self::NoFunction(_) | Self::NoMatch(_) | Self::Nothing(_) => false,
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

/// Debug selector of the area the table draws in, whose laid-out bounds the tests read.
pub(crate) const BODY_SELECTOR: &str = "rows-body";

/// Rows the engine selected, with the filter query that selected them.
struct Filtered<K: RowKind> {
    /// The query, empty for every row.
    query: SharedString,
    /// The engine's rows for it.
    rows: Arc<K::Shown>,
    /// [`LoadedBinary::fingerprint`] of the state the rows were selected from.
    revision: u64,
}

/// The open binary's rows of kind `K`, in a dock.
pub struct RowsPanel<K: RowKind> {
    /// Workspace the panel opens a row's place in.
    workspace: WeakEntity<Workspace>,
    /// The binary whose rows the panel lists.
    binary: Entity<Binary>,
    /// Focus handle of the panel's root.
    focus_handle: FocusHandle,
    /// Focus handle of the table, under the `BorerRows` key context its letter keys need.
    rows_focus: FocusHandle,
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
    /// Whether the highlighted row is drawn and acted on: false while the open function is
    /// not among the rows shown, until a row is picked again.
    lit: bool,
    /// Columns the table shows.
    columns: Columns,
    /// What the rows are of.
    target: K::Target,
    /// The sort in force, `None` for the engine's order.
    sort: Option<Sort>,
    /// Rows asked for while unsorted.
    limit: usize,
    /// Whether the panel is open in its dock.
    active: bool,
    /// Whether the rows shown are not what the panel's state asks for, so opening the
    /// panel asks again.
    stale: bool,
    /// Widths of the shown columns, laid out again when the rows, the columns, the
    /// settings or the table's width change.
    widths: Entity<ResizableColumnsState>,
    /// Per shown column, whether its width is capped under its widest cell, so its cells
    /// carry their whole text in a tooltip.
    capped: Arc<[bool]>,
    /// Width of the table as last painted, the panel's default before its first paint.
    table_width: Pixels,
    /// Dock the panel sits in.
    position: DockPosition,
    /// The running background filter, the newest answer winning.
    filter_job: Job,
    /// The inline editor under the table, renaming or commenting the highlighted row.
    strip: Strip,
    /// Colors of the engine's token kinds, read again when the theme or the settings change.
    palette: CodePalette,
    /// Reruns the filter on each edit, follows the binary's loads, and lays the table out
    /// again on a settings or theme change.
    _subscriptions: [Subscription; 4],
}

impl<K: RowKind> Revision for RowsPanel<K> {
    fn revision(&self) -> Option<u64> {
        self.rows.as_ref().map(|rows| rows.revision)
    }
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
                    this.limit = PAGE_ROWS;
                    this.request(Then::Typed, cx);
                }
            }),
            cx.subscribe_in(
                &binary,
                window,
                |this, _, event: &BinaryEvent, window, cx| match event {
                    BinaryEvent::Revised(loaded) => this.revise(loaded.clone(), cx),
                    BinaryEvent::Opened(_) | BinaryEvent::Closed => this.follow(window, cx),
                    BinaryEvent::Rechecked { .. } => {}
                },
            ),
            cx.observe_global::<SettingsStore>(Self::relayout),
            cx.observe_global::<GlobalTheme>(Self::relayout),
        ];
        let mut panel = Self {
            workspace,
            binary,
            focus_handle: cx.focus_handle(),
            rows_focus: cx.focus_handle(),
            filter,
            table_state: cx.new(|cx| TableInteractionState::new(cx)),
            shown: None,
            rows: None,
            selected: 0,
            lit: true,
            columns: Columns::Brief,
            target: K::Target::default(),
            sort: None,
            limit: PAGE_ROWS,
            active: false,
            stale: false,
            widths: cx.new(|_| ResizableColumnsState::new(0, Vec::<Pixels>::new(), Vec::new())),
            capped: Arc::from([]),
            table_width: px(K::PANEL.size_px),
            position,
            filter_job: Job::default(),
            strip: Strip::default(),
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
        let rows = self.rows().map_or(&[][..], |rows| rows.rows());
        let shown = K::columns(self.columns);
        let widths = widths(shown, rows, ch, pad, self.table_width);
        self.capped = shown
            .iter()
            .zip(&widths)
            .map(|(column, width)| {
                matches!(column.fit, Fit::UpTo(..))
                    && column
                        .chars(rows)
                        .is_some_and(|chars| fit_width(chars, ch, pad) > *width)
            })
            .collect();
        let cols = widths.len();
        let resize = vec![TableResizeBehavior::None; cols];
        self.widths = cx.new(|_| ResizableColumnsState::new(cols, widths, resize));
        cx.notify();
    }

    /// Lays the columns out again for a table now `width` wide, when their width changed:
    /// the table's, less [`scrollbar_room`] while the rows scroll as Zed's scrollbar sees.
    ///
    /// # Arguments
    ///
    /// * `width` - Width the table was painted at.
    /// * `cx` - Panel context.
    fn set_table_width(&mut self, width: Pixels, cx: &mut Context<'_, Self>) {
        let scroll = &self.table_state.read(cx).scroll_handle;
        let tall = scroll.0.borrow().base_handle.max_offset().y > Pixels::ZERO;
        let width = width - if tall { scrollbar_room() } else { Pixels::ZERO };
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
        if self.sort.take().is_some() {
            self.request(Then::First, cx);
        }
        self.relayout(cx);
    }

    /// Returns the sort in force.
    #[must_use]
    pub const fn sort(&self) -> Option<Sort> {
        self.sort
    }

    /// Sorts the rows as `sort` says and asks for them again.
    ///
    /// # Arguments
    ///
    /// * `sort` - The new sort, `None` for the engine's order.
    /// * `cx` - Panel context.
    pub fn set_sort(&mut self, sort: Option<Sort>, cx: &mut Context<'_, Self>) {
        self.sort = sort;
        self.request(Then::First, cx);
    }

    /// Returns what the rows are of.
    #[must_use]
    pub const fn target(&self) -> &K::Target {
        &self.target
    }

    /// Lists the rows of `target` from the first, asking the engine for them while the
    /// panel is open.
    ///
    /// # Arguments
    ///
    /// * `target` - What the rows are of.
    /// * `cx` - Panel context.
    pub fn set_target(&mut self, target: K::Target, cx: &mut Context<'_, Self>) {
        self.target = target;
        self.limit = PAGE_ROWS;
        self.refresh(Then::First, cx);
    }

    /// Keeps only the rows `text` filters, as typing it into the filter does.
    ///
    /// # Arguments
    ///
    /// * `text` - The filter's new text.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub fn set_filter(&mut self, text: &str, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.filter
            .update(cx, |editor, cx| editor.set_text(text, window, cx));
    }

    /// Returns the filter's text.
    #[must_use]
    pub fn filter_text(&self, cx: &App) -> String {
        self.filter.read(cx).text(cx)
    }

    /// Returns the highlighted row, if any.
    #[must_use]
    pub fn selected_row(&self) -> Option<&K::Row> {
        self.rows()?.rows().get(self.selected).filter(|_| self.lit)
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
        let Some(Filtered { query, rows, .. }) = &self.rows else {
            if self.shown.is_some() {
                let reading = format!("Reading {}", K::PANEL.title.to_lowercase());
                return Some(Empty::Nothing(reading.into()));
            }
            return Some(Empty::of_binary(self.binary.read(cx)));
        };
        rows.rows().is_empty().then(|| K::nothing(rows, query))
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

    /// Returns whether the panel shows nothing older than the binary state `now`: its rows
    /// are of `now`, it shows none, or it is closed and asks again when it opens.
    ///
    /// # Arguments
    ///
    /// * `now` - The [`LoadedBinary::fingerprint`] of the binary's state, `None` with none open.
    #[must_use]
    pub fn is_current(&self, now: Option<u64>) -> bool {
        let shown = self.rows.as_ref().map(|rows| rows.revision);
        shown.is_none() || shown == now || (self.stale && !self.active)
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
        self.rows = Some(Filtered {
            query: SharedString::default(),
            rows,
            revision: loaded.fingerprint,
        });
        self.shown = Some(loaded);
        self.filter_job.stop();
        self.selected = 0;
        if !self.filter.read(cx).text(cx).is_empty() {
            self.filter
                .update(cx, |editor, cx| editor.set_text("", window, cx));
        }
        self.scroll_to_selected(cx);
        self.relayout(cx);
    }

    /// Lists the rows the binary open now holds, from the load or asked of the engine, and
    /// opens the first one's place for a kind that previews, or empties the table when none
    /// is open; the filter, the sort and the target start over. It runs on every
    /// [`BinaryEvent`] and reads the binary, not the event, so a panel added after a load
    /// and a load closed in the same update both show what is open.
    ///
    /// Never call it while the workspace is being updated: opening the first row updates
    /// the workspace.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub fn follow(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.target = K::Target::default();
        self.sort = None;
        self.limit = PAGE_ROWS;
        match self.binary.read(cx).loaded().cloned() {
            Some(loaded) => {
                if let Some(first) = K::first(&loaded) {
                    self.show(loaded, first, window, cx);
                } else {
                    self.shown = Some(loaded);
                    self.rows = None;
                    if !self.filter.read(cx).text(cx).is_empty() {
                        self.filter
                            .update(cx, |editor, cx| editor.set_text("", window, cx));
                    }
                    self.refresh(Then::First, cx);
                }
                if K::PREVIEWS {
                    self.open_row(0, TabMode::Preview, window, cx);
                }
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

    /// Asks again under the filter over `loaded`, the state an edit or a project left, for
    /// at least as many rows as the table shows, keeping the highlighted row's place; a
    /// closed panel only marks its rows stale.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary's state now.
    /// * `cx` - Panel context.
    fn revise(&mut self, loaded: Arc<LoadedBinary>, cx: &mut Context<'_, Self>) {
        self.shown = Some(loaded);
        let held = self.rows().map_or(0, |rows| rows.rows().len());
        self.limit = self.limit.max(held);
        self.refresh(Then::Kept, cx);
    }

    /// Asks the engine for the rows the panel's state shows now when the panel is open,
    /// else marks them stale for when it opens.
    ///
    /// # Arguments
    ///
    /// * `then` - Where the highlight goes when the answer comes.
    /// * `cx` - Panel context.
    fn refresh(&mut self, then: Then, cx: &mut Context<'_, Self>) {
        if self.active {
            self.request(then, cx);
        } else {
            self.filter_job.stop();
            self.stale = true;
        }
    }

    /// Asks the engine, in the background, for the rows the panel's state shows: the
    /// filter's text, the target, the sort's order and how many rows, [`SORT_MAX`] when
    /// sorted; the request before is dropped.
    ///
    /// # Arguments
    ///
    /// * `then` - Where the highlight goes when the answer comes.
    /// * `cx` - Panel context spawning the request.
    fn request(&mut self, then: Then, cx: &mut Context<'_, Self>) {
        let Some(loaded) = self.shown.clone() else {
            return;
        };
        self.stale = false;
        let query = SharedString::from(self.filter.read(cx).text(cx));
        let order = self.sort.and_then(|s| {
            let cmp = K::columns(self.columns).get(s.column)?.sort?;
            Some((cmp, s.descending))
        });
        let limit = if order.is_some() {
            SORT_MAX
        } else {
            self.limit
        };
        let (asked, target) = (query.clone(), self.target.clone());
        let revision = loaded.fingerprint;
        let work = move || {
            let mut shown = K::fetch(&loaded, &target, &asked, limit);
            if let Some((cmp, descending)) = order {
                let rows = shown.rows_mut();
                if descending {
                    rows.sort_by(|a, b| cmp(b, a));
                } else {
                    rows.sort_by(cmp);
                }
            }
            Arc::new(shown)
        };
        self.filter_job
            .run(K::FILTERING, cx, work, move |panel, rows, cx| {
                match then {
                    Then::Kept => panel.selected = panel.kept_row(&rows),
                    Then::First => panel.selected = 0,
                    Then::Typed => (panel.selected, panel.lit) = (0, !rows.rows().is_empty()),
                }
                panel.rows = Some(Filtered {
                    query,
                    rows,
                    revision,
                });
                panel.scroll_to_selected(cx);
                panel.relayout(cx);
            });
    }

    /// Returns where the highlighted row is among `rows`, as the panel highlights it now:
    /// the row of its place, the first when no row has it or none is highlighted; a
    /// highlighted row that opens nothing keeps its index while `rows` reach it.
    ///
    /// # Arguments
    ///
    /// * `rows` - The rows about to be shown.
    fn kept_row(&self, rows: &K::Shown) -> usize {
        let rows = rows.rows();
        match self.selected_place() {
            Some(kept) => rows
                .iter()
                .position(|row| K::place(row).as_ref() == Some(&kept))
                .unwrap_or(0),
            None if self.lit && self.selected < rows.len() => self.selected,
            None => 0,
        }
    }

    /// Asks for a page more when the list drew near the end of the rows, the engine has
    /// more and nothing is in flight.
    ///
    /// # Arguments
    ///
    /// * `end` - One past the last row the list drew.
    /// * `cx` - Panel context.
    fn want_rows(&mut self, end: usize, cx: &mut Context<'_, Self>) {
        let Some(shown) = self.rows() else {
            return;
        };
        let len = shown.rows().len();
        let more = len < shown.total() && len == self.limit && self.sort.is_none();
        if more && !self.filter_job.is_running() && end.saturating_add(PAGE_ROWS / 4) >= len {
            self.limit = self.limit.saturating_add(PAGE_ROWS);
            self.request(Then::Kept, cx);
        }
    }

    /// Lists the references to what the highlighted row stands for in the xrefs panel; a
    /// row that stands for no address leaves Xrefs to the workspace.
    ///
    /// # Arguments
    ///
    /// * `place` - The place of the row's referent.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    fn open_referent(
        &mut self,
        place: fn(Referent) -> Place,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        match self.selected_row().and_then(K::referent) {
            Some(referent) => self.open_place(place(referent), TabMode::Permanent, window, cx),
            None => cx.propagate(),
        }
    }

    /// Opens the inline editor for `ask` under the table, over the highlighted row's
    /// referent, once the engine says what it takes; a refusal is the status line's, in the
    /// engine's words, and a row that stands for no address says so there.
    ///
    /// # Arguments
    ///
    /// * `ask` - What is asked.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    fn annotate(&mut self, ask: Ask, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some(r) = self.selected_row().and_then(K::subject) else {
            let why = format!("{}: the highlighted row stands for no address", ask.title());
            self.binary
                .update(cx, |binary, cx| binary.set_status(why, cx));
            return;
        };
        let back = self.rows_focus.clone();
        let binary = self.binary.clone();
        let note = Strip::va(&r).map(|va| format!("{} the row at {va:#x}", ask.title()));
        Strip::ask(
            self,
            |this| &mut this.strip,
            binary,
            (ask, r, note),
            back,
            window,
            cx,
        );
    }

    /// Returns whether the inline editor is open under the table.
    #[cfg(test)]
    pub(crate) fn strip_open(&self) -> bool {
        self.strip.element().is_some()
    }

    /// Returns the focus of the table, under the filter.
    #[must_use]
    pub const fn rows_focus(&self) -> &FocusHandle {
        &self.rows_focus
    }

    /// Sorts by the next sortable column, as [`CycleSort`] asks.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    fn cycle_sort(&mut self, cx: &mut Context<'_, Self>) {
        let next = cycled(self.sort, K::columns(self.columns));
        if next != self.sort {
            self.set_sort(next, cx);
        }
    }

    /// Returns what the highlighted row opens, `None` with no rows or a row that opens
    /// nothing.
    #[must_use]
    pub fn selected_place(&self) -> Option<Place> {
        self.selected_row().and_then(K::place)
    }

    /// Highlights the row shown of `subject`, scrolling it into view only when it is off the
    /// table; with no such row shown, highlights none, so no other row reads as it.
    ///
    /// The highlighted row is looked at first; an unsorted table of functions, in address
    /// order, is searched by halves; any other by a scan.
    ///
    /// # Arguments
    ///
    /// * `subject` - What the row is of.
    /// * `cx` - Panel context.
    pub fn select_subject(&mut self, subject: &Ref, cx: &mut Context<'_, Self>) {
        let of = |row: &K::Row| K::subject(row);
        let found = self.rows().and_then(|rows| {
            let rows = rows.rows();
            if rows.get(self.selected).and_then(of).as_ref() == Some(subject) {
                return Some(self.selected);
            }
            match (self.sort, subject) {
                (None, Ref::Function(entry)) => rows
                    .binary_search_by_key(entry, |row| match of(row) {
                        Some(Ref::Function(at)) => at,
                        Some(_) | None => 0,
                    })
                    .ok(),
                _ => rows
                    .iter()
                    .position(|row| of(row).as_ref() == Some(subject)),
            }
        });
        match found {
            Some(row) if row == self.selected && self.lit => {}
            Some(row) => self.select(row, cx),
            None if self.lit => {
                self.lit = false;
                cx.notify();
            }
            None => {}
        }
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
            .and_then(|rows| rows.rows().get(row))
            .and_then(K::place)
        else {
            return;
        };
        (self.selected, self.lit) = (row, true);
        cx.notify();
        self.open_place(place, mode, window, cx);
    }

    /// Shows `place` as `mode` says, once the update of the panel ends, since showing it
    /// may focus another panel: a permanent tab takes keyboard focus, the preview leaves
    /// it in the panel.
    ///
    /// # Arguments
    ///
    /// * `place` - What to show.
    /// * `mode` - Whether a new tab is the preview tab or a permanent one.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    fn open_place(
        &self,
        place: Place,
        mode: TabMode,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let (Some(loaded), Some(workspace)) = (self.shown.clone(), self.workspace.upgrade()) else {
            return;
        };
        let focus = mode == TabMode::Permanent;
        let how = Opening { mode, focus };
        open_later(
            workspace,
            (self.binary.clone(), loaded),
            place,
            how,
            window,
            cx,
        );
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
        let count = rows.as_ref().map_or(0, |r| r.rows().len());
        let selected = self.lit.then_some(self.selected);
        let colors = cx.theme().colors();
        let (selected_bg, hover_bg) = (colors.element_selected, colors.element_hover);
        let (bar, muted) = (colors.text, colors.text_muted);
        let palette = self.palette;
        let ink = move |ink| match ink {
            Ink::Role(role) => palette.color(role),
            Ink::Muted => muted,
        };
        let panel = cx.entity().downgrade();
        let drawn = panel.clone();
        let shown = K::columns(self.columns);
        let capped = self.capped.clone();
        let headers = self.headers(cx);
        Table::new(shown.len())
            .width_config(ColumnWidthConfig::Resizable(self.widths.clone()))
            .no_ui_font()
            .hide_row_borders()
            .hide_row_hover()
            .interactable(&self.table_state)
            .header(headers)
            .map_row(move |(ix, row_div), _window, _cx| {
                let panel = panel.clone();
                let here = selected == Some(ix);
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
                            window.focus(&this.rows_focus, cx);
                            if K::PREVIEWS {
                                this.open_row(ix, TabMode::Preview, window, cx);
                            } else {
                                this.select(ix, cx);
                            }
                        });
                    })
                    .into_any_element()
            })
            .uniform_list(
                K::PANEL.key,
                count,
                move |range: Range<usize>, _window, cx| {
                    if let Some(panel) = drawn.upgrade() {
                        panel.update(cx, |this, cx| this.want_rows(range.end, cx));
                    }
                    let Some(rows) = &rows else {
                        return Vec::new();
                    };
                    range
                        .filter_map(|ix| Some((ix, rows.rows().get(ix)?)))
                        .map(|(ix, row)| row_cells((ix, row), shown, &capped, ink, ENTRY_SELECTOR))
                        .collect()
                },
            )
            .into_any_element()
    }

    /// Returns the header cells: each shown column's name in the UI font, the sorted one
    /// marked with its direction, a click on a sortable one sorting by it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    fn headers(&self, cx: &mut Context<'_, Self>) -> Vec<AnyElement> {
        let ui_font = ThemeSettings::get_global(cx).ui_font.clone();
        let sort = self.sort;
        K::columns(self.columns)
            .iter()
            .enumerate()
            .map(|(ix, column)| {
                let mark = match sort {
                    Some(Sort {
                        column: c,
                        descending,
                    }) if c == ix => {
                        if descending {
                            " v"
                        } else {
                            " ^"
                        }
                    }
                    Some(_) | None => "",
                };
                let label = Label::new(format!("{}{mark}", column.header))
                    .size(LabelSize::Small)
                    .color(Color::Muted);
                let cell = aligned(column.align, label)
                    .font(ui_font.clone())
                    .debug_selector(|| HEADER_SELECTOR.to_owned());
                if column.sort.is_none() {
                    return cell.into_any_element();
                }
                div()
                    .id(("sort", ix))
                    .w_full()
                    .cursor_pointer()
                    .on_click(cx.listener(move |this, _, _, cx| {
                        this.set_sort(clicked(this.sort, ix), cx);
                    }))
                    .child(cell)
                    .into_any_element()
            })
            .collect()
    }

    /// Returns the count line: the engine's words, then the sort, saying when it sorted
    /// only the first rows the filter keeps.
    ///
    /// # Arguments
    ///
    /// * `shown` - The rows shown.
    fn count_line(&self, shown: &K::Shown) -> SharedString {
        let showing = shown.showing();
        let by = self
            .sort
            .and_then(|s| K::columns(self.columns).get(s.column));
        let (len, total) = (shown.rows().len(), shown.total());
        match by {
            Some(column) if len < total => format!(
                "{showing}; sorted the first {len} of {total} by {}",
                column.header
            )
            .into(),
            Some(column) => format!("{showing}, sorted by {}", column.header).into(),
            None => showing,
        }
    }
}

impl<K: RowKind> RowsPanel<K> {
    /// Returns `root` answering the actions about the highlighted row and the table:
    /// Xrefs, Show Hex, Cycle Sort and Focus Filter, each left to the workspace when the
    /// panel has nothing to answer it with.
    ///
    /// # Arguments
    ///
    /// * `root` - The panel's root element.
    /// * `cx` - Panel context.
    fn answer_row_actions(root: Stateful<Div>, cx: &mut Context<'_, Self>) -> Stateful<Div> {
        answer_asks(root, cx, Self::annotate)
            .on_action(cx.listener(|this, _: &Xrefs, window, cx| {
                this.open_referent(Place::Xrefs, window, cx);
            }))
            .on_action(cx.listener(|this, _: &ShowHex, window, cx| {
                let hex = |referent: Referent| Place::Hex {
                    at: Some(referent.va()),
                };
                this.open_referent(hex, window, cx);
            }))
            .on_action(cx.listener(|this, _: &CycleSort, _, cx| this.cycle_sort(cx)))
            .on_action(cx.listener(|this, _: &FocusFilter, window, cx| {
                if K::FILTERS {
                    window.focus(&this.filter.focus_handle(cx), cx);
                } else {
                    cx.propagate();
                }
            }))
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
                h_flex()
                    .min_w_0()
                    .gap_2()
                    .child(
                        Label::new(self.count_line(rows))
                            .size(LabelSize::Small)
                            .color(Color::Muted)
                            .truncate(),
                    )
                    .children(rows.hidden().map(|(short, tip)| {
                        div().id("rows-hidden").tooltip(Tooltip::text(tip)).child(
                            Label::new(short)
                                .size(LabelSize::Small)
                                .color(Color::Placeholder),
                        )
                    }))
            }));
        let incomplete = rows.and_then(|rows| K::warning(rows)).map(|note| {
            div().px(px(8.0)).child(
                Label::new(note)
                    .size(LabelSize::Small)
                    .color(Color::Warning),
            )
        });
        let filter = K::FILTERS.then(|| {
            h_flex()
                .gap_2()
                .px(px(8.0))
                .py(px(6.0))
                .child(div().flex_1().child(self.filter.clone()))
                .child(Self::filter_hint(cx))
        });
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
        let root = Self::answer_row_actions(div().id(K::PANEL.key), cx)
            .key_context("RowsPanel")
            .track_focus(&self.focus_handle);
        row_keys(root, cx)
            .on_action(cx.listener(|this, _: &menu::SelectFirst, _, cx| this.select(0, cx)))
            .on_action(cx.listener(|this, _: &menu::SelectLast, _, cx| {
                this.select(usize::MAX, cx);
            }))
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| {
                if let Some(place) = this.selected_place() {
                    this.open_place(place, TabMode::Permanent, window, cx);
                }
            }))
            .size_full()
            .flex()
            .flex_col()
            .child(header)
            .children(incomplete)
            .children(filter)
            .child(
                div()
                    .id("rows")
                    .debug_selector(|| BODY_SELECTOR.to_owned())
                    .key_context("BorerRows")
                    .track_focus(&self.rows_focus)
                    .relative()
                    .flex_1()
                    .min_h(px(0.0))
                    .font(font)
                    .text_size(size)
                    .line_height(code_row_height(cx))
                    .child(body)
                    .child(watch_width),
            )
            .children(self.strip.element())
    }
}

/// A view with a highlighted row, which the menu's next and previous keys move.
pub(crate) trait Rows: Sized + 'static {
    /// Returns the index of the highlighted row, `None` while no row is highlighted.
    fn selected(&self) -> Option<usize>;

    /// Moves the highlight to row `row`, held to the rows shown.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row; past the last selects the last.
    /// * `cx` - View context.
    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>);
}

/// Returns `element` with the menu's next and previous keys moving `T`'s highlight; with no
/// row highlighted, next highlights the first and previous the last.
///
/// # Arguments
///
/// * `element` - The view's root element.
/// * `cx` - View context.
pub(crate) fn row_keys<T: Rows>(element: Stateful<Div>, cx: &Context<'_, T>) -> Stateful<Div> {
    element
        .on_action(cx.listener(|this: &mut T, _: &menu::SelectNext, _, cx| {
            let next = this.selected().map_or(0, |row| row.saturating_add(1));
            this.select(next, cx);
        }))
        .on_action(
            cx.listener(|this: &mut T, _: &menu::SelectPrevious, _, cx| {
                let previous = this
                    .selected()
                    .map_or(usize::MAX, |row| row.saturating_sub(1));
                this.select(previous, cx);
            }),
        )
}

impl<K: RowKind> Rows for RowsPanel<K> {
    fn selected(&self) -> Option<usize> {
        self.lit.then_some(self.selected)
    }

    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        let len = self.rows().map_or(0, |r| r.rows().len());
        if len == 0 {
            return;
        }
        (self.selected, self.lit) = (row.min(len - 1), true);
        self.scroll_to_selected(cx);
        cx.notify();
    }
}

/// Builds the rows panel of kind `K` over the window's binary in dock `dock`, lists what the
/// binary holds now, and adds it to `workspace`: every rows kind's [`PanelSpec::add`].
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
/// * `dock` - Dock the panel starts in.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn add<K: RowKind>(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    dock: DockPosition,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let weak = cx.weak_entity();
    let binary = binary.clone();
    let panel = cx.new(|cx| RowsPanel::<K>::new(weak, binary, dock, window, cx));
    if !K::PREVIEWS {
        panel.update(cx, |panel, cx| panel.follow(window, cx));
    }
    workspace.add_panel(panel, window, cx);
}

/// Shows the rows panel of kind `K` and focuses it, or moves focus back to the center
/// pane: every rows kind's [`PanelSpec::focus`].
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn focus<K: RowKind>(
    workspace: &mut Workspace,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    workspace.toggle_panel_focus::<RowsPanel<K>>(window, cx);
}

/// Returns whether the docked rows panel of kind `K` shows nothing older than the binary
/// state `now`: every rows kind's [`PanelSpec::current`].
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `now` - The [`LoadedBinary::fingerprint`] of the binary's state, `None` with none open.
/// * `cx` - Application context reading the panel.
pub fn current<K: RowKind>(workspace: &Workspace, now: Option<u64>, cx: &App) -> bool {
    let panel = workspace.panel::<RowsPanel<K>>(cx);
    panel.is_none_or(|panel| panel.read(cx).is_current(now))
}

impl<K: RowKind> EventEmitter<PanelEvent> for RowsPanel<K> {}

impl<K: RowKind> Focusable for RowsPanel<K> {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl<K: RowKind> Panel for RowsPanel<K> {
    spec_panel!(K::PANEL);

    fn activation_focus_handle(&self, cx: &App) -> FocusHandle {
        if K::FILTERS {
            self.filter.focus_handle(cx)
        } else {
            self.rows_focus.clone()
        }
    }

    fn starts_open(&self, _window: &Window, _cx: &App) -> bool {
        K::PREVIEWS
    }

    fn set_active(&mut self, active: bool, _window: &mut Window, cx: &mut Context<'_, Self>) {
        self.active = active;
        if !active && self.filter_job.is_running() {
            self.filter_job.stop();
            self.stale = true;
        } else if active && self.stale {
            self.request(Then::First, cx);
        }
    }
}

#[cfg(test)]
impl<K: RowKind> crate::binary::Digested for RowsPanel<K> {
    fn digest(&self, _cx: &App) -> u64 {
        use borer_engine::num::from_usize;
        let d = crate::binary::Digest::default().num(from_usize(self.selected));
        let Some(shown) = &self.rows else {
            return d.value();
        };
        let d = d.text(&shown.query).text(&shown.rows.showing());
        let cells = shown.rows.rows().iter().flat_map(|row| {
            K::columns(self.columns)
                .iter()
                .map(move |column| (column.cell)(row))
        });
        cells.fold(d, |d, cell| d.text(&cell)).value()
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::fmt::Debug;
    use std::sync::Arc;

    use borer_engine::analysis::render::symbol_rows;
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, Program, Symbol, SymbolKind};
    use borer_engine::strings::walk::{StringEncoding, WALK_MIN, string_rows};
    use gpui::{Entity, SharedString, TestAppContext, VisualTestContext};
    use ui::IconName;
    use workspace::Workspace;
    use workspace::dock::DockPosition;

    use super::{
        Empty, PAGE_ROWS, Page, RowKind, RowsPanel, Sort, add, clicked, current, cycled, focus,
    };
    use crate::actions::{CycleSort, ToggleXrefs, Xrefs as XrefsAction};
    use crate::app_assets::Glyph;
    use crate::app_view::tests::{binary_in, init, loaded_of, open};
    use crate::binary::Binary;
    use crate::code_view::tests::sample_program;
    use crate::panels::PanelSpec;
    use crate::places::Place;
    use crate::table::{Align, Column, Columns, Fit, Ink, count_text};
    use crate::tables::{Exports, Imports, Strings};
    use crate::worker::{LoadedBinary, Referent};
    use crate::xrefs::Xrefs;

    /// Returns the sample program, a caller, its callee and a string, with an import, two
    /// exports and a forwarder in its symbol table, as a loaded binary.
    pub(crate) fn sample() -> Arc<LoadedBinary> {
        let (mut program, analysis, overlay) = sample_program();
        let symbol = |name: &str, addr, kind| Symbol {
            name: name.to_owned(),
            addr,
            kind,
        };
        program.symbols = vec![
            symbol("KERNEL32.dll!Sleep", 0x1180, SymbolKind::Import),
            symbol("caller", 0x1000, SymbolKind::Export),
            symbol("callee", 0x1030, SymbolKind::Export),
            symbol("forwarded", 0x1100, SymbolKind::Forwarder),
        ];
        loaded_of(program, analysis, overlay)
    }

    /// Shows `loaded` as `workspace`'s binary, opens the panel of kind `K` and returns it
    /// once its rows arrived.
    pub(crate) fn panel_of<K: RowKind>(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        cx: &mut VisualTestContext,
    ) -> Entity<RowsPanel<K>> {
        let binary = binary_in(workspace, cx);
        binary.update(cx, |binary, cx| binary.finish_load(Ok(loaded.clone()), cx));
        let panel = workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<RowsPanel<K>>(window, cx)
        });
        cx.run_until_parked();
        panel.unwrap()
    }

    /// Types `text` into the panel's filter and waits for the answer.
    pub(crate) fn set_filter<K: RowKind>(
        panel: &Entity<RowsPanel<K>>,
        text: &str,
        cx: &mut VisualTestContext,
    ) {
        let editor = panel.read_with(cx, |panel, _| panel.filter.clone());
        editor.update_in(cx, |editor, window, cx| editor.set_text(text, window, cx));
        cx.run_until_parked();
    }

    /// Asserts the panel shows `rows` of `total` under `header`.
    fn assert_shows<K: RowKind<Shown = Page<R>, Row = R>, R: PartialEq + Debug>(
        panel: &Entity<RowsPanel<K>>,
        (rows, total): (&[R], usize),
        header: &str,
        cx: &mut VisualTestContext,
    ) {
        panel.read_with(cx, |panel, _| {
            let shown = panel.rows().unwrap();
            assert_eq!(shown.rows, rows);
            assert_eq!(shown.total, total);
            assert_eq!(&*shown.header, header);
        });
    }

    /// Each table lists the engine's rows for the same filter, unfiltered and filtered,
    /// under the engine's own count; the exports table lists the forwarders after the
    /// exports, and a filter nothing matches is said in the table's own noun.
    #[gpui::test]
    fn each_table_lists_the_engine_rows_and_counts(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (p, a) = (&loaded.program, &loaded.analysis);
        let strings = panel_of::<Strings>(&workspace, &loaded, cx);
        for filter in [None, Some("hello"), Some("zz")] {
            set_filter(&strings, filter.unwrap_or_default(), cx);
            let want = string_rows(p, a, StringEncoding::Both, WALK_MIN, filter, 0, PAGE_ROWS);
            assert_eq!(want.rows.is_empty(), filter == Some("zz"));
            let header = count_text(want.rows.len(), want.total, "strings");
            assert_shows(&strings, (&want.rows, want.total), &header, cx);
        }
        let said = strings.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(
            said,
            Some(Empty::Nothing("No string matches \"zz\"".into()))
        );
        let imports = panel_of::<Imports>(&workspace, &loaded, cx);
        for filter in [None, Some("sleep")] {
            set_filter(&imports, filter.unwrap_or_default(), cx);
            let want = symbol_rows(p, a, Some(SymbolKind::Import), filter, 0, PAGE_ROWS);
            let header = count_text(want.rows.len(), want.total, "imports");
            assert_shows(&imports, (&want.rows, want.total), &header, cx);
        }
        let exports = panel_of::<Exports>(&workspace, &loaded, cx);
        let [exported, forwarded] = [SymbolKind::Export, SymbolKind::Forwarder]
            .map(|kind| symbol_rows(p, a, Some(kind), None, 0, PAGE_ROWS));
        assert_eq!((exported.total, forwarded.total), (2, 1));
        let rows: Vec<_> = exported
            .rows
            .iter()
            .chain(&forwarded.rows)
            .cloned()
            .collect();
        assert_shows(&exports, (&rows, 3), "2 exports, 1 forwarder", cx);
    }

    /// Sorting by a column orders the rows by its fact and never changes which rows show;
    /// a click on the same column turns the order around, a third restores the engine's,
    /// and the palette's cycle visits each sortable column both ways, then the engine's
    /// order.
    #[gpui::test]
    fn a_sort_orders_the_same_rows(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let panel = panel_of::<Exports>(&workspace, &sample(), cx);
        let names = |cx: &mut VisualTestContext| {
            panel.read_with(cx, |panel, _| {
                let rows = &panel.rows().unwrap().rows;
                rows.iter().map(|r| r.name.clone()).collect::<Vec<_>>()
            })
        };
        assert_eq!(names(cx), ["caller", "callee", "forwarded"]);
        let by_name = clicked(None, 1);
        assert_eq!(
            by_name,
            Some(Sort {
                column: 1,
                descending: false
            })
        );
        let mut seen = Vec::new();
        for sort in [
            by_name,
            clicked(by_name, 1),
            clicked(clicked(by_name, 1), 1),
        ] {
            panel.update(cx, |panel, cx| panel.set_sort(sort, cx));
            cx.run_until_parked();
            seen.push(names(cx));
        }
        let want = [
            ["callee", "caller", "forwarded"],
            ["forwarded", "caller", "callee"],
            ["caller", "callee", "forwarded"],
        ];
        assert_eq!(seen, want);
        let columns = Exports::columns(Columns::Brief);
        let mut cycle = vec![cycled(None, columns)];
        while let Some(&Some(last)) = cycle.last() {
            cycle.push(cycled(Some(last), columns));
        }
        assert_eq!(cycle.len(), 2 * columns.len() + 1);
    }

    /// Returns a binary holding `n` strings no section maps, of 5 to 9 letters.
    fn many_strings(n: usize) -> Arc<LoadedBinary> {
        let mut bytes = Vec::new();
        for k in 0..n {
            let letter = b'a' + u8::try_from(k % 26).unwrap();
            bytes.extend(std::iter::repeat_n(letter, 5 + k % 5));
            bytes.push(0);
        }
        let program = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        loaded_of(program, analysis, overlay)
    }

    /// Unsorted, the table holds one page of rows past which the engine has more; sorted,
    /// it holds every row the filter keeps, longest first, so sorting reaches past the
    /// first page.
    #[gpui::test]
    fn a_sort_reaches_past_the_first_page(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let n = PAGE_ROWS + PAGE_ROWS / 2;
        let panel = panel_of::<Strings>(&workspace, &many_strings(n), cx);
        let counts = |cx: &mut VisualTestContext| {
            panel.read_with(cx, |panel, _| {
                let shown = panel.rows().unwrap();
                (shown.rows.len(), shown.total)
            })
        };
        assert_eq!(counts(cx), (PAGE_ROWS, n));
        let by_len = Some(Sort {
            column: 1,
            descending: true,
        });
        panel.update(cx, |panel, cx| panel.set_sort(by_len, cx));
        cx.run_until_parked();
        assert_eq!(counts(cx), (n, n));
        panel.read_with(cx, |panel, _| {
            let lens: Vec<usize> = panel.rows().unwrap().rows.iter().map(|r| r.len).collect();
            assert!(lens.is_sorted_by(|a, b| a >= b));
            assert_eq!(lens.first(), Some(&9));
        });
    }

    /// Arrow keys pressed while a request is in flight stay pressed when its rows land:
    /// the highlight is kept on the place it is on when they land, not when they were
    /// asked for.
    #[gpui::test]
    fn moves_made_while_rows_are_asked_for_are_kept(cx: &mut TestAppContext) {
        use super::Rows as _;
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let panel = panel_of::<Exports>(&app.workspace, &sample(), cx);
        panel.update(cx, |panel, cx| {
            panel.request(super::Then::Kept, cx);
            for _ in 0..2 {
                panel.select(panel.selected().map_or(0, |row| row + 1), cx);
            }
        });
        cx.run_until_parked();
        assert_eq!(panel.read_with(cx, |panel, _| panel.selected), 2);
    }

    /// A kind no module but this test declares.
    #[derive(Debug)]
    enum Probe {}

    /// The probe kind's panel row.
    const PROBE: PanelSpec = PanelSpec {
        key: "Probe",
        title: "Probe",
        icon: Glyph::Zed(IconName::Hash),
        toggle: &ToggleXrefs,
        dock: DockPosition::Left,
        docks: &[DockPosition::Left],
        size_px: 200.0,
        hooks: crate::rail::panel::<RowsPanel<Probe>>(),
        add: add::<Probe>,
        remove: crate::panels::remove::<RowsPanel<Probe>>,
        focus: focus::<Probe>,
        current: current::<Probe>,
    };

    /// The probe kind's one column: an address, sorted by value.
    const PROBE_COLUMNS: &[Column<u64>] = &[Column {
        header: "va",
        cell: |va| format!("{va:#x}").into(),
        align: Align::Start,
        ink: Ink::Muted,
        fit: Fit::Fill,
        sort: Some(|a, b| a.cmp(b)),
    }];

    impl RowKind for Probe {
        type Row = u64;
        type Shown = Page<u64>;
        type Target = ();
        const PANEL: &'static PanelSpec = &PROBE;
        const PLACEHOLDER: &'static str = "";
        const TABLE: &'static str = "probe table";
        const FILTERING: &'static str = "Probing";

        fn columns(_columns: Columns) -> &'static [Column<u64>] {
            PROBE_COLUMNS
        }

        fn fetch(_loaded: &LoadedBinary, (): &(), _filter: &str, _limit: usize) -> Page<u64> {
            Page {
                header: "probe".into(),
                total: 2,
                rows: vec![0x1030, 0x1000],
            }
        }

        fn nothing(shown: &Page<u64>, _query: &SharedString) -> Empty {
            Empty::Nothing(shown.header.clone())
        }

        fn place(_row: &u64) -> Option<Place> {
            None
        }

        fn referent(row: &u64) -> Option<Referent> {
            Some(Referent::Address(*row))
        }

        fn subject(row: &u64) -> Option<borer_engine::view::Ref> {
            (*row != 0x1030).then_some(borer_engine::view::Ref::Address(*row))
        }
    }

    /// Opens a window with a [`Probe`] panel added on the left dock.
    ///
    /// # Returns
    ///
    /// The workspace, the binary it shows, and the window's context.
    fn probed(
        cx: &mut TestAppContext,
    ) -> (Entity<Workspace>, Entity<Binary>, &mut VisualTestContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        let binary = app.binary;
        workspace.update_in(cx, |workspace, window, cx| {
            add::<Probe>(workspace, &binary, DockPosition::Left, window, cx);
        });
        (workspace, binary, cx)
    }

    /// Comment on a row that stands for no address says so on the status line and opens no
    /// editor, in the table or anywhere else.
    #[gpui::test]
    fn comment_on_a_row_with_no_address_says_why(cx: &mut TestAppContext) {
        let (workspace, binary, cx) = probed(cx);
        let probe = panel_of::<Probe>(&workspace, &sample(), cx);
        probe.update_in(cx, |panel, window, cx| window.focus(&panel.rows_focus, cx));
        cx.dispatch_action(crate::annotate::Comment);
        cx.run_until_parked();
        let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
        assert_eq!(status, "Comment: the highlighted row stands for no address");
        assert!(!probe.read_with(cx, |panel, _| panel.strip_open()));
    }

    /// A kind registered only by being added answers Xrefs on its highlighted row and
    /// sorts on Cycle Sort through the panel's own handlers; no workspace chain names it.
    #[gpui::test]
    fn a_kind_added_in_a_test_answers_xrefs_with_no_chain(cx: &mut TestAppContext) {
        let (workspace, _, cx) = probed(cx);
        let loaded = sample();
        let xrefs = panel_of::<Xrefs>(&workspace, &loaded, cx);
        let probe = panel_of::<Probe>(&workspace, &loaded, cx);
        let rows = |cx: &mut VisualTestContext| {
            probe.read_with(cx, |panel, _| panel.rows().unwrap().rows.clone())
        };
        assert_eq!(rows(cx), [0x1030, 0x1000]);
        cx.dispatch_action(CycleSort);
        cx.run_until_parked();
        assert_eq!(rows(cx), [0x1000, 0x1030]);
        cx.dispatch_action(XrefsAction);
        cx.run_until_parked();
        let target = xrefs.read_with(cx, |panel, _| *panel.target());
        assert_eq!(target, Some(Referent::Address(0x1000)));
    }

    /// A kind whose load builds [`MANY`] rows, past one page, and whose engine answers as
    /// many as it is asked for.
    #[derive(Debug)]
    enum Many {}

    /// Rows the many kind's load builds.
    const MANY: usize = PAGE_ROWS + PAGE_ROWS / 2;

    /// The many kind's panel row.
    const MANY_SPEC: PanelSpec = PanelSpec {
        key: "Many",
        title: "Many",
        hooks: crate::rail::panel::<RowsPanel<Many>>(),
        add: add::<Many>,
        remove: crate::panels::remove::<RowsPanel<Many>>,
        focus: focus::<Many>,
        current: current::<Many>,
        ..PROBE
    };

    impl RowKind for Many {
        type Row = u64;
        type Shown = Page<u64>;
        type Target = ();
        const PANEL: &'static PanelSpec = &MANY_SPEC;
        const PLACEHOLDER: &'static str = "";
        const TABLE: &'static str = "many table";
        const FILTERING: &'static str = "Counting";

        fn columns(_columns: Columns) -> &'static [Column<u64>] {
            PROBE_COLUMNS
        }

        fn first(loaded: &LoadedBinary) -> Option<Arc<Page<u64>>> {
            Some(Arc::new(Self::fetch(loaded, &(), "", MANY)))
        }

        fn fetch(_loaded: &LoadedBinary, (): &(), _filter: &str, limit: usize) -> Page<u64> {
            let rows: Vec<u64> = (0..).take(limit.min(MANY)).collect();
            Page {
                header: "many".into(),
                total: MANY,
                rows,
            }
        }

        fn nothing(shown: &Page<u64>, _query: &SharedString) -> Empty {
            Empty::Nothing(shown.header.clone())
        }

        fn place(row: &u64) -> Option<Place> {
            Some(Place::decompile(*row))
        }
    }

    /// After an edit an open panel still holds every row its load built, past one page; a
    /// closed one asks the engine nothing until it opens.
    #[gpui::test]
    fn an_edit_keeps_the_rows_shown_and_spares_a_closed_panel(cx: &mut TestAppContext) {
        use crate::binary::Revision as _;
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let (workspace, binary) = (app.workspace.clone(), app.binary);
        workspace.update_in(cx, |workspace, window, cx| {
            add::<Many>(workspace, &binary, DockPosition::Left, window, cx);
        });
        let panel = panel_of::<Many>(&workspace, &sample(), cx);
        let held = |cx: &mut VisualTestContext| {
            panel.read_with(cx, |panel, _| panel.rows().map(|rows| rows.rows.len()))
        };
        assert_eq!(held(cx), Some(MANY));
        let edit = |name: &str, cx: &mut VisualTestContext| {
            let rename = borer_engine::analysis::edit::Edit::Name {
                at: 0x1000,
                name: name.to_owned(),
            };
            binary.update(cx, |binary, cx| binary.plan_and_commit(&[rename], cx));
            cx.run_until_parked();
            binary.read_with(cx, |binary, _| binary.loaded().map(|l| l.fingerprint))
        };
        let now = edit("first", cx);
        assert_eq!(panel.read_with(cx, |panel, _| panel.revision()), now);
        assert_eq!(held(cx), Some(MANY));
        let set_active = |active, cx: &mut VisualTestContext| {
            use workspace::dock::Panel as _;
            panel.update_in(cx, |panel, window, cx| panel.set_active(active, window, cx));
            cx.run_until_parked();
        };
        set_active(false, cx);
        let later = edit("second", cx);
        assert_ne!(later, now);
        assert_eq!(panel.read_with(cx, |panel, _| panel.revision()), now);
        set_active(true, cx);
        assert_eq!(panel.read_with(cx, |panel, _| panel.revision()), later);
        assert_eq!(held(cx), Some(MANY));
    }
}
