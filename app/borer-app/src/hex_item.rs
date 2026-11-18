//! The hex tab: the bytes of the mapped sections in Zed's center pane, sixteen to a row.
//!
//! Each row is spelled as the engine's hexdump spells it ([`hexdump_sparse`], `??` where
//! nothing backs a byte), read a page at a time in the background around the rows on
//! screen.
//!
//! The rows run over each section's addresses, rounded out to whole rows, sections that
//! touch or overlap joined into one run; a run shows at most [`RUN_MAX_BYTES`] and the
//! tab at most [`MAX_ROWS`] rows. The list shows a window of [`WINDOW_ROWS`] of them, so
//! its scroll offset stays within what a float holds to the pixel; Go to and the cursor
//! keys move the window.

use std::collections::BTreeMap;
use std::ops::{Range, RangeInclusive};
use std::sync::Arc;

use borer_engine::hexdump::{HEXDUMP_MAX, HexFill, HexRows, hexdump_sparse};
use borer_engine::num::from_usize;
use borer_engine::program::Section;
use gpui::{
    AnyElement, App, Context, Entity, EventEmitter, FocusHandle, Focusable, Font, Hsla,
    InteractiveElement as _, IntoElement, ParentElement as _, Pixels, Render, ScrollStrategy,
    SharedString, Styled as _, StyledText, Subscription, Task, TextRun, UniformListScrollHandle,
    WeakEntity, Window, div, px, uniform_list,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};
use theme_settings::ThemeSettings;
use ui::{Icon, IconName};
use workspace::{Item, Workspace};

use crate::actions::{LinkHex, ShowHex, Xrefs};
use crate::binary::{Binary, BinaryEvent, Digest, Revision};
use crate::card::{Card, Tone};
use crate::code_view::theme_color;
use crate::commands;
use crate::decompile_item::{DecompileItem, code_row_height};
use crate::places::{PERMANENT, Place, open_later, shown_binary};
use crate::worker::{Job, LoadedBinary, Referent, hex_blocking, spawn_engine};

/// Left padding in logical pixels before the text of each row.
const CODE_PAD_PX: f32 = 8.0;

/// Bytes one row shows.
pub const ROW_BYTES: u64 = 16;

/// Rows one page holds: one engine hexdump of [`HEXDUMP_MAX`] bytes.
pub const PAGE_ROWS: usize = HEXDUMP_MAX / 16;

/// Most pages the tab holds; past it the pages farthest from the screen are dropped, so a
/// tab holds at most 64 pages of 4 KiB of addresses.
pub const HELD_PAGES: usize = 64;

/// Most addresses one run of rows covers; a section claiming more is cut there.
pub const RUN_MAX_BYTES: u64 = 1 << 32;

/// Most rows a tab lays out, 4 GiB of addresses; the runs past them are left out.
pub const MAX_ROWS: usize = 1 << 28;

/// Most rows the list shows at once, about 9.4 million pixels at 18 pixels a row, within
/// the 16.7 million a float scroll offset holds to the pixel.
pub const WINDOW_ROWS: usize = 1 << 19;

/// One row: its address, its bytes as the engine backs them, and its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HexLine {
    /// Address of the row's first byte.
    pub va: u64,
    /// The row's bytes, `None` where nothing backs one.
    pub cells: Vec<Option<u8>>,
    /// The row as [`hexdump_sparse`] spells it, without its newline.
    pub text: SharedString,
}

/// Returns the engine's runs as rows of [`ROW_BYTES`] bytes from the first address asked
/// for, each spelled by [`hexdump_sparse`].
///
/// # Arguments
///
/// * `rows` - The engine's runs, in address order.
#[must_use]
pub fn lines_of(rows: &HexRows) -> Vec<HexLine> {
    let cells: Vec<Option<u8>> = rows
        .spans
        .iter()
        .flat_map(|span| match &span.fill {
            HexFill::Bytes(bytes) => bytes.iter().copied().map(Some).collect(),
            HexFill::Unbacked | HexFill::Unmapped => vec![None; span.len],
        })
        .collect();
    let mut va = rows.va;
    cells
        .chunks(16)
        .map(|chunk| {
            let spelled = hexdump_sparse(chunk, va);
            let line = HexLine {
                va,
                cells: chunk.to_vec(),
                text: spelled.trim_end_matches('\n').to_owned().into(),
            };
            va = va.wrapping_add(ROW_BYTES);
            line
        })
        .collect()
}

/// What a run of a row's text paints with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ink {
    /// The address.
    Address,
    /// A byte other than zero, the gaps and the text column.
    Byte,
    /// A zero byte, and a byte nothing backs.
    Zero,
}

/// Returns the runs of `line`'s text and what each paints with.
///
/// They are read off the layout [`hexdump_sparse`] spells: the address, two spaces, each
/// byte as two digits and a space (one more before the ninth), padding, then the text
/// column; one [`Ink::Byte`] run when the text is not laid out so.
///
/// # Arguments
///
/// * `line` - The row.
#[must_use]
pub fn inks(line: &HexLine) -> Vec<(usize, Ink)> {
    let len = line.text.len();
    let address = line.text.find("  ").unwrap_or(0);
    let mut runs = vec![(address + 2, Ink::Address)];
    for (k, cell) in line.cells.iter().enumerate() {
        if k == 8 {
            runs.push((1, Ink::Byte));
        }
        let ink = match cell {
            Some(0) | None => Ink::Zero,
            Some(_) => Ink::Byte,
        };
        runs.extend([(2, ink), (1, Ink::Byte)]);
    }
    let used: usize = runs.iter().map(|(n, _)| n).sum();
    match len.checked_sub(used) {
        Some(rest) if address > 0 && len == address + 54 + line.cells.len() => {
            runs.push((rest, Ink::Byte));
            runs
        }
        Some(_) | None => vec![(len, Ink::Byte)],
    }
}

/// Why no row shows an address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Miss {
    /// No section maps it.
    Unmapped,
    /// A section maps it, past the [`RUN_MAX_BYTES`] its run shows or the [`MAX_ROWS`] the
    /// tab lays out.
    Cut,
}

/// One run of rows: whole rows covering one or more sections that touch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Run {
    /// Address of the first row, a multiple of [`ROW_BYTES`].
    start: u64,
    /// One past the last address shown, a multiple of [`ROW_BYTES`] or the top of the space.
    end: u64,
    /// One past the last address the run's sections claim.
    claimed: u64,
    /// Index of the run's first row among every row.
    first: usize,
}

impl Run {
    /// Returns how many rows the run shows.
    fn rows(&self) -> usize {
        usize::try_from(self.end.saturating_sub(self.start) / ROW_BYTES).unwrap_or(usize::MAX)
    }
}

/// The rows of a hex tab: each mapped section's addresses, rounded out to whole rows.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HexLayout {
    /// The runs, in address order, none touching another; a run past [`MAX_ROWS`] shows
    /// no row.
    runs: Vec<Run>,
    /// Rows in all.
    rows: usize,
}

impl HexLayout {
    /// Returns the rows over `sections`: each from its address for the larger of its
    /// memory and file sizes, rounded out to whole rows, runs that touch or overlap joined,
    /// each run cut at [`RUN_MAX_BYTES`] and the whole at [`MAX_ROWS`].
    ///
    /// # Arguments
    ///
    /// * `sections` - The program's sections.
    #[must_use]
    pub fn of(sections: &[Section]) -> Self {
        let mut spans: Vec<(u64, u64)> = sections
            .iter()
            .map(|s| {
                let start = s.va.0 & !(ROW_BYTES - 1);
                let end = s.va.0.saturating_add(s.vsize.max(s.file_size));
                (start, end.saturating_add(ROW_BYTES - 1) & !(ROW_BYTES - 1))
            })
            .filter(|(start, end)| end > start)
            .collect();
        spans.sort_unstable();
        let mut layout = Self::default();
        for (start, end) in spans {
            match layout.runs.last_mut() {
                Some(last) if start <= last.claimed => last.claimed = last.claimed.max(end),
                Some(_) | None => layout.runs.push(Run {
                    start,
                    end,
                    claimed: end,
                    first: 0,
                }),
            }
        }
        let mut first = 0usize;
        for run in &mut layout.runs {
            let span = run.claimed.saturating_sub(run.start).min(RUN_MAX_BYTES);
            let rows = usize::try_from(span / ROW_BYTES).unwrap_or(usize::MAX);
            let rows = rows.min(MAX_ROWS - first);
            run.first = first;
            run.end = run
                .start
                .saturating_add(from_usize(rows).saturating_mul(ROW_BYTES));
            first += rows;
        }
        layout.rows = first;
        layout
    }

    /// Returns how many rows there are.
    #[must_use]
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// Returns the run showing row `row`.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    fn run_of(&self, row: usize) -> Option<&Run> {
        let k = self
            .runs
            .partition_point(|run| run.first <= row && run.rows() > 0)
            .checked_sub(1)?;
        self.runs.get(k).filter(|run| row - run.first < run.rows())
    }

    /// Returns the address of row `row`'s first byte.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    #[must_use]
    pub fn va_of(&self, row: usize) -> Option<u64> {
        let run = self.run_of(row)?;
        let rows = from_usize(row - run.first);
        Some(run.start.saturating_add(rows.saturating_mul(ROW_BYTES)))
    }

    /// Returns the row showing address `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - An address.
    ///
    /// # Errors
    ///
    /// Returns why no row shows it: no section maps it, or the caps cut it off.
    pub fn row_of(&self, va: u64) -> Result<usize, Miss> {
        let k = self
            .runs
            .partition_point(|run| run.start <= va)
            .checked_sub(1);
        let run = k
            .and_then(|k| self.runs.get(k))
            .filter(|run| va < run.claimed);
        let run = run.ok_or(Miss::Unmapped)?;
        if va >= run.end {
            return Err(Miss::Cut);
        }
        let row = usize::try_from((va - run.start) / ROW_BYTES).map_err(|_| Miss::Cut)?;
        run.first.checked_add(row).ok_or(Miss::Cut)
    }

    /// Returns page `page`'s rows, cut where runs end: each piece's first address and rows.
    ///
    /// # Arguments
    ///
    /// * `page` - Zero-based page index.
    fn pieces(&self, page: usize) -> Vec<(u64, usize)> {
        let first = page.saturating_mul(PAGE_ROWS);
        let last = first.saturating_add(PAGE_ROWS).min(self.rows);
        let mut pieces = Vec::new();
        let mut row = first;
        while row < last {
            let (Some(run), Some(va)) = (self.run_of(row), self.va_of(row)) else {
                break;
            };
            let n = (run.first.saturating_add(run.rows()))
                .min(last)
                .saturating_sub(row);
            if n == 0 {
                break;
            }
            pieces.push((va, n));
            row += n;
        }
        pieces
    }
}

/// Returns the rows of page `page` of `layout`, read from the engine a piece at a time.
///
/// Must be called inside [`spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The binary.
/// * `layout` - The tab's rows.
/// * `page` - Zero-based page index.
fn page_lines(loaded: &LoadedBinary, layout: &HexLayout, page: usize) -> Vec<HexLine> {
    layout
        .pieces(page)
        .into_iter()
        .flat_map(|(va, rows)| lines_of(&hex_blocking(loaded, va, rows * 16)))
        .collect()
}

/// What a hex tab paints with, read from the theme and the settings.
#[derive(Debug, Clone)]
struct HexStyle {
    /// The buffer font.
    font: Font,
    /// The buffer font size.
    size: Pixels,
    /// Height of each row.
    row_height: Pixels,
    /// Color of each [`Ink`]: address, byte, zero.
    inks: [Hsla; 3],
    /// Background of the cursor's row.
    cursor_bg: Hsla,
}

impl HexStyle {
    /// Returns the style the active theme and the settings give.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the theme and the settings.
    fn read(cx: &App) -> Self {
        let settings = ThemeSettings::get_global(cx);
        let theme = cx.theme();
        Self {
            font: settings.buffer_font.clone(),
            size: settings.buffer_font_size(cx),
            row_height: code_row_height(cx),
            inks: [
                theme_color(theme, &["borer.address", "comment"]),
                theme_color(theme, &["borer.byte"]),
                theme_color(theme, &["borer.byte.zero", "comment"]),
            ],
            cursor_bg: theme.colors().element_selected,
        }
    }

    /// Returns a run of `len` bytes of text in ink `k` of [`Self::inks`].
    ///
    /// # Arguments
    ///
    /// * `len` - Bytes of text.
    /// * `k` - Index of the ink: address, byte, zero.
    fn run(&self, len: usize, k: usize) -> TextRun {
        TextRun {
            len,
            font: self.font.clone(),
            color: self.inks.get(k).copied().unwrap_or(self.inks[1]),
            background_color: None,
            underline: None,
            strikethrough: None,
        }
    }

    /// Returns the text runs painting `line`.
    ///
    /// # Arguments
    ///
    /// * `line` - The row.
    fn paint(&self, line: &HexLine) -> Vec<TextRun> {
        inks(line)
            .into_iter()
            .map(|(len, ink)| {
                let k = match ink {
                    Ink::Address => 0,
                    Ink::Byte => 1,
                    Ink::Zero => 2,
                };
                self.run(len, k)
            })
            .collect()
    }
}

/// The bytes of one binary's mapped sections as an item of Zed's center pane.
pub struct HexItem {
    /// Workspace the tab is in, where it opens the places of its cursor.
    workspace: WeakEntity<Workspace>,
    /// The window's binary, whose status line the tab writes and whose load a drop starts.
    binary: Entity<Binary>,
    /// The binary whose bytes the tab shows.
    loaded: Arc<LoadedBinary>,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// The rows, once laid out.
    layout: Option<Arc<HexLayout>>,
    /// First row of the window the list shows.
    base: usize,
    /// Pages read, by index.
    pages: BTreeMap<usize, Arc<[HexLine]>>,
    /// Pages being read, by index; dropping one drops its request.
    pending: BTreeMap<usize, Task<()>>,
    /// Pages the rows on screen fall in, as [`Self::want_pages`] last asked for them; the
    /// pages held past [`HELD_PAGES`] are dropped farthest from them first.
    wanted: RangeInclusive<usize>,
    /// The address the cursor is on.
    cursor: Option<u64>,
    /// Why no row shows the cursor's address, when none does.
    miss: Option<Miss>,
    /// Whether the cursor follows the function of the active code tab.
    linked: bool,
    /// Scroll handle of the row list.
    scroll: UniformListScrollHandle,
    /// Colors, font and row height.
    style: HexStyle,
    /// The layout's background request.
    layout_job: Job,
    /// Rebuilds [`Self::style`] on a settings or theme change, follows the active tab, and
    /// moves to the state an edit or a project leaves.
    _subscriptions: Vec<Subscription>,
}

impl std::fmt::Debug for HexItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HexItem")
            .field("cursor", &self.cursor)
            .field("base", &self.base)
            .field("linked", &self.linked)
            .finish_non_exhaustive()
    }
}

impl HexItem {
    /// Returns a hex tab over `loaded`, laying its rows out in the background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab is in, whose active code tab a linked cursor
    ///   follows.
    /// * `binary` - The window's binary.
    /// * `loaded` - The binary whose bytes to show.
    /// * `cx` - Item context.
    #[must_use]
    pub fn new(
        workspace: &Entity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let revised = cx.subscribe(&binary, |item, _, event, _| match event {
            BinaryEvent::Revised(loaded) => item.loaded = loaded.clone(),
            BinaryEvent::Opened(_) | BinaryEvent::Closed | BinaryEvent::Rechecked { .. } => {}
        });
        let mut item = Self {
            workspace: workspace.downgrade(),
            binary,
            loaded,
            focus_handle: cx.focus_handle(),
            layout: None,
            base: 0,
            pages: BTreeMap::new(),
            pending: BTreeMap::new(),
            wanted: 0..=0,
            cursor: None,
            miss: None,
            linked: false,
            scroll: UniformListScrollHandle::new(),
            style: HexStyle::read(cx),
            layout_job: Job::default(),
            _subscriptions: vec![
                cx.observe_global::<SettingsStore>(Self::restyle),
                cx.observe_global::<GlobalTheme>(Self::restyle),
                cx.subscribe(workspace, |item, workspace, event, cx| {
                    if matches!(event, workspace::Event::ActiveItemChanged) {
                        item.follow(&workspace, cx);
                    }
                }),
                revised,
            ],
        };
        let program = item.loaded.program.clone();
        let work = move || Arc::new(HexLayout::of(&program.sections));
        item.layout_job
            .run("Laying out the hex tab", cx, work, |item, layout, cx| {
                item.layout = Some(layout);
                if let Some(va) = item.cursor {
                    item.go_to(va, cx);
                }
                cx.notify();
            });
        item
    }

    /// Rereads the tab's style from the theme and the settings and repaints it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn restyle(&mut self, cx: &mut Context<'_, Self>) {
        self.style = HexStyle::read(cx);
        cx.notify();
    }

    /// Puts a linked cursor on the function of `workspace`'s active code tab.
    ///
    /// # Arguments
    ///
    /// * `workspace` - The workspace.
    /// * `cx` - Item context.
    fn follow(&mut self, workspace: &Entity<Workspace>, cx: &mut Context<'_, Self>) {
        if !self.linked {
            return;
        }
        let item = workspace.read(cx).active_item_as::<DecompileItem>(cx);
        if let Some(entry) = item.and_then(|item| item.read(cx).entry()) {
            self.go_to(entry, cx);
        }
    }

    /// Returns the rows, once laid out.
    #[must_use]
    pub fn layout(&self) -> Option<&HexLayout> {
        self.layout.as_deref()
    }

    /// Returns row `row`, once its page was read.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index among every row.
    #[must_use]
    pub fn line(&self, row: usize) -> Option<&HexLine> {
        self.pages.get(&(row / PAGE_ROWS))?.get(row % PAGE_ROWS)
    }

    /// Returns how many pages the tab holds.
    #[must_use]
    pub fn held_pages(&self) -> usize {
        self.pages.len()
    }

    /// Returns how many pages are being read.
    #[must_use]
    pub fn pending_pages(&self) -> usize {
        self.pending.len()
    }

    /// Returns the address the cursor is on.
    #[must_use]
    pub const fn cursor(&self) -> Option<u64> {
        self.cursor
    }

    /// Returns why no row shows the cursor's address, when none does.
    #[must_use]
    pub const fn miss(&self) -> Option<Miss> {
        self.miss
    }

    /// Returns whether the cursor follows the active code tab's function.
    #[must_use]
    pub const fn linked(&self) -> bool {
        self.linked
    }

    /// Returns the binary the tab shows.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Makes the cursor follow the active code tab's function, or stop following it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    pub fn toggle_link(&mut self, cx: &mut Context<'_, Self>) {
        self.linked = !self.linked;
        cx.notify();
    }

    /// Returns the zero-based index, among every row, of the row at the top of the tab: the
    /// row a scroll not yet laid out asks for, else the first row the offset shows.
    #[must_use]
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "a floored, non-negative, finite row count of a laid-out list"
    )]
    pub fn top_row(&self) -> usize {
        let state = self.scroll.0.borrow();
        let top = if let Some(deferred) = &state.deferred_scroll_to_item {
            deferred.item_index
        } else {
            let rows = (-state.base_handle.offset().y / self.style.row_height).floor();
            if rows.is_finite() && rows > 0.0 {
                rows as usize
            } else {
                0
            }
        };
        self.base.saturating_add(top)
    }

    /// Returns how many rows the list shows: the window from [`Self::base`] on.
    fn window_rows(&self) -> usize {
        let rows = self.layout.as_ref().map_or(0, |layout| layout.rows());
        rows.saturating_sub(self.base).min(WINDOW_ROWS)
    }

    /// Scrolls row `row` (among every row) into view as `strategy` says, moving the window
    /// when it lies outside it.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    /// * `strategy` - Where the row goes on screen.
    fn reveal(&mut self, row: usize, strategy: ScrollStrategy) {
        if row < self.base || row >= self.base.saturating_add(WINDOW_ROWS) {
            self.base = row.saturating_sub(WINDOW_ROWS / 2);
        }
        self.scroll.scroll_to_item_strict(row - self.base, strategy);
    }

    /// Puts the cursor on `va` and scrolls its row to the top of the tab once the rows
    /// are laid out; when no row shows it, [`Self::miss`] and the status line say why.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    /// * `cx` - Item context.
    pub fn go_to(&mut self, va: u64, cx: &mut Context<'_, Self>) {
        self.cursor = Some(va);
        self.miss = None;
        cx.notify();
        let Some(layout) = self.layout.clone() else {
            return;
        };
        match layout.row_of(va) {
            Ok(row) => self.reveal(row, ScrollStrategy::Top),
            Err(miss) => {
                self.miss = Some(miss);
                let said = miss_line(va, miss);
                self.binary
                    .update(cx, |binary, cx| binary.set_status(said, cx));
            }
        }
    }

    /// Scrolls row `row` (among every row) to the top of the tab, as a measurement scrolls
    /// it.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row index.
    /// * `cx` - Item context.
    pub fn scroll_to_row(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        self.reveal(row, ScrollStrategy::Top);
        cx.notify();
    }

    /// Returns the height in logical pixels the row list was last painted at, zero before
    /// its first paint.
    #[must_use]
    pub fn painted_height(&self) -> Pixels {
        self.scroll.0.borrow().base_handle.bounds().size.height
    }

    /// Moves the cursor `rows` rows down (up when negative), to the first row when it has
    /// none, keeping its byte within the row, and scrolls it into view.
    ///
    /// # Arguments
    ///
    /// * `rows` - Rows to move.
    /// * `cx` - Item context.
    fn move_cursor(&mut self, rows: isize, cx: &mut Context<'_, Self>) {
        let Some(layout) = self.layout.clone() else {
            return;
        };
        let Some(last) = layout.rows().checked_sub(1) else {
            return;
        };
        let at = self.cursor.and_then(|va| layout.row_of(va).ok());
        let row = at.map_or(0, |row| row.saturating_add_signed(rows).min(last));
        let column = self.cursor.map_or(0, |va| va % ROW_BYTES);
        if let Some(va) = layout.va_of(row) {
            self.cursor = Some(va + column);
            self.miss = None;
            self.reveal(row, ScrollStrategy::Nearest);
            cx.notify();
        }
    }

    /// Returns how many rows a page key moves: the rows the tab shows, at least one.
    #[expect(
        clippy::cast_possible_truncation,
        reason = "a floored row count of a painted list, clamped to at least one"
    )]
    fn page_rows(&self) -> isize {
        (self.painted_height() / self.style.row_height)
            .floor()
            .max(1.0) as isize
    }

    /// Returns the rows on screen, among every row: from [`Self::top_row`] on, as many as
    /// the list was last painted tall (one before its first paint), and as many above it
    /// while a scroll not yet laid out may put its row at the bottom.
    fn screen_rows(&self) -> Range<usize> {
        let shown = self.page_rows().cast_unsigned().saturating_add(1);
        let top = self.top_row();
        let deferred = self.scroll.0.borrow().deferred_scroll_to_item.is_some();
        let start = if deferred {
            top.saturating_sub(shown)
        } else {
            top
        };
        let end = top
            .saturating_add(shown)
            .min(self.base.saturating_add(self.window_rows()));
        start..end.max(start)
    }

    /// Reads, in the background, the pages of `rows` (among every row) not held or being
    /// read, drops the reads of pages that left them, and drops the pages farthest from
    /// them past [`HELD_PAGES`].
    ///
    /// # Arguments
    ///
    /// * `rows` - Rows on screen.
    /// * `cx` - Item context.
    pub fn want_pages(&mut self, rows: Range<usize>, cx: &mut Context<'_, Self>) {
        let Some(layout) = self.layout.clone() else {
            return;
        };
        let first = rows.start / PAGE_ROWS;
        let last = (rows.end.saturating_sub(1) / PAGE_ROWS).max(first);
        self.wanted = first..=last;
        self.pending.retain(|page, _| (first..=last).contains(page));
        for page in first..=last {
            if self.pages.contains_key(&page) || self.pending.contains_key(&page) {
                continue;
            }
            let (loaded, layout) = (self.loaded.clone(), layout.clone());
            let read = spawn_engine("Reading hex", cx, move || {
                page_lines(&loaded, &layout, page)
            });
            let task = cx.spawn(async move |this, cx| {
                let (Some(lines), Some(this)) = (read.await, this.upgrade()) else {
                    return;
                };
                this.update(cx, |item, cx| {
                    item.pending.remove(&page);
                    item.pages.insert(page, lines.into());
                    item.evict();
                    cx.notify();
                });
            });
            self.pending.insert(page, task);
        }
        self.evict();
    }

    /// Drops the pages farthest from [`Self::wanted`] until at most [`HELD_PAGES`] are held.
    fn evict(&mut self) {
        let (first, last) = (*self.wanted.start(), *self.wanted.end());
        while self.pages.len() > HELD_PAGES {
            let far = self
                .pages
                .keys()
                .copied()
                .max_by_key(|&page| page.abs_diff(first).min(page.abs_diff(last)));
            let Some(far) = far else {
                break;
            };
            self.pages.remove(&far);
        }
    }

    /// Builds the rows in `range` of the list's window from the pages held; [`Self::render`]
    /// asks for the pages of the rows on screen, since the list also builds a row to
    /// measure it.
    ///
    /// # Arguments
    ///
    /// * `range` - Rows of the window the list draws.
    /// * `_window` - Window painting the rows.
    /// * `_cx` - Item context.
    fn render_rows(
        &mut self,
        range: Range<usize>,
        _window: &mut Window,
        _cx: &mut Context<'_, Self>,
    ) -> Vec<AnyElement> {
        let rows = self.base.saturating_add(range.start)..self.base.saturating_add(range.end);
        let cursor_row = self
            .cursor
            .and_then(|va| self.layout.as_ref()?.row_of(va).ok());
        rows.map(|row| {
            let text = match self.line(row) {
                Some(line) => StyledText::new(line.text.clone()).with_runs(self.style.paint(line)),
                None => {
                    let va = self.layout.as_ref().and_then(|l| l.va_of(row));
                    let text = va.map_or_else(String::new, |va| format!("{va:#012x}"));
                    let runs = vec![self.style.run(text.len(), 0)];
                    StyledText::new(text).with_runs(runs)
                }
            };
            let line = div()
                .h(self.style.row_height)
                .px(px(CODE_PAD_PX))
                .flex()
                .items_center()
                .whitespace_nowrap()
                .child(text);
            if cursor_row == Some(row) {
                line.bg(self.style.cursor_bg).into_any_element()
            } else {
                line.into_any_element()
            }
        })
        .collect()
    }

    /// Returns the line over the rows: which rows the window shows of how many, and the
    /// cursor's address.
    fn window_line(&self) -> SharedString {
        let rows = self.layout.as_ref().map_or(0, |layout| layout.rows());
        let shown = self.window_rows();
        let cursor = match (self.cursor, self.miss) {
            (Some(va), Some(miss)) => format!("; {}", miss_line(va, miss)),
            (Some(va), None) => format!("; cursor {va:#x}"),
            (None, _) => String::new(),
        };
        let window = if shown < rows {
            format!(
                "rows {}..{} of {rows} (Go to moves the window)",
                self.base,
                self.base + shown
            )
        } else {
            format!("{rows} rows")
        };
        format!("{window}{cursor}").into()
    }

    /// Returns what the tab says while it shows no rows: the layout running, or that no
    /// section maps an address; `None` once it has rows.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        let says = match self.layout.as_ref().map(|layout| layout.rows()) {
            Some(0) => "No section maps any address.",
            Some(_) => return None,
            None => "Laying out the sections",
        };
        Some(Card {
            says: says.into(),
            tone: Tone::Quiet,
            offers: &[],
        })
    }

    /// Opens `place` at the cursor's address: its xrefs or its function's code.
    ///
    /// # Arguments
    ///
    /// * `place` - The place of the cursor's referent.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn open_cursor(
        &self,
        place: fn(Referent) -> Place,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let (Some(va), Some(workspace)) = (self.cursor, self.workspace.upgrade()) else {
            cx.propagate();
            return;
        };
        let shown = (self.binary.clone(), self.loaded.clone());
        let place = place(Referent::Address(va));
        open_later(workspace, shown, place, PERMANENT, window, cx);
    }
}

/// Returns why no row shows `va`, as the status line says it.
///
/// # Arguments
///
/// * `va` - The address.
/// * `miss` - Why no row shows it.
#[must_use]
pub fn miss_line(va: u64, miss: Miss) -> String {
    match miss {
        Miss::Unmapped => format!("{va:#x} is in no section"),
        Miss::Cut => format!(
            "{va:#x} is past the hex tab's caps: {RUN_MAX_BYTES} bytes a run, {MAX_ROWS} rows in all"
        ),
    }
}

/// Registers the hex tab's commands on `workspace`, over the window's `binary`: show the
/// hex tab where a focused view does not take [`ShowHex`] itself, and link its cursor.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let hex = binary.clone();
    commands::register(
        workspace,
        binary,
        move |workspace, _: &ShowHex, window, cx| {
            if let Some(loaded) = shown_binary(workspace, &hex, cx) {
                let place = Place::Hex { at: None };
                crate::places::open(workspace, &hex, &loaded, place, PERMANENT, window, cx);
            }
        },
    );
    commands::register(workspace, binary, |workspace, _: &LinkHex, _, cx| {
        link_hex(workspace, cx);
    });
}

/// Links the active hex tab's cursor to the active code tab's function, or unlinks it;
/// with no hex tab active, the first hex tab of the workspace.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `cx` - Workspace context.
pub fn link_hex(workspace: &mut Workspace, cx: &mut Context<'_, Workspace>) {
    let hex = workspace
        .active_item_as::<HexItem>(cx)
        .or_else(|| workspace.items_of_type::<HexItem>(cx).next());
    if let Some(hex) = hex {
        hex.update(cx, HexItem::toggle_link);
    }
}

impl EventEmitter<()> for HexItem {}

impl Focusable for HexItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Revision for HexItem {
    fn revision(&self) -> Option<u64> {
        Some(self.loaded.fingerprint)
    }

    fn digest(&self, _cx: &App) -> u64 {
        let rows = self.layout.as_ref().map_or(0, |layout| layout.rows);
        let d = Digest::default().num(from_usize(rows));
        let d = d.text(&format!("{:?} {:?}", self.cursor, self.miss));
        let lines = self.pages.values().flat_map(|page| page.iter());
        lines
            .fold(d, |d, line| d.num(line.va).text(&line.text))
            .value()
    }
}

impl Item for HexItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        let link = if self.linked { ", linked" } else { "" };
        format!("hex{link}").into()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Binary))
    }

    crate::app_view::snapshot_tab!();
}

impl Render for HexItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let (background, muted) = {
            let colors = cx.theme().colors();
            (colors.editor_background, colors.text_muted)
        };
        let body = match self.card() {
            Some(card) => card.render(cx),
            None => {
                self.want_pages(self.screen_rows(), cx);
                uniform_list(
                    "hex-view",
                    self.window_rows(),
                    cx.processor(Self::render_rows),
                )
                .track_scroll(&self.scroll)
                .flex_1()
                .into_any_element()
            }
        };
        div()
            .track_focus(&self.focus_handle)
            .key_context("HexView")
            .on_action(cx.listener(|this, _: &menu::SelectNext, _, cx| this.move_cursor(1, cx)))
            .on_action(cx.listener(|this, _: &menu::SelectPrevious, _, cx| {
                this.move_cursor(-1, cx);
            }))
            .on_action(cx.listener(|this, _: &editor::actions::PageDown, _, cx| {
                this.move_cursor(this.page_rows(), cx);
            }))
            .on_action(cx.listener(|this, _: &editor::actions::PageUp, _, cx| {
                this.move_cursor(-this.page_rows(), cx);
            }))
            .on_action(cx.listener(|this, _: &menu::SelectFirst, _, cx| {
                this.move_cursor(isize::MIN, cx);
            }))
            .on_action(cx.listener(|this, _: &menu::SelectLast, _, cx| {
                this.move_cursor(isize::MAX, cx);
            }))
            .on_action(cx.listener(|this, _: &Xrefs, window, cx| {
                this.open_cursor(Place::Xrefs, window, cx);
            }))
            .on_action(cx.listener(|this, _: &LinkHex, _, cx| this.toggle_link(cx)))
            .size_full()
            .flex()
            .flex_col()
            .bg(background)
            .font(self.style.font.clone())
            .text_size(self.style.size)
            .line_height(self.style.row_height)
            .child(
                div()
                    .px(px(CODE_PAD_PX))
                    .text_color(muted)
                    .child(self.window_line()),
            )
            .child(body)
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::hexdump::hexdump_sparse;
    use borer_engine::program::{Arch, Program, Section};
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use picker::Picker;
    use workspace::{SplitDirection, Workspace};

    use crate::actions::ShowHex;
    use crate::app_view::tests::load_sample;

    use super::{
        HexItem, HexLayout, HexLine, MAX_ROWS, Miss, RUN_MAX_BYTES, WINDOW_ROWS, inks, miss_line,
    };
    use crate::app_view::REFUSED_FOLDER;
    use crate::app_view::tests::{
        binary_in, drop_on_center, folder_with_settings, init, loaded_of, open, open_place,
        take_status,
    };
    use crate::decompile_item::TabMode;
    use crate::goto::{GoTo, GoToDelegate};
    use crate::places::Place;
    use crate::worker::LoadedBinary;

    /// Opens Go to from the focused view, types `text` and confirms the first line.
    pub(crate) fn go_to(workspace: &Entity<Workspace>, text: &str, cx: &mut VisualTestContext) {
        cx.dispatch_action(GoTo);
        cx.run_until_parked();
        let picker = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_modal::<Picker<GoToDelegate>>(cx)
            })
            .unwrap();
        picker.update_in(cx, |picker, window, cx| picker.set_query(text, window, cx));
        cx.run_until_parked();
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
    }

    /// Returns a section `name` at `va`, `size` bytes the file holds none of.
    fn unbacked(name: &str, va: u64, size: u64) -> Section {
        let mut section = Section::mapped(name, va, 0, size, true, false);
        section.file_size = 0;
        section
    }

    /// Returns a binary of four sections.
    ///
    /// `.data` at `0x1000`, `0x18` bytes of `A` on, so its second row ends where nothing
    /// maps; `.text` at `0x2000`, `0x2000` bytes; `.bss` at `0x5000`, `0x10` bytes the file
    /// holds none of; and `.big` at `0x1_0000_0000`, 16 MiB the file holds none of, more rows
    /// than the list's window.
    fn sections() -> Arc<LoadedBinary> {
        let mut bytes = vec![0xccu8; 0x2100];
        for (b, at) in (b'A'..).zip(0..0x18) {
            bytes[at] = b;
        }
        let sections = vec![
            Section::mapped(".data", 0x1000, 0, 0x18, true, false),
            Section::mapped(".text", 0x2000, 0x100, 0x2000, false, true),
            unbacked(".bss", 0x5000, 0x10),
            unbacked(".big", 0x1_0000_0000, 1 << 24),
        ];
        let program = Program::raw(bytes, Arch::X86_64, 0x1000, None, sections);
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        loaded_of(program, analysis, overlay)
    }

    /// The rows round each section out to whole rows and join the ones that touch; each
    /// row and address map to each other; an address past a run's cap is cut, not
    /// unmapped.
    ///
    /// # Panics
    ///
    /// Panics if a run is cut, joined wrongly or a row maps to another address.
    #[test]
    fn rows_cover_each_section_in_whole_rows() {
        let touching = [
            Section::mapped(".a", 0x1004, 0, 0x10, false, false),
            Section::mapped(".b", 0x1020, 0, 0x10, false, false),
            Section::mapped(".c", 0x4000, 0, 0x01, false, false),
        ];
        let layout = HexLayout::of(&touching);
        assert_eq!(layout.rows(), 4);
        let rows: Vec<Option<u64>> = (0..5).map(|row| layout.va_of(row)).collect();
        assert_eq!(
            rows,
            [Some(0x1000), Some(0x1010), Some(0x1020), Some(0x4000), None]
        );
        for (va, row) in [(0x1000, Ok(0)), (0x102f, Ok(2)), (0x4005, Ok(3))] {
            assert_eq!(layout.row_of(va), row, "{va:#x}");
        }
        for va in [0xfff, 0x1030, 0x4010] {
            assert_eq!(layout.row_of(va), Err(Miss::Unmapped), "{va:#x}");
        }
        let huge = HexLayout::of(&[unbacked(".huge", 0, RUN_MAX_BYTES * 2)]);
        assert_eq!(huge.rows(), MAX_ROWS);
        assert_eq!(huge.row_of(RUN_MAX_BYTES + 5), Err(Miss::Cut));
        assert_eq!(huge.row_of(RUN_MAX_BYTES * 2), Err(Miss::Unmapped));
    }

    /// A row is the engine's hexdump line, `??` where nothing backs a byte, and its runs
    /// cover its text, the address first.
    ///
    /// # Panics
    ///
    /// Panics if the text differs from the engine's or a run strays.
    #[test]
    fn a_row_is_the_engine_hexdump_line() {
        let cells = vec![Some(b'A'), Some(0), None, None];
        let text = hexdump_sparse(&cells, 0x1000);
        let line = HexLine {
            va: 0x1000,
            cells,
            text: text.trim_end().to_owned().into(),
        };
        assert!(
            line.text.starts_with("0x0000001000  41 00 ?? ??"),
            "{}",
            line.text
        );
        let runs = inks(&line);
        assert_eq!(
            runs.iter().map(|(len, _)| len).sum::<usize>(),
            line.text.len()
        );
        assert_eq!(
            runs.first().map(|(len, _)| *len),
            Some("0x0000001000  ".len())
        );
    }

    /// Opens a hex tab of `loaded` and reads the pages of `rows`, asking again when a
    /// redraw in between (which asks only for the rows on screen) dropped a page's read.
    fn hex_of(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        rows: std::ops::Range<usize>,
        cx: &mut VisualTestContext,
    ) -> Entity<HexItem> {
        let hex = Place::Hex { at: None };
        open_place(workspace, loaded, hex, TabMode::Permanent, cx);
        cx.run_until_parked();
        let hex = workspace
            .read_with(cx, |workspace, cx| workspace.active_item_as::<HexItem>(cx))
            .unwrap();
        let pages = rows.start / super::PAGE_ROWS..=rows.end.saturating_sub(1) / super::PAGE_ROWS;
        for _ in 0..3 {
            hex.update(cx, |hex, cx| hex.want_pages(rows.clone(), cx));
            cx.run_until_parked();
            let held = hex.read_with(cx, |hex, _| {
                pages
                    .clone()
                    .all(|page| hex.line(page * super::PAGE_ROWS).is_some())
            });
            if held {
                break;
            }
        }
        hex
    }

    /// At the end of `.data` the row shows its mapped bytes, then the engine's `??` for the
    /// bytes nothing maps; `.bss` is all `??`.
    ///
    /// # Panics
    ///
    /// Panics if a row differs from the engine's runs.
    #[gpui::test]
    fn hex_shows_a_section_end_as_the_engine_marks_it(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let hex = hex_of(&workspace, &sections(), 0..515, cx);
        hex.read_with(cx, |hex, _| {
            let end = hex.line(1).unwrap();
            assert_eq!(end.va, 0x1010);
            let bytes = (b'Q'..=b'X').map(Some);
            let want: Vec<Option<u8>> = bytes.chain([None; 8]).collect();
            assert_eq!(end.cells, want);
            assert_eq!(&*end.text, hexdump_sparse(&want, 0x1010).trim_end());
            assert_eq!(hex.line(514).unwrap().cells, [None; 16]);
        });
    }

    /// Show Hex with the hex tab in another pane shows the bytes in the active one.
    ///
    /// # Panics
    ///
    /// Panics if the active pane's item is not a hex tab.
    #[gpui::test]
    fn show_hex_shows_it_in_the_active_pane(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        load_sample(&app, cx);
        let loaded = app
            .binary
            .read_with(cx, |binary, _| binary.loaded().cloned().unwrap());
        hex_of(&workspace, &loaded, 0..1, cx);
        let left = workspace.read_with(cx, |workspace, _| workspace.active_pane().clone());
        let right = workspace.update_in(cx, |workspace, window, cx| {
            workspace.split_pane(left.clone(), SplitDirection::Right, window, cx)
        });
        cx.run_until_parked();
        workspace.update_in(cx, |workspace, window, cx| {
            let start = right.read(cx).active_item();
            if let Some(start) = start {
                workspace.activate_item(start.as_ref(), true, true, window, cx);
            }
        });
        cx.run_until_parked();
        let active = workspace.read_with(cx, |workspace, _| workspace.active_pane().clone());
        assert_eq!(active, right);
        cx.dispatch_action(ShowHex);
        cx.run_until_parked();
        let shown = right.read_with(cx, |pane, _| {
            pane.active_item()
                .and_then(|item| item.downcast::<HexItem>())
        });
        assert!(shown.is_some());
    }

    /// Scrolled page by page past [`super::HELD_PAGES`] pages, the tab still holds the page
    /// on screen and reads nothing more once it lands: the row the list builds to measure
    /// itself never drops the page on screen.
    ///
    /// # Panics
    ///
    /// Panics if the page on screen is dropped or read again.
    #[gpui::test]
    fn hex_keeps_the_page_on_screen_past_the_held_pages(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let hex = hex_of(&app.workspace, &sections(), 0..1, cx);
        let draw = |cx: &mut VisualTestContext| {
            cx.update(|window, cx| window.draw(cx).clear(cx));
            cx.run_until_parked();
        };
        let far = super::HELD_PAGES + 6;
        for page in 1..=far {
            hex.update(cx, |hex, cx| hex.scroll_to_row(page * super::PAGE_ROWS, cx));
            draw(cx);
            draw(cx);
        }
        draw(cx);
        hex.read_with(cx, |hex, _| {
            assert!(hex.line(far * super::PAGE_ROWS).is_some());
            assert_eq!(hex.pending_pages(), 0);
            assert!(hex.held_pages() <= super::HELD_PAGES);
        });
    }

    /// Go to scrolls to an address's row, past the list's window too; the cursor keys move
    /// the cursor a row; an address no section maps says so on the tab and the status line.
    ///
    /// # Panics
    ///
    /// Panics if Go to lands elsewhere or a miss is said otherwise.
    #[gpui::test]
    fn hex_goes_to_an_address(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let hex = hex_of(&workspace, &sections(), 0..1, cx);
        let far = 0x1_0000_0000 + (1 << 24) - 0x10000;
        let far_row = 2 + 512 + 1 + ((1 << 24) - 0x10000) / 16;
        assert!(far_row > WINDOW_ROWS);
        for (va, row) in [(0x2105, 18), (far, far_row)] {
            go_to(&workspace, &format!("{va:#x}"), cx);
            hex.read_with(cx, |hex, _| {
                assert_eq!((hex.cursor(), hex.miss()), (Some(va), None));
                assert_eq!(hex.top_row(), row);
            });
        }
        cx.dispatch_action(menu::SelectNext);
        cx.run_until_parked();
        assert_eq!(hex.read_with(cx, |hex, _| hex.cursor()), Some(far + 16));
        let binary = binary_in(&workspace, cx);
        go_to(&workspace, "0x9000", cx);
        let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
        assert_eq!(status, miss_line(0x9000, Miss::Unmapped));
        assert_eq!(hex.read_with(cx, |hex, _| hex.miss()), Some(Miss::Unmapped));
    }

    /// A folder dropped on the hex tab reaches the binary's loader, which refuses it, and
    /// never becomes a project folder, its settings never read.
    #[gpui::test]
    async fn a_folder_dropped_on_the_hex_tab_never_joins_the_project(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let dir = folder_with_settings(&app_state, "hex-drop").await;
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        hex_of(&workspace, &sections(), 0..1, cx);
        drop_on_center(&dir, cx);
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(take_status(&app, cx).ends_with(REFUSED_FOLDER));
        let folders = workspace.read_with(cx, |workspace, cx| {
            workspace.project().read(cx).worktrees(cx).count()
        });
        assert_eq!(folders, 0);
    }
}
