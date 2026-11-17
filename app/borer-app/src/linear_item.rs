//! The linear listing: the whole image as one listing in address order, in a center tab.
//!
//! The tab keeps a few pages of the engine's linear listing around what it shows, fetched
//! in the background, in the code tab's editor, with a scrollbar over the image's addresses.
//!
//! What is code, data or unexplored is the engine's ([`linear`]); the tab pages and paints.
//! Lines are unknown up front, so the scrollbar maps the image's address range: its thumb
//! sits at the address of the top line, and a click or a drag on it asks for the page at
//! the address under the pointer.
//!
//! Beside the scrollbar, the overview band ([`band`]) splits the same range into one cell
//! per pixel, each in the color of what holds most of its bytes; a click on a cell goes to
//! its first address.
//!
//! [`linear`]: borer_engine::analysis::render::linear
//! [`band`]: borer_engine::analysis::render::band

use std::cell::Cell;
use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::render::{Cell as BandCell, CellKind, Dir, LinearPage, Row};
use borer_engine::num::{as_f64, from_usize};
use borer_engine::view::View;
use editor::scroll::ScrollAnchor;
use editor::{EditorEvent, SelectionEffects, SemanticsProvider};
use gpui::{
    AnyElement, App, AppContext as _, Bounds, Context, Entity, EventEmitter, FocusHandle,
    Focusable, Hsla, InteractiveElement as _, IntoElement, MouseButton, MouseDownEvent,
    MouseMoveEvent, ParentElement as _, Pixels, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity, Window, canvas, div,
    fill, point, px,
};
use language::{Buffer, BufferId, Point};
use theme::ActiveTheme as _;
use ui::{Icon, IconName, Tooltip};
use workspace::{Item, Workspace};

use crate::actions::{BACK_HINT, FollowLink, Hint, ShowInLinear, ShowLinear};
use crate::binary::{Binary, BinaryEvent, Revision};
use crate::card::{Card, Tone};
use crate::code_semantics::ViewSemantics;
use crate::code_view::CodeLines;
use crate::commands;
use crate::decompile_item::{DecompileItem, Form, TabMode, buffer_row, text_buffer, whole_rows};
use crate::places::{Opening, Place, open, shown_binary};
use crate::worker::{Job, LoadedBinary, band_cells, linear_page};

/// Rows one page asks the engine for.
const PAGE_ROWS: usize = 512;

/// Pages the tab keeps; past them, a page that lies wholly [`AHEAD_LINES`] or more from
/// the top line is dropped.
pub const PAGES_MAX: usize = 4;

/// Lines kept above and below the top line: fewer, and the page beyond is fetched. Less
/// than a page holds, so the page with the top line and one each side reach far enough.
const AHEAD_LINES: usize = 384;

/// Width in logical pixels of the address scrollbar.
const SCROLLBAR_PX: f32 = 10.0;

/// Fewest logical pixels the scrollbar's thumb is tall.
const THUMB_MIN_PX: f32 = 4.0;

/// Width in logical pixels of the overview band.
const BAND_PX: f32 = 8.0;

/// One page the tab keeps: its lines, its rows and where the pages beside it start.
#[derive(Debug, Clone)]
struct Page {
    /// The page's lines.
    view: Arc<View>,
    /// The page's rows in address order.
    rows: Vec<Row>,
    /// The address of its first row.
    first: u64,
    /// Where the page after it starts, `None` at the image's end.
    next: Option<u64>,
    /// Where the page before it starts, `None` at the image's start.
    prev: Option<u64>,
}

impl From<LinearPage> for Page {
    fn from(page: LinearPage) -> Self {
        Self {
            view: Arc::new(page.view),
            rows: page.rows,
            first: page.first,
            next: page.next,
            prev: page.prev,
        }
    }
}

/// The pages the tab keeps, in address order, each one starting where the one before ends.
#[derive(Debug, Clone, Default)]
pub struct Pages(Vec<Page>);

/// How a page the tab added moved the lines it kept: lines added above them and lines
/// dropped from above them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Shift {
    /// Lines of a page added before the first kept line.
    added: usize,
    /// Lines of a page dropped from before the first kept line.
    dropped: usize,
}

impl Shift {
    /// Returns where kept line `line` is after the shift.
    ///
    /// # Arguments
    ///
    /// * `line` - Index of the line before the shift.
    #[must_use]
    pub const fn moved(self, line: usize) -> usize {
        line.saturating_add(self.added).saturating_sub(self.dropped)
    }
}

impl Pages {
    /// Returns the kept lines, every page's lines in order.
    #[must_use]
    pub fn lines(&self) -> Arc<CodeLines> {
        Arc::new(CodeLines::new(
            self.0.iter().map(|page| page.view.clone()).collect(),
        ))
    }

    /// Returns how many lines the kept pages hold.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.iter().map(|page| page.view.lines()).sum()
    }

    /// Returns whether no page is kept.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Adds `page` after the last kept page or before the first, as `dir` says; an empty
    /// set takes any page. Past [`PAGES_MAX`] it drops the first page while it ends
    /// [`AHEAD_LINES`] or more above the top line, then the last while it starts as far
    /// below, so what it keeps never asks again for a page it dropped.
    ///
    /// # Arguments
    ///
    /// * `page` - The page.
    /// * `dir` - Whether it follows the kept pages ([`Dir::Next`]) or leads them.
    /// * `top` - The kept line at the top of the tab.
    ///
    /// # Returns
    ///
    /// How the kept lines moved, or `None` when the page does not start where the last
    /// ends (or end where the first starts), so no seam drops or repeats a row.
    fn add(&mut self, page: Page, dir: Dir, top: usize) -> Option<Shift> {
        let mut shift = Shift {
            added: 0,
            dropped: 0,
        };
        match (dir, self.0.first(), self.0.last()) {
            (_, None, _) | (_, _, None) => self.0.push(page),
            (Dir::Next, _, Some(last)) => {
                (last.next == Some(page.first)).then_some(())?;
                self.0.push(page);
            }
            (Dir::Prev, Some(first), _) => {
                (page.next == Some(first.first)).then_some(())?;
                shift.added = page.view.lines();
                self.0.insert(0, page);
            }
        }
        let mut top = shift.moved(top);
        while self.0.len() > PAGES_MAX {
            let lines = |page: Option<&Page>| page.map_or(0, |p| p.view.lines());
            let (front, back) = (lines(self.0.first()), lines(self.0.last()));
            if front.saturating_add(AHEAD_LINES) <= top {
                self.0.remove(0);
                shift.dropped = shift.dropped.saturating_add(front);
                top = top.saturating_sub(front);
            } else if self.len().saturating_sub(back) >= top.saturating_add(AHEAD_LINES) {
                self.0.pop();
            } else {
                break;
            }
        }
        Some(shift)
    }

    /// Returns the kept lines of the row holding `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// From the row's first line up to the next row's, or `None` when no kept row holds
    /// `va`.
    #[must_use]
    pub fn row_lines(&self, va: u64) -> Option<Range<usize>> {
        let mut base = 0usize;
        for page in &self.0 {
            let k = page.rows.partition_point(|r| r.span.start <= va);
            if let Some(row) = k.checked_sub(1).and_then(|k| page.rows.get(k))
                && va < row.span.end
            {
                let first = page.view.line_of(row.span.start)?;
                let last = page.rows.get(k).map_or(Some(page.view.lines()), |next| {
                    page.view.line_of(next.span.start)
                })?;
                return Some(base.saturating_add(first)..base.saturating_add(last));
            }
            base = base.saturating_add(page.view.lines());
        }
        None
    }

    /// Returns the page the tab asks for next with its top line at `top`: the page after
    /// the last kept one when fewer than [`AHEAD_LINES`] lines are kept below the top line,
    /// else the page before the first when fewer are kept above it.
    ///
    /// # Arguments
    ///
    /// * `top` - The kept line at the top of the tab.
    ///
    /// # Returns
    ///
    /// Where the page runs from and which way, `None` when the kept pages reach far
    /// enough or the image's ends.
    #[must_use]
    pub fn wants(&self, top: usize) -> Option<(u64, Dir)> {
        let (first, last) = (self.0.first()?, self.0.last()?);
        match last.next {
            Some(next) if self.len().saturating_sub(top) < AHEAD_LINES => Some((next, Dir::Next)),
            _ if top < AHEAD_LINES && first.prev.is_some() => Some((first.first, Dir::Prev)),
            _ => None,
        }
    }
}

/// What a page request does with the kept pages.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fetch {
    /// Drops them and shows the row holding the address at the top, the cursor on it.
    Reset(u64),
    /// Adds the page beside them, keeping the top line where it is.
    Extend,
}

/// What a background page request hands the tab: the pages to keep, their lines and the
/// text buffer over them, and how the lines kept before moved.
struct Swap {
    /// The pages to keep.
    pages: Pages,
    /// Their lines.
    code: Arc<CodeLines>,
    /// The text buffer over the lines.
    text: language::TextBuffer,
    /// How the lines kept before moved.
    shift: Shift,
}

/// What a page request answers: the swap and the image's range, `None` when the page no
/// longer joins the kept ones, or the engine's reason it listed none.
type Fetched = Result<Option<(Swap, (u64, u64))>, String>;

/// The whole image as one listing, paged by address, as an item of Zed's center pane.
pub struct LinearItem {
    /// The window's binary, whose drops the tab opens.
    binary: Entity<Binary>,
    /// Binary the listing shows.
    loaded: Arc<LoadedBinary>,
    /// The code tab whose editor shows the kept lines.
    code: Entity<DecompileItem>,
    /// The kept pages.
    pages: Pages,
    /// The image's first address and one past its last, once the first page is in.
    range: Option<(u64, u64)>,
    /// The engine's reason the listing was not built.
    failed: Option<String>,
    /// The editor's scroll events.
    scrolls: Option<Subscription>,
    /// Where the scrollbar was last laid out, for the pointer's address.
    scrollbar: Rc<Cell<Bounds<Pixels>>>,
    /// The page request.
    job: Job,
    /// The overview band's cells, in address order.
    band: Vec<BandCell>,
    /// Cells the band was last asked in: one per pixel of its height.
    band_for: usize,
    /// The band request.
    band_job: Job,
    /// Where the band was last laid out, for the cell under the pointer.
    band_laid: Rc<Cell<Bounds<Pixels>>>,
    /// The cell under the pointer, which the band's hover names.
    hovered: Rc<Cell<Option<BandCell>>>,
    /// Lists the image again over the state an edit or a project leaves.
    _revised: Subscription,
}

impl std::fmt::Debug for LinearItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LinearItem")
            .field("pages", &self.pages.0.len())
            .field("job", &self.job)
            .finish_non_exhaustive()
    }
}

impl LinearItem {
    /// Returns a linear listing of `loaded`, its first page fetched in the background; over
    /// each state an edit or a project leaves it lists again from its top line.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace a followed link opens its function in.
    /// * `binary` - The window's binary.
    /// * `loaded` - Binary the listing shows.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let empty = Arc::new(CodeLines::new(Vec::new()));
        let shown = (None, Form::Listing);
        let (source, none) = (loaded.clone(), empty.clone());
        let code = cx.new(|cx| {
            let lines = move || Ok(none);
            let mut code =
                DecompileItem::new(workspace, binary.clone(), source, shown, lines, window, cx);
            code.stop();
            let reservation = cx.reserve_entity::<Buffer>();
            let text = text_buffer(
                &empty,
                BufferId::from(reservation.entity_id().as_non_zero_u64()),
            );
            code.show(Ok((empty, text, None)), reservation, window, cx);
            code
        });
        let revised = cx.subscribe_in(&binary, window, |item, _, event, window, cx| match event {
            BinaryEvent::Revised(loaded) => item.revise(loaded.clone(), window, cx),
            BinaryEvent::Opened(_) | BinaryEvent::Closed => {}
        });
        let mut item = Self {
            binary,
            loaded,
            code,
            pages: Pages::default(),
            range: None,
            failed: None,
            scrolls: None,
            scrollbar: Rc::default(),
            job: Job::default(),
            band: Vec::new(),
            band_for: 0,
            band_job: Job::default(),
            band_laid: Rc::default(),
            hovered: Rc::default(),
            _revised: revised,
        };
        item.fetch(0, Dir::Next, Fetch::Reset(0), window, cx);
        item
    }

    /// Moves the listing to `loaded`, a later state of its binary, and fetches its pages
    /// again from the row on its top line, which stays on top.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary's state now.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn revise(&mut self, loaded: Arc<LoadedBinary>, window: &Window, cx: &mut Context<'_, Self>) {
        self.loaded = loaded;
        let top = self.top_line(cx);
        let va = self.address(top, cx).unwrap_or(0);
        self.fetch(va, Dir::Next, Fetch::Reset(va), window, cx);
    }

    /// Returns the binary the listing shows.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns the code tab whose editor shows the kept lines.
    #[must_use]
    pub const fn code(&self) -> &Entity<DecompileItem> {
        &self.code
    }

    /// Returns whether a page or band request is running.
    #[must_use]
    pub fn is_fetching(&self) -> bool {
        self.job.is_running() || self.band_job.is_running()
    }

    /// Shows the row holding `va` at the top, the cursor on it: at once when a kept page
    /// holds it, else once its page is fetched.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address; one outside the image goes to its nearer end.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn go_to(&mut self, va: u64, window: &Window, cx: &mut Context<'_, Self>) {
        match self.pages.row_lines(va) {
            Some(lines) => {
                self.job.stop();
                self.code
                    .update(cx, |code, cx| code.jump_to_line(lines.start, cx));
            }
            None => self.fetch(va, Dir::Next, Fetch::Reset(va), window, cx),
        }
    }

    /// Asks the engine for the page at `at` running `dir`, and builds the lines to keep
    /// and their buffer with it in the background; a newer request drops this one.
    ///
    /// # Arguments
    ///
    /// * `at` - Address the page runs from.
    /// * `dir` - Which way it runs.
    /// * `how` - What it does with the kept pages.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn fetch(
        &mut self,
        at: u64,
        dir: Dir,
        how: Fetch,
        window: &Window,
        cx: &mut Context<'_, Self>,
    ) {
        let reservation = cx.reserve_entity::<Buffer>();
        let id = BufferId::from(reservation.entity_id().as_non_zero_u64());
        let (loaded, kept, top) = (self.loaded.clone(), self.pages.clone(), self.top_line(cx));
        let (label, known) = (format!("Listing the image at {at:#x}"), self.range);
        let work = move || -> Fetched {
            let range = known.map_or_else(|| image_range(&loaded), Ok)?;
            let (mut pages, top) = match how {
                Fetch::Reset(_) => (Pages::default(), 0),
                Fetch::Extend => (kept, top),
            };
            let page = linear_page(&loaded, at, dir, PAGE_ROWS)?;
            let Some(shift) = pages.add(page.into(), dir, top) else {
                return Ok(None);
            };
            let code = pages.lines();
            let text = text_buffer(&code, id);
            Ok(Some((
                Swap {
                    pages,
                    code,
                    text,
                    shift,
                },
                range,
            )))
        };
        self.job
            .run_in(label, window, cx, work, move |item, built, window, cx| {
                match built {
                    Err(why) => item.failed = Some(why),
                    Ok(None) => {}
                    Ok(Some((swap, range))) => {
                        item.range = Some(range);
                        item.show(swap, how, reservation, window, cx);
                    }
                }
                cx.notify();
            });
    }

    /// Shows the kept lines in the code tab, the top line staying where it was or, after a
    /// reset, the row of the address on top with the cursor on it.
    ///
    /// # Arguments
    ///
    /// * `swap` - The pages to keep, their lines, buffer and shift.
    /// * `how` - What the request did with the pages kept before.
    /// * `reservation` - The buffer's reserved entity.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn show(
        &mut self,
        swap: Swap,
        how: Fetch,
        reservation: gpui::Reservation<Buffer>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let Swap {
            pages,
            code,
            text,
            shift,
        } = swap;
        let editor = self.code.read(cx).editor().clone();
        let y = editor.update(cx, |editor, cx| editor.scroll_position(cx).y);
        let (top, frac) = (self.top_line(cx), y - y.floor());
        let (top, frac, cursor) = match how {
            Fetch::Extend => (shift.moved(top), frac, false),
            Fetch::Reset(va) => (pages.row_lines(va).map_or(0, |l| l.start), 0.0, true),
        };
        self.pages = pages;
        let semantics: Rc<dyn SemanticsProvider> = Rc::new(ViewSemantics { code: code.clone() });
        self.code.update(cx, |item, cx| {
            item.show(Ok((code, text, None)), reservation, window, cx);
            item.editor().update(cx, |editor, cx| {
                editor.set_semantics_provider(Some(semantics));
                let at = Point::new(u32::try_from(top).unwrap_or(u32::MAX), 0);
                if cursor {
                    let effects = SelectionEffects::no_scroll().nav_history(false);
                    editor.change_selections(effects, window, cx, |s| s.select_ranges([at..at]));
                }
                let anchor = editor.buffer().read(cx).snapshot(cx).anchor_before(at);
                let offset = point(0.0, frac);
                editor.set_scroll_anchor(ScrollAnchor { anchor, offset }, window, cx);
            });
        });
        let editor = self.code.read(cx).editor().clone();
        self.scrolls = Some(cx.subscribe_in(
            &editor,
            window,
            |item, _, event: &EditorEvent, window, cx| {
                if let EditorEvent::ScrollPositionChanged { .. } = event {
                    item.follow(window, cx);
                }
            },
        ));
        self.follow(window, cx);
    }

    /// Follows the editor's scroll: asks for the page beyond the kept ones when the top
    /// line nears their end, and redraws the scrollbar.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn follow(&mut self, window: &Window, cx: &mut Context<'_, Self>) {
        let top = self.top_line(cx);
        if !self.job.is_running()
            && let Some((at, dir)) = self.pages.wants(top)
        {
            self.fetch(at, dir, Fetch::Extend, window, cx);
        }
        cx.notify();
    }

    /// Returns the kept line at the top of the tab, as the editor's scroll stands now.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the editor.
    #[must_use]
    pub fn top_line(&self, cx: &mut App) -> usize {
        let editor = self.code.read(cx).editor().clone();
        editor.update(cx, |editor, cx| {
            let top = whole_rows(editor.scroll_position(cx).y);
            buffer_row(&editor.display_snapshot(cx), top)
        })
    }

    /// Returns the address of kept line `line`, `None` past the last.
    ///
    /// # Arguments
    ///
    /// * `line` - Index of a kept line.
    /// * `cx` - Application context reading the code tab.
    #[must_use]
    pub fn address(&self, line: usize, cx: &App) -> Option<u64> {
        let (view, line) = self.code.read(cx).code()?.get(line)?;
        view.address(line)
    }

    /// Returns the address the scrollbar maps a pointer at `y` to: the image's range split
    /// evenly over the scrollbar's height.
    ///
    /// # Arguments
    ///
    /// * `y` - The pointer's height in the window.
    ///
    /// # Returns
    ///
    /// The address, `None` before the image's range is known or the scrollbar laid out.
    #[must_use]
    pub fn address_at(&self, y: Pixels) -> Option<u64> {
        let (lo, hi) = self.range?;
        let bounds = self.scrollbar.get();
        let share = ((y - bounds.top()) / bounds.size.height).clamp(0.0, 1.0);
        Some(lo.saturating_add(scaled(hi.saturating_sub(lo), share)))
    }

    /// Returns where the scrollbar was last laid out.
    #[must_use]
    pub fn scrollbar_bounds(&self) -> Bounds<Pixels> {
        self.scrollbar.get()
    }

    /// Returns the thumb's top and bottom as shares of the scrollbar: the addresses of the
    /// top line and of the line a screen below it, over the image's range.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the editor.
    fn thumb(&self, cx: &mut App) -> Option<(f32, f32)> {
        let (lo, hi) = self.range?;
        let top = self.top_line(cx);
        let shown = self.code.read(cx).editor().read(cx).visible_line_count();
        let rows = shown.map_or(0, whole_rows);
        let first = self.address(top, cx)?;
        let last = self.address(top.saturating_add(rows), cx).unwrap_or(hi);
        let share = |va: u64| share_of(va.saturating_sub(lo), hi.saturating_sub(lo));
        Some((share(first), share(last)))
    }

    /// Goes to the address under the pointer on the scrollbar.
    ///
    /// # Arguments
    ///
    /// * `y` - The pointer's height in the window.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn scroll_to_pointer(&mut self, y: Pixels, window: &Window, cx: &mut Context<'_, Self>) {
        if let Some(va) = self.address_at(y) {
            self.go_to(va, window, cx);
        }
    }

    /// Returns what the tab says while it shows no lines: the engine's reason the listing
    /// was not built, that it is building, or that it has none; `None` once lines show.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        if !self.pages.is_empty() {
            return None;
        }
        let (says, tone, offers): (SharedString, _, &'static [Hint]) = match &self.failed {
            Some(why) => (
                format!("Linear listing failed\n{why}").into(),
                Tone::Error,
                &[BACK_HINT],
            ),
            None if self.job.is_running() => ("Listing the image...".into(), Tone::Quiet, &[]),
            None => ("No lines.".into(), Tone::Quiet, &[]),
        };
        Some(Card { says, tone, offers })
    }

    /// Draws the scrollbar: its track, and its thumb from the top line's address.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn render_scrollbar(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let thumb = self.thumb(cx);
        let colors = cx.theme().colors();
        let (bg, fg) = (
            colors.scrollbar_track_background,
            colors.scrollbar_thumb_background,
        );
        let laid = self.scrollbar.clone();
        let paint = canvas(
            move |bounds, _, _| laid.set(bounds),
            move |bounds, (), window, _| {
                window.paint_quad(fill(bounds, bg));
                if let Some((top, bottom)) = thumb {
                    let height = bounds.size.height;
                    let tall = (height * (bottom - top)).max(px(THUMB_MIN_PX));
                    let origin = point(bounds.left(), bounds.top() + height * top);
                    let size = gpui::size(bounds.size.width, tall);
                    window.paint_quad(fill(Bounds::new(origin, size), fg));
                }
            },
        );
        div()
            .id("linear-scrollbar")
            .w(px(SCROLLBAR_PX))
            .h_full()
            .child(paint.size_full())
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|item, event: &MouseDownEvent, window, cx| {
                    item.scroll_to_pointer(event.position.y, window, cx);
                }),
            )
            .on_mouse_move(cx.listener(|item, event: &MouseMoveEvent, window, cx| {
                if event.pressed_button == Some(MouseButton::Left) {
                    item.scroll_to_pointer(event.position.y, window, cx);
                }
            }))
            .into_any_element()
    }
}

impl LinearItem {
    /// Asks the engine for the band in one cell per pixel of the band's height, when that
    /// height changed since the last request.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn ask_cells(&mut self, cx: &mut Context<'_, Self>) {
        let cells = whole_rows(f64::from(self.band_laid.get().size.height.as_f32()));
        if cells == 0 || cells == self.band_for {
            return;
        }
        self.band_for = cells;
        let loaded = self.loaded.clone();
        let label = format!("Banding the image in {cells} cells");
        let work = move || band_cells(&loaded, cells);
        self.band_job.run(label, cx, work, |item, band, cx| {
            item.band = band;
            cx.notify();
        });
    }

    /// Returns the band's cell under a pointer at `y`, `None` off the band or before it is in.
    ///
    /// # Arguments
    ///
    /// * `y` - The pointer's height in the window.
    #[must_use]
    pub fn cell_at(&self, y: Pixels) -> Option<BandCell> {
        let bounds = self.band_laid.get();
        let share = (y - bounds.top()) / bounds.size.height;
        if !(0.0..1.0).contains(&share) {
            return None;
        }
        let ix = whole_rows(f64::from(share) * as_f64(from_usize(self.band.len())));
        self.band.get(ix).copied()
    }

    /// Returns where the band was last laid out and its cells.
    #[must_use]
    pub fn cells(&self) -> (Bounds<Pixels>, &[BandCell]) {
        (self.band_laid.get(), &self.band)
    }

    /// Draws the overview band: each cell in its kind's color, and the shown addresses
    /// outlined.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn render_cells(&mut self, cx: &mut Context<'_, Self>) -> AnyElement {
        self.ask_cells(cx);
        let colors: Vec<Hsla> = self.band.iter().map(|c| cell_color(c.kind, cx)).collect();
        let (thumb, marker) = (self.thumb(cx), cx.theme().colors().text);
        let (laid, hovered) = (self.band_laid.clone(), self.hovered.clone());
        let paint = canvas(
            move |bounds, window, _| {
                if laid.replace(bounds).size.height != bounds.size.height {
                    window.refresh();
                }
            },
            move |bounds, (), window, _| {
                let n = from_usize(colors.len());
                let y = |i: usize| bounds.size.height * share_of(from_usize(i), n);
                for (i, color) in colors.iter().enumerate() {
                    let origin = point(bounds.left(), bounds.top() + y(i));
                    let size = gpui::size(bounds.size.width, y(i + 1) - y(i));
                    window.paint_quad(fill(Bounds::new(origin, size), *color));
                }
                if let Some((top, bottom)) = thumb {
                    let height = bounds.size.height;
                    let tall = (height * (bottom - top)).max(px(THUMB_MIN_PX));
                    let origin = point(bounds.left(), bounds.top() + height * top);
                    let shown = Bounds::new(origin, gpui::size(bounds.size.width, tall));
                    window.paint_quad(gpui::outline(shown, marker, gpui::BorderStyle::Solid));
                }
            },
        );
        div()
            .id("linear-band")
            .w(px(BAND_PX))
            .h_full()
            .child(paint.size_full())
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|item, event: &MouseDownEvent, window, cx| {
                    if let Some(cell) = item.cell_at(event.position.y) {
                        item.go_to(cell.first, window, cx);
                    }
                }),
            )
            .on_mouse_move(cx.listener(|item, event: &MouseMoveEvent, _, _| {
                item.hovered.set(item.cell_at(event.position.y));
            }))
            .tooltip(move |_, cx| {
                let text = hovered.get().map_or_else(String::new, |cell| {
                    format!("{} at {:#x}", cell_name(cell.kind), cell.first)
                });
                Tooltip::simple(text, cx)
            })
            .into_any_element()
    }
}

/// Returns the color the band paints a cell of `kind` in, from the theme's status colors.
///
/// Code is `info`, data `warning`, strings `success`, unexplored bytes `unreachable` and the
/// gaps between sections `hidden`.
///
/// # Arguments
///
/// * `kind` - What holds most of the cell's bytes.
/// * `cx` - Application context reading the theme.
#[must_use]
pub fn cell_color(kind: CellKind, cx: &App) -> Hsla {
    let status = cx.theme().status();
    match kind {
        CellKind::Code => status.info,
        CellKind::Data => status.warning,
        CellKind::String => status.success,
        CellKind::Unexplored => status.unreachable,
        CellKind::Unmapped => status.hidden,
    }
}

/// Returns what the band's hover says a cell of `kind` holds, in the engine's words.
///
/// # Arguments
///
/// * `kind` - What holds most of the cell's bytes.
#[must_use]
pub const fn cell_name(kind: CellKind) -> &'static str {
    match kind {
        CellKind::Code => "code: instructions of discovered blocks",
        CellKind::Data => "data: a typed value, a pointer, or bytes a name the file states names",
        CellKind::String => "string: a string the walk found",
        CellKind::Unexplored => "unexplored: bytes inside a section no fact covers",
        CellKind::Unmapped => "unmapped: addresses between two sections",
    }
}

/// Opens the linear listing of what the active tab shows, else of the window's binary.
///
/// It reuses the tab already showing it, puts the row holding `at` on top when one is
/// given, and opens nothing before a binary is loaded.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
/// * `at` - The address to show, if any.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn show(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    at: Option<u64>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let Some(loaded) = shown_binary(workspace, binary, cx) else {
        return;
    };
    let how = Opening {
        mode: TabMode::Permanent,
        focus: true,
    };
    open(
        workspace,
        binary,
        &loaded,
        Place::Linear { at },
        how,
        window,
        cx,
    );
}

/// Registers the linear listing's commands on `workspace`, over the window's `binary`:
/// open it, and open it at the code tab's cursor.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let (linear, here) = (binary.clone(), binary.clone());
    commands::register(
        workspace,
        binary,
        move |workspace, _: &ShowLinear, window, cx| {
            show(workspace, &linear, None, window, cx);
        },
    );
    commands::register(
        workspace,
        binary,
        move |workspace, _: &ShowInLinear, window, cx| {
            let code = workspace.active_item_as::<DecompileItem>(cx);
            let at = code.and_then(|item| item.read(cx).cursor_address(cx));
            show(workspace, &here, at, window, cx);
        },
    );
}

/// Returns the image's first address and one past its last: the first row's start and the
/// last row's end.
///
/// # Arguments
///
/// * `loaded` - Previously loaded binary state.
///
/// # Errors
///
/// Returns the engine's reason when it lists no page.
fn image_range(loaded: &LoadedBinary) -> Result<(u64, u64), String> {
    let first = linear_page(loaded, 0, Dir::Next, 1)?.first;
    let last = linear_page(loaded, u64::MAX, Dir::Next, 1)?;
    let end = last.rows.last().map_or(last.first, |row| row.span.end);
    Ok((first, end.max(first)))
}

/// Returns `share` of `span`, rounded down.
///
/// # Arguments
///
/// * `span` - A count of bytes.
/// * `share` - A share from 0 to 1.
fn scaled(span: u64, share: f32) -> u64 {
    let parts = 1u64 << 24;
    let part = whole_rows(f64::from(share.clamp(0.0, 1.0)) * as_f64(parts));
    let part = u64::try_from(part).unwrap_or(parts).min(parts);
    let scaled = u128::from(span) * u128::from(part) / u128::from(parts);
    u64::try_from(scaled).unwrap_or(span)
}

/// Returns `part` over `span` as a share from 0 to 1, 1 for an empty span.
///
/// # Arguments
///
/// * `part` - A count of bytes.
/// * `span` - The whole count.
#[expect(
    clippy::cast_possible_truncation,
    reason = "a share from 0 to 1 fits an f32"
)]
fn share_of(part: u64, span: u64) -> f32 {
    if span == 0 {
        return 1.0;
    }
    (as_f64(part) / as_f64(span)).clamp(0.0, 1.0) as f32
}

impl EventEmitter<()> for LinearItem {}

impl Focusable for LinearItem {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.code.read(cx).focus_handle(cx)
    }
}

impl Revision for LinearItem {
    fn revision(&self) -> Option<u64> {
        Some(self.loaded.fingerprint)
    }
}

impl Item for LinearItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        "Linear".into()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Binary))
    }

    crate::app_view::snapshot_tab!();
}

impl Render for LinearItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let card = self.card().map(|card| card.render(cx));
        div()
            .key_context("LinearView")
            .flex()
            .size_full()
            .on_action(cx.listener(|item, _: &FollowLink, window, cx| {
                item.code
                    .update(cx, |code, cx| code.follow_cursor(true, window, cx));
            }))
            .child(
                div()
                    .relative()
                    .flex_1()
                    .h_full()
                    .child(self.code.clone())
                    .children(card.map(|card| div().absolute().inset_0().child(card))),
            )
            .child(self.render_cells(cx))
            .child(self.render_scrollbar(cx))
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::{CellKind, Dir};
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::num::from_usize;
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use gpui::{Entity, Modifiers, TestAppContext, VisualTestContext, point};
    use picker::Picker;
    use theme::ActiveTheme as _;
    use workspace::Workspace;

    use super::{AHEAD_LINES, LinearItem, PAGE_ROWS, PAGES_MAX, Page, Pages};
    use crate::actions::{CloseBinary, ShowLinear};
    use crate::app_view::tests::{CALLER, init, load_sample, loaded_of, open, open_place, sample};
    use crate::decompile_item::tests::{fourth_instruction, open_tab, put_cursor};
    use crate::decompile_item::{Form, TabMode};
    use crate::goto::GoToDelegate;
    use crate::places::Place;
    use crate::worker::{LoadedBinary, linear_page};

    /// First address of the long sample's code.
    const TEXT: u64 = 0x1000;

    /// One past the long sample's last address.
    const END: u64 = 0x8000;

    /// Returns a sample of many pages: `0x2000` bytes of code that runs to one return, a
    /// gap, and `0x4000` bytes of zeroed data no fact covers.
    pub(crate) fn long_sample() -> Arc<LoadedBinary> {
        let mut bytes = vec![0x90; 0x2000];
        bytes[0x1fff] = 0xc3;
        bytes.extend([0; 0x4000]);
        let sections = vec![
            Section::mapped(".text", TEXT, 0, 0x2000, false, true),
            Section::mapped(".data", 0x4000, 0x2000, 0x4000, true, false),
        ];
        let mut program = Program::raw(bytes, Arch::X86_64, TEXT, Some(TEXT), sections);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        loaded_of(program, analysis, overlay)
    }

    /// Returns every line of the linear listing of `loaded`, page after page from its start.
    fn every_line(loaded: &LoadedBinary) -> Vec<String> {
        let mut out = Vec::new();
        let mut at = Some(0);
        while let Some(va) = at {
            let page = linear_page(loaded, va, Dir::Next, PAGE_ROWS).unwrap();
            out.extend((0..page.view.lines()).map(|l| page.view.line(l).unwrap().to_owned()));
            at = page.next;
        }
        out
    }

    /// Opens the linear listing of `loaded` at `at` and returns its tab once its pages are in.
    pub(crate) fn open_linear(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        at: Option<u64>,
        cx: &mut VisualTestContext,
    ) -> Entity<LinearItem> {
        open_place(
            workspace,
            loaded,
            Place::Linear { at },
            TabMode::Permanent,
            cx,
        );
        let item = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<LinearItem>(cx)
            })
            .unwrap();
        settle(&item, cx);
        item
    }

    /// Runs the tab's work and frames until two frames in a row leave no request running.
    pub(crate) fn settle(item: &Entity<LinearItem>, cx: &mut VisualTestContext) {
        let mut idle = 0;
        for _ in 0..64 {
            cx.run_until_parked();
            cx.update(|window, cx| window.draw(cx).clear(cx));
            cx.run_until_parked();
            idle = if item.read_with(cx, |item, _| item.is_fetching()) {
                0
            } else {
                idle + 1
            };
            if idle == 2 {
                return;
            }
        }
        panic!("the pages never settled");
    }

    /// Returns the tab's text, line by line, and its top line.
    pub(crate) fn shown(
        item: &Entity<LinearItem>,
        cx: &mut VisualTestContext,
    ) -> (Vec<String>, usize) {
        item.update(cx, |item, cx| {
            let text = item.code().read(cx).editor().read(cx).text(cx);
            (
                text.split('\n').map(str::to_owned).collect(),
                item.top_line(cx),
            )
        })
    }

    /// Scrolling from the top to the end of a many-page image a screen past the kept lines
    /// at a time shows every line once, in order: each step's lines are one run of the
    /// whole listing that starts no later than the last step's ended, and no more than
    /// [`PAGES_MAX`] pages are kept.
    #[gpui::test]
    fn scrolling_to_the_end_shows_every_page_once_in_order(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = long_sample();
        let full = every_line(&loaded);
        assert!(full.len() > PAGES_MAX * PAGE_ROWS);
        let item = open_linear(&workspace, &loaded, None, cx);
        let mut reached = 0;
        for _ in 0..full.len() {
            let (lines, top) = shown(&item, cx);
            let fits = |s: &usize| full.get(*s..*s + lines.len()) == Some(lines.as_slice());
            let start = (0..full.len())
                .find(fits)
                .expect("the lines are one run of the listing");
            assert!(start <= reached, "a gap before line {start}");
            assert!(item.read_with(cx, |item, _| item.pages.0.len()) <= PAGES_MAX);
            let before = reached;
            reached = reached.max(start + lines.len());
            if reached == full.len() {
                return;
            }
            let pages = item.read_with(cx, |item, _| {
                let ends: Vec<_> = item.pages.0.iter().map(|p| (p.first, p.next)).collect();
                ends
            });
            assert!(
                reached > before || before == 0,
                "stuck at {reached} of {}: start {start}, {} lines, top {top}, pages {pages:x?}",
                full.len(),
                lines.len()
            );
            item.update(cx, |item, cx| {
                item.code().update(cx, |code, cx| {
                    code.scroll_to(lines.len() - 1);
                    cx.notify();
                });
            });
            settle(&item, cx);
        }
        panic!("the end was never shown");
    }

    /// Going to an address inside an instruction puts that instruction's row on the top
    /// line, the cursor on it.
    #[gpui::test]
    fn going_to_an_address_inside_an_instruction_lands_on_its_line(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let item = open_linear(&workspace, &sample(), Some(CALLER + 2), cx);
        let (lines, top) = shown(&item, cx);
        let at = item.read_with(cx, |item, cx| item.address(top, cx));
        assert_eq!(at, Some(CALLER));
        let row = item.read_with(cx, |item, _| item.pages.row_lines(CALLER).unwrap());
        assert_eq!(row.start, top);
        assert!(lines[row.end - 1].contains("sub"), "{}", lines[row.end - 1]);
    }

    /// A click on the scrollbar shows the row holding the address at the same share of the
    /// image's range as the click is of the scrollbar's height, in code and in data alike.
    #[gpui::test]
    fn a_click_on_the_scrollbar_goes_to_the_address_under_it(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let item = open_linear(&workspace, &long_sample(), None, cx);
        assert_eq!(item.read_with(cx, |item, _| item.range), Some((TEXT, END)));
        for share in [0.25_f32, 0.75] {
            let bounds = item.read_with(cx, |item, _| item.scrollbar_bounds());
            let y = bounds.top() + bounds.size.height * share;
            let share = (y - bounds.top()) / bounds.size.height;
            let want = TEXT + super::scaled(END - TEXT, share);
            cx.simulate_click(point(bounds.center().x, y), Modifiers::none());
            settle(&item, cx);
            let (_, top) = shown(&item, cx);
            let row = item.read_with(cx, |item, _| item.pages.row_lines(want));
            assert_eq!(row.map(|r| r.start), Some(top), "{want:#x}");
        }
    }

    /// A click on a cell of the band shows the row holding the cell's first address at the
    /// top, for a cell of code and one of data no fact covers.
    #[gpui::test]
    fn a_click_on_a_band_cell_goes_to_its_first_address(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let item = open_linear(&workspace, &long_sample(), None, cx);
        let (bounds, cells) = item.read_with(cx, |item, _| {
            let (bounds, cells) = item.cells();
            (bounds, cells.to_vec())
        });
        assert!(cells.len() > 16, "{}", cells.len());
        let n = cells.len();
        for kind in [CellKind::Code, CellKind::Unexplored] {
            let ix = cells.iter().rposition(|c| c.kind == kind).unwrap();
            let share = super::share_of(from_usize(2 * ix + 1), from_usize(2 * n));
            let y = bounds.top() + bounds.size.height * share;
            assert_eq!(
                item.read_with(cx, |item, _| item.cell_at(y)),
                Some(cells[ix])
            );
            cx.simulate_click(point(bounds.center().x, y), Modifiers::none());
            settle(&item, cx);
            let (_, top) = shown(&item, cx);
            let row = item.read_with(cx, |item, _| item.pages.row_lines(cells[ix].first));
            assert_eq!(row.map(|r| r.start), Some(top), "{kind:?}");
        }
    }

    /// From a listing tab the show-in-linear key opens the linear listing with the row of
    /// the cursor's instruction on top; go to inside it moves to the row of the address it
    /// resolves, in the same tab.
    #[gpui::test]
    fn show_in_linear_and_go_to_land_on_their_instructions(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        let tab = open_tab(&workspace, &loaded, (CALLER, Form::Listing), cx);
        put_cursor(&tab, (line, 0), cx);
        cx.simulate_keystrokes("l");
        let linear = |cx: &mut VisualTestContext| {
            let item = workspace.read_with(cx, |workspace, cx| {
                workspace.active_item_as::<LinearItem>(cx)
            });
            let item = item.unwrap();
            settle(&item, cx);
            let (_, top) = shown(&item, cx);
            item.read_with(cx, |item, cx| item.address(top, cx))
        };
        assert_eq!(linear(cx), Some(va));
        let focused = workspace.update_in(cx, |workspace, window, cx| {
            let item = workspace.active_item(cx).unwrap();
            item.item_focus_handle(cx).contains_focused(window, cx)
        });
        assert!(focused, "the linear listing takes focus");
        cx.simulate_keystrokes("g");
        cx.run_until_parked();
        let picker = workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<Picker<GoToDelegate>>(cx)
        });
        picker.unwrap().update_in(cx, |picker, window, cx| {
            picker.set_query(&format!("{:#x}", CALLER + 2), window, cx);
        });
        cx.run_until_parked();
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        assert_eq!(linear(cx), Some(CALLER));
        let tabs = workspace.read_with(cx, |workspace, cx| {
            workspace
                .active_pane()
                .read(cx)
                .items_of_type::<LinearItem>()
                .count()
        });
        assert_eq!(tabs, 1);
    }

    /// Closing the binary closes its linear listing too, so no tab shows a closed binary.
    #[gpui::test]
    fn closing_the_binary_closes_its_linear_listing(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        cx.dispatch_action(ShowLinear);
        cx.run_until_parked();
        let linear = |cx: &mut VisualTestContext| {
            app.workspace.read_with(cx, |workspace, cx| {
                workspace
                    .active_pane()
                    .read(cx)
                    .items_of_type::<LinearItem>()
                    .count()
            })
        };
        assert_eq!(linear(cx), 1);
        cx.dispatch_action(CloseBinary);
        cx.run_until_parked();
        assert_eq!(linear(cx), 0);
    }

    /// Returns whether `kind` is one of the kinds the color test lists; adding a kind
    /// fails to build until it is listed.
    const fn listed(kind: CellKind) -> bool {
        match kind {
            CellKind::Code
            | CellKind::Data
            | CellKind::String
            | CellKind::Unexplored
            | CellKind::Unmapped => true,
        }
    }

    /// Each kind of cell has a color of its own in borer's dark and light themes, none the
    /// editor's background.
    #[gpui::test]
    fn each_cell_kind_has_its_own_color(cx: &mut TestAppContext) {
        let kinds = [
            CellKind::Code,
            CellKind::Data,
            CellKind::String,
            CellKind::Unexplored,
            CellKind::Unmapped,
        ];
        assert!(kinds.into_iter().all(listed));
        init(cx);
        for name in ["borer dark", "borer light"] {
            let (colors, background) = cx.update(|cx| {
                let theme = theme::ThemeRegistry::global(cx).get(name).unwrap();
                theme::GlobalTheme::update_theme(cx, theme);
                let background = cx.theme().colors().editor_background;
                (kinds.map(|kind| super::cell_color(kind, cx)), background)
            });
            for (i, color) in colors.iter().enumerate() {
                assert_ne!(*color, background, "{:?} in {name}", kinds[i]);
                let unique = colors[i + 1..].iter().all(|c| c != color);
                assert!(unique, "{:?} in {name}", kinds[i]);
            }
        }
    }

    /// A page is kept only at the seam of the kept pages, and pages that lie wholly beyond
    /// the lines kept around the top line are dropped past [`PAGES_MAX`].
    #[test]
    fn pages_join_only_at_their_seams() {
        let loaded = long_sample();
        let page = |va: u64, dir| Page::from(linear_page(&loaded, va, dir, PAGE_ROWS).unwrap());
        let mut pages = Pages::default();
        let first = page(TEXT, Dir::Next);
        let next = first.next.unwrap();
        assert!(pages.add(first.clone(), Dir::Next, 0).is_some());
        assert!(pages.add(first, Dir::Next, 0).is_none());
        let mut at = Some(next);
        while let Some(va) = at {
            let added = page(va, Dir::Next);
            at = added.next;
            let top = pages.len().saturating_sub(1);
            assert!(pages.add(added, Dir::Next, top).is_some());
            assert!(pages.0.len() <= PAGES_MAX);
        }
        let top = pages.len() - 1;
        assert!(pages.wants(top).is_none());
        let before = page(pages.0[0].first, Dir::Prev);
        let lines = before.view.lines();
        let shift = pages.add(before, Dir::Prev, 0).unwrap();
        assert_eq!(shift.moved(0), lines);
        assert!(pages.0.len() <= PAGES_MAX);
        assert!(pages.wants(0).is_some_and(|(_, dir)| dir == Dir::Prev));
        assert!(pages.wants(AHEAD_LINES).is_none());
    }
}
