//! A code tab: one function's decompile or listing view in Zed's read-only editor, in
//! Zed's center pane and nav history, colored from the engine's token kinds through the
//! theme's syntax keys.

use std::any::Any;
use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::name_of;
use borer_engine::view::{Ref, View};
use editor::actions::GoToDefinition;
use editor::display_map::{DisplayRow, DisplaySnapshot};
use editor::scroll::ScrollAnchor;
use editor::{
    DisplayPoint, Editor, EditorEvent, HighlightKey, SelectionEffects, SemanticsProvider,
    ToPoint as _,
};
use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable,
    HighlightStyle, InteractiveElement as _, IntoElement, MouseButton, MouseUpEvent,
    ParentElement as _, Pixels, Render, Reservation, SharedString, Styled as _, Subscription,
    TaskExt as _, WeakEntity, Window, div, px,
};
use language::{
    Bias, Buffer, BufferId, Capability, LineEnding, Point, ReplicaId, Rope, TextBuffer,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};
use theme_settings::ThemeSettings;
use ui::{Icon, IconName, Label, LabelCommon as _};
use workspace::item::TabContentParams;
use workspace::searchable::SearchableItemHandle;
use workspace::{Item, ItemNavHistory, Workspace};

use crate::actions::{BACK_HINT, FollowLink, Hint, ToggleListing};
use crate::binary::Binary;
use crate::card::{Card, Tone};
use crate::code_semantics::for_one_view;
use crate::code_view::{ClickOutcome, CodeLines, CodePalette, Role, resolve_ref_click};
use crate::commands;
use crate::places::{Place, open_beside};
use crate::worker::{Job, LoadedBinary, decompile_or_why, listing_blocking};

/// Fewest logical pixels a row of code is tall.
const MIN_ROW_HEIGHT_PX: f32 = 8.0;

/// Most logical pixels a row of code is tall.
const MAX_ROW_HEIGHT_PX: f32 = 64.0;

/// Returns the height of each row of code the app lists outside a code tab's editor.
///
/// That is the buffer font size times the buffer line height of Zed's settings, rounded to
/// a whole pixel and held between [`MIN_ROW_HEIGHT_PX`] and [`MAX_ROW_HEIGHT_PX`], so no
/// setting makes it vanish or endless.
///
/// # Arguments
///
/// * `cx` - Application context reading the settings.
#[must_use]
pub fn code_row_height(cx: &App) -> Pixels {
    let settings = ThemeSettings::get_global(cx);
    let height = (settings.buffer_font_size(cx) * settings.line_height()).round();
    height.clamp(px(MIN_ROW_HEIGHT_PX), px(MAX_ROW_HEIGHT_PX))
}

/// Rows a tall window shows at once; the colored rows reach this far below the top row.
const PAGE_ROWS: usize = 256;

/// Rows colored beyond the shown ones on each side, so a scroll of fewer recolors nothing.
const MARGIN_ROWS: usize = 256;

/// How a function opens in the center pane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TabMode {
    /// In Zed's preview tab, which the next preview replaces.
    Preview,
    /// In a tab of its own that stays until closed.
    Permanent,
}

/// Which view of a function a code tab shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Form {
    /// The decompiled pseudo-C, as the engine's decompile view spells it.
    Decompile,
    /// The disassembly listing with raw bytes, as the engine's listing view spells it.
    Listing,
}

impl Form {
    /// Returns the function's other view.
    #[must_use]
    pub const fn other(self) -> Self {
        match self {
            Self::Decompile => Self::Listing,
            Self::Listing => Self::Decompile,
        }
    }

    /// Builds this view of the function at `entry`; runs in the background.
    ///
    /// # Arguments
    ///
    /// * `loaded` - Binary the function belongs to.
    /// * `entry` - Entry of the function.
    ///
    /// # Errors
    ///
    /// Returns the engine's reason when it builds no view there.
    fn build(self, loaded: &LoadedBinary, entry: u64) -> Result<Arc<CodeLines>, String> {
        let view = match self {
            Self::Decompile => decompile_or_why(loaded, entry),
            Self::Listing => listing_blocking(loaded, entry),
        }?;
        Ok(Arc::new(CodeLines::new(vec![view])))
    }

    /// Returns what a tab of this view says while it builds.
    const fn building(self) -> &'static str {
        match self {
            Self::Decompile => "Decompiling...",
            Self::Listing => "Disassembling...",
        }
    }

    /// Returns what the card of a tab whose view was not built is headed with.
    const fn failed(self) -> &'static str {
        match self {
            Self::Decompile => "Decompile failed",
            Self::Listing => "Listing failed",
        }
    }
}

/// What a background build hands its tab: the lines, the text buffer over them and the
/// function's name as the engine gives it (`None` for measured lines), or the engine's
/// reason for building none.
pub(crate) type Built = Result<(Arc<CodeLines>, TextBuffer, Option<String>), String>;

/// A line to bring to the top of the tab at its next paint, where the window is at hand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Jump {
    /// Zero-based shown line.
    line: usize,
    /// Whether the cursor moves there too.
    cursor: bool,
}

/// One function's decompile or listing view, or a run of measured lines, as an item of
/// Zed's center pane.
pub struct DecompileItem {
    /// Workspace the tab opens further functions in.
    workspace: WeakEntity<Workspace>,
    /// The window's binary, whose status line the tab writes and whose load a drop starts.
    binary: Entity<Binary>,
    /// Binary the tab's function belongs to.
    loaded: Arc<LoadedBinary>,
    /// Entry of the function the tab shows, `None` for a tab of measured lines.
    entry: Option<u64>,
    /// Which view of the function the tab shows.
    form: Form,
    /// The function's name as the engine gives it, once its view is built; `None` while it
    /// builds, when none was built or for measured lines, so the tab keeps the entry.
    name: Option<SharedString>,
    /// Zed's read-only editor: over an empty buffer until the view is built, then over a
    /// read-only buffer of its text.
    editor: Entity<Editor>,
    /// Lines the tab shows, once built; row `i` of the buffer is line `i`.
    code: Option<Arc<CodeLines>>,
    /// The engine's reason the view was not built.
    failed: Option<String>,
    /// Token colors of the active theme.
    palette: CodePalette,
    /// Buffer rows whose tokens are colored now.
    painted: Range<usize>,
    /// Buffer row at the top of the editor, as it last scrolled.
    top: usize,
    /// Buffer row [`PAGE_ROWS`] display rows below the top one.
    bottom: usize,
    /// A jump not yet applied.
    pending: Option<Jump>,
    /// The pane's nav history, handed to each editor the tab shows.
    nav_history: Option<ItemNavHistory>,
    /// The editor's events.
    editor_events: Subscription,
    /// The settings and theme observers.
    _restyle: [Subscription; 2],
    /// An address to move to once the view is built ([`Self::go_to_address`]).
    waiting: Option<u64>,
    /// The background build.
    job: Job,
}

impl std::fmt::Debug for DecompileItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DecompileItem")
            .field("entry", &self.entry)
            .field("form", &self.form)
            .field("job", &self.job)
            .finish_non_exhaustive()
    }
}

/// Returns Zed's editor over `buffer`, read-only and with no scroll margin
/// ([`hold_line_at_top`]).
///
/// # Arguments
///
/// * `buffer` - The text.
/// * `window` - Window the editor is in.
/// * `cx` - Application context.
fn read_only_editor(buffer: Entity<Buffer>, window: &mut Window, cx: &mut App) -> Entity<Editor> {
    cx.new(|cx| {
        let mut editor = Editor::for_buffer(buffer, None, window, cx);
        editor.set_read_only(true);
        hold_line_at_top(&mut editor, cx);
        editor
    })
}

/// Sets `editor`'s vertical scroll margin to none, so a line a jump or the nav history puts
/// at the top stays there when the cursor moves onto it, whatever margin the settings set.
///
/// Zed's editor rereads its margin from the settings on every settings change, so a tab
/// applies this again after each one ([`DecompileItem::restyle`]).
///
/// # Arguments
///
/// * `editor` - The tab's editor.
/// * `cx` - Editor context.
fn hold_line_at_top(editor: &mut Editor, cx: &mut Context<'_, Editor>) {
    if editor.vertical_scroll_margin() != 0 {
        editor.set_vertical_scroll_margin(0, cx);
    }
}

/// Returns the text buffer of `code`: its lines joined by newlines, under buffer id `id`.
///
/// # Arguments
///
/// * `code` - The lines.
/// * `id` - Id of the buffer entity the text will be inserted as.
pub(crate) fn text_buffer(code: &CodeLines, id: BufferId) -> TextBuffer {
    let rope = Rope::from(code.text().as_str());
    TextBuffer::new_normalized(ReplicaId::LOCAL, id, LineEnding::Unix, rope)
}

/// Returns the buffer row a display row of `map` shows, past the last the last one's.
///
/// # Arguments
///
/// * `map` - The editor's display snapshot, with its folds and wraps.
/// * `display` - Zero-based display row.
pub(crate) fn buffer_row(map: &DisplaySnapshot, display: usize) -> usize {
    let row = DisplayRow(u32::try_from(display).unwrap_or(u32::MAX));
    let at = map.clip_point(DisplayPoint::new(row, 0), Bias::Left);
    usize::try_from(map.display_point_to_point(at, Bias::Left).row).unwrap_or(usize::MAX)
}

impl DecompileItem {
    /// Returns a tab for `entry` of `loaded` building its lines with `build` in the
    /// background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab opens further functions in.
    /// * `binary` - The window's binary.
    /// * `loaded` - Binary the lines come from.
    /// * `(entry, form)` - Function the tab shows, `None` for measured lines, and its view.
    /// * `build` - Builds the lines, or says why the engine built none.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub(crate) fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        (entry, form): (Option<u64>, Form),
        build: impl FnOnce() -> Result<Arc<CodeLines>, String> + Send + 'static,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let empty = cx.new(|cx| Buffer::local("", cx));
        let editor = read_only_editor(empty, window, cx);
        let mut item = Self {
            workspace,
            binary,
            loaded,
            entry,
            form,
            name: None,
            editor_events: cx.subscribe(&editor, |item, editor, event, cx| {
                item.on_editor_event(&editor, event, cx);
            }),
            editor,
            code: None,
            failed: None,
            palette: CodePalette::from_theme(cx.theme()),
            painted: 0..0,
            top: 0,
            bottom: PAGE_ROWS,
            pending: None,
            nav_history: None,
            _restyle: [
                cx.observe_global::<SettingsStore>(Self::restyle),
                cx.observe_global::<GlobalTheme>(Self::restyle),
            ],
            waiting: None,
            job: Job::default(),
        };
        item.load(build, window, cx);
        item
    }

    /// Returns a tab for one view of the function at `entry` of `loaded`, building it in
    /// the background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab opens further functions in.
    /// * `binary` - The window's binary.
    /// * `loaded` - Binary the function belongs to.
    /// * `(entry, form)` - Entry virtual address of the function, and its view.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context spawning the build.
    #[must_use]
    pub fn function(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        (entry, form): (u64, Form),
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let source = loaded.clone();
        let build = move || form.build(&source, entry);
        let shown = (Some(entry), form);
        Self::new(workspace, binary, loaded, shown, build, window, cx)
    }

    /// Builds the lines and their text buffer in the background, then shows them.
    ///
    /// The buffer's entity is reserved here, on the UI thread, so the background build can
    /// give the text buffer the id the entity will have; only the entity's insertion is
    /// left to the UI thread.
    ///
    /// # Arguments
    ///
    /// * `build` - Builds the lines, or says why the engine built none.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn load(
        &mut self,
        build: impl FnOnce() -> Result<Arc<CodeLines>, String> + Send + 'static,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let reservation = cx.reserve_entity::<Buffer>();
        let id = BufferId::from(reservation.entity_id().as_non_zero_u64());
        let (loaded, entry) = (self.loaded.clone(), self.entry);
        let label = match (entry, self.form) {
            (None, _) => "Building lines".to_owned(),
            (Some(at), Form::Decompile) => format!("Decompiling {at:#x}"),
            (Some(at), Form::Listing) => format!("Listing {at:#x}"),
        };
        let work = move || {
            let code = build()?;
            let text = text_buffer(&code, id);
            let name = entry.map(|at| name_of(&loaded.analysis, &loaded.overlay, at));
            Ok((code, text, name))
        };
        self.job
            .run_in(label, window, cx, work, |item, built, window, cx| {
                item.show(built, reservation, window, cx);
            });
    }

    /// Shows the built lines in a new editor over their buffer, or the engine's reason.
    ///
    /// # Arguments
    ///
    /// * `built` - The lines, their text buffer and the function's name, or why none were
    ///   built.
    /// * `reservation` - The buffer's reserved entity.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub(crate) fn show(
        &mut self,
        built: Built,
        reservation: Reservation<Buffer>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        match built {
            Err(why) => self.failed = Some(why),
            Ok((code, text, name)) => {
                self.name = name.map(SharedString::from);
                let buffer = cx.insert_entity(reservation, |cx| {
                    Buffer::build(text, None, Capability::ReadOnly, cx)
                });
                let focused = self.editor.focus_handle(cx).is_focused(window);
                self.editor = read_only_editor(buffer, window, cx);
                self.editor_events = cx.subscribe(&self.editor, |item, editor, event, cx| {
                    item.on_editor_event(&editor, event, cx);
                });
                if let Some(history) = self.nav_history.clone() {
                    self.editor
                        .update(cx, |editor, _| editor.set_nav_history(Some(history)));
                }
                if focused {
                    window.focus(&self.editor.focus_handle(cx), cx);
                }
                let semantics =
                    for_one_view(&code).map(|s| -> Rc<dyn SemanticsProvider> { Rc::new(s) });
                self.editor
                    .update(cx, |editor, _| editor.set_semantics_provider(semantics));
                self.code = Some(code);
                self.refresh_search(window, cx);
                self.painted = 0..0;
                self.paint(false, cx);
                if let Some(va) = self.waiting.take() {
                    self.go_to_address(va, cx);
                }
            }
        }
        cx.notify();
    }

    /// Moves to the first line that shows the instruction at `va` ([`View::line_of`]), now
    /// or once the view is built; an address no line shows moves nowhere.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    /// * `cx` - Item context.
    pub fn go_to_address(&mut self, va: u64, cx: &mut Context<'_, Self>) {
        let Some(code) = self.code.clone() else {
            self.waiting = Some(va);
            return;
        };
        if let Some((view, _)) = code.get(0)
            && let Some(line) = view.line_of(va)
        {
            self.jump_to_line(line, cx);
        }
    }

    /// Hands the new editor to the toolbar of the pane showing the tab, once the current
    /// update ends, so the buffer search finds text in the built view, not in the empty
    /// editor the toolbar was given when the tab was activated.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn refresh_search(&self, window: &Window, cx: &mut Context<'_, Self>) {
        let (workspace, item) = (self.workspace.clone(), cx.entity());
        window.defer(cx, move |window, cx| {
            let Some(pane) = workspace.upgrade().and_then(|w| w.read(cx).pane_for(&item)) else {
                return;
            };
            let pane = pane.read(cx);
            if pane
                .active_item()
                .is_some_and(|a| a.item_id() == item.entity_id())
            {
                let toolbar = pane.toolbar().clone();
                toolbar.update(cx, |toolbar, cx| {
                    toolbar.set_active_item(Some(&item), window, cx);
                });
            }
        });
    }

    /// Follows the editor's scroll: notes the buffer rows at the top and a page below it,
    /// through the display map so folds and wraps count, and colors the rows around them.
    ///
    /// # Arguments
    ///
    /// * `editor` - The tab's editor.
    /// * `event` - What the editor did.
    /// * `cx` - Item context.
    fn on_editor_event(
        &mut self,
        editor: &Entity<Editor>,
        event: &EditorEvent,
        cx: &mut Context<'_, Self>,
    ) {
        if let EditorEvent::ScrollPositionChanged { .. } = event {
            (self.top, self.bottom) = editor.update(cx, |editor, cx| {
                let top = whole_rows(editor.scroll_position(cx).y);
                let map = editor.display_snapshot(cx);
                let bottom = buffer_row(&map, top.saturating_add(PAGE_ROWS));
                (buffer_row(&map, top), bottom)
            });
            self.paint(false, cx);
        }
    }

    /// Colors the tokens of the buffer rows around the shown ones, unless they are colored
    /// already, through one update of the editor's display map and one repaint.
    ///
    /// Zed's editor keeps one list of ranges per highlight; coloring a window of rows keeps
    /// that list small however long the text is.
    ///
    /// # Arguments
    ///
    /// * `force` - Whether to recolor although the rows are colored (a theme change).
    /// * `cx` - Item context.
    fn paint(&mut self, force: bool, cx: &mut Context<'_, Self>) {
        let Some(code) = self.code.clone() else {
            return;
        };
        if !force && self.painted.start <= self.top && self.bottom <= self.painted.end {
            return;
        }
        let from = self.top.saturating_sub(MARGIN_ROWS);
        self.painted = from..self.bottom.saturating_add(MARGIN_ROWS);
        let groups = code.highlights(self.painted.clone());
        let palette = self.palette;
        self.editor.update(cx, |editor, cx| {
            let snapshot = editor.buffer().read(cx).snapshot(cx);
            editor.display_map.update(cx, |map, cx| {
                for (role, spans) in Role::ALL.into_iter().zip(groups) {
                    let ranges = spans
                        .into_iter()
                        .filter_map(|(row, span)| {
                            let row = u32::try_from(row).ok()?;
                            let at = |col: usize| Some(Point::new(row, u32::try_from(col).ok()?));
                            Some(
                                snapshot.anchor_after(at(span.start)?)
                                    ..snapshot.anchor_before(at(span.end)?),
                            )
                        })
                        .collect();
                    let style = HighlightStyle {
                        color: Some(palette.color(role)),
                        ..HighlightStyle::default()
                    };
                    map.highlight_text(role_key(role), ranges, style, false, cx);
                }
            });
            cx.notify();
        });
    }

    /// Rereads the token colors from the theme and recolors the shown rows, then, once the
    /// editor has reread its settings, takes its scroll margin away again.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn restyle(&mut self, cx: &mut Context<'_, Self>) {
        self.palette = CodePalette::from_theme(cx.theme());
        self.paint(true, cx);
        let editor = self.editor.clone();
        cx.defer(move |cx| editor.update(cx, hold_line_at_top));
        cx.notify();
    }

    /// Returns the entry of the function the tab shows, `None` for measured lines.
    #[must_use]
    pub const fn entry(&self) -> Option<u64> {
        self.entry
    }

    /// Returns the binary the tab's lines come from.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns which view of its function the tab shows.
    #[must_use]
    pub const fn form(&self) -> Form {
        self.form
    }

    /// Returns the lines the tab shows, once built.
    #[must_use]
    pub const fn code(&self) -> Option<&Arc<CodeLines>> {
        self.code.as_ref()
    }

    /// Returns the tab's editor.
    #[must_use]
    pub const fn editor(&self) -> &Entity<Editor> {
        &self.editor
    }

    /// Returns the height in logical pixels the editor was last painted at, zero before
    /// its first paint.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the editor.
    #[must_use]
    pub fn painted_height(&self, cx: &App) -> Pixels {
        self.editor
            .read(cx)
            .last_bounds()
            .map_or(px(0.0), |bounds| bounds.size.height)
    }

    /// Returns the zero-based index of the line at the top of the tab: the line a jump not
    /// yet painted asks for, else the row the editor last scrolled to.
    #[must_use]
    pub fn top_line(&self) -> usize {
        self.pending.map_or(self.top, |jump| jump.line)
    }

    /// Returns what the tab says while it shows no lines: the engine's reason a build
    /// failed under the failure's heading, the build running, or that it has no lines;
    /// `None` once lines are shown.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        let (says, tone, offers): (SharedString, _, &'static [Hint]) =
            match (&self.code, &self.failed) {
                (Some(_), _) => return None,
                (None, Some(why)) => {
                    let says = format!(
                        "{}
{why}",
                        self.form.failed()
                    );
                    (says.into(), Tone::Error, &[BACK_HINT])
                }
                (None, None) if self.job.is_running() => {
                    (self.form.building().into(), Tone::Quiet, &[])
                }
                (None, None) => ("No lines.".into(), Tone::Quiet, &[]),
            };
        Some(Card { says, tone, offers })
    }

    /// Drops the background build without its answer, so lines shown next come from the
    /// caller ([`Self::show`]).
    pub(crate) fn stop(&mut self) {
        self.job.stop();
    }

    /// Returns whether the background build is still running.
    #[must_use]
    pub fn is_decompiling(&self) -> bool {
        self.job.is_running()
    }

    /// Returns the ticket of the tab's build generation.
    #[must_use]
    pub const fn ticket(&self) -> u64 {
        self.job.ticket()
    }

    /// Returns whether build `ticket` is on screen, cancelled, or superseded.
    ///
    /// # Arguments
    ///
    /// * `ticket` - A [`Self::ticket`] value.
    #[must_use]
    pub fn decompile_settled(&self, ticket: u64) -> bool {
        self.job.settled(ticket)
    }

    /// Scrolls line `line` to the top of the tab at its next paint, without a nav-history
    /// entry, also when the line is already on screen.
    ///
    /// # Arguments
    ///
    /// * `line` - Zero-based index of the shown line.
    pub fn scroll_to(&mut self, line: usize) {
        self.pending = Some(Jump {
            line,
            cursor: false,
        });
    }

    /// Records where the tab is in the nav history, then moves the cursor to line `line`
    /// and scrolls it to the top of the tab.
    ///
    /// # Arguments
    ///
    /// * `line` - Zero-based index of the shown line.
    /// * `cx` - Item context.
    pub fn jump_to_line(&mut self, line: usize, cx: &mut Context<'_, Self>) {
        self.editor
            .update(cx, |editor, cx| editor.create_nav_history_entry(cx));
        self.pending = Some(Jump { line, cursor: true });
        cx.notify();
    }

    /// Applies a jump: moves the cursor when it asks, and anchors the editor's top at the
    /// line's buffer row, wherever folds and wraps put it on screen.
    ///
    /// # Arguments
    ///
    /// * `jump` - The jump.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn apply(&self, jump: Jump, window: &mut Window, cx: &mut Context<'_, Self>) {
        let at = Point::new(u32::try_from(jump.line).unwrap_or(u32::MAX), 0);
        self.editor.update(cx, |editor, cx| {
            if jump.cursor {
                let effects = SelectionEffects::no_scroll().nav_history(false);
                editor.change_selections(effects, window, cx, |s| s.select_ranges([at..at]));
            }
            let anchor = editor.buffer().read(cx).snapshot(cx).anchor_before(at);
            let offset = gpui::point(0.0, 0.0);
            editor.set_scroll_anchor(ScrollAnchor { anchor, offset }, window, cx);
        });
    }

    /// Returns the cursor's buffer row and byte in its row.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the editor.
    fn cursor(&self, cx: &App) -> Option<(usize, usize)> {
        let editor = self.editor.read(cx);
        let snapshot = editor.buffer().read(cx).snapshot(cx);
        let at = editor.selections.newest_anchor().head().to_point(&snapshot);
        Some((
            usize::try_from(at.row).ok()?,
            usize::try_from(at.column).ok()?,
        ))
    }

    /// Returns the address of the cursor's line as its view says, else the tab's function's
    /// entry; `None` for measured lines.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the editor.
    #[must_use]
    pub fn cursor_address(&self, cx: &App) -> Option<u64> {
        let line = self
            .cursor(cx)
            .and_then(|(row, _)| self.code.as_ref()?.get(row));
        line.and_then(|(view, line)| view.address(line))
            .or(self.entry)
    }

    /// Follows the link of the token under the cursor: a call opens its function and an
    /// import is named here, and a link into this view (a label, a branch target, a
    /// definition) goes through Zed's go to definition, which the tab's provider answers.
    ///
    /// # Arguments
    ///
    /// * `same_view` - Whether a link into this view is followed too; a ctrl-click leaves
    ///   it to Zed's own handling of the click.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn follow_cursor(
        &mut self,
        same_view: bool,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let (Some(code), Some((row, col))) = (self.code.clone(), self.cursor(cx)) else {
            return;
        };
        let Some((view, line, (_, _, Some(target)))) = code.token_at(row, col) else {
            return;
        };
        match resolve_ref_click(view, target) {
            ClickOutcome::OpenFunction(_) | ClickOutcome::Import(_) => {
                let (view, target) = (view.clone(), target.clone());
                self.follow(&view, &target, (row, line), window, cx);
            }
            ClickOutcome::ScrollToLine(_) if same_view => {
                self.editor.update(cx, |editor, cx| {
                    let definition = GoToDefinition::default();
                    editor
                        .go_to_definition(&definition, window, cx)
                        .detach_and_log_err(cx);
                });
            }
            ClickOutcome::ScrollToLine(_) | ClickOutcome::None => {}
        }
    }

    /// Follows the link `target` of line `line_ix` of `view`, shown as line `row_ix`: a
    /// function opens in the preview tab and this tab stays, an address or a definition
    /// moves to its line, an import is named in the status line.
    ///
    /// # Arguments
    ///
    /// * `view` - The view whose token is followed.
    /// * `target` - The token's link.
    /// * `(row_ix, line_ix)` - Shown line index and its line in `view`.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn follow(
        &mut self,
        view: &View,
        target: &Ref,
        (row_ix, line_ix): (usize, usize),
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        if let Some(place) = link_place(view, target, self.form) {
            self.open_beside(place, window, cx);
            return;
        }
        match resolve_ref_click(view, target) {
            ClickOutcome::ScrollToLine(def) => {
                self.jump_to_line(row_ix.saturating_sub(line_ix).saturating_add(def), cx);
            }
            ClickOutcome::Import(slot) => {
                let name = view
                    .tokens(line_ix)
                    .find(|(_, _, link)| *link == Some(target))
                    .and_then(|(span, _, _)| view.line(line_ix)?.get(span))
                    .unwrap_or("this name");
                self.say(format!("{name} is an import, at slot {slot:#x}"), cx);
            }
            ClickOutcome::OpenFunction(_) | ClickOutcome::None => {}
        }
    }

    /// Opens the function's other view, decompile or listing, at its start, keeping this
    /// tab; a tab of measured lines has no function to switch.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn toggle_listing(&self, window: &Window, cx: &mut Context<'_, Self>) {
        if let Some(entry) = self.entry {
            let form = self.form.other();
            self.open_beside(
                Place::Code {
                    entry,
                    form,
                    at: None,
                },
                window,
                cx,
            );
        }
    }

    /// Shows `status` in the status line of the tab's binary.
    ///
    /// # Arguments
    ///
    /// * `status` - The line.
    /// * `cx` - Application context.
    fn say(&self, status: String, cx: &mut App) {
        self.binary
            .update(cx, |binary, cx| binary.set_status(status, cx));
    }

    /// Keeps this tab and opens `place` in the preview tab, once the current update ends.
    ///
    /// # Arguments
    ///
    /// * `place` - What to open.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn open_beside(&self, place: Place, window: &Window, cx: &mut Context<'_, Self>) {
        let id = cx.entity_id();
        open_beside(
            &self.workspace,
            &self.binary,
            &self.loaded,
            (id, place),
            window,
            cx,
        );
    }

    /// Opens the function's graph with the block of the cursor's instruction selected,
    /// keeping this tab; a tab of measured lines has no function to graph.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn toggle_graph(&self, window: &Window, cx: &mut Context<'_, Self>) {
        let Some(entry) = self.entry else {
            return;
        };
        let at = self
            .code
            .as_ref()
            .zip(self.cursor(cx))
            .and_then(|(code, (row, _))| {
                let (view, line) = code.get(row)?;
                view.address(line)
            });
        self.open_beside(Place::Graph { entry, at }, window, cx);
    }
}

/// Returns what following link `target` of `view` opens in a tab showing `form`: the
/// called function in the same view; `None` for a link that opens no tab.
///
/// # Arguments
///
/// * `view` - The view holding the link.
/// * `target` - The link.
/// * `form` - The view the tab shows.
#[must_use]
pub fn link_place(view: &View, target: &Ref, form: Form) -> Option<Place> {
    match resolve_ref_click(view, target) {
        ClickOutcome::OpenFunction(entry) => Some(Place::Code {
            entry,
            form,
            at: None,
        }),
        ClickOutcome::ScrollToLine(_) | ClickOutcome::Import(_) | ClickOutcome::None => None,
    }
}

/// Returns the editor highlight a role's tokens are colored through.
///
/// Zed's [`HighlightKey`] is a closed enum with no key for a caller outside Zed's crates.
/// `ConsoleAnsiHighlight(usize)` is the indexed key Zed itself colors a read-only editor
/// with from outside a language (the debugger console); nothing else sets it in a code
/// tab's editor, so one index per role is the tab's alone.
///
/// # Arguments
///
/// * `role` - The role.
#[must_use]
pub const fn role_key(role: Role) -> HighlightKey {
    HighlightKey::ConsoleAnsiHighlight(role.index())
}

/// Returns the whole rows of a scroll position: its floor, zero when negative or not
/// finite.
///
/// # Arguments
///
/// * `y` - The editor's vertical scroll position, in rows.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "a floored, non-negative, finite row count"
)]
pub(crate) fn whole_rows(y: f64) -> usize {
    if y.is_finite() && y > 0.0 {
        y.floor() as usize
    } else {
        0
    }
}

/// Opens a permanent tab showing `code`, lines of `loaded` for no one function.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
/// * `loaded` - Binary the lines come from.
/// * `code` - The lines; their text buffer is built in the background.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
///
/// # Returns
///
/// The new tab.
pub fn open_lines(
    workspace: &mut Workspace,
    binary: Entity<Binary>,
    loaded: Arc<LoadedBinary>,
    code: Arc<CodeLines>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) -> Entity<DecompileItem> {
    let weak = workspace.weak_handle();
    let shown = (None, Form::Decompile);
    let build = move || Ok(code);
    let item = cx.new(|cx| DecompileItem::new(weak, binary, loaded, shown, build, window, cx));
    workspace.add_item_to_active_pane(Box::new(item.clone()), None, true, window, cx);
    item
}

impl EventEmitter<()> for DecompileItem {}

impl Focusable for DecompileItem {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.editor.focus_handle(cx)
    }
}

impl Item for DecompileItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        match (&self.name, self.entry) {
            (Some(name), _) => name.clone(),
            (None, Some(entry)) => format!("{entry:#x}").into(),
            (None, None) => format!("{} lines", self.code.as_ref().map_or(0, |c| c.len())).into(),
        }
    }

    fn tab_content(&self, params: TabContentParams, _window: &Window, cx: &App) -> AnyElement {
        Label::new(self.tab_content_text(0, cx))
            .single_line()
            .buffer_font(cx)
            .color(params.text_color())
            .when(params.preview, Label::italic)
            .into_any_element()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(match self.form {
            Form::Decompile => IconName::Code,
            Form::Listing => IconName::Hash,
        }))
    }

    crate::app_view::snapshot_tab!();

    fn set_nav_history(
        &mut self,
        history: ItemNavHistory,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.nav_history = Some(history.clone());
        self.editor
            .update(cx, |editor, _| editor.set_nav_history(Some(history)));
    }

    fn navigate(
        &mut self,
        data: Arc<dyn Any + Send>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> bool {
        self.pending = None;
        self.editor
            .update(cx, |editor, cx| editor.navigate(data, window, cx))
    }

    fn deactivated(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.editor
            .update(cx, |editor, cx| editor.deactivated(window, cx));
    }

    fn as_searchable(&self, _: &Entity<Self>, _: &App) -> Option<Box<dyn SearchableItemHandle>> {
        Some(Box::new(self.editor.clone()))
    }
}

/// Registers the code tab's actions on `workspace`: follow the link under the cursor and
/// switch between the decompile and the listing, each on the active code tab.
///
/// They stay on the workspace, not the view, so the palette offers them from a panel too.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    commands::register(
        workspace,
        binary,
        |workspace, _: &FollowLink, window, cx| {
            if let Some(item) = workspace.active_item_as::<DecompileItem>(cx) {
                item.update(cx, |item, cx| item.follow_cursor(true, window, cx));
            }
        },
    );
    commands::register(
        workspace,
        binary,
        |workspace, _: &ToggleListing, window, cx| {
            if let Some(item) = workspace.active_item_as::<DecompileItem>(cx) {
                item.update(cx, |item, cx| item.toggle_listing(window, cx));
            }
        },
    );
}

impl Render for DecompileItem {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        if let Some(jump) = self.pending.take() {
            self.apply(jump, window, cx);
        }
        let over = self.card().map(|card| card.render(cx));
        div()
            .key_context("DecompileView")
            .relative()
            .size_full()
            .on_mouse_up(
                MouseButton::Left,
                cx.listener(|item, event: &MouseUpEvent, window, cx| {
                    if event.modifiers.secondary(cx) {
                        item.follow_cursor(false, window, cx);
                    }
                }),
            )
            .child(self.editor.clone())
            .children(over.map(|over| div().absolute().inset_0().child(over)))
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::collections::BTreeSet;
    use std::ops::Range;
    use std::sync::Arc;

    use borer_engine::analysis::decompile::view::view_of;
    use borer_engine::analysis::render::{FunctionOrder, function_rows};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Feature, Program, Section};
    use borer_engine::view::{Kind, Ref, View};
    use editor::{SelectionEffects, SemanticsProvider as _, ToPoint as _};
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use language::{Point, ToPoint as _};
    use search::BufferSearchBar;
    use search::buffer_search::Deploy;
    use theme::ActiveTheme as _;
    use workspace::Workspace;

    use super::{DecompileItem, Form, TabMode, open_lines, role_key};
    use crate::actions::FollowLink;
    use crate::app_view::tests::{
        CALLEE, CALLER, binary_in, init, open, open_place, sample, shown,
    };
    use crate::code_semantics::for_one_view;
    use crate::code_view::tests::sample_program;
    use crate::code_view::{CodeLines, CodePalette, Role, describe};
    use crate::places::Place;
    use crate::worker::{LoadedBinary, decompile_blocking, listing_blocking, load_binary_blocking};

    /// Most functions of the test executable whose tabs are checked.
    const TABS: usize = 12;

    /// Opens view `form` of the function at `entry` and returns its tab once built.
    ///
    /// # Panics
    ///
    /// Panics if no code tab is active.
    pub(crate) fn open_tab(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        (entry, form): (u64, Form),
        cx: &mut VisualTestContext,
    ) -> Entity<DecompileItem> {
        let place = Place::Code {
            entry,
            form,
            at: None,
        };
        open_place(workspace, loaded, place, TabMode::Preview, cx);
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<DecompileItem>(cx)
            })
            .unwrap()
    }

    /// Each tab's buffer holds its view's text byte for byte, decompile and listing alike,
    /// for the first functions of the test executable.
    ///
    /// # Panics
    ///
    /// Panics if a tab's text differs from its view's spelling.
    #[gpui::test]
    fn every_tab_holds_its_view_byte_for_byte(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let exe = std::env::current_exe().unwrap();
        let loaded = load_binary_blocking(exe).unwrap();
        let entries: Vec<u64> = loaded
            .initial_rows
            .rows
            .iter()
            .take(TABS)
            .map(|r| r.entry)
            .collect();
        assert!(!entries.is_empty());
        for entry in entries {
            for form in [Form::Decompile, Form::Listing] {
                let want = match form {
                    Form::Decompile => decompile_blocking(&loaded, entry),
                    Form::Listing => listing_blocking(&loaded, entry).ok(),
                }
                .map(|view| view.spell());
                let tab = open_tab(&workspace, &loaded, (entry, form), cx);
                let got = tab.read_with(cx, |item, cx| {
                    item.code()?;
                    Some(item.editor().read(cx).text(cx))
                });
                assert_eq!(got, want, "{form:?} of {entry:#x}");
            }
        }
    }

    /// Returns every colored span of `tab`'s editor, as its row, bytes and role's index,
    /// checking each highlight's color and that none is underlined.
    ///
    /// # Panics
    ///
    /// Panics if a highlight spans rows, is underlined or has another role's color.
    fn colored(tab: &Entity<DecompileItem>, cx: &mut VisualTestContext) -> BTreeSet<Span> {
        tab.read_with(cx, |item, cx| {
            let palette = CodePalette::from_theme(cx.theme());
            let editor = item.editor().read(cx);
            let snapshot = editor.buffer().read(cx).snapshot(cx);
            let mut got = BTreeSet::new();
            for role in Role::ALL {
                let Some((style, ranges)) = editor.text_highlights(role_key(role), cx) else {
                    continue;
                };
                assert!(style.underline.is_none());
                assert_eq!(style.color, Some(palette.color(role)));
                for range in ranges {
                    let (a, b) = (
                        range.start.to_point(&snapshot),
                        range.end.to_point(&snapshot),
                    );
                    assert_eq!(a.row, b.row);
                    let wide = |n: u32| usize::try_from(n).unwrap();
                    got.insert((wide(a.row), wide(a.column), wide(b.column), role.index()));
                }
            }
            got
        })
    }

    /// One colored span: its row, its first byte, one past its last, its role's index.
    type Span = (usize, usize, usize, usize);

    /// Returns the span of every token of `tab`'s rows `rows` that has a role.
    fn tokens(
        tab: &Entity<DecompileItem>,
        rows: Range<usize>,
        cx: &mut VisualTestContext,
    ) -> BTreeSet<Span> {
        tab.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            let mut want = BTreeSet::new();
            for row in rows.start..rows.end.min(code.len()) {
                let (view, line) = code.get(row).unwrap();
                for (span, kind, link) in view.tokens(line) {
                    if let Some(role) = Role::of(kind, link) {
                        want.insert((row, span.start, span.end, role.index()));
                    }
                }
            }
            want
        })
    }

    /// Every token but whitespace is colored over exactly its bytes, in the color its role
    /// takes and with no underline, in a decompile tab and in a listing tab.
    ///
    /// # Panics
    ///
    /// Panics if a highlight is missing, extra, shifted or in another color.
    #[gpui::test]
    fn every_token_is_colored_over_its_own_bytes(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        for form in [Form::Decompile, Form::Listing] {
            let tab = open_tab(&workspace, &loaded, (CALLER, form), cx);
            let want = tokens(&tab, 0..usize::MAX, cx);
            assert!(!want.is_empty());
            assert_eq!(colored(&tab, cx), want, "{form:?}");
        }
    }

    /// With rows folded above it, a jump still puts its buffer row at the top, and that
    /// row's tokens are colored.
    ///
    /// # Panics
    ///
    /// Panics if the fold shifts the jump or the coloring by display rows.
    #[gpui::test]
    fn a_fold_above_a_line_moves_neither_jump_nor_color(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let tab = open_tab(&workspace, &sample(), (CALLER, Form::Listing), cx);
        let lines = tab.read_with(cx, |item, _| item.code().unwrap().len());
        let target = lines - 2;
        assert!(target > 6);
        tab.update_in(cx, |item, window, cx| {
            item.editor().update(cx, |editor, cx| {
                editor.fold_ranges(vec![Point::new(1, 0)..Point::new(5, 0)], false, window, cx);
            });
            item.jump_to_line(target, cx);
        });
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.run_until_parked();
        assert_eq!(tab.read_with(cx, |item, _| item.top_line()), target);
        let row = tokens(&tab, target..target + 1, cx);
        assert!(!row.is_empty());
        assert!(row.is_subset(&colored(&tab, cx)));
    }

    /// A person's scroll margin does not reach a code tab's editor, before or after a
    /// settings change, so a line put at the top stays at the top.
    ///
    /// # Panics
    ///
    /// Panics if the editor keeps a margin.
    #[gpui::test]
    fn a_code_tab_keeps_no_scroll_margin(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let tab = open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        let margin = |cx: &mut VisualTestContext| {
            tab.read_with(cx, |item, cx| {
                item.editor().read(cx).vertical_scroll_margin()
            })
        };
        assert_eq!(margin(cx), 0);
        cx.update(|_, cx| {
            gpui::BorrowAppContext::update_global(cx, |store: &mut settings::SettingsStore, cx| {
                store.update_user_settings(cx, |content| {
                    content.editor.vertical_scroll_margin = Some(5.0);
                });
            });
        });
        cx.run_until_parked();
        assert_eq!(margin(cx), 0);
    }

    /// A listing the engine cannot build says the engine's reason, not that no function
    /// starts there.
    ///
    /// # Panics
    ///
    /// Panics if the tab says anything else.
    #[gpui::test]
    fn a_listing_that_cannot_be_built_says_why(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let sections = vec![Section::mapped(".text", 0x1000, 0, 0x10, false, true)];
        let program = Program::raw(
            vec![0xc3; 0x10],
            Arch::Unknown,
            0x1000,
            Some(0x1000),
            sections,
        );
        let why = program.isa_for(Feature::Disasm).unwrap_err();
        let analysis = Analysis::compute(&program);
        let overlay = Overlay::default();
        let rows = function_rows(
            &analysis,
            &overlay,
            None,
            FunctionOrder::Address,
            0,
            usize::MAX,
        );
        let loaded = Arc::new(LoadedBinary {
            path: "unknown.bin".into(),
            program: Arc::new(program),
            analysis: Arc::new(analysis),
            overlay: Arc::new(overlay),
            initial_rows: Arc::new(rows),
        });
        let tab = open_tab(&workspace, &loaded, (0x1000, Form::Listing), cx);
        let said = tab.read_with(cx, |item, _| item.failed.clone());
        assert_eq!(said, Some(why));
    }
    /// Puts the cursor of `tab` at byte `col` of row `row`.
    pub(crate) fn put_cursor(
        tab: &Entity<DecompileItem>,
        (row, col): (usize, usize),
        cx: &mut VisualTestContext,
    ) {
        let at = Point::new(u32::try_from(row).unwrap(), u32::try_from(col).unwrap());
        tab.update_in(cx, |item, window, cx| {
            item.editor().update(cx, |editor, cx| {
                editor.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
                    s.select_ranges([at..at]);
                });
            });
        });
    }

    /// Returns the first token of `tab`'s lines whose link `pick` accepts, given the
    /// token's view, its line in that view and the link: its row, its byte span and its
    /// link.
    fn find_link(
        tab: &Entity<DecompileItem>,
        pick: impl Fn(&View, usize, &Ref) -> bool,
        cx: &mut VisualTestContext,
    ) -> (usize, Range<usize>, Ref) {
        tab.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            (0..code.len())
                .find_map(|row| {
                    let (view, line) = code.get(row)?;
                    view.tokens(line).find_map(|(span, _, link)| {
                        let link = link.filter(|link| pick(view, line, link))?;
                        Some((row, span, link.clone()))
                    })
                })
                .unwrap()
        })
    }

    /// Enter on a call opens its callee, and following a link into the view moves the
    /// cursor, through Zed's go to definition, to a listing's branch target and to the line
    /// that defines a label.
    ///
    /// # Panics
    ///
    /// Panics if a link leads anywhere else.
    #[gpui::test]
    fn following_a_link_goes_where_the_view_says(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let caller = open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        let (row, span, _) = find_link(&caller, |_, _, l| *l == Ref::Function(CALLEE), cx);
        put_cursor(&caller, (row, span.start), cx);
        cx.simulate_keystrokes("enter");
        cx.run_until_parked();
        let shown = workspace.read_with(cx, |workspace, cx| {
            let item = workspace.active_item_as::<DecompileItem>(cx)?;
            let item = item.read(cx);
            Some((item.entry()?, item.form()))
        });
        assert_eq!(shown, Some((CALLEE, Form::Decompile)));
        let listing = open_tab(&workspace, &loaded, (CALLER, Form::Listing), cx);
        let operand = |view: &View, line: usize, link: &Ref| match link {
            Ref::Address(va) => view.line_of(*va).is_some_and(|to| to != line),
            _ => false,
        };
        let (row, span, target) = find_link(&listing, operand, cx);
        let want = listing.read_with(cx, |item, _| match target {
            Ref::Address(va) => item.code().unwrap().get(0).unwrap().0.line_of(va),
            _ => None,
        });
        assert!(want.is_some_and(|line| line != row));
        put_cursor(&listing, (row, span.end), cx);
        cx.dispatch_action(FollowLink);
        cx.run_until_parked();
        let at = listing.read_with(cx, |item, cx| item.cursor(cx));
        assert_eq!(at.map(|(row, _)| row), want);
        let (program, analysis, overlay) = sample_program();
        let text = "void sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return;\n}\n";
        let goto = Arc::new(view_of(&program, &analysis, &overlay, CALLER, text).unwrap());
        let code = Arc::new(CodeLines::new(vec![goto.clone()]));
        let binary = binary_in(&workspace, cx);
        let lines = workspace.update_in(cx, |workspace, window, cx| {
            open_lines(workspace, binary, loaded.clone(), code.clone(), window, cx)
        });
        cx.run_until_parked();
        put_cursor(&lines, (1, "    goto L_".len()), cx);
        cx.dispatch_action(FollowLink);
        cx.run_until_parked();
        let label = goto.definition(&Ref::Address(CALLER));
        assert_eq!(label, Some(2));
        let at = lines.read_with(cx, |item, cx| item.cursor(cx));
        assert_eq!(at.map(|(row, _)| row), label);
    }

    /// The hover over a call says what the view says of it, and the document highlights of
    /// a call are every use of its callee the view shows.
    ///
    /// # Panics
    ///
    /// Panics if the hover or the highlights say anything the view does not.
    #[gpui::test]
    async fn hover_and_uses_come_from_the_view(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let tab = open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        let callee = Ref::Function(CALLEE);
        let (row, span, _) = find_link(&tab, |_, _, l| *l == callee, cx);
        let (code, buffer) = tab.read_with(cx, |item, cx| {
            let buffer = item.editor().read(cx).buffer().read(cx).as_singleton();
            (item.code().unwrap().clone(), buffer.unwrap())
        });
        let provider = for_one_view(&code).unwrap();
        let at = Point::new(
            u32::try_from(row).unwrap(),
            u32::try_from(span.start).unwrap(),
        );
        let anchor = buffer.read_with(cx, |buffer, _| buffer.snapshot().anchor_after(at));
        let hover = cx.update(|_, cx| provider.hover(&buffer, anchor, cx));
        let hover = hover.unwrap().await.unwrap().remove(0);
        let (view, line) = code.get(row).unwrap();
        let name = &view.line(line).unwrap()[span.clone()];
        let said = describe(name, Kind::Function, Some(&callee));
        assert_eq!(hover.contents[0].text, said);
        let uses = cx.update(|_, cx| provider.document_highlights(&buffer, anchor, cx));
        let uses = uses.unwrap().await.unwrap();
        let points = buffer.read_with(cx, |buffer, _| {
            let snapshot = buffer.snapshot();
            let wide = |n: u32| usize::try_from(n).unwrap();
            uses.iter()
                .map(|h| {
                    let a = h.range.start.to_point(&snapshot);
                    let b = h.range.end.to_point(&snapshot);
                    (wide(a.row), wide(a.column)..wide(b.column))
                })
                .collect::<Vec<_>>()
        });
        assert!(points.len() >= 2);
        assert_eq!(points, view.uses(&callee).0);
    }

    /// Returns the function, view and top line of the active code tab.
    pub(crate) fn active(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Option<(u64, Form, usize)> {
        let (entry, top) = shown(workspace, cx)?;
        let form = workspace.read_with(cx, |workspace, cx| {
            Some(
                workspace
                    .active_item_as::<DecompileItem>(cx)?
                    .read(cx)
                    .form(),
            )
        })?;
        Some((entry, form, top))
    }

    /// Tab opens the function's listing at its start, and Tab again comes back to its
    /// decompile.
    ///
    /// # Panics
    ///
    /// Panics if a toggle shows another function, view or line.
    #[gpui::test]
    fn the_toggle_switches_between_decompile_and_listing(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        for want in [Form::Listing, Form::Decompile] {
            cx.simulate_keystrokes("tab");
            assert_eq!(active(&workspace, cx), Some((CALLER, want, 0)));
        }
    }

    /// Returns the address of the caller's fourth instruction and the line of its listing
    /// that shows it.
    ///
    /// # Panics
    ///
    /// Panics if the listing does not build or holds fewer instructions.
    pub(crate) fn fourth_instruction(loaded: &LoadedBinary) -> (u64, usize) {
        let view = listing_blocking(loaded, CALLER).unwrap();
        (0..view.lines())
            .filter_map(|line| Some((view.address(line)?, line)))
            .nth(3)
            .unwrap()
    }

    /// A listing opened at an address puts the line that shows that instruction at the top.
    ///
    /// # Panics
    ///
    /// Panics if the listing opens at another line.
    #[gpui::test]
    fn a_listing_opens_at_the_line_of_its_address(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        let place = Place::Code {
            entry: CALLER,
            form: Form::Listing,
            at: Some(va),
        };
        open_place(&workspace, &loaded, place, TabMode::Preview, cx);
        assert_eq!(active(&workspace, cx), Some((CALLER, Form::Listing, line)));
    }

    /// Zed's buffer search opens over a code tab and finds every place its text spells the
    /// query.
    ///
    /// # Panics
    ///
    /// Panics if the bar does not open or finds other places than the text holds.
    #[gpui::test]
    fn find_marks_every_place_the_text_spells_the_query(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let tab = open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        cx.dispatch_action(Deploy::find());
        cx.run_until_parked();
        let bar = workspace
            .read_with(cx, |workspace, cx| {
                let pane = workspace.active_pane().read(cx);
                pane.toolbar().read(cx).item_of_type::<BufferSearchBar>()
            })
            .unwrap();
        assert!(bar.read_with(cx, |bar, _| !bar.is_dismissed()));
        let query = "sub_1030";
        let done = bar.update_in(cx, |bar, window, cx| {
            bar.search(query, None, false, window, cx)
        });
        cx.run_until_parked();
        drop(done);
        let found = tab.update(cx, |item, cx| {
            item.editor()
                .update(cx, |editor, cx| editor.search_background_highlights(cx))
        });
        let text = tab.read_with(cx, |item, cx| item.editor().read(cx).text(cx));
        let want: Vec<_> = text
            .lines()
            .enumerate()
            .flat_map(|(row, line)| {
                line.match_indices(query).map(move |(col, _)| {
                    let at = |c: usize| {
                        Point::new(u32::try_from(row).unwrap(), u32::try_from(c).unwrap())
                    };
                    at(col)..at(col + query.len())
                })
            })
            .collect();
        assert!(!want.is_empty());
        assert_eq!(found, want);
    }

    /// Following an import's link names it in the window's status line, from inside the
    /// workspace's own update, as Enter over an import does.
    #[gpui::test]
    fn following_an_import_names_it_in_the_status_line(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let tab = open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        let view = tab.read_with(cx, |item, _| item.code().unwrap().get(0).unwrap().0.clone());
        workspace.update_in(cx, |_, window, cx| {
            tab.update(cx, |item, cx| {
                item.follow(&view, &Ref::Import(0x2000), (0, 0), window, cx);
            });
        });
        let status = app
            .binary
            .read_with(cx, |binary, _| binary.status().to_owned());
        assert!(status.ends_with("is an import, at slot 0x2000"), "{status}");
    }
}
