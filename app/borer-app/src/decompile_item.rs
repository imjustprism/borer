//! A decompile tab: one function's view of the engine's tokens in Zed's center pane, on
//! Zed's nav history, whose linked tokens open their function or scroll to their line.

use std::any::Any;
use std::ops::Range;
use std::sync::Arc;

use borer_engine::analysis::name_of;
use borer_engine::view::{Ref, View};
use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, AppContext as _, Context, Div, Entity, EventEmitter, FocusHandle, Focusable,
    Font, FontWeight, InteractiveElement as _, InteractiveText, IntoElement, ParentElement as _,
    Pixels, Render, ScrollStrategy, SharedString, Styled as _, StyledText, Subscription, Task,
    UniformListScrollHandle, WeakEntity, Window, div, px, uniform_list,
};
use settings::{Settings as _, SettingsStore};
use theme::{ActiveTheme as _, GlobalTheme};
use theme_settings::ThemeSettings;
use ui::{Color, Icon, IconName, Label, LabelCommon as _, v_flex};
use workspace::item::TabContentParams;
use workspace::{Item, ItemNavHistory, Pane, Workspace};

use crate::actions::{BACK_HINT, hint_row};
use crate::app_view::open_dropped;
use crate::code_view::{ClickOutcome, CodeLines, CodePalette, resolve_ref_click, style_view_line};
use crate::worker::{LoadedBinary, TaskEpoch, decompile_blocking, spawn_engine};

/// Fewest logical pixels a line row of a decompile tab is tall.
const MIN_ROW_HEIGHT_PX: f32 = 8.0;

/// Most logical pixels a line row of a decompile tab is tall.
const MAX_ROW_HEIGHT_PX: f32 = 64.0;

/// Returns the height of each line row of a decompile tab.
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

/// What a decompile tab paints its lines with, read from the theme and the settings.
#[derive(Debug, Clone)]
pub(crate) struct CodeStyle {
    /// Token colors of the active theme.
    pub(crate) palette: CodePalette,
    /// The buffer font.
    pub(crate) font: Font,
    /// The buffer font size.
    pub(crate) size: Pixels,
    /// Height of each line row, from [`code_row_height`].
    pub(crate) row_height: Pixels,
}

impl CodeStyle {
    /// Returns the style the active theme and the settings give.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the theme and the settings.
    fn read(cx: &App) -> Self {
        let settings = ThemeSettings::get_global(cx);
        Self {
            palette: CodePalette::from_theme(cx.theme()),
            font: settings.buffer_font.clone(),
            size: settings.buffer_font_size(cx),
            row_height: code_row_height(cx),
        }
    }
}

/// Corner radius in logical pixels of the card a failed decompile shows.
const CARD_RADIUS_PX: f32 = 6.0;

/// Left padding in logical pixels before the text of each decompile line.
pub const CODE_PAD_PX: f32 = 8.0;

/// How a function opens in the center pane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TabMode {
    /// In Zed's preview tab, which the next preview replaces.
    Preview,
    /// In a tab of its own that stays until closed.
    Permanent,
}

/// Where a decompile tab was when it went into the nav history.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NavData {
    /// Entry of the function the tab shows, `None` for a tab of measured lines.
    entry: Option<u64>,
    /// Zero-based index of the line at the top of the tab.
    top: usize,
}

/// One function's decompile view, or a run of measured lines, as an item of Zed's center pane.
pub struct DecompileItem {
    /// Workspace the tab opens further functions in.
    workspace: WeakEntity<Workspace>,
    /// Binary the tab's function belongs to.
    loaded: Arc<LoadedBinary>,
    /// Entry of the function the tab shows, `None` for a tab of measured lines.
    entry: Option<u64>,
    /// The function's name as the engine gives it, once its decompile is in; `None` while
    /// it runs or when the engine decompiled nothing, so the tab keeps the entry.
    name: Option<SharedString>,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// Lines the tab shows, once decompiled.
    code: Option<Arc<CodeLines>>,
    /// Scroll handle of the virtualized line list.
    scroll: UniformListScrollHandle,
    /// Colors, font and row height, rebuilt when the theme or the settings change.
    style: CodeStyle,
    /// Rebuilds [`Self::style`] on a settings or theme change.
    _restyle: [Subscription; 2],
    /// Generation and cancel flag of the background decompile.
    epoch: TaskEpoch,
    /// Whether the background decompile is still running.
    decompiling: bool,
    /// The pane's nav history, set when the tab is added to a pane.
    nav_history: Option<ItemNavHistory>,
    /// The background decompile.
    task: Option<Task<()>>,
}

impl std::fmt::Debug for DecompileItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DecompileItem")
            .field("entry", &self.entry)
            .field("decompiling", &self.decompiling)
            .finish_non_exhaustive()
    }
}

impl Drop for DecompileItem {
    fn drop(&mut self) {
        self.epoch.invalidate();
    }
}

impl DecompileItem {
    /// Returns a tab for `entry` of `loaded` showing `code`.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab opens further functions in.
    /// * `loaded` - Binary the lines come from.
    /// * `entry` - Function the tab shows, `None` for measured lines.
    /// * `code` - Lines to show, `None` until decompiled.
    /// * `cx` - Item context.
    fn new(
        workspace: WeakEntity<Workspace>,
        loaded: Arc<LoadedBinary>,
        entry: Option<u64>,
        code: Option<Arc<CodeLines>>,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        Self {
            workspace,
            loaded,
            entry,
            name: None,
            focus_handle: cx.focus_handle(),
            code,
            scroll: UniformListScrollHandle::new(),
            style: CodeStyle::read(cx),
            _restyle: [
                cx.observe_global::<SettingsStore>(Self::restyle),
                cx.observe_global::<GlobalTheme>(Self::restyle),
            ],
            epoch: TaskEpoch::new(),
            decompiling: false,
            nav_history: None,
            task: None,
        }
    }

    /// Returns a tab for the function at `entry` of `loaded`, decompiling it in the background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab opens further functions in.
    /// * `loaded` - Binary the function belongs to.
    /// * `entry` - Entry virtual address of the function.
    /// * `cx` - Item context spawning the decompile.
    #[must_use]
    pub fn function(
        workspace: WeakEntity<Workspace>,
        loaded: Arc<LoadedBinary>,
        entry: u64,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let mut item = Self::new(workspace, loaded, Some(entry), None, cx);
        let (ticket, worker_cancel) = item.epoch.begin();
        let check_cancel = worker_cancel.clone();
        let loaded = item.loaded.clone();
        item.decompiling = true;
        let bg = spawn_engine(cx, move || {
            worker_cancel.within(|| {
                let view = decompile_blocking(&loaded, entry);
                let name = view
                    .is_some()
                    .then(|| name_of(&loaded.analysis, &loaded.overlay, entry));
                (view, name)
            })
        });
        item.task = Some(cx.spawn(async move |this, cx| {
            let (built, name) = bg.await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |item, cx| {
                if item.epoch.is_current(ticket, &check_cancel) {
                    item.decompiling = false;
                    item.name = name.map(SharedString::from);
                    item.code = built.map(|view| Arc::new(CodeLines::new(vec![view])));
                    cx.notify();
                }
            });
        }));
        item
    }

    /// Rereads the tab's style from the theme and the settings and repaints it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn restyle(&mut self, cx: &mut Context<'_, Self>) {
        self.style = CodeStyle::read(cx);
        cx.notify();
    }

    /// Returns what the tab paints its lines with.
    #[must_use]
    pub(crate) const fn style(&self) -> &CodeStyle {
        &self.style
    }

    /// Returns the entry of the function the tab shows, `None` for measured lines.
    #[must_use]
    pub const fn entry(&self) -> Option<u64> {
        self.entry
    }

    /// Returns the lines the tab shows, once decompiled.
    #[must_use]
    pub const fn code(&self) -> Option<&Arc<CodeLines>> {
        self.code.as_ref()
    }

    /// Returns the scroll handle of the tab's line list.
    #[must_use]
    pub const fn code_scroll(&self) -> &UniformListScrollHandle {
        &self.scroll
    }

    /// Returns the height in logical pixels the line list was last painted at, zero before
    /// its first paint.
    #[must_use]
    pub fn painted_height(&self) -> Pixels {
        self.scroll.0.borrow().base_handle.bounds().size.height
    }

    /// Returns the zero-based index of the line at the top of the tab: the line a scroll
    /// not yet laid out asks for, else the first line the scroll offset shows whole or in
    /// part.
    #[must_use]
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "a floored, non-negative, finite row count of a laid-out list"
    )]
    pub fn top_line(&self) -> usize {
        let state = self.scroll.0.borrow();
        if let Some(deferred) = &state.deferred_scroll_to_item {
            return deferred.item_index;
        }
        let rows = (-state.base_handle.offset().y / self.style.row_height).floor();
        if rows.is_finite() && rows > 0.0 {
            rows as usize
        } else {
            0
        }
    }

    /// Returns whether the background decompile is still running.
    #[must_use]
    pub const fn is_decompiling(&self) -> bool {
        self.decompiling
    }

    /// Returns the ticket of the tab's decompile generation.
    #[must_use]
    pub const fn ticket(&self) -> u64 {
        self.epoch.seq()
    }

    /// Returns whether decompile `ticket` is on screen, cancelled, or superseded.
    ///
    /// # Arguments
    ///
    /// * `ticket` - A [`Self::ticket`] value.
    #[must_use]
    pub const fn decompile_settled(&self, ticket: u64) -> bool {
        !self.decompiling || self.epoch.seq() > ticket
    }

    /// Scrolls line `line` to the top of the tab without a nav-history entry, also when
    /// the line is already on screen.
    ///
    /// # Arguments
    ///
    /// * `line` - Zero-based index of the shown line.
    pub fn scroll_to(&self, line: usize) {
        self.scroll.scroll_to_item_strict(line, ScrollStrategy::Top);
    }

    /// Records where the tab is in the nav history, then scrolls line `line` to its top.
    ///
    /// # Arguments
    ///
    /// * `line` - Zero-based index of the shown line.
    /// * `cx` - Item context.
    pub fn jump_to_line(&mut self, line: usize, cx: &mut Context<'_, Self>) {
        self.push_location(cx);
        self.scroll_to(line);
        cx.notify();
    }

    /// Follows the link `target` of line `line_ix` of `view`, shown as line `row_ix`: a
    /// function opens in the preview tab and this tab stays, a label scrolls to its line.
    ///
    /// # Arguments
    ///
    /// * `view` - The view whose token was clicked.
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
        match resolve_ref_click(view, target) {
            ClickOutcome::OpenFunction(callee) => self.open_callee(callee, window, cx),
            ClickOutcome::ScrollToLine(def) => {
                self.jump_to_line(row_ix.saturating_sub(line_ix).saturating_add(def), cx);
            }
            ClickOutcome::None => {}
        }
    }

    /// Keeps this tab and opens `callee` in the preview tab, once the click's update ends.
    ///
    /// # Arguments
    ///
    /// * `callee` - Entry of the function to open.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn open_callee(&self, callee: u64, window: &Window, cx: &mut Context<'_, Self>) {
        let (workspace, loaded, id) = (self.workspace.clone(), self.loaded.clone(), cx.entity_id());
        window.defer(cx, move |window, cx| {
            let Some(workspace) = workspace.upgrade() else {
                return;
            };
            workspace.update(cx, |workspace, cx| {
                workspace
                    .active_pane()
                    .update(cx, |pane, _| pane.unpreview_item_if_preview(id));
                open_function(
                    workspace,
                    loaded,
                    callee,
                    TabMode::Preview,
                    true,
                    window,
                    cx,
                );
            });
        });
    }

    /// Pushes the tab's function and top line onto the pane's nav history.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn push_location(&mut self, cx: &mut Context<'_, Self>) {
        let top = self.top_line();
        let data = NavData {
            entry: self.entry,
            top,
        };
        if let Some(history) = self.nav_history.as_mut() {
            history.push(Some(data), u32::try_from(top).ok(), cx);
        }
    }

    /// Builds the visible rows in `range` of the tab's line list.
    ///
    /// # Arguments
    ///
    /// * `range` - Visible shown-line index range requested by `uniform_list`.
    /// * `_window` - Window painting the rows.
    /// * `cx` - Item context.
    ///
    /// # Returns
    ///
    /// Styled line elements covering `range`.
    fn render_rows(
        &mut self,
        range: Range<usize>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Vec<AnyElement> {
        let Some(code) = self.code.clone() else {
            return Vec::new();
        };
        let CodeStyle {
            palette,
            font,
            row_height,
            ..
        } = &self.style;
        let weak = cx.entity().downgrade();
        range
            .filter_map(|ix| {
                let (view, line_ix) = code.get(ix)?;
                let styled = style_view_line(view, line_ix, font, palette);
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
                        .h(*row_height)
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

/// Wraps one [`StyledText`] row in an [`InteractiveText`] that follows its links.
///
/// # Arguments
///
/// * `(row_ix, line_ix)` - Shown line index (also the element identifier) and its line in `view`.
/// * `styled_text` - Highlighted line text and runs.
/// * `click_ranges` - UTF-8 byte ranges of clickable tokens.
/// * `click_refs` - Corroborated [`Ref`] targets matching `click_ranges`.
/// * `view` - The view the line comes from.
/// * `entity` - Weak handle to the tab.
///
/// # Returns
///
/// [`InteractiveText`] element wired to [`DecompileItem::follow`].
fn build_interactive_line(
    (row_ix, line_ix): (usize, usize),
    styled_text: StyledText,
    click_ranges: Vec<Range<usize>>,
    click_refs: Vec<Ref>,
    view: Arc<View>,
    entity: WeakEntity<DecompileItem>,
) -> InteractiveText {
    let line = InteractiveText::new(("code-line", row_ix), styled_text);
    if click_ranges.is_empty() {
        return line;
    }
    line.on_click(click_ranges, move |range_ix, window, cx| {
        let (Some(target), Some(entity)) = (click_refs.get(range_ix), entity.upgrade()) else {
            return;
        };
        entity.update(cx, |item, cx| {
            item.follow(&view, target, (row_ix, line_ix), window, cx);
        });
    })
}

/// Returns what a tab says when the engine decompiles nothing at `entry`, true of every
/// reason it can have: no function there, no lifter for the code, an answer too large.
///
/// # Arguments
///
/// * `entry` - Entry the tab asked the engine for.
#[must_use]
pub fn no_decompile(entry: u64) -> String {
    format!("borer has no decompile for {entry:#x}")
}

/// Returns the card a tab shows when the engine decompiles nothing at `entry`.
///
/// It is a raised card whose label alone is in the error color, then what is true of every
/// way the engine answers nothing, then the way back.
///
/// # Arguments
///
/// * `entry` - Entry the tab asked the engine for.
/// * `cx` - Application context reading the theme and the keymap.
fn failure_card(entry: u64, cx: &App) -> Div {
    let colors = cx.theme().colors();
    v_flex()
        .m(px(12.0))
        .p(px(8.0))
        .gap_1()
        .rounded(px(CARD_RADIUS_PX))
        .border_1()
        .border_color(colors.border)
        .bg(colors.surface_background)
        .font(ThemeSettings::get_global(cx).ui_font.clone())
        .child(
            Label::new("Decompile failed")
                .weight(FontWeight::SEMIBOLD)
                .color(Color::Error),
        )
        .child(
            Label::new(no_decompile(entry))
                .buffer_font(cx)
                .color(Color::Muted),
        )
        .child(hint_row(BACK_HINT, cx))
}

/// Shows the function at `entry` of `loaded` in the workspace's active pane: activates its
/// tab when one is open, else opens one as `mode` says.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `loaded` - Binary the function belongs to.
/// * `entry` - Entry virtual address of the function.
/// * `mode` - Whether a new tab is the preview tab or a permanent one.
/// * `focus` - Whether the tab takes keyboard focus.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn open_function(
    workspace: &mut Workspace,
    loaded: Arc<LoadedBinary>,
    entry: u64,
    mode: TabMode,
    focus: bool,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let weak = workspace.weak_handle();
    let pane = workspace.active_pane().clone();
    let existing = pane.read(cx).items_of_type::<DecompileItem>().find(|item| {
        let item = item.read(cx);
        item.entry == Some(entry) && Arc::ptr_eq(&item.loaded, &loaded)
    });
    pane.update(cx, |pane, cx| {
        if let Some(item) = existing {
            if mode == TabMode::Permanent {
                pane.unpreview_item_if_preview(item.entity_id());
            }
            if let Some(ix) = pane.index_for_item(&item) {
                pane.activate_item(ix, true, focus, window, cx);
            }
            return;
        }
        let at = match mode {
            TabMode::Preview => pane.close_current_preview_item(window, cx),
            TabMode::Permanent => None,
        };
        let item = cx.new(|cx| DecompileItem::function(weak, loaded, entry, cx));
        let id = item.entity_id();
        pane.add_item(Box::new(item), true, focus, at, window, cx);
        if mode == TabMode::Preview {
            pane.replace_preview_item_id(id, window, cx);
        }
    });
}

/// Opens a permanent tab showing `code`, lines of `loaded` for no one function.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `loaded` - Binary the lines come from.
/// * `code` - The lines.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
///
/// # Returns
///
/// The new tab.
pub fn open_lines(
    workspace: &mut Workspace,
    loaded: Arc<LoadedBinary>,
    code: Arc<CodeLines>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) -> Entity<DecompileItem> {
    let weak = workspace.weak_handle();
    let item = cx.new(|cx| DecompileItem::new(weak, loaded, None, Some(code), cx));
    workspace.add_item_to_active_pane(Box::new(item.clone()), None, true, window, cx);
    item
}

impl EventEmitter<()> for DecompileItem {}

impl Focusable for DecompileItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
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
        Some(Icon::new(IconName::Code))
    }

    fn tab_tooltip_text(&self, _cx: &App) -> Option<SharedString> {
        Some(self.loaded.path.display().to_string().into())
    }

    fn set_nav_history(
        &mut self,
        history: ItemNavHistory,
        _window: &mut Window,
        _cx: &mut Context<'_, Self>,
    ) {
        self.nav_history = Some(history);
    }

    fn navigate(
        &mut self,
        data: Arc<dyn Any + Send>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> bool {
        let Some(&NavData { entry, top }) = data.downcast_ref::<NavData>() else {
            return false;
        };
        if entry != self.entry || top == self.top_line() {
            return false;
        }
        self.scroll_to(top);
        cx.notify();
        true
    }

    fn deactivated(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) {
        self.push_location(cx);
    }

    fn handle_drop(
        &self,
        _active_pane: &Pane,
        dropped: &dyn Any,
        _window: &mut Window,
        cx: &mut App,
    ) -> bool {
        open_dropped(&self.workspace, dropped, cx)
    }
}

impl Render for DecompileItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let (background, text, muted) = {
            let colors = cx.theme().colors();
            (colors.editor_background, colors.text, colors.text_muted)
        };
        let line_count = self.code.as_ref().map_or(0, |c| c.len());
        let body = match (line_count, self.decompiling, self.entry) {
            (1.., _, _) => uniform_list("code-view", line_count, cx.processor(Self::render_rows))
                .track_scroll(&self.scroll)
                .size_full()
                .into_any_element(),
            (0, false, Some(entry)) if self.code.is_none() => {
                failure_card(entry, cx).into_any_element()
            }
            (0, decompiling, _) => div()
                .p(px(12.0))
                .text_color(muted)
                .child(if decompiling {
                    "Decompiling..."
                } else {
                    "No lines."
                })
                .into_any_element(),
        };
        div()
            .track_focus(&self.focus_handle)
            .key_context("DecompileView")
            .size_full()
            .bg(background)
            .text_color(text)
            .font(self.style.font.clone())
            .text_size(self.style.size)
            .line_height(self.style.row_height)
            .child(body)
    }
}
