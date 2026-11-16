//! The start tab: the tab a pane holds when it has no decompile tab.
//!
//! A file dropped on any pane so reaches a tab's drop handler and never Zed's own open path.
//! With nothing loaded the tab is the welcome column: the mark, the open button, the
//! binaries opened before and the keys that matter first; while a binary loads it says which.

use std::any::Any;

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, AppContext as _, ClickEvent, Context, Entity, EventEmitter, FocusHandle,
    Focusable, FontWeight, InteractiveElement as _, IntoElement, KeyDownEvent, ParentElement as _,
    Render, SharedString, StatefulInteractiveElement as _, Styled as _, Subscription, Window, div,
    px, svg,
};
use theme::ActiveTheme as _;
use ui::{Color, KeyBinding, Label, LabelCommon as _, LabelSize, h_flex, rems_from_px, v_flex};
use workspace::{Item, Pane};

use crate::actions::{Open, PALETTE_HINT, hint_row};
use crate::app_assets::MARK_PATH;
use crate::app_view::open_dropped;
use crate::binary::{Binary, reading_label};
use crate::recent::{RecentBinary, SHOWN_MAX};
use crate::rows_panel::{Rows, row_keys};

/// Side in logical pixels of the borer mark on the welcome column.
const MARK_PX: f32 = 64.0;

/// Size in logical pixels of the welcome column's headline.
const HEADLINE_PX: f32 = 20.0;

/// Size in logical pixels of the chrome's text: the welcome column, the title bar and the
/// menu bar.
pub(crate) const TEXT_PX: f32 = 12.5;

/// Height in logical pixels of the open button.
const BUTTON_PX: f32 = 32.0;

/// Corner radius in logical pixels of the open button.
const BUTTON_RADIUS_PX: f32 = 6.0;

/// Width in logical pixels of the recent list.
const RECENT_WIDTH_PX: f32 = 520.0;

/// Height in logical pixels of a row of the recent list.
const ROW_PX: f32 = 28.0;

/// Width in logical pixels of the name column of the recent list.
const NAME_PX: f32 = 160.0;

/// What the welcome column says the app reads.
const READS: &str = "PE, ELF or Mach-O. x86, x64 or arm64. Nothing leaves this machine.";

/// A tab that says how to open a binary and opens a binary dropped on it.
pub struct StartItem {
    /// The window's binary, which a drop, the button or a recent row opens.
    binary: Entity<Binary>,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// Index of the highlighted recent row.
    selected: usize,
    /// Repaints the tab when the binary starts or ends a load.
    _observe: Subscription,
}

impl std::fmt::Debug for StartItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StartItem")
            .field("selected", &self.selected)
            .finish_non_exhaustive()
    }
}

/// Keeps `pane` holding a tab: a start tab while it has none, gone once another tab opens.
///
/// The pane shows no tab bar while it holds only start tabs, and no button that opens a
/// file, a terminal or a search.
///
/// Zed's pane hands a dropped file to its active tab and, with no tab, to Zed's own open
/// path, which adds the folder to the project and runs its settings.
///
/// # Arguments
///
/// * `pane` - The pane to keep filled.
/// * `binary` - The window's binary.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
pub fn keep_filled(
    pane: &Entity<Pane>,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut App,
) {
    pane.update(cx, |pane, cx| {
        pane.set_render_tab_bar_buttons(cx, |_, _, _| (None, None));
    });
    fill(pane, binary, window, cx);
    let binary = binary.clone();
    window
        .subscribe(
            pane,
            cx,
            move |pane, event: &workspace::pane::Event, window, cx| match event {
                workspace::pane::Event::RemovedItem { .. } => {
                    fill(&pane, &binary, window, cx);
                    pane.update(cx, show_tab_bar_for_code);
                }
                workspace::pane::Event::AddItem { item }
                    if item.downcast::<StartItem>().is_none() =>
                {
                    let starts: Vec<_> = pane.read(cx).items_of_type::<StartItem>().collect();
                    pane.update(cx, |pane, cx| {
                        for start in starts {
                            pane.remove_item(start.entity_id(), false, false, window, cx);
                        }
                        show_tab_bar_for_code(pane, cx);
                    });
                }
                _ => {}
            },
        )
        .detach();
}

/// Shows `pane`'s tab bar only while it holds a tab other than a start tab.
///
/// The pane asks its hook while it renders, when it cannot be read, so the hook is a
/// constant set again on every change of its tabs.
///
/// # Arguments
///
/// * `pane` - The pane.
/// * `cx` - Pane context.
fn show_tab_bar_for_code(pane: &mut Pane, cx: &mut Context<'_, Pane>) {
    let show = pane
        .items()
        .any(|item| item.downcast::<StartItem>().is_none());
    pane.set_should_display_tab_bar(move |_, _| show);
    cx.notify();
}

/// Adds a start tab to `pane` when it holds no tab.
///
/// # Arguments
///
/// * `pane` - The pane.
/// * `binary` - The window's binary.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
fn fill(pane: &Entity<Pane>, binary: &Entity<Binary>, window: &mut Window, cx: &mut App) {
    if pane.read(cx).items_len() > 0 {
        return;
    }
    let item = cx.new(|cx| StartItem {
        binary: binary.clone(),
        focus_handle: cx.focus_handle(),
        selected: 0,
        _observe: cx.observe(binary, |_, _, cx| cx.notify()),
    });
    pane.update(cx, |pane, cx| {
        pane.add_item(Box::new(item), false, false, None, window, cx);
        show_tab_bar_for_code(pane, cx);
    });
}

impl StartItem {
    /// Returns the recent rows the column shows, at most [`SHOWN_MAX`].
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the binary.
    fn shown<'a>(&self, cx: &'a App) -> &'a [RecentBinary] {
        let recent = self.binary.read(cx).recent();
        &recent[..recent.len().min(SHOWN_MAX)]
    }

    /// Opens recent row `row`, when there is one and no engine load still runs.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based row.
    /// * `cx` - Tab context.
    fn open_row(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        if self.binary.read(cx).busy().is_some() {
            return;
        }
        let Some(path) = self.shown(cx).get(row).map(|recent| recent.path.clone()) else {
            return;
        };
        self.selected = row;
        self.binary
            .update(cx, |binary, cx| binary.open_path(path, cx));
    }

    /// Opens the recent row whose digit `event` typed, `1` for the first.
    ///
    /// # Arguments
    ///
    /// * `event` - A key press on the tab.
    /// * `cx` - Tab context.
    fn open_by_digit(&mut self, event: &KeyDownEvent, cx: &mut Context<'_, Self>) {
        let stroke = &event.keystroke;
        if stroke.modifiers.modified() {
            return;
        }
        let Ok(digit) = stroke.key.parse::<usize>() else {
            return;
        };
        if (1..=SHOWN_MAX).contains(&digit) {
            self.open_row(digit - 1, cx);
        }
    }

    /// Returns the recent list: a header, then one row per binary opened before.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_recent(&self, cx: &mut Context<'_, Self>) -> Option<AnyElement> {
        let shown = self.shown(cx).to_vec();
        if shown.is_empty() {
            return None;
        }
        let colors = cx.theme().colors();
        let (line, lit, hover) = (colors.border, colors.element_selected, colors.element_hover);
        let header = h_flex()
            .justify_between()
            .px(px(10.0))
            .pb(px(4.0))
            .border_b_1()
            .border_color(line)
            .child(small("Recent", Color::Placeholder))
            .child(small("enter opens", Color::Placeholder));
        let rows = shown.into_iter().enumerate().map(|(ix, recent)| {
            div()
                .id(("recent", ix))
                .h(px(ROW_PX))
                .px(px(10.0))
                .flex()
                .items_center()
                .gap(px(12.0))
                .rounded(px(4.0))
                .when(ix == self.selected, |row| row.bg(lit))
                .hover(move |row| row.bg(hover))
                .cursor_pointer()
                .on_click(cx.listener(move |this, _: &ClickEvent, _, cx| this.open_row(ix, cx)))
                .child(
                    div().w(px(NAME_PX)).child(
                        Label::new(recent.name())
                            .buffer_font(cx)
                            .size(LabelSize::Small)
                            .truncate(),
                    ),
                )
                .child(
                    div().flex_1().min_w(px(0.0)).child(
                        Label::new(recent.folder())
                            .buffer_font(cx)
                            .size(LabelSize::Small)
                            .color(Color::Placeholder)
                            .truncate(),
                    ),
                )
                .child(small(recent.kind, Color::Placeholder))
                .child(small((ix + 1).to_string(), Color::Placeholder))
        });
        Some(
            v_flex()
                .w(px(RECENT_WIDTH_PX))
                .gap(px(2.0))
                .child(header)
                .children(rows)
                .into_any_element(),
        )
    }

    /// Returns the primary button, which opens the file dialog, with its key.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_open_button(cx: &mut Context<'_, Self>) -> AnyElement {
        let colors = cx.theme().colors();
        let (fill, ink) = (colors.text, colors.editor_background);
        div()
            .id("open-binary")
            .h(px(BUTTON_PX))
            .px(px(14.0))
            .flex()
            .items_center()
            .gap(px(10.0))
            .rounded(px(BUTTON_RADIUS_PX))
            .bg(fill)
            .text_color(ink)
            .cursor_pointer()
            .on_click(|_, window, cx| window.dispatch_action(Box::new(Open), cx))
            .child(
                Label::new("Open binary")
                    .size(LabelSize::Custom(rems_from_px(TEXT_PX)))
                    .weight(FontWeight::SEMIBOLD)
                    .color(Color::Custom(ink)),
            )
            .child(KeyBinding::for_action(&Open, cx))
            .into_any_element()
    }
}

/// Returns a label in the chrome's text size ([`TEXT_PX`]) and `color`.
///
/// # Arguments
///
/// * `text` - What it says.
/// * `color` - Its color.
pub(crate) fn small(text: impl Into<SharedString>, color: Color) -> Label {
    Label::new(text)
        .size(LabelSize::Custom(rems_from_px(TEXT_PX)))
        .color(color)
}

impl Rows for StartItem {
    fn selected(&self) -> usize {
        self.selected
    }

    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        let len = self.shown(cx).len();
        if len > 0 {
            self.selected = row.min(len - 1);
            cx.notify();
        }
    }
}

impl EventEmitter<()> for StartItem {}

impl Focusable for StartItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Item for StartItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        SharedString::from("Start")
    }

    fn include_in_nav_history() -> bool {
        false
    }

    fn handle_drop(
        &self,
        _active_pane: &Pane,
        dropped: &dyn Any,
        window: &mut Window,
        cx: &mut App,
    ) -> bool {
        open_dropped(&self.binary, dropped, window, cx)
    }
}

impl Render for StartItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let column = v_flex().items_center().gap(px(14.0)).child(
            svg()
                .path(MARK_PATH)
                .size(px(MARK_PX))
                .text_color(cx.theme().colors().text_muted),
        );
        let binary = self.binary.read(cx);
        let column = if let Some(busy) = binary.busy() {
            column.child(headline(reading_label(busy)))
        } else {
            let error = binary
                .load_error()
                .map(|e| small(e.to_owned(), Color::Error));
            let hints = h_flex()
                .gap(px(10.0))
                .pt(px(18.0))
                .child(small("Drop a file here", Color::Placeholder))
                .child(hint_row(PALETTE_HINT, cx));
            column
                .child(headline("Open a binary".to_owned()))
                .child(small(READS, Color::Placeholder))
                .children(error)
                .child(div().pt(px(10.0)).child(Self::render_open_button(cx)))
                .children(
                    self.render_recent(cx)
                        .map(|list| div().pt(px(26.0)).child(list)),
                )
                .child(hints)
        };
        let root = div()
            .id("start")
            .debug_selector(|| "start-item".to_owned())
            .key_context("StartItem")
            .track_focus(&self.focus_handle);
        row_keys(root, cx)
            .on_action(cx.listener(|this, _: &menu::Confirm, _, cx| {
                this.open_row(this.selected, cx);
            }))
            .on_key_down(cx.listener(|this, event: &KeyDownEvent, _, cx| {
                this.open_by_digit(event, cx);
            }))
            .size_full()
            .bg(cx.theme().colors().editor_background)
            .flex()
            .items_center()
            .justify_center()
            .child(column)
    }
}

/// Returns the welcome column's headline.
///
/// # Arguments
///
/// * `text` - What it says.
fn headline(text: impl Into<SharedString>) -> Label {
    Label::new(text)
        .size(LabelSize::Custom(rems_from_px(HEADLINE_PX)))
        .weight(FontWeight::SEMIBOLD)
}
