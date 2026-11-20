//! The start tab: the tab a pane holds when it has no decompile tab.
//!
//! A file dropped on any pane so reaches a tab's drop handler and never Zed's own open path.
//! With nothing loaded the tab is one narrow centred column, as Zed's welcome page is: the
//! mark and a greeting, the actions to start with, then the binaries opened before; while a
//! binary loads it says which.

use std::any::Any;

use gpui::{
    Action, AnyElement, App, AppContext as _, Context, Entity, EventEmitter, FocusHandle,
    Focusable, InteractiveElement as _, IntoElement, KeyDownEvent, ParentElement as _, Pixels,
    Render, SharedString, StatefulInteractiveElement as _, Styled as _, Subscription, Window,
    canvas, div, px, svg,
};
use theme::ActiveTheme as _;
use ui::{
    Color, Divider, DividerColor, Headline, Icon, IconName, IconSize, KeyBinding, Label,
    LabelCommon as _, LabelSize, ListItem, ListItemSpacing, Toggleable as _, h_flex, rems_from_px,
    v_flex,
};
use workspace::{Item, Pane};

use crate::actions::{KEY_PX, Open};
use crate::app_assets::MARK_PATH;
use crate::app_view::open_dropped;
use crate::binary::{Binary, reading_label};
use crate::recent::{RecentBinary, SHOWN_MAX};
use crate::rows_panel::{Rows, row_keys};
use crate::status::{Work, gauge, spinner};
use crate::title_bar::MARK_CELL_PX;

/// Side in logical pixels of the borer mark beside the greeting.
const MARK_PX: f32 = 40.0;

/// Width in logical pixels of the start column.
const COLUMN_PX: f32 = 360.0;

/// Least space in logical pixels left and right of the start column.
const SIDE_PX: f32 = 16.0;

/// Size in logical pixels of the chrome's text: the title bar and the menu bar.
pub(crate) const TEXT_PX: f32 = 12.5;

/// What the line under the greeting says borer is, in the project's own words.
const TAGLINE: &str = "Reverse engineering for people and agents";

/// The actions the start column offers first, each with its icon and label, in order.
const STARTS: [(IconName, &str, &dyn Action); 3] = [
    (IconName::FolderOpen, "Open File...", &Open),
    (
        IconName::ListCollapse,
        "Open Command Palette",
        &zed_actions::command_palette::Toggle,
    ),
    (
        IconName::Settings,
        "Open Settings File",
        &zed_actions::OpenSettingsFile,
    ),
];

/// A tab that says how to open a binary and opens a binary dropped on it.
pub struct StartItem {
    /// The window's binary, which a drop, an action row or a recent row opens.
    binary: Entity<Binary>,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// Index of the highlighted row: the [`STARTS`] rows, then the recent ones.
    selected: usize,
    /// How far the tab sits from the window's left and right edges, as laid out last frame:
    /// the rail and any docks, which a resize of the window does not move.
    pane: Edges,
    /// The status bar's work item, whose progress words the tab shows while a load runs.
    work: Option<Entity<Work>>,
    /// Repaints the tab when the binary starts or ends a load and when the work item's
    /// progress words change.
    _observe: Vec<Subscription>,
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
/// * `work` - The status bar's work item, `None` when the bar has none.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
pub fn keep_filled(
    pane: &Entity<Pane>,
    binary: &Entity<Binary>,
    work: Option<Entity<Work>>,
    window: &mut Window,
    cx: &mut App,
) {
    pane.update(cx, |pane, cx| {
        pane.set_render_tab_bar_buttons(cx, |_, _, _| (None, None));
    });
    fill(pane, binary, work.as_ref(), window, cx);
    let binary = binary.clone();
    window
        .subscribe(
            pane,
            cx,
            move |pane, event: &workspace::pane::Event, window, cx| match event {
                workspace::pane::Event::RemovedItem { .. } => {
                    fill(&pane, &binary, work.as_ref(), window, cx);
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
/// * `work` - The status bar's work item, `None` when the bar has none.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
fn fill(
    pane: &Entity<Pane>,
    binary: &Entity<Binary>,
    work: Option<&Entity<Work>>,
    window: &mut Window,
    cx: &mut App,
) {
    if pane.read(cx).items_len() > 0 {
        return;
    }
    let recent = binary.read(cx).recent().len();
    let item = cx.new(|cx| StartItem {
        binary: binary.clone(),
        focus_handle: cx.focus_handle(),
        selected: first_selected(recent),
        pane: Edges::BESIDE_RAIL,
        work: work.cloned(),
        _observe: std::iter::once(cx.observe(binary, |_, _, cx| cx.notify()))
            .chain(work.map(|work| cx.observe(work, |_, _, cx| cx.notify())))
            .collect(),
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
        self.selected = STARTS.len() + row;
        self.binary
            .update(cx, |binary, cx| binary.open_path(path, cx));
    }

    /// Runs the highlighted row: its action for a [`STARTS`] row, else opens its binary.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    fn activate(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        match STARTS.get(self.selected) {
            Some((_, _, action)) => window.dispatch_action(action.boxed_clone(), cx),
            None => self.open_row(self.selected.saturating_sub(STARTS.len()), cx),
        }
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

    /// Returns the greeting: the mark beside `Welcome to borer`, `Welcome back` once a binary
    /// was opened before, and what borer is under it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_greeting(&self, cx: &Context<'_, Self>) -> AnyElement {
        let welcome = if self.shown(cx).is_empty() {
            "Welcome to borer"
        } else {
            "Welcome back to borer"
        };
        h_flex()
            .w_full()
            .justify_center()
            .gap_4()
            .mb_4()
            .child(
                svg()
                    .path(MARK_PATH)
                    .size(px(MARK_PX))
                    .flex_none()
                    .text_color(cx.theme().colors().text_muted),
            )
            .child(
                v_flex().child(Headline::new(welcome)).child(
                    Label::new(TAGLINE)
                        .size(LabelSize::Small)
                        .color(Color::Muted)
                        .italic(),
                ),
            )
            .into_any_element()
    }

    /// Returns the action rows, then a line saying a file can be dropped instead.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_starts(&self, cx: &mut Context<'_, Self>) -> AnyElement {
        let focus = self.focus_handle.clone();
        let rows = STARTS
            .iter()
            .enumerate()
            .map(|(ix, (icon, label, action))| {
                let key = KeyBinding::for_action_in(*action, &focus, cx).size(rems_from_px(KEY_PX));
                let row = start_row(("start", ix), (*icon, Label::new(*label)), key);
                row.toggle_state(ix == self.selected).on_click(cx.listener(
                    move |this, _, window, cx| {
                        this.selected = ix;
                        this.activate(window, cx);
                    },
                ))
            });
        let drop = Label::new("or drop a file on the window")
            .size(LabelSize::Small)
            .color(Color::Placeholder);
        v_flex()
            .w_full()
            .child(section("Get Started", cx))
            .children(rows)
            .child(div().px_2().pt_1().child(drop))
            .into_any_element()
    }

    /// Returns the binaries opened before, one row each with its digit, `None` with none.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_recent(&self, cx: &mut Context<'_, Self>) -> Option<AnyElement> {
        let shown = self.shown(cx).to_vec();
        if shown.is_empty() {
            return None;
        }
        let rows = shown.into_iter().enumerate().map(|(ix, recent)| {
            let name = h_flex()
                .min_w_0()
                .gap_2()
                .child(div().flex_none().child(Label::new(recent.name())))
                .child(
                    Label::new(recent.folder())
                        .size(LabelSize::Small)
                        .color(Color::Muted)
                        .truncate_start(),
                );
            let digit = div().pr_0p5().child(
                Label::new((ix + 1).to_string())
                    .size(LabelSize::Small)
                    .color(Color::Muted),
            );
            let tip = format!("{} - {}", recent.kind, recent.path.display());
            start_row(("recent", ix), (IconName::File, name), digit)
                .toggle_state(STARTS.len() + ix == self.selected)
                .tooltip(ui::Tooltip::text(tip))
                .on_click(cx.listener(move |this, _, _, cx| this.open_row(ix, cx)))
        });
        Some(
            v_flex()
                .w_full()
                .child(section("Recent", cx))
                .children(rows)
                .into_any_element(),
        )
    }
}

/// Returns a section's header as Zed's welcome page draws it: its title in small capitals,
/// then a hairline to the column's edge.
///
/// # Arguments
///
/// * `title` - The section's title.
/// * `cx` - Application context reading the buffer font.
fn section(title: &str, cx: &App) -> impl IntoElement {
    h_flex()
        .px_1()
        .mb_2()
        .gap_2()
        .child(
            Label::new(title.to_ascii_uppercase())
                .buffer_font(cx)
                .color(Color::Muted)
                .size(LabelSize::XSmall),
        )
        .child(Divider::horizontal().color(DividerColor::BorderVariant))
}

/// Returns one row of the start column as Zed's lists draw it: a muted icon and `label` on
/// the left, `end` against the right edge, the whole row one click target.
///
/// # Arguments
///
/// * `id` - The row's element id.
/// * `(icon, label)` - What the row shows on its left.
/// * `end` - What the row shows on its right: a key binding or a digit.
fn start_row(
    id: impl Into<gpui::ElementId>,
    (icon, label): (IconName, impl IntoElement),
    end: impl IntoElement,
) -> ListItem {
    ListItem::new(id)
        .inset(true)
        .spacing(ListItemSpacing::Sparse)
        .start_slot(Icon::new(icon).color(Color::Muted).size(IconSize::Small))
        .child(label)
        .end_slot(div().flex_none().child(end))
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
    fn selected(&self) -> Option<usize> {
        Some(self.selected)
    }

    fn select(&mut self, row: usize, cx: &mut Context<'_, Self>) {
        let last = STARTS
            .len()
            .saturating_add(self.shown(cx).len())
            .saturating_sub(1);
        self.selected = row.min(last);
        cx.notify();
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
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let column = v_flex().w(px(COLUMN_PX)).max_w_full().gap_6();
        let binary = self.binary.read(cx);
        let column = if let Some(busy) = binary.busy() {
            let words = self.work.as_ref().map(|work| work.read(cx).load_words(cx));
            let (phase, percent) = words.unwrap_or_default();
            let reading = v_flex()
                .items_center()
                .gap_2()
                .child(Label::new(reading_label(busy)).color(Color::Muted))
                .child(
                    h_flex()
                        .gap_2()
                        .child(spinner())
                        .children(phase.map(|phase| {
                            Label::new(phase)
                                .size(LabelSize::Small)
                                .color(Color::Placeholder)
                        }))
                        .children(percent.map(|percent| gauge(Some(percent), cx))),
                );
            column.child(reading)
        } else {
            let error = binary.load_error().map(|e| {
                Label::new(e.to_owned())
                    .size(LabelSize::Small)
                    .color(Color::Error)
            });
            column
                .child(self.render_greeting(cx))
                .children(error)
                .child(self.render_starts(cx))
                .children(self.render_recent(cx))
        };
        let width = window.viewport_size().width;
        let Edges { left, right } = self.pane;
        let (left, right) = centring(width, left, width - left - right);
        let item = cx.entity().downgrade();
        let watch = watch_edges(move |edges, cx| {
            item.upgrade().is_some_and(|item| {
                item.update(cx, |item, _| {
                    std::mem::replace(&mut item.pane, edges) != edges
                })
            })
        });
        let root = div()
            .id("start")
            .debug_selector(|| "start-item".to_owned())
            .key_context("StartItem")
            .track_focus(&self.focus_handle);
        row_keys(root, cx)
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| {
                this.activate(window, cx);
            }))
            .on_key_down(cx.listener(|this, event: &KeyDownEvent, _, cx| {
                this.open_by_digit(event, cx);
            }))
            .relative()
            .size_full()
            .bg(cx.theme().colors().editor_background)
            .child(watch)
            .child(
                div()
                    .id("start-scroll")
                    .size_full()
                    .overflow_y_scroll()
                    .child(
                        v_flex()
                            .min_h_full()
                            .w_full()
                            .items_center()
                            .justify_center()
                            .py_8()
                            .pl(px(SIDE_PX) + left)
                            .pr(px(SIDE_PX) + right)
                            .child(column),
                    ),
            )
    }
}

/// How far an element sits from the window's left and right edges, in logical pixels: a
/// start tab, or the title bar's children beside the window controls.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub(crate) struct Edges {
    /// From the window's left edge to the element's.
    pub(crate) left: Pixels,
    /// From the element's right edge to the window's.
    pub(crate) right: Pixels,
}

/// Returns an empty layer over its parent that hands `keep` the parent's [`Edges`] as it
/// lays out, and draws the window again when `keep` says they moved.
///
/// # Arguments
///
/// * `keep` - Stores the edges, and returns whether they differ from those stored.
pub(crate) fn watch_edges(keep: impl Fn(Edges, &mut App) -> bool + 'static) -> impl IntoElement {
    canvas(
        move |bounds, window, cx| {
            let width = window.viewport_size().width;
            let edges = Edges {
                left: bounds.origin.x,
                right: width - bounds.right(),
            };
            if keep(edges, cx) {
                window.defer(cx, |window, _| window.refresh());
            }
        },
        |_, (), _, _| {},
    )
    .absolute()
    .size_full()
}

impl Edges {
    /// Where a start tab sits before it is laid out: right of the rail with no dock open, as
    /// in a window with no binary loaded, whose first frame is then centred already. A start
    /// tab beside an open dock, after a loaded binary's last tab closes, or in a split's
    /// right pane draws its first frame off by the dock or the pane left of it, and the
    /// frame its measure asks for centres it.
    const BESIDE_RAIL: Self = Self {
        left: px(MARK_CELL_PX),
        right: px(0.0),
    };
}

/// Returns the highlighted row a new start tab begins on: the first binary opened before,
/// so Enter opens it, else Open File.
///
/// # Arguments
///
/// * `recent` - How many binaries were opened before.
const fn first_selected(recent: usize) -> usize {
    if recent > 0 { STARTS.len() } else { 0 }
}

/// Returns the padding to add left and right of the start column to centre it on the window.
///
/// The column then sits under the title-bar title rather than at the middle of the pane
/// beside the rail and docks; with no room for that, no padding, and it centres on the pane.
///
/// # Arguments
///
/// * `window` - Width of the window.
/// * `left` - Left edge of the pane, in the window.
/// * `pane` - Width of the pane.
fn centring(window: Pixels, left: Pixels, pane: Pixels) -> (Pixels, Pixels) {
    let shift = window / 2.0 - left - pane / 2.0;
    let pad = shift.abs() * 2.0;
    if pane - pad < px(COLUMN_PX + 2.0 * SIDE_PX) {
        return (px(0.0), px(0.0));
    }
    if shift < px(0.0) {
        (px(0.0), pad)
    } else {
        (pad, px(0.0))
    }
}
#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use command_palette::CommandPalette;
    use gpui::{TestAppContext, px};

    use super::{COLUMN_PX, Edges, SIDE_PX, STARTS, StartItem, centring, first_selected};
    use crate::app_view::tests::{init, open};
    use crate::rows_panel::Rows as _;

    /// A new start tab highlights the first binary opened before, so Enter opens it, and
    /// Open File when none was.
    #[test]
    fn the_highlight_starts_on_the_first_recent_binary() {
        assert_eq!(first_selected(0), 0);
        assert_eq!(first_selected(1), STARTS.len());
        assert_eq!(first_selected(5), STARTS.len());
    }

    /// A new window's start tab is centred from its first frame: the edges it lays out at
    /// are the ones it assumed, so it asks for no second frame.
    ///
    /// # Panics
    ///
    /// Panics if the first frame measures other edges than the tab assumed.
    #[gpui::test]
    fn the_first_frame_is_centred_already(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let start = app
            .workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<StartItem>(cx)
            })
            .unwrap();
        assert_eq!(
            start.read_with(cx, |start, _| start.pane),
            Edges::BESIDE_RAIL
        );
        cx.update(|window, cx| window.draw(cx).clear(cx));
        assert_eq!(
            start.read_with(cx, |start, _| start.pane),
            Edges::BESIDE_RAIL
        );
    }

    /// Enter on an action row runs its action: the palette row opens the command palette.
    #[gpui::test]
    fn enter_on_an_action_row_runs_it(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        cx.run_until_parked();
        let start = app
            .workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<StartItem>(cx)
            })
            .unwrap();
        let palette = STARTS
            .iter()
            .position(|(_, label, _)| *label == "Open Command Palette")
            .unwrap();
        cx.update(|window, cx| {
            start.update(cx, |start, cx| {
                start.select(palette, cx);
                window.focus(&start.focus_handle, cx);
            });
        });
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let opened = app.workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<CommandPalette>(cx).is_some()
        });
        assert!(opened);
    }

    /// The column centres on the window, beside a rail on the left or a dock on the right,
    /// and on the pane when it would not fit there.
    #[test]
    fn the_column_centres_on_the_window_when_it_fits() {
        assert_eq!(
            centring(px(1440.0), px(40.0), px(1400.0)),
            (px(0.0), px(40.0))
        );
        assert_eq!(
            centring(px(1440.0), px(0.0), px(1040.0)),
            (px(400.0), px(0.0))
        );
        assert_eq!(
            centring(px(1440.0), px(0.0), px(1440.0)),
            (px(0.0), px(0.0))
        );
        let tight = px(COLUMN_PX + 2.0 * SIDE_PX + 30.0);
        assert_eq!(centring(px(1440.0), px(1000.0), tight), (px(0.0), px(0.0)));
    }
}
