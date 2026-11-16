//! The start tab: the tab a pane holds when it has no decompile tab, so a file dropped on
//! any pane reaches a tab's drop handler and never Zed's own open path.

use std::any::Any;

use gpui::{
    App, AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString, Styled as _,
    WeakEntity, Window, px, svg,
};
use theme::ActiveTheme as _;
use ui::{Color, Label, LabelCommon as _, LabelSize, v_flex};
use workspace::{Item, Pane, Workspace};

use crate::actions::{OPEN_HINT, PALETTE_HINT, hint_row};
use crate::app_assets::MARK_PATH;
use crate::app_view::open_dropped;

/// Side in logical pixels of the borer mark on the start tab.
const MARK_PX: f32 = 48.0;

/// A tab that says how to open a binary and opens a binary dropped on it.
pub struct StartItem {
    /// Workspace whose binary a drop opens.
    workspace: WeakEntity<Workspace>,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
}

impl std::fmt::Debug for StartItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StartItem").finish_non_exhaustive()
    }
}

/// Keeps `pane` holding a tab: a start tab while it has none, gone once another tab opens.
///
/// Zed's pane hands a dropped file to its active tab and, with no tab, to Zed's own open
/// path, which adds the folder to the project and runs its settings.
///
/// # Arguments
///
/// * `pane` - The pane to keep filled.
/// * `workspace` - Workspace the pane belongs to.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
pub fn keep_filled(
    pane: &Entity<Pane>,
    workspace: &WeakEntity<Workspace>,
    window: &mut Window,
    cx: &mut App,
) {
    fill(pane, workspace, window, cx);
    let workspace = workspace.clone();
    window
        .subscribe(
            pane,
            cx,
            move |pane, event: &workspace::pane::Event, window, cx| match event {
                workspace::pane::Event::RemovedItem { .. } => {
                    fill(&pane, &workspace, window, cx);
                }
                workspace::pane::Event::AddItem { item }
                    if item.downcast::<StartItem>().is_none() =>
                {
                    let starts: Vec<_> = pane.read(cx).items_of_type::<StartItem>().collect();
                    pane.update(cx, |pane, cx| {
                        for start in starts {
                            pane.remove_item(start.entity_id(), false, false, window, cx);
                        }
                    });
                }
                _ => {}
            },
        )
        .detach();
}

/// Adds a start tab to `pane` when it holds no tab.
///
/// # Arguments
///
/// * `pane` - The pane.
/// * `workspace` - Workspace the pane belongs to.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
fn fill(pane: &Entity<Pane>, workspace: &WeakEntity<Workspace>, window: &mut Window, cx: &mut App) {
    if pane.read(cx).items_len() > 0 {
        return;
    }
    let workspace = workspace.clone();
    let item = cx.new(|cx| StartItem {
        workspace,
        focus_handle: cx.focus_handle(),
    });
    pane.update(cx, |pane, cx| {
        pane.add_item(Box::new(item), false, false, None, window, cx);
    });
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
        _window: &mut Window,
        cx: &mut App,
    ) -> bool {
        open_dropped(&self.workspace, dropped, cx)
    }
}

impl Render for StartItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let drop = Label::new("Drop a file anywhere")
            .size(LabelSize::Small)
            .color(Color::Muted);
        v_flex()
            .track_focus(&self.focus_handle)
            .size_full()
            .bg(cx.theme().colors().editor_background)
            .items_center()
            .justify_center()
            .gap_4()
            .child(
                svg()
                    .path(MARK_PATH)
                    .size(px(MARK_PX))
                    .text_color(cx.theme().colors().text_muted),
            )
            .child(Label::new("Open a binary").size(LabelSize::Large))
            .child(
                v_flex()
                    .gap_2()
                    .child(hint_row(OPEN_HINT, cx))
                    .child(drop)
                    .child(hint_row(PALETTE_HINT, cx)),
            )
    }
}
