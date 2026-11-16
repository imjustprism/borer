//! The start tab: the tab a pane holds when it has no decompile tab, so a file dropped on
//! any pane reaches a tab's drop handler and never Zed's own open path.

use std::any::Any;

use gpui::{
    Action, AnyElement, App, AppContext as _, Context, Entity, EventEmitter, FocusHandle,
    Focusable, InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    Styled as _, WeakEntity, Window, div,
};
use theme::ActiveTheme as _;
use ui::{Color, KeyBinding, Label, LabelCommon as _, LabelSize};
use workspace::{Item, Pane, Workspace};

use crate::actions::Open;
use crate::app_view::open_dropped;

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

/// Returns one line of the start tab: `label`, then the binding of `action` when it has one.
///
/// # Arguments
///
/// * `label` - What the line says.
/// * `action` - The action whose key the line shows, if any.
/// * `cx` - Application context reading the keymap.
fn hint(label: &'static str, action: Option<&dyn Action>, cx: &App) -> AnyElement {
    div()
        .flex()
        .gap_2()
        .items_center()
        .child(Label::new(label).color(Color::Muted))
        .children(action.map(|action| KeyBinding::for_action(action, cx)))
        .into_any_element()
}

impl Render for StartItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let palette = cx.build_action("command_palette::Toggle", None).ok();
        div()
            .track_focus(&self.focus_handle)
            .size_full()
            .bg(cx.theme().colors().editor_background)
            .flex()
            .flex_col()
            .gap_2()
            .items_center()
            .justify_center()
            .child(Label::new("Open a binary").size(LabelSize::Large))
            .child(hint("Open", Some(&Open), cx))
            .child(hint("Drop a file anywhere", None, cx))
            .child(hint("Every command", palette.as_deref(), cx))
    }
}
