//! The in-window menu bar of Windows and Linux, a port of the logic of Zed's
//! `ApplicationMenu` over the menus [`crate::commands`] generates; macOS draws the same
//! menus natively from `cx.set_menus`.
//!
//! A row is disabled exactly when its action has no handler in reach of the focused
//! element, the rule gpui applies to macOS's menus, and then says what it needs.

use gpui::prelude::FluentBuilder as _;
use gpui::{
    Action, App, Context, Entity, InteractiveElement as _, IntoElement, ParentElement as _, Render,
    SharedString, StatefulInteractiveElement as _, Styled as _, Window, div,
};
use ui::{
    Button, ButtonCommon as _, ButtonStyle, ContextMenu, LabelSize, PopoverMenu, PopoverMenuHandle,
    rems_from_px,
};

use crate::binary::Binary;
use crate::commands::{MenuName, menu_rows};
use crate::start_item::TEXT_PX;

gpui::actions!(
    menu_bar,
    [
        /// Opens the menu left of the open one in the window's menu bar; with none open the
        /// key goes on to whatever else takes it.
        ActivateMenuLeft,
        /// Opens the menu right of the open one in the window's menu bar; with none open the
        /// key goes on to whatever else takes it.
        ActivateMenuRight,
    ]
);

/// Returns `label` as a row shows it: with the reason it is disabled, when it is.
///
/// # Arguments
///
/// * `label` - The row's label.
/// * `unmet` - Why it is disabled, `None` when it is not.
fn shown_label(label: &'static str, unmet: Option<&'static str>) -> SharedString {
    unmet.map_or_else(
        || SharedString::from(label),
        |why| format!("{label} ({why})").into(),
    )
}

/// One shown row of a menu: its label with the reason it is off, whether it is off, and
/// its action; `None` is a separator.
type Shown = Option<(SharedString, bool, Box<dyn Action>)>;

/// Returns the rows of `menu` as the bar shows them: off exactly when `available` holds no
/// handler of the row's action, then labelled with why.
///
/// # Arguments
///
/// * `menu` - The menu.
/// * `binary_open` - Whether the window has a binary open, which words an off row.
/// * `available` - The actions with a handler in reach of the focused element.
/// * `cx` - Application context that builds the actions.
fn shown_rows(
    menu: MenuName,
    binary_open: bool,
    available: &[Box<dyn Action>],
    cx: &App,
) -> Vec<Shown> {
    menu_rows(menu, cx)
        .into_iter()
        .map(|row| {
            row.map(|(row, action)| {
                let id = action.as_any().type_id();
                let on = available.iter().any(|ready| ready.as_any().type_id() == id);
                let unmet = (!on).then(|| row.needs.why_off(binary_open));
                (shown_label(row.label, unmet), !on, action)
            })
        })
        .collect()
}

/// Returns the context menu of `menu`, its rows disabled where no handler of their action
/// is in reach of the element focused when it opened, and run in that element's context.
///
/// # Arguments
///
/// * `menu` - The menu.
/// * `binary` - The window's binary, which words the disabled rows.
/// * `window` - Window the menu opens in.
/// * `cx` - Application context.
fn context_menu(
    menu: MenuName,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<ContextMenu> {
    let open = binary.read(cx).is_open();
    let rows = shown_rows(menu, open, &window.available_actions(cx), cx);
    ContextMenu::build(window, cx, move |built, window, cx| {
        let built = built.when_some(window.focused(cx), |built, focused| built.context(focused));
        rows.into_iter().fold(built, |built, row| match row {
            Some((label, off, action)) => built.action_disabled_when(off, label, action),
            None => built.separator(),
        })
    })
}

/// The in-window menu bar of Windows and Linux: one popover per menu of
/// [`MenuName::ALL`].
pub struct MenuBar {
    /// The window's binary, whose state words the disabled rows.
    binary: Entity<Binary>,
    /// One handle per menu, in [`MenuName::ALL`] order.
    handles: Vec<PopoverMenuHandle<ContextMenu>>,
}

impl std::fmt::Debug for MenuBar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MenuBar").finish_non_exhaustive()
    }
}

/// Which way [`MenuBar::step`] moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    /// To the menu on the left, the last after the first.
    Left,
    /// To the menu on the right, the first after the last.
    Right,
}

impl MenuBar {
    /// Returns the menu bar over `binary`.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    #[must_use]
    pub fn new(binary: Entity<Binary>) -> Self {
        Self {
            binary,
            handles: MenuName::ALL.map(|_| PopoverMenuHandle::default()).to_vec(),
        }
    }

    /// Returns the index of the open menu, if one is.
    #[must_use]
    pub fn open_menu(&self) -> Option<usize> {
        self.handles.iter().position(PopoverMenuHandle::is_deployed)
    }

    /// Opens the first menu, closing any other.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the bar is in.
    /// * `cx` - Bar context.
    pub fn open_first(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.handles.iter().for_each(|handle| handle.hide(cx));
        if let Some(first) = self.handles.first().cloned() {
            cx.defer_in(window, move |_, window, cx| first.show(window, cx));
        }
    }

    /// Closes the open menu and opens the one beside it; with none open the key goes on to
    /// whatever else takes it.
    ///
    /// # Arguments
    ///
    /// * `step` - Which way to move.
    /// * `window` - Window the bar is in.
    /// * `cx` - Bar context.
    fn step(&mut self, step: Step, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some(open) = self.open_menu() else {
            cx.propagate();
            return;
        };
        let last = self.handles.len().saturating_sub(1);
        let next = match step {
            Step::Left if open == 0 => last,
            Step::Left => open - 1,
            Step::Right if open == last => 0,
            Step::Right => open + 1,
        };
        if let Some(handle) = self.handles.get(open) {
            handle.hide(cx);
        }
        if let Some(next) = self.handles.get(next).cloned() {
            cx.defer_in(window, move |_, window, cx| next.show(window, cx));
        }
    }
}

impl Render for MenuBar {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let all = self.handles.clone();
        let menus = MenuName::ALL
            .into_iter()
            .zip(self.handles.iter().cloned())
            .map(|(menu, handle)| {
                let name = menu.name();
                let binary = self.binary.clone();
                let all = all.clone();
                let hovered = handle.clone();
                div()
                    .id(SharedString::from(format!("{name}-menu")))
                    .occlude()
                    .child(
                        PopoverMenu::new(SharedString::from(format!("{name}-menu-popover")))
                            .menu(move |window, cx| Some(context_menu(menu, &binary, window, cx)))
                            .trigger(
                                Button::new(
                                    SharedString::from(format!("{name}-menu-trigger")),
                                    name,
                                )
                                .style(ButtonStyle::Subtle)
                                .label_size(LabelSize::Custom(rems_from_px(TEXT_PX))),
                            )
                            .with_handle(handle),
                    )
                    .on_hover(move |entered, window, cx| {
                        if *entered
                            && !hovered.is_deployed()
                            && all.iter().any(PopoverMenuHandle::is_deployed)
                        {
                            all.iter().for_each(|handle| handle.hide(cx));
                            let show = hovered.clone();
                            window.defer(cx, move |window, cx| show.show(window, cx));
                        }
                    })
            });
        div()
            .key_context("MenuBar")
            .on_action(cx.listener(|bar, _: &ActivateMenuLeft, window, cx| {
                bar.step(Step::Left, window, cx);
            }))
            .on_action(cx.listener(|bar, _: &ActivateMenuRight, window, cx| {
                bar.step(Step::Right, window, cx);
            }))
            .flex()
            .flex_row()
            .items_center()
            .gap(gpui::px(2.0))
            .when(!cfg!(target_os = "macos"), |bar| bar.children(menus))
    }
}

#[cfg(test)]
mod tests {
    use gpui::{AppContext as _, TestAppContext, VisualTestContext};

    use super::{MenuBar, Step, shown_rows};
    use crate::actions::CloseBinary;
    use crate::app_view::tests::{init, load_sample, open};
    use crate::binary::{Binary, NO_BINARY};
    use crate::commands::{COMMANDS, MenuName, Need};
    use crate::decompile_item::DecompileItem;
    use crate::functions_panel::FunctionsPanel;
    use crate::start_item::StartItem;

    /// No action whose row needs a binary has a handler in reach before one is open, the
    /// panel toggles and the project and struct actions among them; once one is, the
    /// window-wide ones are.
    ///
    /// # Panics
    ///
    /// Panics naming an action in reach without a binary.
    #[gpui::test]
    fn no_binary_action_is_in_reach_without_a_binary(cx: &mut TestAppContext) {
        no_binary_action_is_in_reach_without_a_binary_steps(cx);
    }

    /// Runs the steps of [`no_binary_action_is_in_reach_without_a_binary`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`no_binary_action_is_in_reach_without_a_binary`]
    /// says.
    fn no_binary_action_is_in_reach_without_a_binary_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let available = |cx: &mut VisualTestContext| {
            cx.update(|window, cx| window.draw(cx).clear(cx));
            let actions = cx.update(|window, cx| window.available_actions(cx));
            let names: Vec<&str> = actions.iter().map(|action| action.name()).collect();
            COMMANDS
                .iter()
                .filter(|row| row.needs == Need::Binary && names.contains(&row.action))
                .map(|row| row.action)
                .collect::<Vec<_>>()
        };
        assert_eq!(available(cx), Vec::<&str>::new());
        load_sample(&app, cx);
        let loaded = available(cx);
        for name in [
            "borer::ToggleTypes",
            "borer::SaveProject",
            "borer::OpenProject",
        ] {
            assert!(loaded.contains(&name), "{name}: {loaded:?}");
        }
    }

    /// Close Binary has no handler in reach while no binary is open, so macOS greys it
    /// (gpui asks `is_action_available`) and the menu bar disables it with its need; once
    /// a binary is open it is available and enabled in both.
    ///
    /// # Panics
    ///
    /// Panics if Close Binary is available without a binary, or not with one.
    #[gpui::test]
    fn close_binary_is_off_until_a_binary_opens(cx: &mut TestAppContext) {
        close_binary_is_off_until_a_binary_opens_steps(cx);
    }

    /// Runs the steps of [`close_binary_is_off_until_a_binary_opens`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`close_binary_is_off_until_a_binary_opens`] says.
    fn close_binary_is_off_until_a_binary_opens_steps(cx: &mut TestAppContext) {
        assert_eq!(Need::Binary.why_off(false), "needs a binary");
        assert_eq!(Need::Binary.why_off(true), "not here");
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let state = |cx: &mut VisualTestContext| {
            cx.update(|window, cx| window.draw(cx).clear(cx));
            let platform = cx.update(|window, cx| window.is_action_available(&CloseBinary, cx));
            let open = app.binary.read_with(cx, |binary, _| binary.is_open());
            let labels: Vec<String> = cx.update(|window, cx| {
                let available = window.available_actions(cx);
                let rows = shown_rows(MenuName::File, open, &available, cx);
                let shown = rows.into_iter().flatten();
                let off = |off: bool| if off { " off" } else { "" };
                shown
                    .map(|(label, is_off, _)| format!("{label}{}", off(is_off)))
                    .collect()
            });
            (platform, labels)
        };
        let (platform, labels) = state(cx);
        assert!(!platform);
        assert!(
            labels.contains(&String::from("Close Binary (needs a binary) off")),
            "{labels:?}"
        );
        load_sample(&app, cx);
        let (platform, labels) = state(cx);
        assert!(platform);
        assert!(labels.contains(&String::from("Close Binary")), "{labels:?}");
    }

    /// The bar opens its first menu, walks left past the first to the last and right back
    /// to the first.
    ///
    /// # Panics
    ///
    /// Panics if the wrong menu is open after a step.
    #[gpui::test]
    fn the_menu_bar_opens_and_walks_its_menus(cx: &mut TestAppContext) {
        the_menu_bar_opens_and_walks_its_menus_steps(cx);
    }

    /// Runs the steps of [`the_menu_bar_opens_and_walks_its_menus`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_menu_bar_opens_and_walks_its_menus`] says.
    fn the_menu_bar_opens_and_walks_its_menus_steps(cx: &mut TestAppContext) {
        init(cx);
        let binary = cx.new(|cx| Binary::new(cx));
        let (bar, cx) = cx.add_window_view(|_, _| MenuBar::new(binary));
        let settle = |cx: &mut VisualTestContext| {
            cx.run_until_parked();
            cx.update(|window, cx| window.draw(cx).clear(cx));
        };
        let open = |cx: &mut VisualTestContext| bar.read_with(cx, |bar, _| bar.open_menu());
        settle(cx);
        assert_eq!(open(cx), None);
        bar.update_in(cx, |bar, window, cx| bar.open_first(window, cx));
        settle(cx);
        if !cfg!(target_os = "macos") {
            assert_eq!(open(cx), Some(0));
            let last = MenuName::ALL.len() - 1;
            bar.update_in(cx, |bar, window, cx| bar.step(Step::Left, window, cx));
            settle(cx);
            assert_eq!(open(cx), Some(last));
            bar.update_in(cx, |bar, window, cx| bar.step(Step::Right, window, cx));
            settle(cx);
            assert_eq!(open(cx), Some(0));
        }
    }

    /// Close Binary, pressed while a second binary is being read, stops showing that read,
    /// takes the panel out of the dock and the function's tab away, leaves the start tab and
    /// says no binary is open; the next load docks the panel again.
    ///
    /// # Panics
    ///
    /// Panics if anything of the binary stays or the next load docks nothing.
    #[gpui::test]
    fn close_binary_returns_to_the_welcome_column(cx: &mut TestAppContext) {
        close_binary_returns_to_the_welcome_column_steps(cx);
    }

    /// Runs the steps of [`close_binary_returns_to_the_welcome_column`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`close_binary_returns_to_the_welcome_column`] says.
    fn close_binary_returns_to_the_welcome_column_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        let missing = std::env::temp_dir().join("borer-app-closed-while-reading.exe");
        app.binary
            .update(cx, |binary, cx| binary.open_path(missing, cx));
        assert!(
            app.binary
                .read_with(cx, |binary, _| binary.reading().is_some())
        );
        cx.dispatch_action(CloseBinary);
        cx.run_until_parked();
        app.workspace.read_with(cx, |workspace, cx| {
            assert!(workspace.panel::<FunctionsPanel>(cx).is_none());
            assert!(workspace.active_item_as::<DecompileItem>(cx).is_none());
            assert!(workspace.active_item_as::<StartItem>(cx).is_some());
        });
        app.binary.read_with(cx, |binary, _| {
            assert!(binary.loaded().is_none());
            assert!(binary.facts().is_empty());
            assert!(binary.reading().is_none());
            assert_eq!(binary.status(), NO_BINARY);
        });
        load_sample(&app, cx);
    }
}
