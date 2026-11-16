//! The app's menus, one table ([`MENUS`]) of actions the app handles.
//!
//! The table is given to the platform with `cx.set_menus` (macOS draws it as the system menu
//! bar) and drawn in the window by [`MenuBar`] on Windows and Linux, a port of the logic of
//! Zed's `ApplicationMenu`.
//!
//! Every row is an action, so it is in the command palette under the same name with the
//! same key, and the key a menu shows is read from the keymap. A row whose need is unmet is
//! shown disabled with the reason, never hidden. Only actions with a handler are rows: a
//! menu the app has nothing for yet is left out rather than drawn empty.

use gpui::prelude::FluentBuilder as _;
use gpui::{
    Action, App, Context, Entity, InteractiveElement as _, IntoElement, Menu, MenuItem,
    ParentElement as _, Render, SharedString, StatefulInteractiveElement as _, Styled as _,
    Subscription, Window, div,
};
use ui::{
    Button, ButtonCommon as _, ButtonStyle, ContextMenu, LabelSize, PopoverMenu, PopoverMenuHandle,
    rems_from_px,
};

use crate::actions::{
    CloseBinary, FocusFilter, FollowLink, FollowSystemTheme, MinimizeWindow, Open,
    ToggleFunctionColumns, ToggleFunctions, ToggleListing, ToggleTheme, ZoomWindow,
};
use crate::binary::Binary;
use crate::goto::GoTo;
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

/// What a row needs before it can run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Need {
    /// Nothing: it runs at any time.
    Nothing,
    /// An open binary.
    Binary,
}

impl Need {
    /// Returns why a row with this need is disabled, `None` when `binary_open` meets it.
    ///
    /// # Arguments
    ///
    /// * `binary_open` - Whether the window has a binary open.
    #[must_use]
    pub const fn unmet(self, binary_open: bool) -> Option<&'static str> {
        match self {
            Self::Binary if !binary_open => Some("needs a binary"),
            Self::Binary | Self::Nothing => None,
        }
    }
}

/// One row of a menu.
#[derive(Debug, Clone, Copy)]
pub enum Row {
    /// An action, its label and what it needs.
    Item {
        /// What the menu and the palette call it.
        label: &'static str,
        /// Builds the action the row runs.
        action: fn() -> Box<dyn Action>,
        /// What it needs before it can run.
        need: Need,
    },
    /// A hairline between groups of rows.
    Separator,
}

/// One menu of the menu bar.
#[derive(Debug, Clone, Copy)]
pub struct AppMenu {
    /// The menu's name in the bar.
    pub name: &'static str,
    /// Its rows, top to bottom.
    pub rows: &'static [Row],
}

/// Returns a boxed `A`, for a [`Row`]'s action.
fn boxed<A: Action + Default>() -> Box<dyn Action> {
    Box::new(A::default())
}

/// Returns a row running `A`, labelled `label`, that needs `need`.
///
/// # Arguments
///
/// * `label` - What the menu calls it.
/// * `need` - What it needs before it can run.
const fn row<A: Action + Default>(label: &'static str, need: Need) -> Row {
    Row::Item {
        label,
        action: boxed::<A>,
        need,
    }
}

/// The menu bar, left to right. Analysis, Edit's code commands and the rest of the
/// designed rows join it with the actions that run them.
pub const MENUS: &[AppMenu] = &[
    AppMenu {
        name: "File",
        rows: &[
            row::<Open>("Open Binary...", Need::Nothing),
            row::<CloseBinary>("Close Binary", Need::Binary),
            Row::Separator,
            row::<zed_actions::OpenSettingsFile>("Settings File", Need::Nothing),
            row::<zed_actions::Quit>("Quit", Need::Nothing),
        ],
    },
    AppMenu {
        name: "Edit",
        rows: &[row::<FocusFilter>("Find Function", Need::Binary)],
    },
    AppMenu {
        name: "View",
        rows: &[
            row::<ToggleFunctions>("Functions", Need::Binary),
            row::<ToggleFunctionColumns>("Function Columns", Need::Binary),
            row::<ToggleListing>("Toggle Listing", Need::Binary),
            Row::Separator,
            row::<workspace::ToggleLeftDock>("Toggle Left Dock", Need::Nothing),
            row::<workspace::ToggleBottomDock>("Toggle Bottom Dock", Need::Nothing),
            row::<workspace::ToggleRightDock>("Toggle Right Dock", Need::Nothing),
            Row::Separator,
            row::<ToggleTheme>("Toggle Light and Dark", Need::Nothing),
            row::<FollowSystemTheme>("Follow System Theme", Need::Nothing),
        ],
    },
    AppMenu {
        name: "Go",
        rows: &[
            row::<GoTo>("Go to Address or Name...", Need::Binary),
            row::<FollowLink>("Follow Link", Need::Binary),
            Row::Separator,
            row::<workspace::pane::GoBack>("Back", Need::Binary),
            row::<workspace::pane::GoForward>("Forward", Need::Binary),
        ],
    },
    AppMenu {
        name: "Window",
        rows: &[
            row::<MinimizeWindow>("Minimize", Need::Nothing),
            row::<ZoomWindow>("Zoom", Need::Nothing),
        ],
    },
    AppMenu {
        name: "Help",
        rows: &[
            row::<zed_actions::command_palette::Toggle>("Command Palette", Need::Nothing),
            Row::Separator,
            row::<zed_actions::About>("About borer", Need::Nothing),
        ],
    },
];

/// Returns `label` as a disabled row shows it: with the reason it is disabled.
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

/// Returns the menu bar for the platform's menus (macOS draws them), with the rows whose
/// need is unmet disabled.
///
/// # Arguments
///
/// * `binary_open` - Whether the window has a binary open.
#[must_use]
pub fn platform_menus(binary_open: bool) -> Vec<Menu> {
    MENUS
        .iter()
        .map(|menu| {
            Menu::new(menu.name).items(menu.rows.iter().map(|row| match *row {
                Row::Item {
                    label,
                    action,
                    need,
                } => {
                    let unmet = need.unmet(binary_open);
                    MenuItem::Action {
                        name: shown_label(label, unmet),
                        action: action(),
                        os_action: None,
                        checked: false,
                        disabled: unmet.is_some(),
                    }
                }
                Row::Separator => MenuItem::separator(),
            }))
        })
        .collect()
}

/// Gives the platform the menu bar for `binary`'s state, and again on each change of it.
///
/// # Arguments
///
/// * `binary` - The window's binary.
/// * `cx` - Application context.
///
/// # Returns
///
/// The observation, which keeps the menus following the binary while it is held.
pub fn follow_binary(binary: &Entity<Binary>, cx: &mut App) -> Subscription {
    let open = binary.read(cx).loaded().is_some();
    cx.set_menus(platform_menus(open));
    cx.observe(binary, |binary, cx| {
        let open = binary.read(cx).loaded().is_some();
        cx.set_menus(platform_menus(open));
    })
}

/// Returns the context menu of `menu`, its rows disabled where the window's binary does not
/// meet their need, run in the context of the element focused when it opened.
///
/// # Arguments
///
/// * `menu` - The menu.
/// * `binary` - The window's binary.
/// * `window` - Window the menu opens in.
/// * `cx` - Application context.
fn context_menu(
    menu: AppMenu,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<ContextMenu> {
    let open = binary.read(cx).loaded().is_some();
    ContextMenu::build(window, cx, move |built, window, cx| {
        let built = built.when_some(window.focused(cx), |built, focused| built.context(focused));
        menu.rows.iter().fold(built, |built, row| match *row {
            Row::Item {
                label,
                action,
                need,
            } => {
                let unmet = need.unmet(open);
                built.action_disabled_when(unmet.is_some(), shown_label(label, unmet), action())
            }
            Row::Separator => built.separator(),
        })
    })
}

/// The in-window menu bar of Windows and Linux: one popover per menu of [`MENUS`].
pub struct MenuBar {
    /// The window's binary, whose state enables the rows.
    binary: Entity<Binary>,
    /// One handle per menu, in [`MENUS`] order.
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
            handles: MENUS.iter().map(|_| PopoverMenuHandle::default()).collect(),
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
        let menus = MENUS
            .iter()
            .zip(self.handles.iter().cloned())
            .map(|(menu, handle)| {
                let menu = *menu;
                let binary = self.binary.clone();
                let all = all.clone();
                let hovered = handle.clone();
                div()
                    .id(SharedString::from(format!("{}-menu", menu.name)))
                    .occlude()
                    .child(
                        PopoverMenu::new(SharedString::from(format!("{}-menu-popover", menu.name)))
                            .menu(move |window, cx| Some(context_menu(menu, &binary, window, cx)))
                            .trigger(
                                Button::new(
                                    SharedString::from(format!("{}-menu-trigger", menu.name)),
                                    menu.name,
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
    use std::collections::BTreeSet;

    use gpui::{AppContext as _, TestAppContext, VisualTestContext};

    use super::{MENUS, MenuBar, Need, Row, Step, platform_menus};
    use crate::actions::CloseBinary;
    use crate::app_view::tests::{init, load_sample, open};
    use crate::binary::{Binary, NO_BINARY};
    use crate::decompile_item::DecompileItem;
    use crate::functions_panel::FunctionsPanel;
    use crate::start_item::StartItem;

    /// Returns the names of every action in [`MENUS`].
    fn menu_actions() -> BTreeSet<&'static str> {
        MENUS
            .iter()
            .flat_map(|menu| menu.rows.iter())
            .filter_map(|row| match row {
                Row::Item { action, .. } => Some(action().name()),
                Row::Separator => None,
            })
            .collect()
    }

    /// A row needing a binary says so while none is open, and runs once one is.
    ///
    /// # Panics
    ///
    /// Panics if a need is met or unmet wrongly.
    #[test]
    fn a_row_says_what_it_needs() {
        assert_eq!(Need::Binary.unmet(false), Some("needs a binary"));
        assert_eq!(Need::Binary.unmet(true), None);
        assert_eq!(Need::Nothing.unmet(false), None);
        let names = |open| -> Vec<String> {
            platform_menus(open)
                .into_iter()
                .flat_map(|menu| menu.owned().items)
                .filter_map(|item| match item {
                    gpui::OwnedMenuItem::Action { name, disabled, .. } => {
                        Some(format!("{name}{}", if disabled { " off" } else { "" }))
                    }
                    _ => None,
                })
                .collect()
        };
        assert!(names(false).contains(&String::from("Close Binary (needs a binary) off")));
        assert!(names(true).contains(&String::from("Close Binary")));
        assert!(names(false).contains(&String::from("Open Binary...")));
    }

    /// Every `borer` action is in a menu, and with a
    /// binary open every menu action is available where the person works, so the palette
    /// offers it and running it reaches a handler; the platform holds the same menus.
    ///
    /// # Panics
    ///
    /// Panics if an action is in no menu, a menu row has no handler in reach, or the
    /// platform holds other menus.
    #[gpui::test]
    fn every_menu_row_has_a_handler_and_every_action_a_row(cx: &mut TestAppContext) {
        every_menu_row_has_a_handler_and_every_action_a_row_steps(cx);
    }

    /// Runs the steps of [`every_menu_row_has_a_handler_and_every_action_a_row`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`every_menu_row_has_a_handler_and_every_action_a_row`] says.
    fn every_menu_row_has_a_handler_and_every_action_a_row_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        let rows = menu_actions();
        let declared: Vec<&str> = cx.update(|_, cx| {
            cx.all_action_names()
                .iter()
                .copied()
                .filter(|name| name.starts_with("borer::"))
                .collect()
        });
        for name in &declared {
            assert!(rows.contains(name), "{name} is in no menu");
        }
        let available = cx.update(|window, cx| window.available_actions(cx));
        for name in &rows {
            assert!(
                available.iter().any(|action| action.name() == *name),
                "{name} has no handler in reach"
            );
        }
        let held: Vec<String> = cx
            .update(|_, cx| cx.get_menus())
            .unwrap_or_default()
            .into_iter()
            .map(|menu| menu.name.to_string())
            .collect();
        let want: Vec<String> = MENUS.iter().map(|menu| menu.name.to_owned()).collect();
        assert_eq!(held, want, "the platform holds other menus");
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
            let last = MENUS.len() - 1;
            bar.update_in(cx, |bar, window, cx| bar.step(Step::Left, window, cx));
            settle(cx);
            assert_eq!(open(cx), Some(last));
            bar.update_in(cx, |bar, window, cx| bar.step(Step::Right, window, cx));
            settle(cx);
            assert_eq!(open(cx), Some(0));
        }
    }

    /// Close Binary takes the panel out of the dock and the function's tab away, leaves the
    /// start tab and says no binary is open; the next load docks the panel again.
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
