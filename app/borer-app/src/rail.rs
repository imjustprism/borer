//! The rail: a column of icons left of the docks, one per panel, that shows which panel is
//! open and opens, closes or moves it, with Settings in its last cell.
//!
//! # Adding a panel
//!
//! The rail draws one cell per row of [`crate::panels::PANELS`], then one disabled cell per
//! row of [`PLANNED`], the panels the design has that are not built yet. A branch that
//! builds a panel moves its row from [`PLANNED`] to `PANELS`, its hooks built by [`panel`]:
//!
//! ```ignore
//! hooks: panel::<StringsPanel>(),
//! ```
//!
//! The panel type is Zed's [`Panel`], docked by the workspace once a binary loads (as
//! [`crate::app_view::dock_panels`] docks every panel), and the action
//! toggles it and is registered on the workspace and bound in the keymap, so the cell's
//! tooltip shows its key. Every cell reads its state from Zed's docks through the public
//! [`Workspace`] API, so a dock changed from anywhere (a key, a drag, a restore) shows here.

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, Context, Entity, InteractiveElement as _, IntoElement, ParentElement as _,
    Render, SharedString, StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity,
    Window, div, px,
};
use theme::ActiveTheme as _;
use ui::{Color, ContextMenu, IconName, IconSize, Tooltip, right_click_menu, v_flex};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel};

use crate::app_assets::{AppIcon, Glyph};
use crate::binary::Binary;
use crate::panels::{PANELS, PanelSpec};
use crate::title_bar::MARK_CELL_PX;

/// Side in logical pixels of a rail cell.
const CELL_PX: f32 = 32.0;

/// Gap in logical pixels between rail cells.
const GAP_PX: f32 = 2.0;

/// Padding in logical pixels above the first rail cell and below the last.
const PAD_PX: f32 = 6.0;

/// Corner radius in logical pixels of a rail cell.
const RADIUS_PX: f32 = 5.0;

/// Width in logical pixels of the bar marking the open panel's cell.
const BAR_PX: f32 = 2.0;

/// Where a panel sits, read from Zed's docks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Placement {
    /// The dock it is in.
    pub dock: DockPosition,
    /// Whether it is the open panel of an open dock.
    pub open: bool,
}

/// The workspace hooks of one panel type, each a function of Zed's public API.
#[derive(Debug, Clone, Copy)]
pub struct PanelHooks {
    /// Returns where the panel sits, `None` while it is not docked.
    pub placed: fn(&Workspace, &Window, &App) -> Option<Placement>,
    /// Closes the panel's dock when the panel is open, else opens and focuses it.
    pub click: fn(&mut Workspace, &mut Window, &mut Context<'_, Workspace>),
    /// Returns whether the panel may sit in a dock.
    pub fits: fn(&Workspace, DockPosition, &App) -> bool,
    /// Moves the panel to a dock.
    pub move_to: fn(&mut Workspace, DockPosition, &mut Window, &mut Context<'_, Workspace>),
}

/// What a rail cell stands for.
#[derive(Debug, Clone, Copy)]
pub enum Slot {
    /// A panel the app has.
    Panel(&'static PanelSpec),
    /// A panel the design has that is not built yet; its cell is drawn disabled.
    Planned,
}

/// One cell of the rail.
#[derive(Debug, Clone, Copy)]
pub struct RailEntry {
    /// The panel's name, in the tooltip and the menus.
    pub name: &'static str,
    /// Its icon.
    pub glyph: Glyph,
    /// What it stands for.
    pub slot: Slot,
}

/// Returns where the panel of type `T` sits.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `window` - The window.
/// * `cx` - Application context reading the docks.
fn placed<T: Panel>(workspace: &Workspace, window: &Window, cx: &App) -> Option<Placement> {
    let panel = workspace.panel::<T>(cx)?;
    let dock = panel.read(cx).position(window, cx);
    let docked = workspace.dock_at_position(dock).read(cx);
    let open = docked.is_open()
        && docked
            .active_panel()
            .is_some_and(|active| active.panel_id() == panel.entity_id());
    Some(Placement { dock, open })
}

/// Closes the dock of the panel of type `T` when the panel is open in it, else opens and
/// focuses the panel.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `window` - The window.
/// * `cx` - Workspace context.
fn click<T: Panel>(
    workspace: &mut Workspace,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    if placed::<T>(workspace, window, cx).is_some_and(|placement| placement.open) {
        workspace.close_panel::<T>(window, cx);
    } else {
        workspace.focus_panel::<T>(window, cx);
    }
}

/// Returns whether the panel of type `T` may sit in `dock`.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `dock` - The dock.
/// * `cx` - Application context.
fn fits<T: Panel>(workspace: &Workspace, dock: DockPosition, cx: &App) -> bool {
    workspace
        .panel::<T>(cx)
        .is_some_and(|panel| panel.read(cx).position_is_valid(dock))
}

/// Moves the panel of type `T` to `dock`, when it may sit there.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `dock` - The dock.
/// * `window` - The window.
/// * `cx` - Workspace context.
fn move_to<T: Panel>(
    workspace: &mut Workspace,
    dock: DockPosition,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    if let Some(panel) = workspace
        .panel::<T>(cx)
        .filter(|_| fits::<T>(workspace, dock, cx))
    {
        panel.update(cx, |panel, cx| panel.set_position(dock, window, cx));
    }
}

/// Returns the rail hooks of panel type `T`.
#[must_use]
pub const fn panel<T: Panel>() -> PanelHooks {
    PanelHooks {
        placed: placed::<T>,
        click: click::<T>,
        fits: fits::<T>,
        move_to: move_to::<T>,
    }
}

/// Returns the rail's cells, top to bottom: every built panel of [`PANELS`], then every
/// cell of [`PLANNED`].
#[must_use]
pub fn cells() -> Vec<RailEntry> {
    let built = PANELS.iter().map(|spec| RailEntry {
        name: spec.title,
        glyph: spec.icon,
        slot: Slot::Panel(spec),
    });
    built.chain(PLANNED.iter().copied()).collect()
}

/// The panels the design has that are not built yet, drawn as disabled cells below the
/// built ones; a branch that builds one moves its row to [`PANELS`].
pub const PLANNED: &[RailEntry] = &[
    RailEntry {
        name: "Search",
        glyph: Glyph::Zed(IconName::MagnifyingGlass),
        slot: Slot::Planned,
    },
    RailEntry {
        name: "Packs",
        glyph: Glyph::App(AppIcon::Packs),
        slot: Slot::Planned,
    },
];

/// The docks a panel can be moved to from its cell's menu, with their names.
const DOCKS: [(DockPosition, &str); 3] = [
    (DockPosition::Left, "Move to Left"),
    (DockPosition::Bottom, "Move to Bottom"),
    (DockPosition::Right, "Move to Right"),
];

/// What a cell shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellState {
    /// Its panel is not built yet.
    Planned,
    /// No binary is open, so no panel is docked.
    NeedsBinary,
    /// Its panel is docked but not the open one of an open dock.
    Closed,
    /// Its panel is the open one of an open dock.
    Open,
}

/// The rail, left of Zed's workspace.
pub struct Rail {
    /// The window's workspace, whose docks the cells read.
    workspace: WeakEntity<Workspace>,
    /// The window's binary; with none open every panel cell is disabled.
    binary: Entity<Binary>,
    /// Redraws the rail when a dock or the binary changes.
    _observe: Vec<Subscription>,
}

impl std::fmt::Debug for Rail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rail").finish_non_exhaustive()
    }
}

impl Rail {
    /// Returns the rail over `workspace`'s docks.
    ///
    /// # Arguments
    ///
    /// * `workspace` - The window's workspace.
    /// * `binary` - The window's binary.
    /// * `cx` - Rail context.
    #[must_use]
    pub fn new(
        workspace: &Entity<Workspace>,
        binary: Entity<Binary>,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let docks = {
            let workspace = workspace.read(cx);
            [
                workspace.left_dock().clone(),
                workspace.bottom_dock().clone(),
                workspace.right_dock().clone(),
            ]
        };
        let mut observe: Vec<Subscription> = docks
            .iter()
            .map(|dock| cx.observe(dock, |_, _, cx| cx.notify()))
            .collect();
        observe.push(cx.observe(&binary, |_, _, cx| cx.notify()));
        Self {
            workspace: workspace.downgrade(),
            binary,
            _observe: observe,
        }
    }

    /// Returns what the cell of `entry` shows.
    ///
    /// # Arguments
    ///
    /// * `entry` - A row of [`cells`].
    /// * `window` - The window.
    /// * `cx` - Application context reading the docks.
    #[must_use]
    pub fn state(&self, entry: &RailEntry, window: &Window, cx: &App) -> CellState {
        let Slot::Panel(spec) = entry.slot else {
            return CellState::Planned;
        };
        let hooks = spec.hooks;
        let placed = self
            .workspace
            .upgrade()
            .and_then(|workspace| (hooks.placed)(workspace.read(cx), window, cx));
        match placed {
            Some(Placement { open: true, .. }) => CellState::Open,
            Some(Placement { open: false, .. }) => CellState::Closed,
            None if self.binary.read(cx).loaded().is_none() => CellState::NeedsBinary,
            None => CellState::Closed,
        }
    }

    /// Runs `f` on the workspace, when it is still open.
    ///
    /// # Arguments
    ///
    /// * `workspace` - The workspace.
    /// * `window` - The window.
    /// * `cx` - Application context.
    /// * `f` - What to do.
    fn on_workspace(
        workspace: &WeakEntity<Workspace>,
        window: &mut Window,
        cx: &mut App,
        f: impl FnOnce(&mut Workspace, &mut Window, &mut Context<'_, Workspace>),
    ) {
        if let Some(workspace) = workspace.upgrade() {
            workspace.update(cx, |workspace, cx| f(workspace, window, cx));
        }
    }

    /// Returns the menu that moves `hooks`' panel to another dock.
    ///
    /// # Arguments
    ///
    /// * `hooks` - The panel's hooks.
    /// * `workspace` - The window's workspace.
    /// * `window` - The window.
    /// * `cx` - Application context.
    fn move_menu(
        hooks: PanelHooks,
        workspace: &WeakEntity<Workspace>,
        window: &mut Window,
        cx: &mut App,
    ) -> Entity<ContextMenu> {
        let here = workspace.upgrade().and_then(|workspace| {
            (hooks.placed)(workspace.read(cx), window, cx).map(|placement| placement.dock)
        });
        let fits = |dock| {
            workspace
                .upgrade()
                .is_some_and(|workspace| (hooks.fits)(workspace.read(cx), dock, cx))
        };
        let rows: Vec<(DockPosition, &str, bool)> = DOCKS
            .into_iter()
            .map(|(dock, label)| (dock, label, here != Some(dock) && fits(dock)))
            .collect();
        let workspace = workspace.clone();
        ContextMenu::build(window, cx, move |menu, _, _| {
            rows.into_iter().fold(menu, |menu, (dock, label, enabled)| {
                let workspace = workspace.clone();
                menu.item(ui::ContextMenuEntry::new(label).disabled(!enabled).handler(
                    move |window, cx| {
                        Self::on_workspace(&workspace, window, cx, |workspace, window, cx| {
                            (hooks.move_to)(workspace, dock, window, cx);
                        });
                    },
                ))
            })
        })
    }

    /// Returns the cell of `entry`, at row `ix`.
    ///
    /// # Arguments
    ///
    /// * `ix` - The row's index in [`cells`].
    /// * `entry` - The row.
    /// * `window` - The window.
    /// * `cx` - Rail context.
    fn render_cell(
        &self,
        ix: usize,
        entry: &RailEntry,
        window: &Window,
        cx: &mut Context<'_, Self>,
    ) -> AnyElement {
        let state = self.state(entry, window, cx);
        let colors = cx.theme().colors();
        let (hover, lit, fg) = (colors.element_hover, colors.element_selected, colors.text);
        let color = match state {
            CellState::Planned | CellState::NeedsBinary => Color::Disabled,
            CellState::Closed => Color::Placeholder,
            CellState::Open => Color::Default,
        };
        let icon = entry.glyph.icon().size(IconSize::Medium).color(color);
        let cell = div()
            .id(("rail-cell", ix))
            .relative()
            .size(px(CELL_PX))
            .flex()
            .items_center()
            .justify_center()
            .rounded(px(RADIUS_PX))
            .when(state == CellState::Open, |cell| {
                cell.bg(lit).child(
                    div()
                        .absolute()
                        .left(px(-(MARK_CELL_PX - CELL_PX) / 2.0))
                        .top_0()
                        .h_full()
                        .w(px(BAR_PX))
                        .bg(fg),
                )
            })
            .child(icon);
        let name = entry.name;
        let Slot::Panel(spec) = entry.slot else {
            let why = format!("{name}: not built yet");
            return cell.tooltip(Tooltip::text(why)).into_any_element();
        };
        if state == CellState::NeedsBinary {
            let why = format!("{name}: open a binary first");
            return cell.tooltip(Tooltip::text(why)).into_any_element();
        }
        let hooks = spec.hooks;
        let workspace = self.workspace.clone();
        let menu_workspace = self.workspace.clone();
        let cell = cell
            .cursor_pointer()
            .hover(move |cell| cell.bg(hover))
            .tooltip(Tooltip::for_action_title(name, spec.toggle))
            .on_click(move |_, window, cx| {
                Self::on_workspace(&workspace, window, cx, hooks.click);
            });
        right_click_menu(SharedString::from(format!("rail-menu-{ix}")))
            .trigger(move |_, _, _| cell)
            .menu(move |window, cx| Self::move_menu(hooks, &menu_workspace, window, cx))
            .into_any_element()
    }

    /// Returns the Settings cell at the rail's foot, which opens the settings file.
    ///
    /// # Arguments
    ///
    /// * `cx` - Rail context.
    fn render_settings(cx: &mut Context<'_, Self>) -> AnyElement {
        let hover = cx.theme().colors().element_hover;
        let open = zed_actions::OpenSettingsFile;
        div()
            .id("rail-settings")
            .size(px(CELL_PX))
            .flex()
            .items_center()
            .justify_center()
            .rounded(px(RADIUS_PX))
            .cursor_pointer()
            .hover(move |cell| cell.bg(hover))
            .tooltip(Tooltip::for_action_title("Settings File", &open))
            .on_click(|_, window, cx| {
                window.dispatch_action(Box::new(zed_actions::OpenSettingsFile), cx);
            })
            .child(
                Glyph::Zed(IconName::Settings)
                    .icon()
                    .size(IconSize::Medium)
                    .color(Color::Placeholder),
            )
            .into_any_element()
    }
}

impl Render for Rail {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let cells: Vec<AnyElement> = cells()
            .iter()
            .enumerate()
            .map(|(ix, entry)| self.render_cell(ix, entry, window, cx))
            .collect();
        let colors = cx.theme().colors();
        v_flex()
            .w(px(MARK_CELL_PX))
            .h_full()
            .flex_none()
            .items_center()
            .justify_between()
            .py(px(PAD_PX))
            .bg(colors.title_bar_background)
            .border_r_1()
            .border_color(colors.border)
            .child(v_flex().gap(px(GAP_PX)).children(cells))
            .child(Self::render_settings(cx))
    }
}

#[cfg(test)]
mod tests {
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use workspace::dock::{DockPosition, PanelButtons};

    use super::{CellState, PLANNED, Rail, Slot, cells};
    use crate::app_view::AppWindow;
    use crate::app_view::tests::{init, load_sample, open};
    use crate::functions_panel::FunctionsPanel;
    use crate::panels::PANELS;
    use crate::shell::Shell;

    /// Returns the window's rail.
    ///
    /// # Panics
    ///
    /// Panics if the window's root is not the app's shell.
    fn rail(cx: &mut VisualTestContext) -> Entity<Rail> {
        let shell = cx
            .update(|window, _| window.root::<Shell>())
            .flatten()
            .unwrap();
        shell.read_with(cx, |shell, _| shell.rail().clone())
    }

    /// Returns the state of every rail cell.
    fn states(rail: &Entity<Rail>, cx: &mut VisualTestContext) -> Vec<CellState> {
        cx.update(|window, cx| {
            let rail = rail.read(cx);
            cells()
                .iter()
                .map(|entry| rail.state(entry, window, cx))
                .collect()
        })
    }

    /// Runs the functions cell's click, as a click on it does.
    ///
    /// # Panics
    ///
    /// Panics if the first cell is not the functions panel.
    fn click_functions(app: &AppWindow, cx: &mut VisualTestContext) {
        let Slot::Panel(spec) = cells()[0].slot else {
            panic!("the first cell is the functions panel");
        };
        app.workspace.update_in(cx, |workspace, window, cx| {
            (spec.hooks.click)(workspace, window, cx);
        });
        cx.run_until_parked();
    }

    /// Before a load every cell is disabled; the load opens the functions cell; a click
    /// closes and opens it, Zed's own dock key closes it too, and after a move to the right
    /// dock it opens there, a move to the bottom being refused; Zed's own dock buttons are
    /// gone from the status bar, so the rail is the one switch.
    ///
    /// # Panics
    ///
    /// Panics if a cell's state differs from Zed's docks.
    #[gpui::test]
    fn each_cell_shows_its_panels_dock(cx: &mut TestAppContext) {
        each_cell_shows_its_panels_dock_steps(cx);
    }

    /// Runs the steps of [`each_cell_shows_its_panels_dock`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`each_cell_shows_its_panels_dock`] says.
    fn each_cell_shows_its_panels_dock_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let rail = rail(cx);
        let first = |states: Vec<CellState>| states[0];
        let before = states(&rail, cx);
        let (built, planned) = before.split_at(PANELS.len());
        assert!(built.iter().all(|state| *state == CellState::NeedsBinary));
        assert!(planned.iter().all(|state| *state == CellState::Planned));
        load_sample(&app, cx);
        assert_eq!(first(states(&rail, cx)), CellState::Open);
        click_functions(&app, cx);
        assert_eq!(first(states(&rail, cx)), CellState::Closed);
        click_functions(&app, cx);
        assert_eq!(first(states(&rail, cx)), CellState::Open);
        cx.dispatch_action(workspace::ToggleLeftDock);
        cx.run_until_parked();
        assert_eq!(first(states(&rail, cx)), CellState::Closed);
        let Slot::Panel(spec) = cells()[0].slot else {
            panic!("the first cell is the functions panel");
        };
        let hooks = spec.hooks;
        app.workspace.update_in(cx, |workspace, window, cx| {
            assert!(!(hooks.fits)(workspace, DockPosition::Bottom, cx));
            (hooks.move_to)(workspace, DockPosition::Bottom, window, cx);
            (hooks.move_to)(workspace, DockPosition::Right, window, cx);
        });
        cx.run_until_parked();
        app.workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        cx.run_until_parked();
        let placed = cx.update(|window, cx| (hooks.placed)(app.workspace.read(cx), window, cx));
        assert_eq!(
            placed.map(|p| (p.dock, p.open)),
            Some((DockPosition::Right, true))
        );
        assert_eq!(first(states(&rail, cx)), CellState::Open);
        let buttons = app.workspace.read_with(cx, |workspace, cx| {
            workspace
                .status_bar()
                .read(cx)
                .position_of_item::<PanelButtons>()
        });
        assert_eq!(buttons, None);
    }

    /// The rail draws one cell per built panel, in [`PANELS`]' order with its title and
    /// icon, then every cell of [`PLANNED`], each drawn not built.
    ///
    /// # Panics
    ///
    /// Panics if a cell is missing, out of order, built when planned, or drawn twice.
    #[test]
    fn the_rail_draws_every_panel_and_every_planned_cell() {
        let cells = cells();
        assert_eq!(cells.len(), PANELS.len() + PLANNED.len());
        for (cell, spec) in cells.iter().zip(PANELS) {
            let Slot::Panel(built) = cell.slot else {
                panic!("{} is drawn not built", spec.key);
            };
            assert_eq!((cell.name, built.key), (spec.title, spec.key));
        }
        for (cell, planned) in cells[PANELS.len()..].iter().zip(PLANNED) {
            assert!(matches!(cell.slot, Slot::Planned), "{}", cell.name);
            assert_eq!(cell.name, planned.name);
        }
        let names: Vec<_> = cells.iter().map(|cell| cell.name).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(
            unique.len(),
            names.len(),
            "a panel is both built and planned"
        );
    }
}
