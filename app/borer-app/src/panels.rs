//! The app's dock panels, one row each.
//!
//! A row holds what the rail, the docks and the command palette read of a panel (its key,
//! title, icon, toggle, docks, size, rail hooks and activation priority); [`add_panels`] is
//! the one way to add them to a workspace, each in the dock the last run left it active in.

use gpui::{Action, App, Context, Entity, Window};
use workspace::DockStructure;
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel};

use crate::app_assets::Glyph;
use crate::binary::Binary;
use crate::rail::PanelHooks;

/// One dock panel's facts.
pub struct PanelSpec {
    /// Name Zed saves the panel's dock state and size under.
    pub key: &'static str,
    /// What the panel is called on its header, its rail cell and its tooltip.
    pub title: &'static str,
    /// Icon of its rail cell and dock button.
    pub icon: Glyph,
    /// The action that shows the panel and focuses it, or moves focus back (the chat's hides it).
    pub toggle: &'static dyn Action,
    /// Dock the panel starts in before the person moves it.
    pub dock: DockPosition,
    /// Docks the panel may sit in.
    pub docks: &'static [DockPosition],
    /// Width or height in logical pixels before the person resizes it.
    pub size_px: f32,
    /// What the rail does with the panel: find it, open or close it, move it.
    pub hooks: PanelHooks,
    /// Builds the panel over the window's binary in a dock and adds it to the workspace.
    pub add:
        fn(&mut Workspace, &Entity<Binary>, DockPosition, &mut Window, &mut Context<'_, Workspace>),
    /// Takes the panel out of its dock, when it is docked.
    pub remove: fn(&mut Workspace, &mut Window, &mut Context<'_, Workspace>),
    /// What [`Self::toggle`] does: shows the panel and focuses it, or moves focus back; the
    /// chat's hides it.
    pub focus: fn(&mut Workspace, &mut Window, &mut Context<'_, Workspace>),
    /// Returns whether the panel shows nothing older than the binary state of the given
    /// fingerprint; true while it is not docked.
    pub current: fn(&Workspace, Option<u64>, &App) -> bool,
}

/// Registers every panel's toggle on `workspace`, docked or not yet, in reach as its
/// command row says ([`crate::commands::register_boxed`]).
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
pub fn register_toggles(workspace: &mut Workspace, binary: &Entity<Binary>) {
    for spec in PANELS {
        crate::commands::register_boxed(workspace, binary, spec.toggle, spec.focus);
    }
    crate::chat::register(workspace, binary);
}

impl std::fmt::Debug for PanelSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PanelSpec")
            .field("key", &self.key)
            .field("dock", &self.dock)
            .finish_non_exhaustive()
    }
}

/// Takes the panel of type `T` out of its dock, when it is docked: a row's
/// [`PanelSpec::remove`].
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn remove<T: Panel>(
    workspace: &mut Workspace,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    if let Some(panel) = workspace.panel::<T>(cx) {
        workspace.remove_panel(&panel, window, cx);
    }
}

/// Writes the methods of Zed's [`Panel`] that a panel reads from its [`PanelSpec`] row,
/// inside the panel's `impl Panel`.
///
/// The panel keeps its dock in a `position` field. Moving it pokes the settings store
/// once: Zed's dock moves a panel only when the store changes (the settings observer
/// `Dock::add_panel` sets), and the app keeps no dock setting of its own to write.
///
/// # Arguments
///
/// * `$spec` - The panel's row, a `&PanelSpec` expression.
macro_rules! spec_panel {
    ($spec:expr) => {
        fn persistent_name() -> &'static str {
            $spec.key
        }

        fn panel_key() -> &'static str {
            $spec.key
        }

        fn position(&self, _window: &::gpui::Window, _cx: &::gpui::App) -> DockPosition {
            self.position
        }

        fn position_is_valid(&self, position: DockPosition) -> bool {
            $spec.docks.contains(&position)
        }

        fn set_position(
            &mut self,
            position: DockPosition,
            _window: &mut ::gpui::Window,
            cx: &mut ::gpui::Context<'_, Self>,
        ) {
            use ::gpui::BorrowAppContext as _;
            self.position = position;
            cx.notify();
            cx.update_global::<::settings::SettingsStore, _>(|_, _| {});
        }

        fn default_size(&self, _window: &::gpui::Window, _cx: &::gpui::App) -> ::gpui::Pixels {
            ::gpui::px($spec.size_px)
        }

        fn icon(&self, _window: &::gpui::Window, _cx: &::gpui::App) -> Option<::ui::IconName> {
            match $spec.icon {
                $crate::app_assets::Glyph::Zed(name) => Some(name),
                $crate::app_assets::Glyph::App(_) => None,
            }
        }

        fn icon_tooltip(
            &self,
            _window: &::gpui::Window,
            _cx: &::gpui::App,
        ) -> Option<&'static str> {
            Some($spec.title)
        }

        fn toggle_action(&self) -> Box<dyn ::gpui::Action> {
            $spec.toggle.boxed_clone()
        }

        fn activation_priority(&self) -> u32 {
            $crate::panels::priority($spec.key)
        }
    };
}
pub(crate) use spec_panel;

/// Every dock panel of the app, in activation order.
pub const PANELS: &[&PanelSpec] = &[
    &crate::functions_panel::PANEL,
    &crate::tables::STRINGS,
    &crate::tables::IMPORTS,
    &crate::tables::EXPORTS,
    &crate::xrefs::XREFS,
    &crate::types::PANEL,
    &crate::call_tree_panel::PANEL,
    &crate::chat::PANEL,
];

/// Returns the activation priority of the panel saved under `key`: its place in [`PANELS`]
/// plus one, so no two panels share one, as Zed's dock requires.
///
/// # Arguments
///
/// * `key` - The panel's key.
///
/// # Returns
///
/// The priority; one past every listed panel for a key [`PANELS`] does not hold.
#[must_use]
pub fn priority(key: &str) -> u32 {
    let at = PANELS.iter().position(|spec| spec.key == key);
    let at = at.unwrap_or(PANELS.len());
    u32::try_from(at).unwrap_or(u32::MAX).saturating_add(1)
}

/// Returns the dock a saved layout shows the panel `key` active in, else `default`.
///
/// # Arguments
///
/// * `saved` - The layout the last run left, if any.
/// * `key` - The panel's key.
/// * `default` - Where the panel goes when the layout does not name it.
#[must_use]
pub fn saved_dock(saved: Option<&DockStructure>, key: &str, default: DockPosition) -> DockPosition {
    let Some(docks) = saved else {
        return default;
    };
    let named = [
        (DockPosition::Left, &docks.left),
        (DockPosition::Right, &docks.right),
        (DockPosition::Bottom, &docks.bottom),
    ];
    named
        .into_iter()
        .find(|(_, dock)| dock.active_panel.as_deref() == Some(key))
        .map_or(default, |(position, _)| position)
}

/// Adds every panel of [`PANELS`] to `workspace`, each in the dock `saved` shows it in, else
/// its own.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary, which every panel follows.
/// * `saved` - The layout the last run left, if any.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn add_panels(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    saved: Option<&DockStructure>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    for spec in PANELS {
        let dock = saved_dock(saved, spec.key, spec.dock);
        let dock = if spec.docks.contains(&dock) {
            dock
        } else {
            spec.dock
        };
        (spec.add)(workspace, binary, dock, window, cx);
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use gpui::{Entity, TestAppContext};
    use workspace::dock::DockPosition;
    use workspace::{DockData, DockStructure};

    use super::{PANELS, priority, saved_dock};
    use crate::app_view::tests::{init, load_sample, open};

    /// Every panel the workspace docks is a row of [`PANELS`], and it activates at the
    /// priority its row's place gives, never a number of its own.
    #[gpui::test]
    fn every_docked_panel_takes_its_priority_from_its_row(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        let workspace = app.workspace.clone();
        let mut docked = Vec::new();
        workspace.update_in(cx, |workspace, window, cx| {
            for dock in workspace.all_docks().map(Entity::clone) {
                for ix in 0..dock.read(cx).panels_len() {
                    dock.update(cx, |dock, cx| dock.activate_panel(ix, window, cx));
                    let panel = dock.read(cx).active_panel().unwrap().clone();
                    docked.push((panel.persistent_name(), panel.activation_priority(cx)));
                }
            }
        });
        docked.sort_unstable();
        let mut rows: Vec<_> = PANELS.iter().map(|s| (s.key, priority(s.key))).collect();
        rows.sort_unstable();
        assert_eq!(docked, rows);
    }

    /// Within each dock, the panels that may sit there have distinct priorities, every key
    /// is its own, and a priority is the panel's place in the list.
    ///
    /// # Panics
    ///
    /// Panics if two panels of one dock share a priority or a key.
    #[test]
    fn every_panel_has_a_unique_priority_in_every_dock() {
        for dock in [
            DockPosition::Left,
            DockPosition::Right,
            DockPosition::Bottom,
        ] {
            let mut seen: Vec<u32> = PANELS
                .iter()
                .filter(|spec| spec.docks.contains(&dock))
                .map(|spec| priority(spec.key))
                .collect();
            let count = seen.len();
            seen.sort_unstable();
            seen.dedup();
            assert_eq!(seen.len(), count, "{dock:?}");
        }
        for (at, spec) in PANELS.iter().enumerate() {
            assert_eq!(
                priority(spec.key),
                u32::try_from(at).unwrap() + 1,
                "{}",
                spec.key
            );
            assert!(spec.docks.contains(&spec.dock), "{}", spec.key);
        }
    }

    /// A saved layout names the dock a panel was active in, the bottom one included; a
    /// layout that names it nowhere, or none, leaves it in its own.
    ///
    /// # Panics
    ///
    /// Panics if a dock is missed.
    #[test]
    fn saved_dock_finds_a_panel_in_any_dock() {
        let data = |key: Option<&str>| DockData {
            visible: true,
            active_panel: key.map(str::to_owned),
            zoom: false,
        };
        let layout = |left, right, bottom| DockStructure {
            left: data(left),
            right: data(right),
            bottom: data(bottom),
        };
        let found = |docks: &DockStructure| saved_dock(Some(docks), "P", DockPosition::Left);
        assert_eq!(found(&layout(Some("P"), None, None)), DockPosition::Left);
        assert_eq!(found(&layout(None, Some("P"), None)), DockPosition::Right);
        assert_eq!(found(&layout(None, None, Some("P"))), DockPosition::Bottom);
        let elsewhere = layout(Some("Q"), Some("R"), None);
        assert_eq!(
            saved_dock(Some(&elsewhere), "P", DockPosition::Right),
            DockPosition::Right
        );
        assert_eq!(
            saved_dock(None, "P", DockPosition::Bottom),
            DockPosition::Bottom
        );
    }
}
