//! The app's dock panels, one row each.
//!
//! A row holds what the rail, the docks and the command palette read of a panel (its key,
//! title, icon, toggle, docks, size, rail hooks and activation priority); [`add_panels`] is
//! the one way to add them to a workspace, each in the dock the last run left it active in.

use gpui::{Action, Context, Entity, Window};
use workspace::DockStructure;
use workspace::Workspace;
use workspace::dock::DockPosition;

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
    /// The action that shows the panel and focuses it, or moves focus back.
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
}

impl std::fmt::Debug for PanelSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PanelSpec")
            .field("key", &self.key)
            .field("dock", &self.dock)
            .finish_non_exhaustive()
    }
}

/// Every dock panel of the app, in activation order.
pub const PANELS: &[&PanelSpec] = &[&crate::functions_panel::PANEL];

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
mod tests {
    use workspace::dock::DockPosition;
    use workspace::{DockData, DockStructure};

    use super::{PANELS, priority, saved_dock};

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
