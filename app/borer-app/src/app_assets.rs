//! The app's assets: Zed's, with the borer mark and borer's own icons added.
//!
//! Zed's [`IconName`] is a closed enum over Zed's bundled icons. An [`Icon`] built from a
//! path under `icons/` is drawn like a bundled one (one color, sized by the icon size), so
//! the app serves its icons at `icons/borer/<name>.svg` and names them with [`AppIcon`];
//! [`Glyph`] holds either kind where a place takes both.

use std::borrow::Cow;

use gpui::{AssetSource, SharedString};
use ui::{Icon, IconName};

/// Asset path the borer mark is served at.
pub const MARK_PATH: &str = "borer/mark.svg";

/// An icon of borer's own, drawn in Zed's icon style: 16 by 16, a 1.2 px stroke, round caps
/// and joins, no fill.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AppIcon {
    /// The imports and exports panel: one arrow in, one arrow out.
    ImportsExports,
    /// The types panel: a brace beside fields.
    Types,
    /// The packs panel: stacked layers.
    Packs,
    /// A control-flow graph tab.
    Graph,
    /// A call tree tab.
    CallTree,
    /// The triage view.
    Triage,
    /// The light and dark switch.
    Theme,
}

impl AppIcon {
    /// Every app icon, in declaration order.
    pub const ALL: [Self; 7] = [
        Self::ImportsExports,
        Self::Types,
        Self::Packs,
        Self::Graph,
        Self::CallTree,
        Self::Triage,
        Self::Theme,
    ];

    /// Returns the asset path the icon is served at.
    #[must_use]
    pub const fn path(self) -> &'static str {
        match self {
            Self::ImportsExports => "icons/borer/imports_exports.svg",
            Self::Types => "icons/borer/types.svg",
            Self::Packs => "icons/borer/packs.svg",
            Self::Graph => "icons/borer/graph.svg",
            Self::CallTree => "icons/borer/call_tree.svg",
            Self::Triage => "icons/borer/triage.svg",
            Self::Theme => "icons/borer/theme.svg",
        }
    }

    /// Returns the icon's SVG.
    const fn svg(self) -> &'static [u8] {
        match self {
            Self::ImportsExports => include_bytes!("../assets/icons/imports_exports.svg"),
            Self::Types => include_bytes!("../assets/icons/types.svg"),
            Self::Packs => include_bytes!("../assets/icons/packs.svg"),
            Self::Graph => include_bytes!("../assets/icons/graph.svg"),
            Self::CallTree => include_bytes!("../assets/icons/call_tree.svg"),
            Self::Triage => include_bytes!("../assets/icons/triage.svg"),
            Self::Theme => include_bytes!("../assets/icons/theme.svg"),
        }
    }
}

/// An icon from Zed's bundled set or from borer's own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Glyph {
    /// One of Zed's bundled icons.
    Zed(IconName),
    /// One of borer's own icons.
    App(AppIcon),
}

impl Glyph {
    /// Returns the icon, in the default size and color.
    #[must_use]
    pub fn icon(self) -> Icon {
        match self {
            Self::Zed(name) => Icon::new(name),
            Self::App(icon) => Icon::from_path(icon.path()),
        }
    }
}

/// The app's assets: the borer mark at [`MARK_PATH`], borer's icons at their
/// [`AppIcon::path`], and every other path from Zed's [`assets::Assets`].
#[derive(Debug, Clone, Copy)]
pub struct AppAssets;

impl AssetSource for AppAssets {
    fn load(&self, path: &str) -> anyhow::Result<Option<Cow<'static, [u8]>>> {
        if path == MARK_PATH {
            return Ok(Some(Cow::Borrowed(include_bytes!(
                "../../../brand/mark.svg"
            ))));
        }
        if let Some(icon) = AppIcon::ALL.into_iter().find(|icon| icon.path() == path) {
            return Ok(Some(Cow::Borrowed(icon.svg())));
        }
        assets::Assets.load(path)
    }

    fn list(&self, path: &str) -> anyhow::Result<Vec<SharedString>> {
        assets::Assets.list(path)
    }
}

#[cfg(test)]
mod tests {
    use gpui::AssetSource as _;

    use super::{AppAssets, AppIcon, MARK_PATH};

    /// The app's assets serve the borer mark and every borer icon as an SVG under Zed's
    /// icon folder that Zed's own assets lack, and every other path as Zed's do.
    ///
    /// # Panics
    ///
    /// Panics if the mark or an icon is missing, shadows a Zed icon, or another path
    /// answers differently.
    #[test]
    fn the_assets_add_the_mark_and_the_icons_to_zeds() {
        let mark = AppAssets.load(MARK_PATH).unwrap().unwrap();
        assert!(mark.starts_with(b"<svg"));
        assert!(assets::Assets.load(MARK_PATH).is_err());
        for icon in AppIcon::ALL {
            let path = icon.path();
            assert!(path.starts_with("icons/"), "{path} would load as a raster");
            let svg = AppAssets.load(path).unwrap().unwrap();
            assert!(svg.starts_with(b"<svg"), "{path}");
            assert!(
                assets::Assets.load(path).is_err(),
                "{path} shadows a Zed asset"
            );
        }
        let icon = "icons/code.svg";
        let zed = assets::Assets.load(icon).unwrap();
        assert_eq!(AppAssets.load(icon).unwrap(), zed);
        assert!(zed.is_some());
        assert_eq!(
            AppAssets.list("icons").unwrap(),
            assets::Assets.list("icons").unwrap()
        );
    }
}
