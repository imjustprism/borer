//! The app's assets: Zed's, with the borer mark added.

use std::borrow::Cow;

use gpui::{AssetSource, SharedString};

/// Asset path the borer mark is served at.
pub const MARK_PATH: &str = "borer/mark.svg";

/// The app's assets: the borer mark at [`MARK_PATH`], and every other path from Zed's
/// [`assets::Assets`].
#[derive(Debug, Clone, Copy)]
pub struct AppAssets;

impl AssetSource for AppAssets {
    fn load(&self, path: &str) -> anyhow::Result<Option<Cow<'static, [u8]>>> {
        if path == MARK_PATH {
            return Ok(Some(Cow::Borrowed(include_bytes!(
                "../../../brand/mark.svg"
            ))));
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

    use super::{AppAssets, MARK_PATH};

    /// The app's assets serve the borer mark, an SVG, and every other path as Zed's do.
    ///
    /// # Panics
    ///
    /// Panics if the mark is missing or another path answers differently.
    #[test]
    fn the_assets_add_the_mark_to_zeds() {
        let mark = AppAssets.load(MARK_PATH).unwrap().unwrap();
        assert!(mark.starts_with(b"<svg"));
        assert!(assets::Assets.load(MARK_PATH).is_err());
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
