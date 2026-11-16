//! The app's actions, under the `borer` namespace, and its key bindings: Zed's default
//! keymap, then the app's keymap asset, which holds only the bindings Zed's lacks.

use gpui::App;
use settings::{DEFAULT_KEYMAP_PATH, KeymapFile, KeymapFileLoadResult};

gpui::actions!(
    borer,
    [
        /// Opens a binary through the system file dialog.
        Open,
        /// Shows the functions panel and moves focus to its filter.
        FocusFilter,
        /// Shows the functions panel and focuses it, or moves focus back to the center pane.
        ToggleFunctions,
    ]
);

/// The app's keymap: the bindings Zed's default keymap lacks, in Zed's keymap format.
const APP_KEYMAP: &str = include_str!("../keymap.json");

/// Binds Zed's default keymap for this platform, then the app's keymap over it.
///
/// Zed's bindings for actions of crates the app does not link are left out, as Zed's
/// partial loader does; every binding of the app's keymap must load.
///
/// # Arguments
///
/// * `cx` - Application context receiving the keymap entries.
///
/// # Errors
///
/// Returns an error when none of Zed's default bindings load, or when a binding of the
/// app's keymap names an unknown action or does not parse.
pub fn bind_keys(cx: &mut App) -> anyhow::Result<()> {
    cx.bind_keys(KeymapFile::load_asset_allow_partial_failure(
        DEFAULT_KEYMAP_PATH,
        cx,
    )?);
    match KeymapFile::load(APP_KEYMAP, cx) {
        KeymapFileLoadResult::Success { key_bindings } => cx.bind_keys(key_bindings),
        KeymapFileLoadResult::SomeFailedToLoad { error_message, .. } => {
            anyhow::bail!("the app keymap does not load: {error_message}")
        }
        KeymapFileLoadResult::JsonParseFailure { error } => {
            anyhow::bail!("the app keymap does not parse: {error}")
        }
    }
    Ok(())
}
