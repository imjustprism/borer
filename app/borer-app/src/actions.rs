//! The app's actions, under the `borer` namespace, and its key bindings: Zed's default
//! keymap, then the app's keymap asset, which holds only the bindings Zed's lacks.

use gpui::{Action, App, Div, ParentElement as _, Styled as _};
use settings::{DEFAULT_KEYMAP_PATH, KeymapFile, KeymapFileLoadResult};
use ui::{Color, KeyBinding, Label, LabelCommon as _, LabelSize, h_flex};

gpui::actions!(
    borer,
    [
        /// Opens a binary through the system file dialog.
        Open,
        /// Shows the functions panel and moves focus to its filter.
        FocusFilter,
        /// Shows the functions panel and focuses it, or moves focus back to the center pane.
        ToggleFunctions,
        /// Shows or hides the function table's blocks, instrs, callees and src columns.
        ToggleFunctionColumns,
        /// Switches between borer's dark and light theme and keeps the choice in the app's
        /// settings file.
        ToggleTheme,
        /// Follows the system's light or dark appearance again, and keeps that in the app's
        /// settings file.
        FollowSystemTheme,
        /// Follows the link of the token under the cursor: a call opens its function, a label
        /// or a branch target goes to its line, an import is named in the status line.
        FollowLink,
        /// Switches the code tab between its function's decompile and its listing, opening
        /// the other at the function's start.
        ToggleListing,
    ]
);

/// A hint a surface shows: an action, then what it does in the hint's words.
pub type Hint = (&'static dyn Action, &'static str);

/// The hint for opening a binary.
pub const OPEN_HINT: Hint = (&Open, "Open");

/// The hint for Zed's command palette.
pub const PALETTE_HINT: Hint = (&zed_actions::command_palette::Toggle, "Every command");

/// The hint for going back to where the person was before.
pub const BACK_HINT: Hint = (&workspace::pane::GoBack, "Go back");

/// Returns a hint as a row: the binding the keymap holds for its action, as Zed's
/// [`KeyBinding`] draws it, then what the action does.
///
/// # Arguments
///
/// * `(action, what)` - The hint.
/// * `cx` - Application context reading the keymap.
#[must_use]
pub fn hint_row((action, what): Hint, cx: &App) -> Div {
    h_flex()
        .gap_2()
        .child(KeyBinding::for_action(action, cx))
        .child(Label::new(what).size(LabelSize::Small).color(Color::Muted))
}

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
