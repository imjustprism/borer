//! The app's actions and their default key bindings: the one list a button or a
//! palette reads a shortcut from, through gpui's keymap.

use gpui::{App, KeyBinding};

gpui::actions!(
    borer_app,
    [
        /// Opens a binary file via the native file dialog.
        Open,
        /// Moves keyboard focus into the function filter input.
        FocusFilter,
        /// Opens the decompile view for the currently highlighted function row.
        OpenSelected,
        /// Moves the function-table selection down by one row.
        NextRow,
        /// Moves the function-table selection up by one row.
        PreviousRow,
        /// Moves the function-table selection down by one page.
        PageDown,
        /// Moves the function-table selection up by one page.
        PageUp,
        /// Navigates to the previous function in history.
        GoBack,
        /// Navigates to the next function in history.
        GoForward,
    ]
);

/// Registers the default key binding of every action in gpui's keymap.
///
/// `AppRoot` bindings hold anywhere in the window; `AppBrowse` ones only while
/// the filter field does not have focus, so typing there is never taken.
///
/// # Arguments
///
/// * `cx` - Application context receiving the keymap entries.
pub fn bind_keys(cx: &mut App) {
    cx.bind_keys([
        KeyBinding::new("ctrl-o", Open, Some("AppRoot")),
        KeyBinding::new("ctrl-f", FocusFilter, Some("AppRoot")),
        KeyBinding::new("/", FocusFilter, Some("AppBrowse")),
        KeyBinding::new("enter", OpenSelected, Some("AppBrowse")),
        KeyBinding::new("down", NextRow, Some("AppBrowse")),
        KeyBinding::new("j", NextRow, Some("AppBrowse")),
        KeyBinding::new("up", PreviousRow, Some("AppBrowse")),
        KeyBinding::new("k", PreviousRow, Some("AppBrowse")),
        KeyBinding::new("pagedown", PageDown, Some("AppBrowse")),
        KeyBinding::new("pageup", PageUp, Some("AppBrowse")),
        KeyBinding::new("alt-left", GoBack, Some("AppRoot")),
        KeyBinding::new("alt-right", GoForward, Some("AppRoot")),
    ]);
}
