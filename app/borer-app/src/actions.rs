//! Single action registry and default key bindings for `borer-app`.

use gpui::{Action, App, KeyBinding};

gpui::actions!(
    borer_app,
    [
        /// Opens or closes the keyboard command palette.
        TogglePalette,
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
        /// Runs the built-in UI frame and latency measurement suite.
        Measure,
    ]
);

/// Strongly typed identifier for every action declared in [`ACTION_REGISTRY`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionId {
    /// Opens or closes the keyboard command palette.
    TogglePalette,
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
    /// Runs the built-in UI frame and latency measurement suite.
    Measure,
}

impl ActionId {
    /// Constructs a boxed GPUI [`Action`] matching `self` for palette dispatch.
    ///
    /// # Returns
    ///
    /// Heap-allocated GPUI [`Action`] instance ready for `Window::dispatch_action`.
    #[must_use]
    pub fn boxed_action(self) -> Box<dyn Action> {
        match self {
            Self::TogglePalette => Box::new(TogglePalette),
            Self::Open => Box::new(Open),
            Self::FocusFilter => Box::new(FocusFilter),
            Self::OpenSelected => Box::new(OpenSelected),
            Self::NextRow => Box::new(NextRow),
            Self::PreviousRow => Box::new(PreviousRow),
            Self::PageDown => Box::new(PageDown),
            Self::PageUp => Box::new(PageUp),
            Self::GoBack => Box::new(GoBack),
            Self::GoForward => Box::new(GoForward),
            Self::Measure => Box::new(Measure),
        }
    }
}

/// Metadata for one registered action displayed in the command palette.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ActionSpec {
    /// Typed action variant used to construct the dispatched GPUI action.
    pub id: ActionId,
    /// Registered GPUI action identifier.
    pub name: &'static str,
    /// Primary keyboard shortcut string.
    pub shortcut: &'static str,
    /// Human-readable description of what the action does.
    pub summary: &'static str,
}

/// Complete registry of user-facing actions declared by `borer-app`.
pub const ACTION_REGISTRY: &[ActionSpec] = &[
    ActionSpec {
        id: ActionId::TogglePalette,
        name: "borer_app::TogglePalette",
        shortcut: "ctrl-shift-p",
        summary: "Toggle command palette",
    },
    ActionSpec {
        id: ActionId::Open,
        name: "borer_app::Open",
        shortcut: "ctrl-o",
        summary: "Open binary",
    },
    ActionSpec {
        id: ActionId::FocusFilter,
        name: "borer_app::FocusFilter",
        shortcut: "ctrl-f",
        summary: "Focus function filter",
    },
    ActionSpec {
        id: ActionId::OpenSelected,
        name: "borer_app::OpenSelected",
        shortcut: "enter",
        summary: "Decompile selected function",
    },
    ActionSpec {
        id: ActionId::NextRow,
        name: "borer_app::NextRow",
        shortcut: "down",
        summary: "Select next function",
    },
    ActionSpec {
        id: ActionId::PreviousRow,
        name: "borer_app::PreviousRow",
        shortcut: "up",
        summary: "Select previous function",
    },
    ActionSpec {
        id: ActionId::PageDown,
        name: "borer_app::PageDown",
        shortcut: "pagedown",
        summary: "Page down function table",
    },
    ActionSpec {
        id: ActionId::PageUp,
        name: "borer_app::PageUp",
        shortcut: "pageup",
        summary: "Page up function table",
    },
    ActionSpec {
        id: ActionId::GoBack,
        name: "borer_app::GoBack",
        shortcut: "alt-left",
        summary: "Navigate back",
    },
    ActionSpec {
        id: ActionId::GoForward,
        name: "borer_app::GoForward",
        shortcut: "alt-right",
        summary: "Navigate forward",
    },
    ActionSpec {
        id: ActionId::Measure,
        name: "borer_app::Measure",
        shortcut: "ctrl-shift-m",
        summary: "Run frame and latency measurement",
    },
];

/// Registers default keyboard bindings for every action in [`ACTION_REGISTRY`].
///
/// # Arguments
///
/// * `cx` - Application context receiving the keymap entries.
pub fn bind_keys(cx: &mut App) {
    cx.bind_keys([
        KeyBinding::new("ctrl-shift-p", TogglePalette, Some("AppRoot")),
        KeyBinding::new("f1", TogglePalette, Some("AppRoot")),
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
        KeyBinding::new("ctrl-shift-m", Measure, Some("AppRoot")),
    ]);
}
