//! The app's actions, under the `borer` namespace, and the hints that show their keys;
//! each action's row, keys and menu are in [`crate::commands::COMMANDS`].

use gpui::{Action, App, Div, ParentElement as _, Styled as _};
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
        /// Closes the open binary, its tabs and its panels, and shows the welcome column.
        CloseBinary,
        /// Minimizes the window.
        MinimizeWindow,
        /// Maximizes the window, or restores it when it is maximized.
        ZoomWindow,
        /// Opens the first menu of the window's menu bar (Windows and Linux).
        OpenMenuBar,
        /// Opens the overview of the open binary: what the file is, how it is protected,
        /// what it can do and which functions to read first, as the engine's triage says.
        Overview,
        /// Opens the linear listing of the whole image: the tab already open, else a new one
        /// at the image's start.
        ShowLinear,
        /// Opens the linear listing at the address of the code tab's cursor line, else of its
        /// function's entry.
        ShowInLinear,
        /// Opens the control-flow graph of the code tab's function.
        ShowGraph,
        /// Switches between a function's graph and its listing at the same address.
        ToggleGraph,
        /// Zooms the graph in; the engine's layout is only scaled.
        ZoomIn,
        /// Zooms the graph out; the engine's layout is only scaled.
        ZoomOut,
        /// Zooms and pans the graph so the whole function fits the tab.
        FitGraph,
        /// Selects the graph block nearest above the selected one along an edge.
        WalkUp,
        /// Selects the graph block nearest below the selected one along an edge.
        WalkDown,
        /// Selects the graph block nearest left of the selected one along an edge.
        WalkLeft,
        /// Selects the graph block nearest right of the selected one along an edge.
        WalkRight,
        /// Shows or hides the evidence behind the selected graph block's grade.
        ShowCheck,
        /// Shows the strings panel and focuses its filter, or moves focus back to the center
        /// pane.
        ToggleStrings,
        /// Shows the imports panel and focuses its filter, or moves focus back to the center
        /// pane.
        ToggleImports,
        /// Shows the exports panel and focuses its filter, or moves focus back to the center
        /// pane.
        ToggleExports,
        /// Shows the xrefs panel and focuses it, or moves focus back to the center pane.
        ToggleXrefs,
        /// Sorts the focused table by its next sortable column, ascending then descending,
        /// then in the engine's order again.
        CycleSort,
        /// Lists the references to what the focus is on: a table's highlighted row, a code
        /// tab's function or the hex tab's cursor; on nothing, Go to asks for an address.
        Xrefs,
        /// Shows the bytes at what the focus is on in the hex tab: a table's highlighted
        /// row or a code tab's function; on nothing, the hex tab as it was.
        ShowHex,
        /// Makes the hex tab's cursor follow the active code tab's function, or stop.
        LinkHex,
        /// Opens the theme picker: moving the selection shows a theme, Enter keeps it in the
        /// app's settings file, and leaving puts back the one shown before.
        SelectTheme,
        /// Opens the file dialog for a theme file, checks each of its themes against the
        /// theme contract and shows the report, from which it is copied into the themes folder.
        ImportTheme,
        /// Lists the theme files Zed has installed, its themes folder's and its extensions',
        /// and opens the import report of the one picked, with borer's keys it lacks.
        ImportThemeFromZed,
        /// Roots the call tree at the function of the active tab and focuses its panel.
        CallTree,
        /// Flips the call tree between what its functions call and what calls them.
        CallTreeDirection,
        /// Lists the instructions making the selected call of the call tree, or hides them.
        ShowCallSites,
        /// Lists or hides, in the call tree's callees, the virtual calls the decompiler
        /// resolves, which decompiles each function opened.
        ToggleVirtualCalls,
        /// Picks the symbol cache directory the next open looks for a binary's PDB in.
        ChooseSymbolCache,
        /// Puts the symbol cache back to the one the server uses by default.
        ForgetSymbolCache,
        /// Picks the pack files that load for every binary the next open analyzes.
        ChoosePacks,
        /// Loads no pack files beyond those the pack directory fits to a binary.
        ForgetPacks,
        /// Opens a project file's names, comments and types over the open binary, as the
        /// engine admits them.
        OpenProject,
        /// Saves the names, comments and types to the project file last saved or opened.
        SaveProject,
        /// Saves the names, comments and types to a project file picked in the system dialog.
        SaveProjectAs,
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
