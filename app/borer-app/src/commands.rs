//! The app's commands: one table, [`COMMANDS`], every surface is generated from.
//!
//! A row names an action and holds everything the app says about it: its label, the menu
//! and group it sits in, its keys per platform and the context they work in, what it needs
//! before it can run, the agent capabilities it serves and the Zed actions whose keys it
//! takes over. The keymap ([`keymap`], loaded over Zed's base by [`bind_keys`]), the menus
//! ([`menus`] for the platform, [`crate::menus::MenuBar`] in the window) and every key a
//! view shows (Zed's `KeyBinding::for_action`, which reads the bound keymap) come from it.
//!
//! A row's keys use Zed's `secondary-` modifier (cmd on macOS, ctrl elsewhere) wherever a
//! key is the platform's command key; the key rules R1 to R7 and the clash test in this
//! module's tests hold every row to the rules on all three platforms.
//!
//! # Adding a command
//!
//! Declare the action in the module that handles it (`gpui::actions!(borer, [...])`),
//! handle it there (a view's `on_action`, or the module's `register`), and add its one row
//! here, in menu order:
//!
//! ```ignore
//! Command {
//!     action: "borer::ToggleStrings",
//!     label: "Strings",
//!     menu: Some((MenuName::View, 0)),
//!     keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-a"])],
//!     needs: Need::Nothing,
//!     serves: &["strings"],
//!     replaces: &[],
//! },
//! ```
//!
//! Nothing else changes: the palette, the menu bar, the keymap and every hint follow, and
//! the tests refuse a key the rules or Zed's own bindings do not allow.

use std::rc::Rc;

use gpui::{Action, App, Context, Entity, InteractiveElement as _, Menu, MenuItem, Window};
use settings::{DEFAULT_KEYMAP_PATH, KeymapFile, KeymapFileLoadResult};
use workspace::Workspace;

use crate::binary::Binary;
use crate::places::shown_binary;

/// A platform the app binds keys for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Os {
    /// Windows.
    Windows,
    /// Linux and the other Unix desktops.
    Linux,
    /// macOS.
    Mac,
}

impl Os {
    /// Every platform, in the order the tests check them.
    pub const ALL: [Self; 3] = [Self::Windows, Self::Linux, Self::Mac];

    /// Returns the platform the app is built for.
    #[must_use]
    pub const fn current() -> Self {
        if cfg!(target_os = "macos") {
            Self::Mac
        } else if cfg!(target_os = "windows") {
            Self::Windows
        } else {
            Self::Linux
        }
    }
}

/// Where a binding works: the key context it is bound in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ctx {
    /// Everywhere, whatever is focused or nothing.
    Global,
    /// Anywhere in the workspace.
    Workspace,
    /// A code tab's read-only body.
    Code,
    /// A table's filter field, which never takes a printable key.
    Rows,
    /// The start tab.
    Start,
    /// The overview tab.
    Overview,
    /// A graph tab.
    Graph,
    /// A hex tab.
    Hex,
    /// A table's rows, not its filter.
    Table,
    /// The call tree panel.
    CallTree,
    /// A struct tab's lines, not its editor.
    Struct,
    /// A struct tab's editor, where a field's new name or type is typed.
    StructEditor,
    /// The inline editor's text field, where a name, a comment or a type is typed.
    Annotate,
    /// The in-window menu bar.
    MenuBar,
}

impl Ctx {
    /// Every context, in the order the keymap's sections go.
    pub const ALL: [Self; 14] = [
        Self::Global,
        Self::Workspace,
        Self::Code,
        Self::Rows,
        Self::Start,
        Self::Overview,
        Self::Graph,
        Self::Hex,
        Self::Table,
        Self::CallTree,
        Self::Struct,
        Self::StructEditor,
        Self::Annotate,
        Self::MenuBar,
    ];

    /// Returns the context's predicate in Zed's keymap, `None` for [`Ctx::Global`].
    #[must_use]
    pub const fn predicate(self) -> Option<&'static str> {
        match self {
            Self::Global => None,
            Self::Workspace => Some("Workspace"),
            Self::Code => Some("(DecompileView > Editor) && !Annotating"),
            Self::Rows => Some("(RowsPanel > Editor) && !Annotating"),
            Self::Start => Some("StartItem"),
            Self::Overview => Some("Overview"),
            Self::Graph => Some("GraphView"),
            Self::Hex => Some("HexView && !Annotating"),
            Self::Table => Some("BorerRows"),
            Self::CallTree => Some("CallTreePanel"),
            Self::Struct => Some("StructItem && !Editor"),
            Self::StructEditor => Some("StructItem > Editor"),
            Self::Annotate => Some("Annotating > Editor"),
            Self::MenuBar => Some("MenuBar"),
        }
    }
}

/// One binding set of a command: its keys per platform in one context.
#[derive(Debug, Clone, Copy)]
pub struct Keys {
    /// Keys on every platform without its own list, in Zed's syntax with `secondary-`.
    pub all: &'static [&'static str],
    /// Keys on Windows in place of `all`, when not empty.
    pub win: &'static [&'static str],
    /// Keys on Linux in place of `all`, when not empty.
    pub linux: &'static [&'static str],
    /// Keys on macOS in place of `all`, when not empty.
    pub mac: &'static [&'static str],
    /// Where the keys work.
    pub context: Ctx,
}

impl Keys {
    /// Returns `keys` on every platform, in `context`.
    #[must_use]
    pub const fn all(context: Ctx, keys: &'static [&'static str]) -> Self {
        Self {
            all: keys,
            win: &[],
            linux: &[],
            mac: &[],
            context,
        }
    }

    /// Returns `keys` on Windows and Linux only, in `context`.
    #[must_use]
    pub const fn not_mac(context: Ctx, keys: &'static [&'static str]) -> Self {
        Self {
            all: &[],
            win: keys,
            linux: keys,
            mac: &[],
            context,
        }
    }

    /// Returns `others` on Windows and Linux and `mac` on macOS, in `context`.
    #[must_use]
    pub const fn split(
        context: Ctx,
        others: &'static [&'static str],
        mac: &'static [&'static str],
    ) -> Self {
        Self {
            all: &[],
            win: others,
            linux: others,
            mac,
            context,
        }
    }

    /// Returns the keys on `os`.
    #[must_use]
    pub const fn on(&self, os: Os) -> &'static [&'static str] {
        if !self.has_own() {
            return self.all;
        }
        match os {
            Os::Windows => self.win,
            Os::Linux => self.linux,
            Os::Mac => self.mac,
        }
    }

    /// Returns whether any platform has its own list, so `all` is not used.
    const fn has_own(&self) -> bool {
        !self.win.is_empty() || !self.linux.is_empty() || !self.mac.is_empty()
    }
}

/// What a command needs before it can run; its handler is registered only while the need
/// is met, so the platform's menus, the menu bar and the palette all read one availability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Need {
    /// Nothing: it runs at any time.
    Nothing,
    /// An open binary: loaded or being read, or shown by the active tab.
    Binary,
}

impl Need {
    /// Returns why a row whose action has no handler in reach is disabled: its need while
    /// that is unmet, else that the focused element does not take it.
    ///
    /// # Arguments
    ///
    /// * `binary_open` - Whether the window has a binary open.
    #[must_use]
    pub const fn why_off(self, binary_open: bool) -> &'static str {
        match self {
            Self::Binary if !binary_open => "needs a binary",
            Self::Binary | Self::Nothing => "not here",
        }
    }
}

/// A menu of the menu bar.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MenuName {
    /// Opening, closing and settings.
    File,
    /// Finding and, later, editing.
    Edit,
    /// Panels, docks and theme.
    View,
    /// Moving between places.
    Go,
    /// The window itself.
    Window,
    /// The palette and about.
    Help,
}

impl MenuName {
    /// Every menu, left to right.
    pub const ALL: [Self; 6] = [
        Self::File,
        Self::Edit,
        Self::View,
        Self::Go,
        Self::Window,
        Self::Help,
    ];

    /// Returns the menu's name in the bar.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::File => "File",
            Self::Edit => "Edit",
            Self::View => "View",
            Self::Go => "Go",
            Self::Window => "Window",
            Self::Help => "Help",
        }
    }
}

/// One command: an action and everything the app says about it.
#[derive(Debug, Clone, Copy)]
pub struct Command {
    /// The action's name, as `cx.build_action` takes it.
    pub action: &'static str,
    /// What the menu calls it.
    pub label: &'static str,
    /// The menu and the group in it, top to bottom; `None` keeps it out of the menus.
    pub menu: Option<(MenuName, u8)>,
    /// Its bindings, one set per context.
    pub keys: &'static [Keys],
    /// What it needs before it can run.
    pub needs: Need,
    /// The agent capabilities it gives a person: tool names and `borer://` resources.
    pub serves: &'static [&'static str],
    /// Zed actions with the same meaning whose keys it takes: Find Function's key is Zed's
    /// find in the view in front of the person (a code tab keeps Zed's buffer search, a
    /// table filters), and a table's up and down move its selection as the editor's move
    /// the cursor.
    pub replaces: &'static [&'static str],
}

/// Returns Redo Edit's keys in `context`: secondary-shift-z everywhere, and ctrl-y too on
/// Windows, as its other programs redo.
///
/// # Arguments
///
/// * `context` - Where the keys work.
const fn redo_keys(context: Ctx) -> Keys {
    Keys {
        all: &[],
        win: &["ctrl-shift-z", "ctrl-y"],
        linux: &["ctrl-shift-z"],
        mac: &["cmd-shift-z"],
        context,
    }
}

/// Returns a row for `action` that is in no menu, binds `keys` and needs nothing.
const fn binding(action: &'static str, label: &'static str, keys: &'static [Keys]) -> Command {
    Command {
        action,
        label,
        menu: None,
        keys,
        needs: Need::Nothing,
        serves: &[],
        replaces: &[],
    }
}

/// Returns a row for `action` in `menu`'s `group`, unbound, that needs `needs`.
const fn item(
    action: &'static str,
    label: &'static str,
    (menu, group): (MenuName, u8),
    needs: Need,
) -> Command {
    Command {
        action,
        label,
        menu: Some((menu, group)),
        keys: &[],
        needs,
        serves: &[],
        replaces: &[],
    }
}

/// Every command, in menu order, then the bindings in no menu.
pub const COMMANDS: &[Command] = &[
    Command {
        keys: &[
            Keys::all(Ctx::Global, &["secondary-o"]),
            Keys::all(Ctx::Workspace, &["secondary-o"]),
        ],
        serves: &["load_binary"],
        replaces: &["workspace::Open", "workspace::OpenFiles"],
        ..item(
            "borer::Open",
            "Open Binary...",
            (MenuName::File, 0),
            Need::Nothing,
        )
    },
    Command {
        keys: &[Keys::split(Ctx::Workspace, &["ctrl-r"], &["ctrl-r"])],
        ..item(
            "borer::OpenRecent",
            "Open Recent...",
            (MenuName::File, 0),
            Need::Nothing,
        )
    },
    item(
        "borer::CloseBinary",
        "Close Binary",
        (MenuName::File, 0),
        Need::Binary,
    ),
    item(
        "borer::OpenProject",
        "Open Project...",
        (MenuName::File, 1),
        Need::Binary,
    ),
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-s"])],
        serves: &["save_project"],
        replaces: &["workspace::Save"],
        ..item(
            "borer::SaveProject",
            "Save Project",
            (MenuName::File, 1),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-s"])],
        serves: &["save_project"],
        replaces: &["workspace::SaveAs"],
        ..item(
            "borer::SaveProjectAs",
            "Save Project As...",
            (MenuName::File, 1),
            Need::Binary,
        )
    },
    item(
        "borer::ChooseSymbolCache",
        "Choose Symbol Cache...",
        (MenuName::File, 2),
        Need::Nothing,
    ),
    item(
        "borer::ForgetSymbolCache",
        "Forget Symbol Cache",
        (MenuName::File, 2),
        Need::Nothing,
    ),
    item(
        "borer::ChoosePacks",
        "Choose Packs...",
        (MenuName::File, 2),
        Need::Nothing,
    ),
    item(
        "borer::ForgetPacks",
        "Forget Packs",
        (MenuName::File, 2),
        Need::Nothing,
    ),
    item(
        "zed::OpenSettingsFile",
        "Settings File",
        (MenuName::File, 3),
        Need::Nothing,
    ),
    item("zed::Quit", "Quit", (MenuName::File, 3), Need::Nothing),
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-f"])],
        serves: &["functions"],
        replaces: &["buffer_search::Deploy", "search::FocusSearch"],
        ..item(
            "borer::FocusFilter",
            "Find Function",
            (MenuName::Edit, 0),
            Need::Binary,
        )
    },
    Command {
        serves: &["borer://certify"],
        ..item(
            "borer::RecheckBlock",
            "Recheck Block",
            (MenuName::Edit, 0),
            Need::Binary,
        )
    },
    Command {
        serves: &["borer://fields"],
        ..item(
            "borer::ProposeStruct",
            "Propose Struct from Accesses",
            (MenuName::Edit, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["secondary-z"]),
            Keys::all(Ctx::Table, &["secondary-z"]),
            Keys::all(Ctx::Hex, &["secondary-z"]),
        ],
        replaces: &["editor::Undo"],
        ..item(
            "borer::UndoEdit",
            "Undo Edit",
            (MenuName::Edit, 1),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            redo_keys(Ctx::Code),
            redo_keys(Ctx::Table),
            redo_keys(Ctx::Hex),
        ],
        replaces: &["editor::Redo"],
        ..item(
            "borer::RedoEdit",
            "Redo Edit",
            (MenuName::Edit, 1),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["n", "f2"]),
            Keys::all(Ctx::Table, &["n", "f2"]),
            Keys::all(Ctx::Hex, &["n", "f2"]),
        ],
        serves: &["set_name"],
        replaces: &["editor::Rename"],
        ..item("borer::Rename", "Rename", (MenuName::Edit, 2), Need::Binary)
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &[";"]),
            Keys::all(Ctx::Table, &[";"]),
            Keys::all(Ctx::Hex, &[";"]),
        ],
        serves: &["set_comment"],
        ..item(
            "borer::Comment",
            "Comment",
            (MenuName::Edit, 2),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["q"]),
            Keys::all(Ctx::Table, &["q"]),
            Keys::all(Ctx::Hex, &["q"]),
        ],
        serves: &["set_comment", "annotations"],
        ..item(
            "borer::AskQuestion",
            "Ask a Question",
            (MenuName::Edit, 2),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Code, &["y"])],
        serves: &["set_type"],
        ..item(
            "borer::SetType",
            "Set Type",
            (MenuName::Edit, 2),
            Need::Binary,
        )
    },
    Command {
        serves: &["set_type"],
        ..item(
            "borer::DeclareC",
            "Declare C...",
            (MenuName::Edit, 3),
            Need::Binary,
        )
    },
    Command {
        serves: &["set_type"],
        ..item(
            "borer::DeclareHeader",
            "Declare C from Header...",
            (MenuName::Edit, 3),
            Need::Binary,
        )
    },
    Command {
        serves: &["set_type"],
        ..item(
            "borer::NewEnum",
            "New Enum...",
            (MenuName::Edit, 3),
            Need::Binary,
        )
    },
    Command {
        serves: &["set_type"],
        ..item(
            "borer::NewTypedef",
            "New Typedef...",
            (MenuName::Edit, 3),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-m"])],
        serves: &["borer://triage"],
        ..item(
            "borer::Overview",
            "Overview",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-b"])],
        serves: &["callgraph"],
        ..item(
            "borer::CallTree",
            "Call Tree",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-e"])],
        serves: &["functions"],
        ..item(
            "borer::ToggleFunctions",
            "Functions",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    item(
        "borer::ToggleFunctionColumns",
        "Function Columns",
        (MenuName::View, 0),
        Need::Binary,
    ),
    Command {
        keys: &[Keys::all(Ctx::Code, &["tab"])],
        serves: &["disassemble_function"],
        ..item(
            "borer::ToggleListing",
            "Toggle Listing",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::split(Ctx::Workspace, &["ctrl-5"], &["cmd-alt-5"])],
        serves: &["disassemble"],
        ..item(
            "borer::ShowLinear",
            "Linear Listing",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Code, &["l"])],
        serves: &["disassemble"],
        ..item(
            "borer::ShowInLinear",
            "Show in Linear Listing",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::split(Ctx::Workspace, &["ctrl-3"], &["cmd-alt-3"])],
        serves: &["cfg"],
        ..item(
            "borer::ShowGraph",
            "Graph",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["space"]),
            Keys::all(Ctx::Graph, &["space"]),
        ],
        serves: &["cfg"],
        ..item(
            "borer::ToggleGraph",
            "Toggle Graph",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Graph, &["secondary-="])],
        replaces: &["zed::IncreaseBufferFontSize"],
        ..item(
            "borer::ZoomIn",
            "Zoom In Graph",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Graph, &["secondary--"])],
        replaces: &["zed::DecreaseBufferFontSize"],
        ..item(
            "borer::ZoomOut",
            "Zoom Out Graph",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Graph, &["secondary-0"])],
        replaces: &["zed::ResetBufferFontSize"],
        ..item(
            "borer::FitGraph",
            "Fit Graph",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Graph, &["i"]), Keys::all(Ctx::Code, &["i"])],
        serves: &["borer://certify"],
        ..item(
            "borer::ShowCheck",
            "Block Evidence",
            (MenuName::View, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::split(Ctx::Workspace, &["ctrl-4"], &["cmd-alt-4"]),
            Keys::all(Ctx::Code, &["h"]),
            Keys::all(Ctx::Table, &["h"]),
        ],
        serves: &["hexdump", "read"],
        ..item("borer::ShowHex", "Hex", (MenuName::View, 0), Need::Binary)
    },
    item(
        "borer::LinkHex",
        "Link Hex to Code",
        (MenuName::View, 0),
        Need::Binary,
    ),
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-a"])],
        serves: &["strings"],
        ..item(
            "borer::ToggleStrings",
            "Strings",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    Command {
        serves: &["symbols"],
        ..item(
            "borer::ToggleImports",
            "Imports",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    Command {
        serves: &["symbols"],
        ..item(
            "borer::ToggleExports",
            "Exports",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-r"])],
        serves: &["xrefs"],
        ..item(
            "borer::ToggleXrefs",
            "Xrefs",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-shift-v"])],
        serves: &["types"],
        ..item(
            "borer::ToggleTypes",
            "Types",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    Command {
        serves: &["query", "set_name"],
        ..item(
            "borer::ToggleChat",
            "Chat",
            (MenuName::View, 1),
            Need::Binary,
        )
    },
    item(
        "borer::CycleSort",
        "Sort Table by Next Column",
        (MenuName::View, 1),
        Need::Binary,
    ),
    item(
        "workspace::ToggleLeftDock",
        "Toggle Left Dock",
        (MenuName::View, 2),
        Need::Nothing,
    ),
    item(
        "workspace::ToggleBottomDock",
        "Toggle Bottom Dock",
        (MenuName::View, 2),
        Need::Nothing,
    ),
    item(
        "workspace::ToggleRightDock",
        "Toggle Right Dock",
        (MenuName::View, 2),
        Need::Nothing,
    ),
    item(
        "borer::ToggleTheme",
        "Toggle Light and Dark",
        (MenuName::View, 3),
        Need::Nothing,
    ),
    item(
        "borer::FollowSystemTheme",
        "Follow System Theme",
        (MenuName::View, 3),
        Need::Nothing,
    ),
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-k secondary-t"])],
        replaces: &["theme_selector::Toggle"],
        ..item(
            "borer::SelectTheme",
            "Select Theme...",
            (MenuName::View, 3),
            Need::Nothing,
        )
    },
    item(
        "borer::ImportTheme",
        "Import Theme...",
        (MenuName::View, 3),
        Need::Nothing,
    ),
    item(
        "borer::ImportThemeFromZed",
        "Import Theme from Zed...",
        (MenuName::View, 3),
        Need::Nothing,
    ),
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["g"]),
            Keys::all(Ctx::Hex, &["g"]),
            Keys::all(Ctx::Table, &["g"]),
        ],
        serves: &["borer://addr"],
        ..item(
            "borer::GoTo",
            "Go to Address or Name...",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Workspace, &["secondary-p"])],
        serves: &["borer://find"],
        replaces: &["file_finder::Toggle", "menu::SelectPrevious"],
        ..item(
            "borer::FindEverywhere",
            "Find Everywhere...",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["f12", "enter"]),
            Keys::all(Ctx::Graph, &["enter"]),
        ],
        serves: &["decompile"],
        replaces: &["editor::GoToDefinition", "editor::Newline"],
        ..item(
            "borer::FollowLink",
            "Follow Link",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[
            Keys::all(Ctx::Code, &["x"]),
            Keys::all(Ctx::Hex, &["x"]),
            Keys::all(Ctx::Table, &["x"]),
        ],
        serves: &["xrefs"],
        ..item(
            "borer::Xrefs",
            "Xrefs to Cursor",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Code, &["f8"])],
        serves: &["borer://certify"],
        replaces: &["editor::GoToDiagnostic"],
        ..item(
            "borer::NextWrongBlock",
            "Next Wrong Block",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    Command {
        keys: &[Keys::all(Ctx::Code, &["shift-f8"])],
        serves: &["borer://certify"],
        replaces: &["editor::GoToPreviousDiagnostic"],
        ..item(
            "borer::PreviousWrongBlock",
            "Previous Wrong Block",
            (MenuName::Go, 0),
            Need::Binary,
        )
    },
    item("pane::GoBack", "Back", (MenuName::Go, 1), Need::Nothing),
    item(
        "pane::GoForward",
        "Forward",
        (MenuName::Go, 1),
        Need::Nothing,
    ),
    item(
        "borer::MinimizeWindow",
        "Minimize",
        (MenuName::Window, 0),
        Need::Nothing,
    ),
    item(
        "borer::ZoomWindow",
        "Zoom",
        (MenuName::Window, 0),
        Need::Nothing,
    ),
    item(
        "command_palette::Toggle",
        "Command Palette",
        (MenuName::Help, 0),
        Need::Nothing,
    ),
    item(
        "zed::About",
        "About borer",
        (MenuName::Help, 1),
        Need::Nothing,
    ),
    item(
        "borer::CheckForUpdates",
        "Check for Updates",
        (MenuName::Help, 1),
        Need::Nothing,
    ),
    Command {
        replaces: &["app_menu::OpenApplicationMenu"],
        ..binding(
            "borer::OpenMenuBar",
            "Open the Menu Bar",
            &[Keys::not_mac(Ctx::Global, &["f10"])],
        )
    },
    Command {
        replaces: &["editor::MoveUp"],
        ..binding(
            "menu::SelectPrevious",
            "Previous Row",
            &[
                Keys::all(Ctx::Rows, &["up"]),
                Keys::all(Ctx::Start, &["up"]),
                Keys::all(Ctx::Overview, &["up"]),
                Keys::all(Ctx::Hex, &["up"]),
                Keys::all(Ctx::Struct, &["up"]),
            ],
        )
    },
    Command {
        replaces: &["editor::MoveDown"],
        ..binding(
            "menu::SelectNext",
            "Next Row",
            &[
                Keys::all(Ctx::Rows, &["down"]),
                Keys::all(Ctx::Start, &["down"]),
                Keys::all(Ctx::Overview, &["down"]),
                Keys::all(Ctx::Hex, &["down"]),
                Keys::all(Ctx::Struct, &["down"]),
            ],
        )
    },
    binding(
        "menu::Confirm",
        "Open Row",
        &[
            Keys::all(Ctx::Start, &["enter"]),
            Keys::all(Ctx::Overview, &["enter"]),
        ],
    ),
    Command {
        needs: Need::Binary,
        ..binding(
            "borer::WalkUp",
            "Graph Block Above",
            &[Keys::all(Ctx::Graph, &["up"])],
        )
    },
    Command {
        needs: Need::Binary,
        ..binding(
            "borer::WalkDown",
            "Graph Block Below",
            &[Keys::all(Ctx::Graph, &["down"])],
        )
    },
    Command {
        needs: Need::Binary,
        ..binding(
            "borer::WalkLeft",
            "Graph Block Left",
            &[Keys::all(Ctx::Graph, &["left"])],
        )
    },
    Command {
        needs: Need::Binary,
        ..binding(
            "borer::WalkRight",
            "Graph Block Right",
            &[Keys::all(Ctx::Graph, &["right"])],
        )
    },
    Command {
        serves: &["callgraph"],
        ..binding("borer::CallTreeDirection", "Flip the Call Tree", &[])
    },
    Command {
        serves: &["callgraph"],
        ..binding(
            "borer::ToggleVirtualCalls",
            "Virtual Calls in the Call Tree",
            &[],
        )
    },
    Command {
        serves: &["calls"],
        ..binding("borer::ShowCallSites", "Call Sites in the Call Tree", &[])
    },
    binding("borer::StopChat", "Stop the Chat's Turn", &[]),
    binding("borer::NewChatThread", "New Chat Thread", &[]),
    binding("borer::SendChat", "Send the Chat Message", &[]),
    binding("borer::SaveChatKey", "Save the Chat Provider's Key", &[]),
    binding("borer::NextChatProvider", "Next Chat Provider", &[]),
    binding("borer::NextChatModel", "Next Chat Model", &[]),
    binding("borer::PickChatModel", "Pick the Chat's Model", &[]),
    binding(
        "borer::ForgetChatKey",
        "Forget the Chat Provider's Saved Key",
        &[],
    ),
    binding("borer::RetryChat", "Retry the Chat's Failed Turn", &[]),
    binding(
        "borer::ToggleChatCall",
        "Open the Chat's Newest Tool Call",
        &[],
    ),
    binding(
        "borer::OpenChatCallAddress",
        "Open the Address of the Chat's Newest Tool Call",
        &[],
    ),
    binding("borer::SendHeldChat", "Send the Held Chat Message", &[]),
    binding(
        "borer::DontSendHeldChat",
        "Don't Send the Held Chat Message",
        &[],
    ),
    Command {
        needs: Need::Binary,
        serves: &["set_name"],
        ..binding(
            "borer::PlanChatProposalAgain",
            "Plan the Chat's Proposal Again",
            &[],
        )
    },
    Command {
        needs: Need::Binary,
        serves: &["set_name"],
        ..binding(
            "borer::AcceptChatProposal",
            "Accept the Chat's Proposal",
            &[],
        )
    },
    binding(
        "borer::RejectChatProposal",
        "Reject the Chat's Proposal",
        &[],
    ),
    binding(
        "menu::SelectParent",
        "Collapse or Go to Parent",
        &[Keys::all(Ctx::CallTree, &["left"])],
    ),
    binding(
        "menu::SelectChild",
        "Expand or Go to Child",
        &[Keys::all(Ctx::CallTree, &["right"])],
    ),
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding(
            "borer::RenameField",
            "Rename Field",
            &[Keys::all(Ctx::Struct, &["f2"])],
        )
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding(
            "borer::RetypeField",
            "Retype Field",
            &[Keys::all(Ctx::Struct, &["shift-f2"])],
        )
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding(
            "borer::AddField",
            "Add Field",
            &[Keys::all(Ctx::Struct, &["insert"])],
        )
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding(
            "borer::DeleteField",
            "Delete Field",
            &[Keys::all(Ctx::Struct, &["delete"])],
        )
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding("borer::ResizeStruct", "Resize Struct", &[])
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding("borer::CopyToUserType", "Copy to a User Type", &[])
    },
    Command {
        needs: Need::Binary,
        serves: &["set_type"],
        ..binding("borer::AcceptProposal", "Accept the Proposal", &[])
    },
    Command {
        replaces: &["workspace::Unfollow", "editor::Cancel"],
        ..binding(
            "menu::Cancel",
            "Drop the Planned Edit",
            &[
                Keys::all(Ctx::Struct, &["escape"]),
                Keys::all(Ctx::StructEditor, &["escape"]),
                Keys::all(Ctx::Annotate, &["escape"]),
            ],
        )
    },
    binding(
        "menu::SelectFirst",
        "First Row",
        &[Keys::all(Ctx::Hex, &["secondary-home"])],
    ),
    binding(
        "menu::SelectLast",
        "Last Row",
        &[Keys::all(Ctx::Hex, &["secondary-end"])],
    ),
    Command {
        replaces: &["menu::SelectFirst"],
        ..binding(
            "editor::PageUp",
            "Page Up",
            &[Keys::all(Ctx::Hex, &["pageup"])],
        )
    },
    Command {
        replaces: &["menu::SelectLast"],
        ..binding(
            "editor::PageDown",
            "Page Down",
            &[Keys::all(Ctx::Hex, &["pagedown"])],
        )
    },
    binding(
        "menu_bar::ActivateMenuLeft",
        "Menu on the Left",
        &[Keys::all(Ctx::MenuBar, &["left"])],
    ),
    binding(
        "menu_bar::ActivateMenuRight",
        "Menu on the Right",
        &[Keys::all(Ctx::MenuBar, &["right"])],
    ),
];

/// Zed's bindings the app removes, each with the Zed action it stood for: a key of an open
/// path that would add a folder to the project, which no command takes over.
pub const UNBOUND: &[(Keys, &str)] = &[(
    Keys::not_mac(Ctx::Global, &["ctrl-k ctrl-o"]),
    "workspace::Open",
)];

/// Returns the row of `action`, if it has one.
///
/// # Arguments
///
/// * `action` - The action's name.
#[must_use]
pub fn command(action: &str) -> Option<&'static Command> {
    COMMANDS.iter().find(|row| row.action == action)
}

/// Registers `handle` for `A` on `workspace`, in reach only while the need of `A`'s row is
/// met, so every surface that asks whether `A` can run (macOS's menus, the menu bar, the
/// palette) gets one answer.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, which meets [`Need::Binary`].
/// * `handle` - What `A` does.
pub fn register<A: Action>(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    handle: impl Fn(&mut Workspace, &A, &mut Window, &mut Context<'_, Workspace>) + 'static,
) {
    let needs = needs_of(A::name_for_type());
    let binary = binary.clone();
    let handle = Rc::new(handle);
    workspace.register_action_renderer(move |div, workspace, _, cx| {
        if !met(needs, workspace, &binary, cx) {
            return div;
        }
        let handle = handle.clone();
        div.on_action(cx.listener(move |workspace, action: &A, window, cx| {
            handle(workspace, action, window, cx);
        }))
    });
}

/// Registers `handle` for `action`, an action known only as a value, on `workspace`, in
/// reach as [`register`] keeps a typed one.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, which meets [`Need::Binary`].
/// * `action` - The action.
/// * `handle` - What it does.
pub fn register_boxed(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    action: &'static dyn Action,
    handle: fn(&mut Workspace, &mut Window, &mut Context<'_, Workspace>),
) {
    let needs = needs_of(action.name());
    let binary = binary.clone();
    workspace.register_action_renderer(move |div, workspace, _, cx| {
        if !met(needs, workspace, &binary, cx) {
            return div;
        }
        let this = cx.weak_entity();
        div.on_boxed_action(action, move |_, window, cx| {
            this.update(cx, |workspace, cx| handle(workspace, window, cx))
                .unwrap_or_default();
        })
    });
}

/// Returns what the row of the action named `name` needs, nothing for an action with no
/// row.
///
/// # Arguments
///
/// * `name` - The action's name.
fn needs_of(name: &str) -> Need {
    command(name).map_or(Need::Nothing, |row| row.needs)
}

/// Returns whether `needs` is met in `workspace`: always for nothing, and for a binary while
/// the window's is open or a tab shows one.
///
/// # Arguments
///
/// * `needs` - What a row needs.
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `cx` - Application context reading them.
fn met(needs: Need, workspace: &Workspace, binary: &Entity<Binary>, cx: &App) -> bool {
    match needs {
        Need::Nothing => true,
        Need::Binary => binary.read(cx).is_open() || shown_binary(workspace, binary, cx).is_some(),
    }
}

/// Returns the app's keymap on `os` in Zed's keymap format: one section per context, the
/// removed bindings first, then each row's keys in table order.
///
/// # Arguments
///
/// * `os` - The platform whose keys to emit.
#[must_use]
pub fn keymap(os: Os) -> String {
    let mut sections = Vec::new();
    for ctx in Ctx::ALL {
        let mut bindings = Vec::new();
        let unbound = UNBOUND.iter().map(|(keys, _)| (keys, None));
        let bound = COMMANDS
            .iter()
            .flat_map(|row| row.keys.iter().map(|keys| (keys, Some(row.action))));
        for (keys, action) in unbound.chain(bound).filter(|(keys, _)| keys.context == ctx) {
            let action = action.map_or_else(|| "null".to_owned(), |name| format!("\"{name}\""));
            bindings.extend(keys.on(os).iter().map(|key| format!("\"{key}\": {action}")));
        }
        if bindings.is_empty() {
            continue;
        }
        let context = ctx
            .predicate()
            .map_or_else(String::new, |at| format!("\"context\": \"{at}\", "));
        let bindings = bindings.join(", ");
        sections.push(format!("{{{context}\"bindings\": {{{bindings}}}}}"));
    }
    format!("[{}]", sections.join(", "))
}

/// Binds Zed's default keymap for this platform, then the app's [`keymap`] over it.
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
    match KeymapFile::load(&keymap(Os::current()), cx) {
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

/// Returns the rows of `menu` with the action each runs, a `None` row between groups.
///
/// # Arguments
///
/// * `menu` - The menu.
/// * `cx` - Application context that builds the actions.
#[must_use]
pub fn menu_rows(menu: MenuName, cx: &App) -> Vec<Option<(&'static Command, Box<dyn Action>)>> {
    let mut rows = Vec::new();
    let mut group = None;
    for row in COMMANDS {
        let Some((at, in_group)) = row.menu else {
            continue;
        };
        let Ok(action) = cx.build_action(row.action, None) else {
            continue;
        };
        if at != menu {
            continue;
        }
        if group.is_some_and(|last| last != in_group) {
            rows.push(None);
        }
        group = Some(in_group);
        rows.push(Some((row, action)));
    }
    rows
}

/// Returns the platform's menus, which macOS draws.
///
/// Each item's availability is its action's: gpui asks the focused window whether a
/// handler is in reach, and the app registers a command's handler only while its need is
/// met.
///
/// # Arguments
///
/// * `cx` - Application context that builds the actions.
#[must_use]
pub fn menus(cx: &App) -> Vec<Menu> {
    MenuName::ALL
        .into_iter()
        .map(|menu| {
            Menu::new(menu.name()).items(menu_rows(menu, cx).into_iter().map(|row| match row {
                Some((row, action)) => MenuItem::Action {
                    name: row.label.into(),
                    action,
                    os_action: None,
                    checked: false,
                    disabled: false,
                },
                None => MenuItem::separator(),
            }))
        })
        .collect()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests;
