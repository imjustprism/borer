//! The command table's tests: the key rules R1 to R7 on every platform, the clash test
//! against Zed's three base keymaps, one row per action, and no key text in a view.

use std::collections::BTreeSet;

use gpui::{Focusable as _, TestAppContext, VisualTestContext};
use settings::KeymapFile;

use super::{COMMANDS, Ctx, Keys, MenuName, Os, UNBOUND, keymap};
use crate::app_view::tests::{init, load_sample, open};
use crate::decompile_item::{DecompileItem, TabMode};
use crate::places::{Opening, Place};

/// One binding as a keymap holds it: context predicate, normalized keys, action name
/// (`None` for a removed binding).
type Bound = (String, String, Option<String>);

/// Returns `os`'s name, for messages.
const fn os_name(os: Os) -> &'static str {
    match os {
        Os::Windows => "windows",
        Os::Linux => "linux",
        Os::Mac => "macos",
    }
}

/// Returns one keystroke with `secondary` resolved for `os` and its modifiers sorted, so
/// `shift-alt-x` and `alt-shift-x` compare equal.
fn stroke(text: &str, os: Os) -> String {
    let (mods, key) = text.strip_suffix("--").map_or_else(
        || text.rsplit_once('-').unwrap_or(("", text)),
        |mods| (mods, "-"),
    );
    let mut mods: Vec<&str> = mods
        .split('-')
        .filter(|part| !part.is_empty())
        .map(|part| match part {
            "secondary" if os == Os::Mac => "cmd",
            "secondary" => "ctrl",
            "option" => "alt",
            other => other,
        })
        .collect();
    mods.sort_unstable();
    mods.dedup();
    mods.push(key);
    mods.join("-")
}

/// Returns a key sequence with each keystroke normalized by [`stroke`].
fn keys(text: &str, os: Os) -> String {
    let strokes: Vec<String> = text.split(' ').map(|part| stroke(part, os)).collect();
    strokes.join(" ")
}

/// Returns the bindings of a keymap in Zed's format, in file order, keys normalized for
/// `os`.
///
/// # Panics
///
/// Panics if the keymap does not parse.
fn bindings(json: &str, os: Os) -> Vec<Bound> {
    let file = KeymapFile::parse(json).unwrap();
    let mut out = Vec::new();
    for section in file.sections() {
        for (key, action) in section.bindings() {
            let shown = action.to_string();
            let name = shown
                .split(", ")
                .next()
                .unwrap_or_default()
                .trim_matches('"');
            let name = (name != "null").then(|| name.to_owned());
            out.push((section.context.clone(), keys(key, os), name));
        }
    }
    out
}

/// Returns Zed's base keymap of `os` as the app links it.
///
/// # Panics
///
/// Panics if the keymap is not among Zed's settings assets.
fn zed_base(os: Os) -> String {
    let path = match os {
        Os::Windows => "keymaps/default-windows.json",
        Os::Linux => "keymaps/default-linux.json",
        Os::Mac => "keymaps/default-macos.json",
    };
    util::asset_str::<settings::SettingsAssets>(path).into_owned()
}

/// On macOS, Zed's base then the app's bindings leave `cmd-o` on `borer::Open` in the
/// workspace, where Zed's base has it on Zed's open.
///
/// # Panics
///
/// Panics if `cmd-o` ends on anything but `borer::Open`.
#[test]
fn macos_binds_cmd_o_to_open() {
    let mut all = bindings(&zed_base(Os::Mac), Os::Mac);
    all.extend(bindings(&keymap(Os::Mac), Os::Mac));
    let last = all
        .iter()
        .rev()
        .find(|(context, key, _)| key == "cmd-o" && matches!(context.as_str(), "" | "Workspace"));
    assert_eq!(
        last.and_then(|(_, _, action)| action.as_deref()),
        Some("borer::Open")
    );
}

/// Returns whether `key` is a key that types a character.
fn printable(key: &str) -> bool {
    key.chars().count() == 1 || key == "space"
}

/// Returns whether `key` is a punctuation key, whose place moves with the layout.
fn punctuation(key: &str) -> bool {
    key.chars().count() == 1 && key.chars().all(|ch| ch.is_ascii_punctuation())
}

/// Keys the platforms keep for themselves (R7), as normalized keystrokes or prefixes.
const fn reserved(os: Os) -> &'static [&'static str] {
    match os {
        Os::Mac => &[
            "cmd-shift-q",
            "cmd-h",
            "cmd-m",
            "cmd-shift-3",
            "cmd-shift-4",
            "cmd-shift-5",
            "cmd-space",
            "cmd-q",
        ],
        Os::Windows => &["ctrl-shift-escape", "alt-f4", "super-", "win-"],
        Os::Linux => &["super-", "alt-ctrl-"],
    }
}

/// Returns the rules (R1 to R4, R6 and R7) `text` breaks as a key of `keys` on `os`.
fn broken(text: &str, keys: &Keys, replaces: bool, os: Os) -> Vec<&'static str> {
    let mut out = Vec::new();
    if keys.all.contains(&text) && text.split(['-', ' ']).any(|m| m == "ctrl" || m == "cmd") {
        out.push("R1 secondary- for ctrl and cmd");
    }
    let normal = self::keys(text, os);
    for one in normal.split(' ') {
        let mut parts: Vec<&str> = one.split('-').collect();
        let key = if one.ends_with("--") {
            "-"
        } else {
            parts.pop().unwrap_or_default()
        };
        let has = |m: &str| parts.contains(&m);
        if os != Os::Mac && has("ctrl") && has("alt") && printable(key) {
            out.push("R2 no ctrl-alt-<printable> (AltGr)");
        }
        let texty = matches!(keys.context, Ctx::Global | Ctx::Workspace | Ctx::Rows);
        let only_alt = has("alt") && parts.iter().all(|m| *m == "alt" || *m == "shift");
        if os == Os::Mac && texty && only_alt && printable(key) {
            out.push("R3 no alt-<printable> where text is typed (Option characters)");
        }
        let bare = parts.iter().all(|m| *m == "shift");
        let readonly = matches!(keys.context, Ctx::Code | Ctx::Start | Ctx::MenuBar);
        if bare && printable(key) && !readonly {
            out.push("R4 single keys only where nothing is typed");
        }
        let global = matches!(keys.context, Ctx::Global | Ctx::Workspace);
        if global && punctuation(key) && !replaces {
            out.push("R6 no punctuation keys for global commands");
        }
        if reserved(os)
            .iter()
            .any(|held| one == *held || (held.ends_with('-') && one.starts_with(held)))
        {
            out.push("R7 a key the platform keeps");
        }
    }
    let host = match os {
        Os::Windows => gpui::OperatingSystem::Windows,
        Os::Linux => gpui::OperatingSystem::Linux,
        Os::Mac => gpui::OperatingSystem::Mac,
    };
    if text
        .split(' ')
        .any(|one| gpui::Keystroke::parse_with_os(one, host).is_err())
    {
        out.push("a key gpui does not parse");
    }
    out
}

/// Every key of every row keeps the key rules on all three platforms.
///
/// # Panics
///
/// Panics listing each key that breaks a rule, with the rule.
#[test]
fn no_command_breaks_a_key_rule() {
    let mut found = Vec::new();
    for os in Os::ALL {
        for row in COMMANDS {
            for set in row.keys {
                for text in set.on(os) {
                    for rule in broken(text, set, !row.replaces.is_empty(), os) {
                        found.push(format!("{}: {} {text}: {rule}", os_name(os), row.action));
                    }
                }
            }
        }
    }
    assert!(found.is_empty(), "{found:#?}");
}

/// States of Zed's editor the app's views never enter: completions, snippets, code
/// actions, signature help, the debugger's hover and inline inputs.
const NEVER: &[&str] = &[
    "showing_completions",
    "in_snippet",
    "showing_code_actions",
    "showing_signature_help",
    "DebuggerHover",
    "inline_input",
];

/// Returns whether a Zed binding in context `zed` can be in force where `ctx` is.
///
/// Then one of the two shadows the other: a binding with no context is everywhere, else
/// the context's first name must be one the app's `ctx` has around it or below it, and it
/// must not need a state of [`NEVER`].
fn overlaps(ctx: Ctx, zed: &str) -> bool {
    let words: Vec<&str> = zed
        .split([' ', '(', ')'])
        .filter(|word| !word.is_empty())
        .collect();
    if words.iter().any(|word| NEVER.contains(word)) {
        return false;
    }
    let Some(first) = zed
        .split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .find(|word| !word.is_empty())
    else {
        return true;
    };
    let around: &[&str] = match ctx {
        Ctx::Global | Ctx::Workspace => &[
            "Workspace",
            "Pane",
            "Editor",
            "Picker",
            "menu",
            "BufferSearchBar",
            "Dock",
        ],
        Ctx::Code => &["Workspace", "Pane", "Editor"],
        Ctx::Rows => &["Workspace", "Dock", "Editor"],
        Ctx::Start | Ctx::Overview => &["Workspace", "Pane"],
        Ctx::MenuBar => &["Workspace", "menu"],
    };
    around.contains(&first)
}

/// Returns the names of the actions with a handler in reach, for each place a row's keys
/// work.
///
/// The window has a binary open; a code tab and the functions panel's filter are focused
/// in turn, and the workspace-wide places take what either has.
///
/// # Panics
///
/// Panics if the window does not open or the sample does not load.
fn handled(cx: &mut TestAppContext) -> Vec<(Ctx, BTreeSet<&'static str>)> {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    let panel = load_sample(&app, cx);
    let loaded = app
        .binary
        .read_with(cx, |binary, _| binary.loaded().cloned())
        .unwrap();
    let binary = app.binary.clone();
    app.workspace.update_in(cx, |workspace, window, cx| {
        let how = Opening {
            mode: TabMode::Permanent,
            focus: true,
        };
        let place = Place::decompile(crate::app_view::tests::CALLER);
        crate::places::open(workspace, &binary, &loaded, place, how, window, cx);
    });
    let take = |cx: &mut VisualTestContext| {
        cx.run_until_parked();
        cx.update(|window, cx| {
            window.draw(cx).clear(cx);
            window
                .available_actions(cx)
                .iter()
                .map(|action| action.name())
                .collect()
        })
    };
    let code = app.workspace.read_with(cx, |workspace, cx| {
        workspace.active_item_as::<DecompileItem>(cx)
    });
    let code = code
        .unwrap()
        .read_with(cx, |item, cx| item.focus_handle(cx));
    cx.update(|window, cx| window.focus(&code, cx));
    let in_code: BTreeSet<&str> = take(cx);
    let rows = panel.read_with(cx, |panel, cx| panel.focus_handle(cx));
    cx.update(|window, cx| window.focus(&rows, cx));
    let in_rows: BTreeSet<&str> = take(cx);
    let anywhere: BTreeSet<&str> = in_code.union(&in_rows).copied().collect();
    Ctx::ALL
        .into_iter()
        .map(|ctx| {
            let names = match ctx {
                Ctx::Code => in_code.clone(),
                Ctx::Rows => in_rows.clone(),
                Ctx::Global | Ctx::Workspace | Ctx::Start | Ctx::Overview | Ctx::MenuBar => {
                    anywhere.clone()
                }
            };
            (ctx, names)
        })
        .collect()
}

/// No row's key lands on a Zed binding of the base keymaps whose action the app handles
/// in a context that can be in force at once, unless the row says it takes that action's
/// place (`replaces`).
///
/// # Panics
///
/// Panics listing each clash: platform, key, the row's action and Zed's.
#[gpui::test]
fn no_command_clashes_with_a_linked_zed_binding(cx: &mut TestAppContext) {
    let handled = handled(cx);
    let mut found = Vec::new();
    for os in Os::ALL {
        let base = bindings(&zed_base(os), os);
        for row in COMMANDS {
            for set in row.keys {
                let in_reach = handled.iter().find(|(ctx, _)| *ctx == set.context);
                let in_reach = in_reach.map(|(_, names)| names).unwrap();
                for text in set.on(os) {
                    let key = keys(text, os);
                    let clashes = base.iter().filter(|(context, at, zed)| {
                        *at == key
                            && zed.as_deref().is_some_and(|zed| {
                                zed != row.action
                                    && in_reach.contains(zed)
                                    && !row.replaces.contains(&zed)
                            })
                            && overlaps(set.context, context)
                    });
                    found.extend(clashes.map(|(context, _, zed)| {
                        let zed = zed.as_deref().unwrap_or_default();
                        format!(
                            "{}: {key} {} over {zed} in {context:?}",
                            os_name(os),
                            row.action
                        )
                    }));
                }
            }
        }
    }
    assert!(found.is_empty(), "{found:#?}");
}

/// Every removed binding is a Zed base binding of the action it names.
///
/// # Panics
///
/// Panics if a removed key is not in Zed's base keymap on its action.
#[test]
fn every_unbound_key_is_a_zed_binding() {
    for os in Os::ALL {
        let base = bindings(&zed_base(os), os);
        for (set, zed) in UNBOUND {
            for text in set.on(os) {
                let key = keys(text, os);
                let held = base
                    .iter()
                    .any(|(_, at, action)| *at == key && action.as_deref() == Some(*zed));
                assert!(held, "{}: {key} is not {zed}", os_name(os));
            }
        }
    }
}

/// Every `borer` action has exactly one row, every row builds its action, the platform
/// holds the table's menus, and with a binary open every menu row is in reach of the
/// person, so the palette offers it and running it reaches a handler.
///
/// # Panics
///
/// Panics naming an action with no row or two, a row that does not build, a menu row out
/// of reach, or other menus on the platform.
#[gpui::test]
fn every_borer_action_has_one_row_and_every_row_builds(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    load_sample(&app, cx);
    let declared: Vec<&str> = cx.update(|_, cx| cx.all_action_names().to_vec());
    for name in declared.iter().filter(|name| name.starts_with("borer::")) {
        let rows = COMMANDS.iter().filter(|row| row.action == *name).count();
        assert_eq!(rows, 1, "{name} has {rows} rows");
    }
    for row in COMMANDS {
        let built = cx.update(|_, cx| cx.build_action(row.action, None));
        assert!(built.is_ok(), "{} does not build", row.action);
        let twice = COMMANDS
            .iter()
            .filter(|other| other.action == row.action)
            .count();
        assert_eq!(twice, 1, "{} has two rows", row.action);
    }
    let available = cx.update(|window, cx| {
        window.draw(cx).clear(cx);
        window.available_actions(cx)
    });
    for row in COMMANDS.iter().filter(|row| row.menu.is_some()) {
        assert!(
            available.iter().any(|action| action.name() == row.action),
            "{} has no handler in reach",
            row.action
        );
    }
    let held: Vec<String> = cx
        .update(|_, cx| cx.get_menus())
        .unwrap_or_default()
        .into_iter()
        .map(|menu| menu.name.to_string())
        .collect();
    let want: Vec<String> = MenuName::ALL
        .iter()
        .map(|menu| menu.name().to_owned())
        .collect();
    assert_eq!(held, want, "the platform holds other menus");
}

/// No view's code outside its tests spells a key: every key shown is read from the keymap
/// the table generates.
///
/// # Panics
///
/// Panics naming each line with key text.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "reads the crate's own sources, not a path borer is given"
)]
fn no_view_prints_key_text() {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut found = Vec::new();
    let mut dirs = vec![src];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
                continue;
            }
            let table = path.ends_with("commands.rs") || dir.ends_with("commands");
            if path.extension().is_none_or(|ext| ext != "rs") || table {
                continue;
            }
            let text = std::fs::read_to_string(&path).unwrap();
            let code = text.split("#[cfg(test)]").next().unwrap_or_default();
            for (at, line) in code.lines().enumerate() {
                let lower = line.to_ascii_lowercase();
                let spelled = [
                    "\"ctrl",
                    "\"cmd",
                    "\"alt-",
                    "\"alt ",
                    "\"secondary",
                    "ctrl-",
                    "cmd-",
                ]
                .iter()
                .any(|text| lower.contains(text));
                if spelled && !line.trim_start().starts_with("//") {
                    found.push(format!("{}:{}: {}", path.display(), at + 1, line.trim()));
                }
            }
        }
    }
    assert!(found.is_empty(), "{found:#?}");
}
