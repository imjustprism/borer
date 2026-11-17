//! The command table's tests: one row per action, every row built, the platform holding
//! the table's menus.

use gpui::TestAppContext;

use super::{COMMANDS, MenuName};
use crate::app_view::tests::{init, load_sample, open};

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
