//! The conformance suite: what every panel of [`PANELS`] and every [`Place`] variant keeps,
//! run over each of them, with coverage checks that fail when a new one is not listed.
//!
//! A new panel adds its key to [`PANELS_RUN`]; a new place variant adds an example to
//! [`places`], whose match stops compiling until it does.

use gpui::{TestAppContext, VisualTestContext};

use crate::app_view::REFUSED_FOLDER;
use crate::app_view::tests::{
    CALLER, drop_on_center, init, load_sample, open, open_place, sample, take_status,
};
use crate::card::CARD_SELECTOR;
use crate::decompile_item::{DecompileItem, TabMode};
use crate::panels::PANELS;
use crate::places::{Place, place_of};
use crate::rows_panel::HEADER_SELECTOR;
use crate::start_item::StartItem;
use crate::worker::Jobs;

/// The panels the suite runs over, by key, in [`PANELS`] order.
const PANELS_RUN: &[&str] = &[
    "Functions",
    "Strings",
    "Imports",
    "Exports",
    "Xrefs",
    "CallTree",
];

/// Returns one example of every [`Place`] variant a tab shows; an xrefs place shows in its
/// panel, which the panel tests run.
fn places() -> Vec<Place> {
    let code = Place::decompile(CALLER);
    match code {
        Place::Code { .. }
        | Place::Graph { .. }
        | Place::Overview
        | Place::Linear { .. }
        | Place::Hex { .. }
        | Place::Xrefs(_) => {
            let graph = Place::Graph {
                entry: CALLER,
                at: None,
            };
            let (linear, hex) = (Place::Linear { at: None }, Place::Hex { at: None });
            vec![code, graph, Place::Overview, linear, hex]
        }
    }
}

/// Settles the work in flight and lays the window out.
fn draw(cx: &mut VisualTestContext) {
    cx.run_until_parked();
    cx.update(|window, cx| window.draw(cx).clear(cx));
}

/// The suite runs over every panel of [`PANELS`], and over nothing else.
#[test]
fn the_suite_lists_every_panel() {
    let keys: Vec<&str> = PANELS.iter().map(|spec| spec.key).collect();
    assert_eq!(
        keys, PANELS_RUN,
        "a panel is missing from the conformance suite"
    );
}

/// Every panel, added before any binary and shown, draws its card and no column header.
#[gpui::test]
fn every_panel_shows_a_card_without_a_binary(cx: &mut TestAppContext) {
    let app_state = init(cx);
    for spec in PANELS {
        let (app, cx) = open(&app_state, cx);
        let binary = app.binary.clone();
        app.workspace.update_in(cx, |workspace, window, cx| {
            (spec.add)(workspace, &binary, spec.dock, window, cx);
            (spec.focus)(workspace, window, cx);
        });
        draw(cx);
        draw(cx);
        assert!(
            cx.debug_bounds(CARD_SELECTOR).is_some(),
            "{}: no card",
            spec.key
        );
        assert!(
            cx.debug_bounds(HEADER_SELECTOR).is_none(),
            "{}: a header",
            spec.key
        );
    }
}

/// Every panel's toggle, with a binary open, focuses the panel, and again gives focus
/// back.
#[gpui::test]
fn every_panel_toggle_focuses_it_and_back(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    load_sample(&app, cx);
    for spec in PANELS {
        let focused = |cx: &mut VisualTestContext| {
            draw(cx);
            let dock = app.workspace.read_with(cx, |workspace, cx| {
                workspace
                    .dock_at_position(spec.dock)
                    .read(cx)
                    .active_panel()
                    .cloned()
            });
            let dock = dock.unwrap_or_else(|| panic!("{}: not docked", spec.key));
            cx.update(|window, cx| dock.panel_focus_handle(cx).contains_focused(window, cx))
        };
        cx.update(|window, cx| window.dispatch_action(spec.toggle.boxed_clone(), cx));
        assert!(focused(cx), "{}: the toggle does not focus it", spec.key);
        cx.update(|window, cx| window.dispatch_action(spec.toggle.boxed_clone(), cx));
        assert!(
            !focused(cx),
            "{}: the toggle does not give focus back",
            spec.key
        );
    }
}

/// Every place opened twice keeps one tab, which names that place.
#[gpui::test]
fn every_place_opens_one_tab_that_names_it(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    let loaded = sample();
    for place in places() {
        open_place(&app.workspace, &loaded, place, TabMode::Permanent, cx);
        open_place(&app.workspace, &loaded, place, TabMode::Permanent, cx);
        draw(cx);
        let (named, tabs) = app.workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            let tabs = pane
                .items()
                .filter(|item| place_of(item.as_ref(), cx) == Some(place));
            let named = pane
                .active_item()
                .and_then(|item| place_of(item.as_ref(), cx));
            (named, tabs.count())
        });
        assert_eq!(tabs, 1, "{place:?}: {tabs} tabs");
        assert_eq!(named, Some(place), "{place:?}");
    }
}

/// A folder dropped on each kind of tab (the start tab and every place's) reaches the
/// binary's loader and never joins the project.
#[gpui::test]
async fn a_folder_dropped_on_any_tab_never_joins_the_project(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let dir = std::env::temp_dir().join(format!("borer-app-conform-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    app_state
        .fs
        .as_fake()
        .insert_tree(&dir, serde_json::json!({ "a": "" }))
        .await;
    let (app, cx) = open(&app_state, cx);
    let loaded = sample();
    let mut kinds = vec![(String::from("start"), None)];
    kinds.extend(
        places()
            .into_iter()
            .map(|place| (format!("{place:?}"), Some(place))),
    );
    for (kind, place) in kinds {
        if let Some(place) = place {
            open_place(&app.workspace, &loaded, place, TabMode::Permanent, cx);
        }
        let active_is_start = app.workspace.read_with(cx, |workspace, cx| {
            workspace.active_item_as::<StartItem>(cx).is_some()
        });
        assert_eq!(
            active_is_start,
            place.is_none(),
            "{kind}: another tab is active"
        );
        drop_on_center(&dir, cx);
        assert!(
            take_status(&app, cx).ends_with(REFUSED_FOLDER),
            "{kind}: not refused"
        );
        let folders = app.workspace.read_with(cx, |workspace, cx| {
            workspace.project().read(cx).worktrees(cx).count()
        });
        assert_eq!(folders, 0, "{kind}: the folder joined the project");
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

/// Closing a place's tab while its view is being built leaves no live request in [`Jobs`],
/// before any background work could run and answer it; the tab is released on the next
/// update.
#[gpui::test]
fn closing_a_view_leaves_no_live_job(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    let loaded = sample();
    for place in places() {
        open_place(&app.workspace, &loaded, place, TabMode::Permanent, cx);
        let running = cx.update(|_, cx| Jobs::running(cx).len());
        assert!(running > 0, "{place:?}: no request to stop");
        app.workspace.update_in(cx, |workspace, window, cx| {
            let pane = workspace.active_pane().clone();
            let tab = pane.read(cx).active_item().map(|item| item.item_id());
            pane.update(cx, |pane, cx| {
                if let Some(tab) = tab {
                    pane.remove_item(tab, false, false, window, cx);
                }
            });
        });
        cx.update(|_, _| {});
        let running = cx.update(|_, cx| Jobs::running(cx));
        assert!(running.is_empty(), "{place:?}: {running:?}");
        draw(cx);
    }
    let tabs = app.workspace.read_with(cx, |workspace, cx| {
        workspace
            .active_pane()
            .read(cx)
            .items_of_type::<DecompileItem>()
            .count()
    });
    assert_eq!(tabs, 0);
}
