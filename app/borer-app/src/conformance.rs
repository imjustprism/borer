//! The conformance suite: what every panel of [`PANELS`] and every [`Place`] variant keeps,
//! run over each of them, with coverage checks that fail when a new one is not listed.
//!
//! A new panel adds its key to [`PANELS_RUN`]; a new place variant adds an example to
//! [`places`], whose match stops compiling until it does.

use std::num::NonZeroUsize;
use std::sync::Arc;

use borer_engine::analysis::utypes::{TypeKind, TypeSource};
use borer_engine::progress::Workers;
use gpui::{App, Entity, TestAppContext, VisualTestContext};
use workspace::{AppState, ItemHandle, Workspace};

use crate::app_view::REFUSED_FOLDER;
use crate::app_view::tests::{
    CALLER, drop_on_center, init, load_sample, loaded_of, open, open_place, sample, take_status,
};
use crate::binary::{Digest, Digested};
use crate::card::CARD_SELECTOR;
use crate::code_view::tests::{LEAVES, wide_program};
use crate::decompile_item::{DecompileItem, TabMode};
use crate::functions_panel::FunctionsPanel;
use crate::graph_item::GraphItem;
use crate::hex_item::HexItem;
use crate::linear_item::LinearItem;
use crate::overview::OverviewItem;
use crate::panels::PANELS;
use crate::places::{Place, place_of};
use crate::rows_panel::HEADER_SELECTOR;
use crate::start_item::StartItem;
use crate::types::{StructItem, TypeKey};
use crate::worker::{Jobs, LoadedBinary, Referent};

/// The panels the suite runs over, by key, in [`PANELS`] order.
const PANELS_RUN: &[&str] = &[
    "Functions",
    "Strings",
    "Imports",
    "Exports",
    "Xrefs",
    "Types",
    "CallTree",
];

/// Returns one example of every [`Place`] variant a tab shows; an xrefs place shows in its
/// panel, which the panel tests run.
///
/// The examples chain one variant to the next, one arm each, so a new variant does not
/// compile until its arm names the example after it.
pub(crate) fn places() -> Vec<Place> {
    let next = |place: &Place| match place {
        Place::Code { .. } => Some(Place::Graph {
            entry: CALLER,
            at: None,
        }),
        Place::Graph { .. } => Some(Place::Overview),
        Place::Overview => Some(Place::Linear { at: None }),
        Place::Linear { .. } => Some(Place::Hex { at: None }),
        Place::Hex { .. } => Some(Place::Type(TypeKey {
            name: "CONFORMANCE".into(),
            source: TypeSource::User,
            kind: TypeKind::Struct,
        })),
        Place::Type(_) => Some(Place::Proposal { entry: CALLER }),
        Place::Proposal { .. } => Some(Place::Xrefs(Referent::Address(CALLER))),
        Place::Xrefs(_) => None,
    };
    std::iter::successors(Some(Place::decompile(CALLER)), next)
        .filter(|place| !matches!(place, Place::Xrefs(_)))
        .collect()
}

/// Opens `place` of `loaded` in a permanent tab of `workspace`.
fn open_permanent(
    workspace: &Entity<Workspace>,
    loaded: &Arc<LoadedBinary>,
    place: &Place,
    cx: &mut VisualTestContext,
) {
    open_place(workspace, loaded, place.clone(), TabMode::Permanent, cx);
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
        open_permanent(&app.workspace, &loaded, &place, cx);
        open_permanent(&app.workspace, &loaded, &place, cx);
        draw(cx);
        let (named, tabs) = app.workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            let tabs = pane
                .items()
                .filter(|item| place_of(item.as_ref(), cx).as_ref() == Some(&place));
            let named = pane
                .active_item()
                .and_then(|item| place_of(item.as_ref(), cx));
            (named, tabs.count())
        });
        assert_eq!(tabs, 1, "{place:?}: {tabs} tabs");
        assert_eq!(named.as_ref(), Some(&place), "{place:?}");
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
        if let Some(place) = &place {
            open_permanent(&app.workspace, &loaded, place, cx);
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

/// Returns [`wide_program`] as a loaded binary.
fn wide_sample() -> Arc<LoadedBinary> {
    let (program, analysis, overlay) = wide_program();
    loaded_of(program, analysis, overlay)
}

/// Returns the digest of what `item` shows, `None` for an item that shows no binary.
fn digest_of(item: &dyn ItemHandle, cx: &App) -> Option<u64> {
    /// Returns the digest of `item` as a `T`, `None` when it is another kind.
    fn of<T: Digested + 'static>(item: &dyn ItemHandle, cx: &App) -> Option<u64> {
        Some(item.downcast::<T>()?.read(cx).digest(cx))
    }
    of::<DecompileItem>(item, cx)
        .or_else(|| of::<GraphItem>(item, cx))
        .or_else(|| of::<OverviewItem>(item, cx))
        .or_else(|| of::<LinearItem>(item, cx))
        .or_else(|| of::<HexItem>(item, cx))
        .or_else(|| of::<StructItem>(item, cx))
}

/// Returns the digest of every place of [`places`], each named by its place, and of the
/// functions panel.
///
/// They are read in a new window over a fresh load of [`wide_sample`] whose engine work,
/// the load's and the views', runs under a cap of `workers` threads.
fn digests(
    app_state: &Arc<AppState>,
    workers: usize,
    cx: &mut TestAppContext,
) -> Vec<(String, u64)> {
    let cap = Workers(NonZeroUsize::new(workers).unwrap());
    cap.within(|| {
        let (app, cx) = open(app_state, cx);
        let loaded = wide_sample();
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        let mut out = Vec::new();
        for place in places() {
            open_permanent(&app.workspace, &loaded, &place, cx);
            draw(cx);
            draw(cx);
            let digest = app.workspace.read_with(cx, |workspace, cx| {
                let item = workspace.active_item(cx).unwrap();
                digest_of(item.as_ref(), cx).unwrap()
            });
            out.push((format!("{place:?}"), digest));
        }
        let panel = app.workspace.read_with(cx, |workspace, cx| {
            let panel = workspace.panel::<FunctionsPanel>(cx).unwrap();
            panel.read(cx).digest(cx)
        });
        out.push(("FunctionsPanel".to_owned(), panel));
        out
    })
}

/// Every place, and the functions panel, shows the same digest whether the engine ran on
/// one thread or on sixteen, each over its own load of a program wide enough to run on
/// both, and no digest is the empty fold.
#[gpui::test]
fn every_place_shows_the_same_digest_at_one_and_sixteen_workers(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let one = digests(&app_state, 1, cx);
    let sixteen = digests(&app_state, 16, cx);
    assert_eq!(one.len(), places().len() + 1);
    let functions = wide_sample().initial_rows.rows.len();
    assert!(
        functions > usize::try_from(LEAVES).unwrap(),
        "{functions} functions"
    );
    assert_eq!(one, sixteen);
    let empty = Digest::default().value();
    assert!(one.iter().all(|(_, digest)| *digest != empty), "{one:?}");
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
        open_permanent(&app.workspace, &loaded, &place, cx);
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
