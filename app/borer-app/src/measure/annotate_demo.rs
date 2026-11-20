//! The annotating demo, `--annotate-demo [binary]`: each inline editor on screen, for
//! screenshots.
//!
//! Over the open binary (default notepad) the demo renames a call's function from its call
//! token, is refused a taken name, asks a question at a line, sets a prototype, defines an
//! enum, undoes an edit, and opens the inline editor under a hex tab and the functions
//! table. Each state on screen is announced as `ANNOTATE_STAGE <name>` and held a while
//! ([`super::stage::stage`]), so a caller can capture the window; then `ANNOTATE_DONE`, and
//! the app quits.

use editor::SelectionEffects;
use gpui::{AsyncWindowContext, Entity, WeakEntity};
use language::Point;

use super::stage::{POLL, poll, stage};
use super::{Harness, say};
use crate::annotate::{Annotator, Ask, Comment};
use crate::decompile_item::DecompileItem;
use crate::functions_panel::FunctionsPanel;
use crate::history::Way;
use crate::places::{self, PERMANENT, Place};
use borer_engine::view::Ref;

/// The word this demo's stages are said with.
const ANNOTATE: &str = "ANNOTATE";

/// Polls `found` until it gives a value.
///
/// # Errors
///
/// When `what` is still not there after a minute of polls ([`poll`]), or the window is gone.
async fn until<T>(
    what: &str,
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
    found: impl Fn(&Harness, &gpui::App) -> Option<T>,
) -> anyhow::Result<T> {
    poll(what, cx, |cx| {
        this.read_with(cx, |h, cx| found(h, cx)).ok().flatten()
    })
    .await
}

/// Opens `place` of the binary in a tab of its own.
///
/// # Errors
///
/// When the window is gone or nothing is loaded.
fn open(
    this: &WeakEntity<Harness>,
    place: Place,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    this.update_in(cx, |h, window, cx| {
        let binary = h.binary.clone();
        let loaded = binary.read(cx).loaded().cloned();
        let loaded = loaded.ok_or_else(|| anyhow::anyhow!("nothing loaded"))?;
        h.workspace.update(cx, |workspace, cx| {
            places::open(workspace, &binary, &loaded, place, PERMANENT, window, cx);
        });
        Ok(())
    })?
}

/// Waits for the active code tab to show its code.
///
/// # Errors
///
/// When none does.
async fn code_tab(
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<Entity<DecompileItem>> {
    until("a code tab", this, cx, |h, cx| {
        let item = h.workspace.read(cx).active_item_as::<DecompileItem>(cx)?;
        item.read(cx).code().is_some().then_some(item)
    })
    .await
}

/// Puts the tab's cursor on the first token `pick` accepts, else on the first line `line`
/// accepts.
///
/// # Errors
///
/// When the window is gone or nothing is accepted.
fn cursor_on(
    tab: &Entity<DecompileItem>,
    pick: impl Fn(Option<&Ref>, Option<u64>) -> bool,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    let at = tab.read_with(cx, |item, _| {
        let code = item.code()?;
        (0..code.len()).find_map(|row| {
            let (view, line) = code.get(row)?;
            if pick(None, view.origin(line)) {
                return Some((row, 0));
            }
            view.tokens(line)
                .find_map(|(span, _, link)| pick(link, None).then_some((row, span.start)))
        })
    });
    let (row, col) = at.ok_or_else(|| anyhow::anyhow!("no line to stand on"))?;
    let point = Point::new(u32::try_from(row)?, u32::try_from(col)?);
    tab.update_in(cx, |item, window, cx| {
        item.editor().update(cx, |editor, cx| {
            editor.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
                s.select_ranges([point..point]);
            });
        });
    })
}

/// Opens the inline editor for `ask` in `tab` at its cursor, types `text` in it and waits
/// for the engine's answer.
///
/// # Errors
///
/// When the window is gone or the editor never opens or answers.
async fn ask(
    this: &WeakEntity<Harness>,
    tab: &Entity<DecompileItem>,
    (ask, text): (Ask, Option<&str>),
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<Entity<Annotator>> {
    tab.update_in(cx, |item, window, cx| item.annotate(ask, window, cx))?;
    let shown = tab.clone();
    let editor = until("the inline editor", this, cx, move |_, cx| {
        shown.read(cx).inline().cloned()
    })
    .await?;
    let Some(text) = text else {
        return Ok(editor);
    };
    editor.update_in(cx, |editor, window, cx| {
        let input = editor.input().clone();
        input.update(cx, |input, cx| input.set_text(text, window, cx));
    })?;
    let answered = editor.clone();
    until("the engine's answer", this, cx, move |_, cx| {
        answered.read(cx).said(cx).map(|_| ())
    })
    .await?;
    Ok(editor)
}

/// Presses Enter in `editor` and waits for `tab`'s inline editor to close.
///
/// # Errors
///
/// When the window is gone or it never closes.
async fn enter(
    this: &WeakEntity<Harness>,
    (tab, editor): (&Entity<DecompileItem>, &Entity<Annotator>),
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    editor.update(cx, |editor, cx| editor.confirm(cx));
    let shown = tab.clone();
    until("the commit", this, cx, move |_, cx| {
        shown.read(cx).inline().is_none().then_some(())
    })
    .await
}

/// Walks every inline editor state worth a screenshot.
///
/// # Errors
///
/// When the window is gone, a wait gives up or stdout fails.
pub(super) async fn demo(
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    let entry = until("the binary", this, cx, |h, cx| {
        let loaded = h.binary.read(cx).loaded()?;
        let calls = |e: &u64| {
            loaded
                .analysis
                .function(*e)
                .is_some_and(|f| !f.callees.is_empty())
        };
        let entries = loaded.analysis.functions.iter().map(|f| f.entry);
        loaded
            .program
            .entry
            .filter(calls)
            .or_else(|| entries.clone().find(calls))
    })
    .await?;
    open(this, Place::decompile(entry), cx)?;
    let tab = code_tab(this, cx).await?;
    let callee =
        |r: Option<&Ref>, _: Option<u64>| matches!(r, Some(Ref::Function(e)) if *e != entry);
    cursor_on(&tab, callee, cx)?;
    let editor = ask(this, &tab, (Ask::Rename, Some("init_runtime")), cx).await?;
    stage(ANNOTATE, "rename", cx).await?;
    enter(this, (&tab, &editor), cx).await?;
    stage(ANNOTATE, "renamed", cx).await?;
    let tab = code_tab(this, cx).await?;
    cursor_on(&tab, callee, cx)?;
    let taken = this.read_with(cx, |h, cx| {
        let loaded = h.binary.read(cx).loaded()?;
        Some(borer_engine::analysis::name_of(
            &loaded.analysis,
            &loaded.overlay,
            entry,
        ))
    })?;
    let editor = ask(this, &tab, (Ask::Rename, taken.as_deref()), cx).await?;
    stage(ANNOTATE, "refused", cx).await?;
    editor.update(cx, |editor, cx| editor.cancel(cx));
    cursor_on(&tab, callee, cx)?;
    let editor = ask(this, &tab, (Ask::Type, None), cx).await?;
    stage(ANNOTATE, "set-type", cx).await?;
    editor.update(cx, |editor, cx| editor.cancel(cx));
    cursor_on(&tab, |_, origin| origin.is_some(), cx)?;
    let editor = ask(
        this,
        &tab,
        (Ask::Question, Some("? what does it check here")),
        cx,
    )
    .await?;
    stage(ANNOTATE, "question", cx).await?;
    enter(this, (&tab, &editor), cx).await?;
    let tab = code_tab(this, cx).await?;
    let editor = ask(
        this,
        &tab,
        (Ask::Enum, Some("Mode: Closed = 0, Open, Saved = 0x10")),
        cx,
    )
    .await?;
    stage(ANNOTATE, "enum", cx).await?;
    enter(this, (&tab, &editor), cx).await?;
    this.update(cx, |h, cx| {
        h.binary.update(cx, |b, cx| b.step(Way::Undo, cx));
    })?;
    cx.background_executor().timer(POLL).await;
    stage(ANNOTATE, "undo", cx).await?;
    open(this, Place::Hex { at: Some(entry) }, cx)?;
    cx.background_executor().timer(POLL).await;
    this.update_in(cx, |_, window, cx| {
        window.dispatch_action(Box::new(crate::annotate::Rename), cx);
    })?;
    cx.background_executor().timer(POLL * 5).await;
    stage(ANNOTATE, "hex", cx).await?;
    this.update_in(cx, |_, window, cx| {
        window.dispatch_action(Box::new(menu::Cancel), cx);
    })?;
    cx.background_executor().timer(POLL).await;
    this.update_in(cx, |h, window, cx| {
        h.workspace.update(cx, |workspace, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        let panel = h.workspace.read(cx).panel::<FunctionsPanel>(cx);
        if let Some(panel) = panel {
            let rows = panel.read(cx).rows_focus().clone();
            window.focus(&rows, cx);
        }
    })?;
    cx.background_executor().timer(POLL).await;
    this.update_in(cx, |_, window, cx| {
        window.dispatch_action(Box::new(Comment), cx);
    })?;
    cx.background_executor().timer(POLL * 5).await;
    stage(ANNOTATE, "functions", cx).await?;
    say("ANNOTATE_DONE")
}
