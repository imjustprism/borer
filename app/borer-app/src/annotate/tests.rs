//! The inline editor commits only the plan on screen, in the engine's words, and every
//! commit is undone and redone through the engine's revert.

use std::sync::Arc;

use borer_engine::analysis::edit::{Edit, Force};
use borer_engine::view::Ref;
use gpui::{Entity, Focusable as _, TestAppContext, VisualTestContext};
use workspace::Workspace;

use super::{Annotator, Ask};
use crate::app_view::tests::{binary_in, init, loaded_of, open, open_place, shown};
use crate::binary::Binary;
use crate::code_view::tests::three_functions;
use crate::decompile_item::tests::put_cursor;
use crate::decompile_item::{DecompileItem, Form, TabMode};
use crate::history::Way;
use crate::places::Place;
use crate::worker::{LoadedBinary, planned_blocking};

/// Entry of [`fixture`]'s caller, which calls [`CALLEE`].
const CALLER: u64 = 0x1000;

/// Address of the caller's call.
const CALL: u64 = 0x1004;

/// Entry of [`fixture`]'s callee.
const CALLEE: u64 = 0x1030;

/// Entry of [`fixture`]'s function nothing calls, named by an export.
const APART: u64 = 0x1060;

/// Returns [`three_functions`] as a loaded binary.
fn fixture() -> Arc<LoadedBinary> {
    let (program, analysis, overlay) = three_functions();
    loaded_of(program, analysis, overlay)
}

/// Opens a window with [`fixture`] loaded and returns its workspace, binary and context.
fn window(cx: &mut TestAppContext) -> (Entity<Workspace>, Entity<Binary>, &mut VisualTestContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    let binary = binary_in(&app.workspace, cx);
    binary.update(cx, |binary, cx| binary.finish_load(Ok(fixture()), cx));
    cx.run_until_parked();
    (app.workspace, binary, cx)
}

/// Opens `place` of the binary's state in a permanent tab and returns it, built and drawn.
fn tab(
    workspace: &Entity<Workspace>,
    binary: &Entity<Binary>,
    place: Place,
    cx: &mut VisualTestContext,
) -> Entity<DecompileItem> {
    let loaded = state(binary, cx);
    open_place(workspace, &loaded, place, TabMode::Permanent, cx);
    shown(workspace, cx);
    workspace
        .read_with(cx, |workspace, cx| {
            workspace.active_item_as::<DecompileItem>(cx)
        })
        .unwrap()
}

/// Returns the binary's state now.
fn state(binary: &Entity<Binary>, cx: &mut VisualTestContext) -> Arc<LoadedBinary> {
    binary.read_with(cx, |binary, _| binary.loaded().cloned().unwrap())
}

/// Puts `tab`'s cursor on the first token linked to `target`.
fn on(tab: &Entity<DecompileItem>, target: &Ref, cx: &mut VisualTestContext) {
    on_first(tab, |link| link == target, cx);
}

/// Puts `tab`'s cursor on the first token whose link `pick` accepts.
fn on_first(tab: &Entity<DecompileItem>, pick: impl Fn(&Ref) -> bool, cx: &mut VisualTestContext) {
    let at = tab.read_with(cx, |item, _| {
        let code = item.code().unwrap();
        (0..code.len())
            .find_map(|row| {
                let (view, line) = code.get(row)?;
                let mut tokens = view.tokens(line);
                tokens
                    .find_map(|(span, _, link)| link.filter(|l| pick(l)).map(|_| (row, span.start)))
            })
            .unwrap()
    });
    put_cursor(tab, at, cx);
}

/// Puts `tab`'s cursor on the first line its view says shows the instruction at `va`.
fn on_line(tab: &Entity<DecompileItem>, va: u64, cx: &mut VisualTestContext) {
    let row = tab.read_with(cx, |item, _| {
        let code = item.code().unwrap();
        (0..code.len())
            .find(|&row| code.get(row).and_then(|(view, line)| view.address(line)) == Some(va))
            .unwrap()
    });
    put_cursor(tab, (row, 0), cx);
}

/// Asks `ask` in `tab` at its cursor and returns the inline editor that opens.
fn ask(tab: &Entity<DecompileItem>, ask: Ask, cx: &mut VisualTestContext) -> Entity<Annotator> {
    tab.update_in(cx, |item, window, cx| item.annotate(ask, window, cx));
    cx.run_until_parked();
    tab.read_with(cx, |item, _| item.inline().cloned()).unwrap()
}

/// Types `text` in the inline editor, in place of what it holds, without waiting.
fn type_text(annotator: &Entity<Annotator>, text: &str, cx: &mut VisualTestContext) {
    annotator.update_in(cx, |annotator, window, cx| {
        let input = annotator.input().clone();
        input.update(cx, |input, cx| input.set_text(text, window, cx));
    });
}

/// Lets typing pause past [`super::DEBOUNCE`], the engine answer and the window draw, so the
/// answer's lines are on screen.
fn settle(cx: &mut VisualTestContext) {
    cx.executor().advance_clock(super::DEBOUNCE);
    cx.run_until_parked();
    cx.update(|window, cx| window.draw(cx).clear(cx));
    cx.run_until_parked();
}

/// Presses Enter in the inline editor and lets every view settle.
fn enter(annotator: &Entity<Annotator>, cx: &mut VisualTestContext) {
    annotator.update(cx, |annotator, cx| annotator.confirm(cx));
    settle(cx);
}

/// Presses Enter after `undraw` leaves the typed `name`'s plan undrawn, checks that it
/// commits nothing, then draws the plan and checks that Enter commits `name` to the callee.
fn commits_only_once_drawn(
    binary: &Entity<Binary>,
    editor: &Entity<Annotator>,
    name: &str,
    cx: &mut VisualTestContext,
    undraw: impl FnOnce(&mut Annotator),
) {
    editor.update(cx, |editor, cx| {
        undraw(editor);
        editor.confirm(cx);
        cx.notify();
    });
    cx.run_until_parked();
    let named = |cx: &mut VisualTestContext| state(binary, cx).overlay.names.get(&CALLEE).cloned();
    assert_eq!(named(cx), None, "Enter committed lines never drawn");
    settle(cx);
    enter(editor, cx);
    assert_eq!(named(cx).as_deref(), Some(name));
}

/// Returns the first view of `tab`, as its lines hold it.
fn view_of(
    tab: &Entity<DecompileItem>,
    cx: &mut VisualTestContext,
) -> Arc<borer_engine::view::View> {
    tab.read_with(cx, |item, _| {
        item.code().and_then(|c| c.get(0)).map(|(v, _)| v.clone())
    })
    .unwrap()
}

/// The caller's tab and the tab of the function apart.
type Tabs = (Entity<DecompileItem>, Entity<DecompileItem>);

/// Renames the callee from its call token in the caller's tab.
///
/// It is planned as the name is typed and committed on Enter; returns the caller's tab,
/// the tab of the function apart and its view before the rename, and the binary.
fn rename_from_the_call(
    cx: &mut TestAppContext,
) -> (
    Tabs,
    Arc<borer_engine::view::View>,
    Entity<Binary>,
    &mut VisualTestContext,
) {
    let (workspace, binary, cx) = window(cx);
    let apart = tab(&workspace, &binary, Place::decompile(APART), cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let kept = view_of(&apart, cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Rename, cx);
    type_text(&editor, "load_settings", cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(
        matches!(&said, Some(Ok(lines)) if !lines.is_empty()),
        "{said:?}"
    );
    enter(&editor, cx);
    ((caller, apart), kept, binary, cx)
}

/// Renaming a callee from its call token commits on Enter, the caller's view spells the
/// new name, and the change feed holds the person's edit.
#[gpui::test]
fn renaming_a_callee_from_its_call_rebuilds_the_callers_view(cx: &mut TestAppContext) {
    let ((caller, _), _, binary, cx) = rename_from_the_call(cx);
    let text = view_of(&caller, cx).spell();
    assert!(text.contains("load_settings"), "{text}");
    assert!(caller.read_with(cx, |item, _| item.inline().is_none()));
    let last = binary.read_with(cx, |binary, _| binary.changes().last().cloned());
    assert_eq!(
        last.map(|e| e.author),
        Some(borer_engine::analysis::edit::Author::Person)
    );
}

/// A view that names nothing the rename changed is the same view after it.
#[gpui::test]
fn a_rename_keeps_each_view_that_names_nothing_it_changed(cx: &mut TestAppContext) {
    let ((_, apart), kept, _, cx) = rename_from_the_call(cx);
    assert!(
        Arc::ptr_eq(&kept, &view_of(&apart, cx)),
        "the apart view was built again"
    );
}

/// A taken name is refused in exactly the words the engine's plan gives, less the way an
/// agent's call takes it anyway, and Enter on the refusal commits nothing.
#[gpui::test]
fn a_taken_name_is_refused_in_the_plans_own_words(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let before = state(&binary, cx);
    let taken = Edit::Name {
        at: CALLEE,
        name: "apart".to_owned(),
    };
    let want = planned_blocking(&before, &[taken], Force::Refuse).map(|(_, said)| said);
    assert!(want.is_err(), "{want:?}");
    let want = want.map_err(|why| why.replace(borer_engine::analysis::edit::TAKE_IT, ""));
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Rename, cx);
    type_text(&editor, "apart", cx);
    settle(cx);
    assert_eq!(
        editor.read_with(cx, |editor, cx| editor.said(cx)),
        Some(want)
    );
    enter(&editor, cx);
    assert_eq!(state(&binary, cx).fingerprint, before.fingerprint);
}

/// Commits the rename of the callee to `name` through the inline editor of `tab`.
fn rename_callee(tab: &Entity<DecompileItem>, name: &str, cx: &mut VisualTestContext) {
    on(tab, &Ref::Function(CALLEE), cx);
    let editor = ask(tab, Ask::Rename, cx);
    type_text(&editor, name, cx);
    settle(cx);
    enter(&editor, cx);
}

/// Undo restores the overlay's fingerprint and redo the edited one; an undo the engine
/// refuses, because a later edit off the stack (another author's) took the name it would
/// give back, says the engine's reason, never an agent's `force`, and leaves the stack as
/// it was.
#[gpui::test]
fn undo_and_redo_restore_each_fingerprint_and_a_refused_undo_keeps_the_stack(
    cx: &mut TestAppContext,
) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let fingerprint = |cx: &mut VisualTestContext| state(&binary, cx).fingerprint;
    let step = |way: Way, cx: &mut VisualTestContext| {
        binary.update(cx, |binary, cx| binary.step(way, cx));
        settle(cx);
    };
    let before = fingerprint(cx);
    rename_callee(&caller, "first", cx);
    let named = fingerprint(cx);
    assert_ne!(named, before);
    step(Way::Undo, cx);
    assert_eq!(fingerprint(cx), before);
    step(Way::Redo, cx);
    assert_eq!(fingerprint(cx), named);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    rename_callee(&caller, "second", cx);
    let rename = Edit::Name {
        at: CALLER,
        name: "first".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[rename], cx));
    settle(cx);
    binary.update(cx, |binary, _| binary.forget_newest_step());
    let held = fingerprint(cx);
    step(Way::Undo, cx);
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert_eq!(fingerprint(cx), held, "{status}");
    assert!(status.starts_with("Undo refused: 'first' "), "{status}");
    assert!(!status.contains("force"), "{status}");
    let rename = Edit::Name {
        at: CALLER,
        name: "caller".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[rename], cx));
    settle(cx);
    binary.update(cx, |binary, _| binary.forget_newest_step());
    step(Way::Undo, cx);
    let names = state(&binary, cx).overlay.names.get(&CALLEE).cloned();
    assert_eq!(
        names.as_deref(),
        Some("first"),
        "the refused step stayed on the stack"
    );
}

/// Escape closes the inline editor and writes nothing, and nothing in the edit flow asks
/// a blocking question.
#[gpui::test]
fn escape_writes_nothing(cx: &mut TestAppContext) {
    let (caller, binary, editor, cx) = renaming_the_callee(cx);
    let before = state(&binary, cx).fingerprint;
    type_text(&editor, "never_written", cx);
    settle(cx);
    editor.update(cx, |editor, cx| editor.cancel(cx));
    settle(cx);
    assert_eq!(state(&binary, cx).fingerprint, before);
    assert!(caller.read_with(cx, |item, _| item.inline().is_none()));
    for (name, text) in [
        ("annotate.rs", include_str!("../annotate.rs")),
        ("history.rs", include_str!("../history.rs")),
    ] {
        assert!(
            !text.contains(".prompt("),
            "{name} asks a blocking question"
        );
    }
}

/// Returns the first row of `tab` not opening with a comment whose line comes from a block,
/// by `has`: with the block it comes from, or one that comes from none.
fn row_by_origin(
    tab: &Entity<DecompileItem>,
    has: bool,
    cx: &mut VisualTestContext,
) -> (usize, Option<u64>) {
    tab.read_with(cx, |item, _| {
        let code = item.code().unwrap();
        (0..code.len())
            .find_map(|row| {
                let (view, line) = code.get(row)?;
                let origin = view.origin(line);
                let noted = view
                    .token_at(line, 0)
                    .is_some_and(|(_, _, link)| matches!(link, Some(Ref::Comment(_))));
                (origin.is_some() == has && !noted).then_some((row, origin))
            })
            .unwrap()
    })
}

/// Asks `ask` at `row` of `tab`, types `text` and commits it, returning the editor's note.
fn comment_at(
    tab: &Entity<DecompileItem>,
    (row, ask_for): (usize, Ask),
    text: &str,
    cx: &mut VisualTestContext,
) -> String {
    put_cursor(tab, (row, 0), cx);
    let editor = ask(tab, ask_for, cx);
    let note = editor
        .read_with(cx, |editor, _| editor.note.clone())
        .unwrap_or_default();
    type_text(&editor, text, cx);
    settle(cx);
    enter(&editor, cx);
    note
}

/// A comment from a listing line lands at the line's address; from a decompile line that
/// comes from no block, at the function's entry, which the editor says.
#[gpui::test]
fn a_comment_lands_at_the_listing_lines_address_and_else_the_entry(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let listing = Place::Code {
        entry: CALLER,
        form: Form::Listing,
        at: None,
    };
    let lines = tab(&workspace, &binary, listing, cx);
    on_line(&lines, CALL, cx);
    let editor = ask(&lines, Ask::Comment, cx);
    type_text(&editor, "calls the callee", cx);
    settle(cx);
    enter(&editor, cx);
    let comment =
        |at: u64, cx: &mut VisualTestContext| state(&binary, cx).overlay.comments.get(&at).cloned();
    assert_eq!(comment(CALL, cx).as_deref(), Some("calls the callee"));
    let code = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let (row, _) = row_by_origin(&code, false, cx);
    let note = comment_at(&code, (row, Ask::Comment), "the caller", cx);
    assert!(note.contains(&format!("entry {CALLER:#x}")), "{note}");
    assert_eq!(comment(CALLER, cx).as_deref(), Some("the caller"));
}

/// A question asked at a decompile line that comes from a block lands at that block, which
/// the editor says.
#[gpui::test]
fn a_question_at_a_decompile_line_lands_at_its_block(cx: &mut TestAppContext) {
    let app_state = init(cx);
    let (app, cx) = open(&app_state, cx);
    let binary = binary_in(&app.workspace, cx);
    let loaded = crate::check_marks::tests::one_function(&[
        0x48, 0x89, 0x0a, // ASM: mov [rdx], rcx
        0xc3, // ASM: ret
    ]);
    binary.update(cx, |binary, cx| binary.finish_load(Ok(loaded), cx));
    cx.run_until_parked();
    let code = tab(&app.workspace, &binary, Place::decompile(CALLER), cx);
    let (row, block) = row_by_origin(&code, true, cx);
    let block = block.unwrap_or_default();
    let note = comment_at(&code, (row, Ask::Question), "? what does it store", cx);
    assert!(note.contains(&format!("{block:#x}, the block")), "{note}");
    let comments = state(&binary, cx).overlay.comments.clone();
    assert_eq!(
        comments.get(&block).map(String::as_str),
        Some("? what does it store")
    );
}

/// Enter while the plan of the text typed last has not landed commits nothing, though
/// the older text's plan is on screen; once the newer plan lands, Enter commits it.
#[gpui::test]
fn the_name_committed_is_the_one_typed_last(cx: &mut TestAppContext) {
    let (_, binary, editor, cx) = renaming_the_callee(cx);
    type_text(&editor, "older_name", cx);
    settle(cx);
    type_text(&editor, "newer_name", cx);
    editor.update(cx, |editor, cx| editor.confirm(cx));
    settle(cx);
    let named = |cx: &mut VisualTestContext| state(&binary, cx).overlay.names.get(&CALLEE).cloned();
    assert_eq!(named(cx), None, "Enter committed a plan of another text");
    enter(&editor, cx);
    assert_eq!(named(cx).as_deref(), Some("newer_name"));
}

/// Opens a window with a code tab of the caller and the inline editor renaming the callee
/// from its call token, returning the tab, the binary and the editor.
fn renaming_the_callee(
    cx: &mut TestAppContext,
) -> (
    Entity<DecompileItem>,
    Entity<Binary>,
    Entity<Annotator>,
    &mut VisualTestContext,
) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Rename, cx);
    (caller, binary, editor, cx)
}

/// Opens a window with a hex tab at the caller, returning the binary.
fn hex_at_the_caller(cx: &mut TestAppContext) -> (Entity<Binary>, &mut VisualTestContext) {
    let (workspace, binary, cx) = window(cx);
    let loaded = state(&binary, cx);
    let hex = Place::Hex { at: Some(CALLER) };
    open_place(&workspace, &loaded, hex, TabMode::Permanent, cx);
    settle(cx);
    (binary, cx)
}

/// Opens a hex tab at the caller, presses n there and selects the strip's text, returning
/// the binary.
fn rename_in_hex(cx: &mut TestAppContext) -> (Entity<Binary>, &mut VisualTestContext) {
    let (binary, cx) = hex_at_the_caller(cx);
    cx.simulate_keystrokes("n");
    settle(cx);
    cx.dispatch_action(editor::actions::SelectAll);
    (binary, cx)
}

/// Keys the hex tab binds stay out of the hex strip's editor: n opens Rename, and the
/// name typed after it, n included, is the name committed.
#[gpui::test]
fn a_hex_key_types_into_the_hex_strip(cx: &mut TestAppContext) {
    let (binary, cx) = rename_in_hex(cx);
    cx.simulate_keystrokes("m a i n");
    settle(cx);
    cx.simulate_keystrokes("enter");
    settle(cx);
    let names = state(&binary, cx).overlay.names.get(&CALLER).cloned();
    assert_eq!(names.as_deref(), Some("main"));
}

/// Asking a question where a comment is opens with the `?` before that comment, so
/// Enter keeps what was written.
#[gpui::test]
fn a_question_keeps_the_comment_it_asks_about(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let comment = Edit::Comment {
        at: CALLER,
        text: "counts the callers".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[comment], cx));
    settle(cx);
    let code = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    put_cursor(&code, (1, 0), cx);
    let editor = ask(&code, Ask::Question, cx);
    let text = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert_eq!(text, "? counts the callers");
}

/// An Enter the binary refuses, because another edit still runs, keeps the editor open
/// with its text, planned again over the state that edit left: a second Enter commits it.
#[gpui::test]
fn a_refused_enter_keeps_the_editor_and_its_text(cx: &mut TestAppContext) {
    let (binary, cx) = rename_in_hex(cx);
    cx.simulate_keystrokes("k e p t");
    settle(cx);
    let other = Edit::Comment {
        at: CALLER,
        text: "elsewhere".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[other], cx));
    cx.simulate_keystrokes("enter");
    let names = |cx: &mut VisualTestContext| state(&binary, cx).overlay.names.get(&CALLER).cloned();
    settle(cx);
    assert_eq!(names(cx), None, "the refused Enter committed");
    cx.simulate_keystrokes("enter");
    settle(cx);
    assert_eq!(names(cx).as_deref(), Some("kept"));
}

/// After a commit of C declarations the status line says what the commit did, not what a
/// dry run would do.
#[gpui::test]
fn a_commit_says_what_it_did(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let editor = ask(&caller, Ask::Declare, cx);
    type_text(&editor, "struct Pair { int a; int b; };", cx);
    settle(cx);
    enter(&editor, cx);
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert!(
        state(&binary, cx).overlay.types.contains_key("Pair"),
        "{status}"
    );
    assert!(!status.starts_with("dry-run"), "{status}");
    assert!(!status.contains('\n'), "{status}");
}

/// A tab building its view again after an edit drops the inline editor of the view it
/// replaced, and the focus goes to the new view.
#[gpui::test]
fn a_rebuilt_tab_drops_its_inline_editor(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    ask(&caller, Ask::Rename, cx);
    let rename = Edit::Name {
        at: APART,
        name: "renamed_apart".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[rename], cx));
    settle(cx);
    assert!(caller.read_with(cx, |item, _| item.inline().is_none()));
    let focused = caller.update_in(cx, |item, window, cx| {
        item.editor().focus_handle(cx).is_focused(window)
    });
    assert!(focused);
}

/// Set Type on a call types its function by a prototype, opened with the signature its
/// text spells, and on the function's own variable states its type under the name typed.
#[gpui::test]
fn set_type_states_a_callees_prototype_and_a_variables_type(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Type, cx);
    let prefill = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert!(prefill.contains('('), "{prefill}");
    type_text(&editor, "int count_up(int *n)", cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(
        matches!(&said, Some(Ok(lines)) if !lines.is_empty()),
        "{said:?}"
    );
    enter(&editor, cx);
    let proto = state(&binary, cx)
        .overlay
        .prototypes
        .get(&CALLEE)
        .map(|p| p.spell());
    assert!(
        proto.as_ref().is_some_and(|p| p.contains("int *n")),
        "{proto:?}"
    );
    let callee = tab(&workspace, &binary, Place::decompile(CALLEE), cx);
    on_first(
        &callee,
        |link| matches!(link, Ref::Variable { name, .. } if &**name == "n"),
        cx,
    );
    let editor = ask(&callee, Ask::Type, cx);
    type_text(&editor, "unsigned int *", cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(
        matches!(&said, Some(Ok(lines)) if !lines.is_empty()),
        "{said:?}"
    );
    enter(&editor, cx);
    let vars = state(&binary, cx)
        .overlay
        .vars
        .get(&CALLEE)
        .cloned()
        .unwrap_or_default();
    assert!(
        vars.values().any(|v| v.name == "n" && v.ty.is_some()),
        "{vars:?}"
    );
}

/// New Enum and New Typedef define the type typed, read in their own short forms, and a
/// malformed one is refused before anything is written.
#[gpui::test]
fn new_enum_and_new_typedef_define_their_types(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let before = state(&binary, cx).fingerprint;
    let editor = ask(&caller, Ask::Enum, cx);
    type_text(&editor, "Run = 1", cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(matches!(said, Some(Err(_))), "{said:?}");
    enter(&editor, cx);
    assert_eq!(state(&binary, cx).fingerprint, before);
    type_text(&editor, "State: Run = 1, Stop", cx);
    settle(cx);
    enter(&editor, cx);
    let editor = ask(&caller, Ask::Typedef, cx);
    type_text(&editor, "Handle = u64", cx);
    settle(cx);
    enter(&editor, cx);
    let types = state(&binary, cx).overlay.types.clone();
    assert!(
        types.contains_key("State") && types.contains_key("Handle"),
        "{types:?}"
    );
}

/// A string's row takes a comment and refuses a name in the engine's words: a string row
/// asks the engine about the string, not about a data address.
#[gpui::test]
fn a_strings_row_is_asked_about_its_string(cx: &mut TestAppContext) {
    use crate::rows_panel::RowKind as _;
    use crate::tables::Strings;
    let (_, binary, cx) = window(cx);
    let loaded = state(&binary, cx);
    let row = borer_engine::strings::walk::StringLine {
        off: 0x100,
        va: Some(CALLER + 0x100),
        len: 4,
        encoding: borer_engine::strings::Encoding::Ascii,
        text: "text".to_owned(),
    };
    let r = Strings::subject(&row).unwrap();
    assert_eq!(r, Ref::String(CALLER + 0x100));
    let renamed = Ask::Rename.offered(&loaded, Some(&r));
    let literal = Ask::Rename.offered(&loaded, Some(&Ref::String(CALLER + 0x100)));
    assert_eq!(renamed, literal);
    assert!(renamed.is_err());
    assert!(Ask::Comment.offered(&loaded, Some(&r)).is_ok());
}

/// Rename on a row of the functions table renames that row's function, typed in the strip
/// under the table.
#[gpui::test]
fn a_functions_row_renames_its_function(cx: &mut TestAppContext) {
    use crate::functions_panel::FunctionsPanel;
    let (workspace, binary, cx) = window(cx);
    let panel = workspace.update_in(cx, |workspace, window, cx| {
        workspace.focus_panel::<FunctionsPanel>(window, cx);
        workspace.panel::<FunctionsPanel>(cx)
    });
    let panel = panel.unwrap();
    panel.update_in(cx, |panel, window, cx| {
        let rows = panel.rows_focus().clone();
        window.focus(&rows, cx);
    });
    settle(cx);
    cx.dispatch_action(super::Rename);
    settle(cx);
    assert!(panel.read_with(cx, |panel, _| panel.strip_open()));
    cx.dispatch_action(editor::actions::SelectAll);
    cx.simulate_keystrokes("s t a r t");
    settle(cx);
    cx.simulate_keystrokes("enter");
    settle(cx);
    let names = state(&binary, cx).overlay.names.get(&CALLER).cloned();
    assert_eq!(names.as_deref(), Some("start"));
}

/// Opens the inline editor for `ask` over `offer` in `tab`, as Declare C from Header opens it.
fn open_offer(
    tab: &Entity<DecompileItem>,
    (ask, offer): (Ask, borer_engine::analysis::edit::Offer),
    cx: &mut VisualTestContext,
) -> Entity<Annotator> {
    tab.update_in(cx, |item, window, cx| {
        item.open_inline((ask, offer), None, window, cx);
    });
    tab.read_with(cx, |item, _| item.inline().cloned()).unwrap()
}

/// A header with CRLF line ends and tab indents declares its types as read: the field holds
/// the text as it is, with nothing written out.
#[gpui::test]
fn a_header_with_crlf_and_tabs_declares_its_types(cx: &mut TestAppContext) {
    use borer_engine::analysis::edit::{Form as EditForm, Offer};
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let header = "struct Pair {\r\n\tint a;\r\n\tint b;\r\n};\r\n".to_owned();
    let offer = Offer {
        form: EditForm::Declare,
        now: header.clone(),
    };
    let editor = open_offer(&caller, (Ask::Declare, offer), cx);
    let text = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert_eq!(text.replace("\r\n", "\n"), header.replace("\r\n", "\n"));
    assert!(text.contains('\t'), "{text:?}");
    type_text(&editor, &header, cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(matches!(&said, Some(Ok(_))), "{said:?}");
    enter(&editor, cx);
    assert!(state(&binary, cx).overlay.types.contains_key("Pair"));
}

/// Editing a comment that holds a hidden character keeps it: the field holds the comment as
/// stored, and a line below writes the character out.
#[gpui::test]
fn editing_a_comment_keeps_its_hidden_characters(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let hidden = "a\u{200b}b";
    let comment = Edit::Comment {
        at: CALLEE,
        text: hidden.to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[comment], cx));
    settle(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let r = Ref::Function(CALLEE);
    let offer = Ask::Comment.offered(&state(&binary, cx), Some(&r)).unwrap();
    let editor = open_offer(&caller, (Ask::Comment, offer), cx);
    let text = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert_eq!(text, hidden);
    type_text(&editor, &format!("{hidden} more"), cx);
    settle(cx);
    enter(&editor, cx);
    let stored = state(&binary, cx).overlay.comments.get(&CALLEE).cloned();
    assert_eq!(stored.as_deref(), Some("a\u{200b}b more"));
}

/// A name left as the person stated it plans a plan that changes nothing, and Enter closes
/// the editor writing nothing and logging nothing.
#[gpui::test]
fn an_unchanged_name_commits_nothing(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let kept = Edit::Name {
        at: CALLEE,
        name: "kept".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[kept], cx));
    settle(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Rename, cx);
    let before = state(&binary, cx).fingerprint;
    settle(cx);
    let text = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert_eq!(text, "kept");
    enter(&editor, cx);
    assert_eq!(state(&binary, cx).fingerprint, before);
    assert!(caller.read_with(cx, |item, _| item.inline().is_none()));
    assert_eq!(binary.read_with(cx, |binary, _| binary.changes().len()), 1);
}

/// A header read as it is, LF line ends and all, declares its types on Enter with nothing
/// typed: what opens the editor is a plan like any other.
#[gpui::test]
fn a_header_declares_its_types_as_opened(cx: &mut TestAppContext) {
    use borer_engine::analysis::edit::{Form as EditForm, Offer};
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let offer = Offer {
        form: EditForm::Declare,
        now: "struct Pair {
	int a;
	int b;
};
"
        .to_owned(),
    };
    let editor = open_offer(&caller, (Ask::Declare, offer), cx);
    settle(cx);
    enter(&editor, cx);
    assert!(state(&binary, cx).overlay.types.contains_key("Pair"));
}

/// A prototype the text infers, which no one stated, is stated on Enter as it opened.
#[gpui::test]
fn an_inferred_prototype_is_stated_as_opened(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let editor = ask(&caller, Ask::Type, cx);
    settle(cx);
    let said = editor.read_with(cx, |editor, cx| {
        (editor.input().read(cx).text(cx), editor.said(cx))
    });
    enter(&editor, cx);
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert!(
        state(&binary, cx).overlay.prototypes.contains_key(&CALLEE),
        "{said:?} {status}"
    );
}

/// A plan that lands again for the same text, after an edit elsewhere, is not committed by
/// Enter until its own lines are drawn.
#[gpui::test]
fn a_new_plan_for_the_same_text_commits_only_once_drawn(cx: &mut TestAppContext) {
    let (_, binary, editor, cx) = renaming_the_callee(cx);
    type_text(&editor, "replanned", cx);
    settle(cx);
    commits_only_once_drawn(&binary, &editor, "replanned", cx, |editor| {
        if let Some((id, ..)) = editor.answer.as_mut() {
            *id = id.saturating_add(1);
        }
    });
}

/// An editor left open while another binary opens closes, planning nothing over the old one.
#[gpui::test]
fn an_editor_closes_when_another_binary_opens(cx: &mut TestAppContext) {
    let (_, binary, editor, cx) = renaming_the_callee(cx);
    let closed = std::rc::Rc::new(std::cell::Cell::new(false));
    let seen = closed.clone();
    let _watch = cx.update(|_, cx| {
        cx.subscribe(&editor, move |_, event: &super::Annotated, _| {
            seen.set(*event == super::Annotated::Closed);
        })
    });
    binary.update(cx, |binary, cx| binary.finish_load(Ok(fixture()), cx));
    settle(cx);
    assert!(closed.get());
}

/// Enter on a plan that landed but whose lines were not drawn commits nothing; once they
/// are drawn, Enter commits.
#[gpui::test]
fn enter_before_the_plan_is_drawn_commits_nothing(cx: &mut TestAppContext) {
    let (_, binary, editor, cx) = renaming_the_callee(cx);
    type_text(&editor, "undrawn", cx);
    cx.executor().advance_clock(super::DEBOUNCE);
    cx.run_until_parked();
    let said = editor.read_with(cx, |editor, cx| editor.said(cx));
    assert!(matches!(&said, Some(Ok(_))), "{said:?}");
    commits_only_once_drawn(&binary, &editor, "undrawn", cx, |editor| {
        editor.painted = None;
    });
}

/// `n` in a code tab opens Rename under the cursor's token, and what is typed after it is
/// the name committed.
#[gpui::test]
fn n_in_a_code_tab_renames_what_is_typed(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    caller.update_in(cx, |item, window, cx| {
        window.focus(&item.editor().focus_handle(cx), cx);
    });
    cx.simulate_keystrokes("n");
    settle(cx);
    cx.dispatch_action(editor::actions::SelectAll);
    cx.simulate_keystrokes("l o a d");
    settle(cx);
    cx.simulate_keystrokes("enter");
    settle(cx);
    let names = state(&binary, cx).overlay.names.get(&CALLEE).cloned();
    assert_eq!(names.as_deref(), Some("load"));
}

/// A strip asked for while another edit lands plans over the state that edit left, so its
/// Enter commits.
#[gpui::test]
fn a_strip_asked_while_an_edit_lands_plans_over_it(cx: &mut TestAppContext) {
    let (binary, cx) = hex_at_the_caller(cx);
    cx.simulate_keystrokes("n");
    let other = Edit::Comment {
        at: CALLEE,
        text: "landed".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[other], cx));
    settle(cx);
    cx.dispatch_action(editor::actions::SelectAll);
    cx.simulate_keystrokes("f r e s h");
    settle(cx);
    cx.simulate_keystrokes("enter");
    settle(cx);
    let names = state(&binary, cx).overlay.names.get(&CALLER).cloned();
    assert_eq!(names.as_deref(), Some("fresh"));
}

/// Rename in a hex tab with no cursor says why on the status line and opens nothing in the
/// code tab beside it.
#[gpui::test]
fn rename_in_a_hex_tab_with_no_cursor_says_why(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    let loaded = state(&binary, cx);
    open_place(
        &workspace,
        &loaded,
        Place::Hex { at: None },
        TabMode::Permanent,
        cx,
    );
    settle(cx);
    cx.dispatch_action(super::Rename);
    settle(cx);
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert_eq!(status, "Rename: put the cursor on a byte first");
    assert!(caller.read_with(cx, |item, _| item.inline().is_none()));
}

/// Comment on a rendered comment edits that comment where it is, opened with its text.
#[gpui::test]
fn comment_on_a_comment_line_edits_it(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let note = Edit::Comment {
        at: CALL,
        text: "first note".to_owned(),
    };
    binary.update(cx, |binary, cx| binary.plan_and_commit(&[note], cx));
    settle(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Comment(CALL), cx);
    let editor = ask(&caller, Ask::Comment, cx);
    let text = editor.read_with(cx, |editor, cx| editor.input().read(cx).text(cx));
    assert_eq!(text, "first note");
    type_text(&editor, "second note", cx);
    settle(cx);
    enter(&editor, cx);
    let comments = state(&binary, cx).overlay.comments.clone();
    assert_eq!(comments.get(&CALL).map(String::as_str), Some("second note"));
    assert_eq!(comments.len(), 1);
}

/// After a commit rebuilds the tab, the cursor is on the line it was on.
#[gpui::test]
fn a_commit_keeps_the_cursors_line(cx: &mut TestAppContext) {
    let (workspace, binary, cx) = window(cx);
    let caller = tab(&workspace, &binary, Place::decompile(CALLER), cx);
    on(&caller, &Ref::Function(CALLEE), cx);
    let (row, _) = caller.read_with(cx, |item, cx| item.cursor(cx)).unwrap();
    assert!(row > 0);
    let editor = ask(&caller, Ask::Rename, cx);
    type_text(&editor, "kept_line", cx);
    settle(cx);
    enter(&editor, cx);
    let after = caller.read_with(cx, |item, cx| item.cursor(cx)).unwrap();
    assert_eq!(after.0, row);
}

/// What is typed plans only once typing pauses: before the pause ends nothing is planned,
/// after it the text typed last is.
#[gpui::test]
fn typing_plans_once_it_pauses(cx: &mut TestAppContext) {
    let (_, _, editor, cx) = renaming_the_callee(cx);
    type_text(&editor, "first_try", cx);
    type_text(&editor, "second_try", cx);
    cx.run_until_parked();
    let planned = |cx: &mut VisualTestContext| {
        editor.read_with(cx, |editor, _| {
            editor.answer.as_ref().map(|(_, text, _)| text.clone())
        })
    };
    assert_eq!(planned(cx), None);
    settle(cx);
    assert_eq!(planned(cx).as_deref(), Some("second_try"));
}

/// Undo passes over an edit another has changed since and takes back the newest one it
/// still can, saying whose edit it was.
#[gpui::test]
fn undo_passes_over_an_edit_changed_since(cx: &mut TestAppContext) {
    let (_, binary, cx) = window(cx);
    let rename = |at: u64, name: &str| Edit::Name {
        at,
        name: name.to_owned(),
    };
    binary.update(cx, |binary, cx| {
        binary.plan_and_commit(&[rename(CALLER, "p_caller")], cx);
    });
    settle(cx);
    binary.update(cx, |binary, cx| {
        binary.plan_and_commit(&[rename(CALLEE, "first")], cx);
    });
    settle(cx);
    binary.update(cx, |binary, cx| {
        binary.plan_and_commit(&[rename(CALLEE, "other")], cx);
    });
    settle(cx);
    binary.update(cx, |binary, _| binary.forget_newest_step());
    binary.update(cx, |binary, cx| binary.step(Way::Undo, cx));
    settle(cx);
    let names = state(&binary, cx).overlay.names.clone();
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert_eq!(names.get(&CALLER), None, "{status}");
    assert_eq!(names.get(&CALLEE).map(String::as_str), Some("other"));
    assert!(status.starts_with("Undo: your edit: "), "{status}");
}

/// A model's proposal the person accepted is undone like the person's own edit, and the
/// status line names the model; the change feed holds both, the undo by the person.
#[gpui::test]
fn an_accepted_proposal_is_undone_as_the_models(cx: &mut TestAppContext) {
    use borer_engine::analysis::edit::Author;
    let (_, binary, cx) = window(cx);
    let model = Author::Model {
        provider: "Fake".to_owned(),
        model: "fake".to_owned(),
    };
    let rename = Edit::Name {
        at: CALLEE,
        name: "proposed".to_owned(),
    };
    binary.update(cx, |binary, cx| {
        binary.plan_and_commit_by(&[rename], model.clone(), cx);
    });
    settle(cx);
    binary.update(cx, |binary, cx| binary.step(Way::Undo, cx));
    settle(cx);
    let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
    assert!(status.starts_with("Undo: Fake fake's edit: "), "{status}");
    assert_eq!(state(&binary, cx).overlay.names.get(&CALLEE), None);
    let authors: Vec<Author> = binary.read_with(cx, |binary, _| {
        binary.changes().iter().map(|e| e.author.clone()).collect()
    });
    assert_eq!(authors, [model, Author::Person]);
}
