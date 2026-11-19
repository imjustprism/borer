//! The chat panel's keys, focus, keychain entry, locality hint and the thread's bookkeeping
//! behind what the panel draws: the cards' fields, the tool calls' state and the errors'
//! kinds.

use gpui::{
    Focusable as _, KeyDownEvent, KeyUpEvent, Keystroke, TestAppContext, VisualTestContext,
};
use serde_json::json;

use super::{ask_each, chatting, docked, have_proposed, remote, talking, verdicts_of};
use crate::chat::card::{CHANGES_SHOWN, Kind, shown};
use crate::chat::providers::{Endpoint, KEY_ENTRY, Offered, key_entry};
use crate::chat::thread::{Arg, Entry, FENCE_OPEN, Fault, Ran, Verdict, first_lines, key_of};
use crate::chat::view::hint;
use borer_engine::analysis::edit::{Edit, Force, plan};

/// Sends Enter's key down, `held` repeats of it, then its key up, to what has focus.
fn press_enter(held: usize, cx: &mut VisualTestContext) {
    let enter = Keystroke::parse("enter").unwrap();
    cx.simulate_event(KeyDownEvent {
        keystroke: enter.clone(),
        is_held: false,
        prefer_character_input: false,
    });
    for _ in 0..held {
        cx.simulate_event(KeyDownEvent {
            keystroke: enter.clone(),
            is_held: true,
            prefer_character_input: false,
        });
    }
    cx.simulate_event(KeyUpEvent { keystroke: enter });
    cx.run_until_parked();
}

/// Enter on the focused card accepts it once, even held down, and hands focus to the input,
/// so a second Enter never decides the card queued behind it; Escape on a card rejects it.
#[gpui::test]
fn enter_decides_one_card_and_hands_focus_to_the_input(cx: &mut TestAppContext) {
    let (app, panel, _, cx) = docked(cx);
    let (thread, fake, model) = talking(&panel, cx);
    have_proposed(&app, &thread, &fake, &model, &["chat_a", "chat_b"], cx);
    cx.update(|window, cx| window.draw(cx).clear(cx));
    panel.update_in(cx, |panel, window, cx| panel.show_head(window, cx));
    cx.update(|window, cx| window.draw(cx).clear(cx));
    press_enter(3, cx);
    assert_eq!(
        verdicts_of(&thread, cx),
        [Verdict::Accepted, Verdict::Waiting]
    );
    let on_input = panel.update_in(cx, |panel, window, cx| {
        panel.input.focus_handle(cx).is_focused(window)
    });
    assert!(on_input, "focus stayed on the cards");
    cx.update(|window, cx| window.draw(cx).clear(cx));
    press_enter(0, cx);
    assert_eq!(
        verdicts_of(&thread, cx),
        [Verdict::Accepted, Verdict::Waiting]
    );
    panel.update_in(cx, |panel, window, cx| panel.show_head(window, cx));
    cx.update(|window, cx| window.draw(cx).clear(cx));
    cx.simulate_keystrokes("escape");
    assert_eq!(
        verdicts_of(&thread, cx),
        [Verdict::Accepted, Verdict::Rejected]
    );
}

/// Revealing the card that waits stops the list following the newest entry, so the reveal
/// is not undone by the next frame; the person's next message follows again.
#[gpui::test]
fn revealing_a_card_stops_following(cx: &mut TestAppContext) {
    let (app, panel, _, cx) = docked(cx);
    let (thread, fake, model) = talking(&panel, cx);
    have_proposed(&app, &thread, &fake, &model, &["chat_a"], cx);
    let long: String = (0..200)
        .map(|n| format!("line {n} of a long reply\n"))
        .collect();
    fake.send_last_text(&model, long);
    fake.end_last(&model);
    cx.run_until_parked();
    cx.update(|window, cx| window.draw(cx).clear(cx));
    assert!(panel.read_with(cx, |p, _| p.list.is_following_tail()));
    panel.update_in(cx, |panel, window, cx| panel.show_head(window, cx));
    cx.update(|window, cx| window.draw(cx).clear(cx));
    let card = thread.read_with(cx, |t, _| {
        t.entries()
            .iter()
            .position(|e| matches!(e, Entry::Proposal(_)))
    });
    let (following, drawn) = panel.read_with(cx, |p, _| {
        (
            p.list.is_following_tail(),
            card.and_then(|ix| p.list.bounds_for_item(ix)),
        )
    });
    assert!(!following);
    assert!(drawn.is_some(), "the revealed card is not drawn");
    thread.update(cx, |t, cx| t.send("And then?".to_owned(), cx));
    cx.run_until_parked();
    assert!(panel.read_with(cx, |p, _| p.list.is_following_tail()));
}

/// Enter in the picker with an empty key field deletes nothing and asks the provider for
/// nothing; the chat keeps keys under an entry of its own, never the provider's bare URL.
#[gpui::test]
fn an_empty_key_field_never_deletes_a_saved_key(cx: &mut TestAppContext) {
    let (_app, panel, requests, cx) = docked(cx);
    panel.update_in(cx, |panel, window, cx| {
        panel.picked = Some(Offered::Anthropic);
        panel.save_key(window, cx);
    });
    cx.run_until_parked();
    let error = panel.read_with(cx, |p, _| p.error.clone());
    assert!(error.is_some_and(|e| e.contains("type a key first")));
    assert_eq!(requests.load(std::sync::atomic::Ordering::SeqCst), 0);
    let url = "https://api.anthropic.com";
    assert_eq!(key_entry(url), format!("{KEY_ENTRY}{url}"));
    assert_ne!(key_entry(url), url);
}

/// The header says `local` only for a model nothing sent to leaves the machine: a cloud
/// model behind a local Ollama sends elsewhere.
#[gpui::test]
fn a_cloud_model_behind_local_ollama_is_not_local(cx: &mut TestAppContext) {
    let (_app, _thread, fake, model, _cx) = chatting(None, cx);
    let mut cloud = remote(&fake, &model);
    cloud.endpoint = Endpoint {
        offered: Offered::Ollama,
        url: "http://localhost:11434/v1".into(),
    };
    let local = cloud.clone();
    cloud.model.id = "gpt-oss:120b-cloud".to_owned().into();
    assert!(hint(&cloud).starts_with("sends to"), "{}", hint(&cloud));
    assert_eq!(hint(&local), "local");
}

/// Send the Held Chat Message from the palette with nothing held agrees to nothing: the
/// next send to a new receiver still shows its notice and waits.
#[gpui::test]
fn the_palette_send_with_nothing_held_agrees_to_nothing(cx: &mut TestAppContext) {
    let (_app, panel, _, cx) = docked(cx);
    let (thread, fake, model) = talking(&panel, cx);
    let mut proxy = remote(&fake, &model);
    proxy.endpoint.url = "https://proxy.example.com".into();
    thread.update(cx, |t, cx| t.choose(proxy, cx));
    cx.update(|window, cx| window.draw(cx).clear(cx));
    cx.dispatch_action(crate::chat::SendHeldChat);
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.send("Is it packed?".to_owned(), cx));
    cx.run_until_parked();
    assert!(thread.read_with(cx, |t, _| t.held().is_some()));
    assert!(fake.pending_completions().is_empty());
}

/// A card reads each field from what its plan writes and bounds a large plan.
///
/// Two comments at one address show the one Accept writes, twice; a plan of many changes
/// spells out only the first [`CHANGES_SHOWN`] and counts the rest.
#[test]
fn a_card_shows_what_the_plan_writes_and_bounds_a_large_plan() {
    let (program, analysis, overlay) = crate::code_view::tests::sample_program();
    let comment = |at: u64, text: &str| Edit::Comment {
        at,
        text: text.to_owned(),
    };
    let twice = [comment(0x1000, "first"), comment(0x1000, "second")];
    let plan_of = |edits: &[Edit]| plan(&program, &analysis, &overlay, edits, Force::Refuse);
    let seen = shown(&plan_of(&twice).unwrap());
    let comments: Vec<&str> = seen
        .fields
        .iter()
        .filter(|f| f.kind == Kind::Comment)
        .map(|f| f.value.as_str())
        .collect();
    assert_eq!(comments, ["second", "second"]);
    let many: Vec<Edit> = (0..120u64).map(|n| comment(0x1000 + n, "x")).collect();
    let seen = shown(&plan_of(&many).unwrap());
    assert_eq!(seen.changes, 120);
    assert_eq!(seen.fields.len(), CHANGES_SHOWN * 2);
    assert_eq!(seen.kinds, [("comments", 120)]);
    assert!(!seen.takes);
}

/// The first lines kept of an answer stop at twelve lines and at their byte cap, even
/// within one long line.
#[test]
fn first_lines_are_bounded_by_lines_and_bytes() {
    let lines: String = (0..20).map(|n| format!("line {n}\n")).collect();
    assert_eq!(first_lines(&lines).lines().count(), 12);
    let long = "é".repeat(5000);
    let kept = first_lines(&long);
    assert!(kept.len() <= 2048 && long.starts_with(&kept));
}

/// A call's key is its `address` parameter when it has one, which alone links to the
/// binary; a query that looks like an address is not one.
#[test]
fn only_an_address_parameter_is_an_address() {
    let at = key_of(&json!({ "address": "0x401000" }));
    assert_eq!(at, Some(("0x401000".to_owned(), Arg::Address)));
    let query = key_of(&json!({ "query": "0x401000" }));
    assert_eq!(query, Some(("0x401000".to_owned(), Arg::Other)));
    assert_eq!(key_of(&json!({})), None);
}

/// A call's row counts what the model was sent for it, the answer fenced, and keeps its
/// first lines.
#[gpui::test]
fn a_call_shows_what_the_model_was_sent(cx: &mut TestAppContext) {
    let (_app, thread, fake, model, cx) = chatting(None, cx);
    let said = ask_each(
        &thread,
        &fake,
        &model,
        &[("query", json!({ "uri": "borer://triage" }))],
        cx,
    );
    let ran = thread.read_with(cx, |t, _| {
        let ix = t
            .entries()
            .iter()
            .position(|e| matches!(e, Entry::Tool(_)))
            .unwrap();
        t.call_at(ix).unwrap().ran.clone()
    });
    let Ran::Answered { bytes, head } = ran else {
        panic!("{ran:?}");
    };
    assert_eq!(bytes, said[0].len());
    assert!(head.starts_with(FENCE_OPEN), "{head}");
}

/// An error carries its kind from where it was made: a call whose arguments do not parse
/// is the model's, whatever its tool is called; Retry is offered for a provider's failure
/// of the newest turn only, and not once the person wrote again.
#[gpui::test]
fn errors_carry_their_kind_and_retry_only_the_newest(cx: &mut TestAppContext) {
    let (_app, thread, fake, model, cx) = chatting(None, cx);
    thread.update(cx, |t, cx| t.send("Read it".to_owned(), cx));
    cx.run_until_parked();
    let unparsed = language_model::LanguageModelCompletionEvent::ToolUseJsonParseError {
        id: "1".into(),
        tool_name: "byte budget".into(),
        raw_input: "{".into(),
        json_parse_error: "eof".to_owned(),
    };
    fake.send_last_event(&model, unparsed);
    fake.end_last(&model);
    cx.run_until_parked();
    let fault = thread.read_with(cx, |t, _| {
        let ix = t
            .entries()
            .iter()
            .position(|e| matches!(e, Entry::Error(_)));
        ix.and_then(|ix| t.fault_at(ix))
    });
    assert_eq!(fault, Some(Fault::Model));
    fake.end_last(&model);
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.send("Again".to_owned(), cx));
    cx.run_until_parked();
    fake.send_last_error(
        &model,
        language_model::LanguageModelCompletionError::Other(anyhow::anyhow!("overloaded")),
    );
    fake.end_last(&model);
    cx.run_until_parked();
    let failed = thread.read_with(cx, |t, _| t.entries().len() - 1);
    let retry = thread.read_with(cx, |t, _| t.retry_at(failed).map(str::to_owned));
    assert_eq!(retry.as_deref(), Some("Again"));
    thread.update(cx, |t, cx| t.send("Something else".to_owned(), cx));
    cx.run_until_parked();
    assert_eq!(
        thread.read_with(cx, |t, _| t.retry_at(failed).map(str::to_owned)),
        None
    );
}
