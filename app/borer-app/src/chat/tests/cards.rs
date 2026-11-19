//! The chat's proposal cards: each edit the model asks to apply waits as one card until
//! the person accepts it, and the card shows what Accept writes.

use gpui::{TestAppContext, VisualTestContext};
use serde_json::json;

use super::{answers, ask_each, call, chatting, first_two, have_proposed, verdicts_of};
use crate::binary::Author;
use crate::chat::thread::Verdict;

/// A dry run, `set_name`'s default, answers the model with what it would do and makes no
/// card; each apply makes one card, a batch of names one card holding every rename, and one
/// that takes a held name says so on its card and still does once planned again.
#[gpui::test]
fn only_an_apply_makes_a_card_and_it_shows_force(cx: &mut TestAppContext) {
    let (app, thread, fake, model, cx) = chatting(None, cx);
    let rows = first_two(&app, cx);
    let (first, second) = (format!("{:#x}", rows.0), format!("{:#x}", rows.1));
    let calls = [
        ("set_name", json!({ "address": first, "name": "chat_dry" })),
        (
            "set_name",
            json!({ "names": [format!("{first}=chat_one"), format!("{second}=chat_two")], "dry_run": false }),
        ),
        (
            "set_name",
            json!({ "address": second, "name": "chat_one", "force": true, "dry_run": false }),
        ),
    ];
    let said = ask_each(&thread, &fake, &model, &calls, cx);
    assert!(said[0].contains("dry-run: would "), "{}", said[0]);
    assert!(!said[0].contains("proposed, not applied"), "{}", said[0]);
    let cards = thread.read_with(cx, |t, _| t.proposals().to_vec());
    assert_eq!(cards.len(), 2, "{said:?}");
    assert_eq!(cards[0].plan.lines().len(), 2);
    let shown = |p: &crate::chat::thread::Proposal| {
        let text: Vec<String> = crate::chat::card_lines(p)
            .into_iter()
            .map(|(l, _)| l)
            .collect();
        text.join("\n")
    };
    assert!(
        shown(&cards[0]).contains("chat_two"),
        "{}",
        shown(&cards[0])
    );
    assert_eq!(cards[1].force, borer_engine::analysis::edit::Force::Take);
    thread.update(cx, |t, cx| t.accept(cards[0].id, cx));
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.accept(cards[1].id, cx));
    cx.run_until_parked();
    assert_eq!(verdicts_of(&thread, cx)[1], Verdict::Stale);
    thread.update(cx, |t, cx| t.plan_again(cards[1].id, cx));
    cx.run_until_parked();
    let again = thread.read_with(cx, |t, _| t.proposals()[1].clone());
    assert_eq!(again.force, borer_engine::analysis::edit::Force::Take);
    assert_eq!(again.verdict, Verdict::Waiting, "{:?}", again.verdict);
}

/// Every edit row the model asks to apply makes exactly one card and changes nothing until
/// Accept, which commits it with the model named in the change feed: `set_name` alone and
/// as a batch, `set_comment`, `set_type` by fields and by a C declaration, `class_layout`'s
/// apply and a script's renames.
#[gpui::test]
fn every_edit_row_waits_for_accept_as_one_card(cx: &mut TestAppContext) {
    let (program, analysis, mut overlay) = crate::code_view::tests::sample_program();
    let (caller, callee) = (
        crate::app_view::tests::CALLER,
        crate::app_view::tests::CALLEE,
    );
    overlay.names = [(callee, "Foo::Get".to_owned())].into_iter().collect();
    let loaded = crate::app_view::tests::loaded_of(program, analysis, overlay);
    let (app, thread, fake, model, cx) = chatting(Some(loaded), cx);
    let (at, to) = (format!("{caller:#x}"), format!("{callee:#x}"));
    let rows = [
        (
            "set_name",
            json!({ "address": at, "name": "chat_one", "dry_run": false }),
        ),
        (
            "set_name",
            json!({ "names": [format!("{at}=chat_two"), format!("{to}=Foo::Two")], "dry_run": false }),
        ),
        (
            "set_comment",
            json!({ "address": at, "comment": "checks it", "dry_run": false }),
        ),
        (
            "set_type",
            json!({ "name": "S", "fields": ["0:a:u32"], "dry_run": false }),
        ),
        (
            "set_type",
            json!({ "type": "struct D { int x; };", "dry_run": false }),
        ),
        (
            "class_layout",
            json!({ "class": "Foo", "apply": "FooS", "dry_run": false }),
        ),
        (
            "script",
            json!({ "code": format!("rename({caller}, \"chat_s\");"), "dry_run": false }),
        ),
    ];
    let author = Author::Model {
        provider: "Fake".into(),
        model: "fake".into(),
    };
    for (name, args) in rows {
        thread.update(cx, |t, cx| t.clear(cx));
        let before = app
            .binary
            .read_with(cx, |b, _| b.loaded().unwrap().fingerprint);
        let said = ask_each(&thread, &fake, &model, &[(name, args)], cx);
        let cards = thread.read_with(cx, |t, _| t.proposals().to_vec());
        assert_eq!(cards.len(), 1, "{name}: {said:?}");
        assert!(
            said[0].contains("proposed, not applied"),
            "{name}: {}",
            said[0]
        );
        let now = app
            .binary
            .read_with(cx, |b, _| b.loaded().unwrap().fingerprint);
        assert_eq!(now, before, "{name} changed the names before Accept");
        thread.update(cx, |t, cx| t.accept(cards[0].id, cx));
        cx.run_until_parked();
        assert_eq!(verdicts_of(&thread, cx), [Verdict::Accepted], "{name}");
        let last = app.binary.read_with(cx, |b, _| b.changes().last().cloned());
        assert_eq!(last.map(|c| c.author), Some(author.clone()), "{name}");
    }
}

/// A comment's card shows the comment whole with every character that hides itself
/// written out, beside its address.
#[gpui::test]
fn a_comment_card_writes_out_what_hides(cx: &mut TestAppContext) {
    let (_app, thread, fake, model, cx) = chatting(None, cx);
    let comment = "safe\u{200b}to\u{2060}run";
    let args = json!({ "address": "0x1000", "comment": comment, "dry_run": false });
    let said = ask_each(&thread, &fake, &model, &[("set_comment", args)], cx);
    let cards = thread.read_with(cx, |t, _| t.proposals().to_vec());
    assert_eq!(cards.len(), 1, "{said:?}");
    let lines: Vec<String> = crate::chat::card_lines(&cards[0])
        .into_iter()
        .map(|(l, _)| l)
        .collect();
    assert!(lines.contains(&"address 0x1000".to_owned()), "{lines:?}");
    let shown = lines.iter().find(|l| l.starts_with("comment: ")).unwrap();
    assert!(!shown.contains(['\u{200b}', '\u{2060}']), "{shown}");
    assert!(shown.contains("safe") && shown.contains("run"), "{shown}");
    assert!(shown.len() > "comment: safetorun".len(), "{shown}");
}

/// Accept commits the plan its card showed, and the card says what the commit did: of
/// two quick Accepts the second still waits while the first runs, and once the first
/// lands the second's plan, made over the names before it, is stale; planned again it
/// commits what its new card says.
#[gpui::test]
fn accept_commits_the_plan_the_card_showed(cx: &mut TestAppContext) {
    let (app, thread, fake, model, cx) = chatting(None, cx);
    let entry = have_proposed(&app, &thread, &fake, &model, &["chat_a", "chat_b"], cx);
    let verdicts = |cx: &mut VisualTestContext| verdicts_of(&thread, cx);
    let named = |cx: &mut VisualTestContext| {
        app.binary.read_with(cx, |b, _| {
            let rows = &b.loaded().unwrap().initial_rows.rows;
            rows.iter()
                .find(|r| r.entry == entry)
                .map(|r| r.name.clone())
        })
    };
    thread.update(cx, |t, cx| {
        t.accept(0, cx);
        t.accept(1, cx);
    });
    assert!(matches!(
        &*verdicts(cx),
        [Verdict::Accepting, Verdict::Accepting]
    ));
    cx.run_until_parked();
    let [first, second] = &*verdicts(cx) else {
        panic!("two proposals");
    };
    assert_eq!(first, &Verdict::Accepted);
    assert_eq!(
        second,
        &Verdict::Waiting,
        "a busy refusal leaves the card waiting"
    );
    assert_eq!(named(cx).as_deref(), Some("chat_a"));
    thread.update(cx, |t, cx| t.accept(1, cx));
    cx.run_until_parked();
    assert_eq!(verdicts(cx)[1], Verdict::Stale);
    assert_eq!(named(cx).as_deref(), Some("chat_a"));
    thread.update(cx, |t, cx| t.plan_again(1, cx));
    cx.run_until_parked();
    assert_eq!(verdicts(cx)[1], Verdict::Waiting);
    let lines = thread.read_with(cx, |t, _| t.proposals()[1].lines.join("\n"));
    assert!(
        lines.contains("chat_a") && lines.contains("chat_b"),
        "{lines}"
    );
    thread.update(cx, |t, cx| t.accept(1, cx));
    cx.run_until_parked();
    assert_eq!(verdicts(cx)[1], Verdict::Accepted);
    assert_eq!(named(cx).as_deref(), Some("chat_b"));
    let changes = app.binary.read_with(cx, |b, _| b.changes().len());
    assert_eq!(changes, 2);
}

/// A proposal card shows the address, the name now and the new name as fields of their
/// own, each written out: a name the binary wrote, padded with zero-width characters to
/// spell a rename of its own, cannot stand in for the name Accept commits. A name that
/// does not show whole is refused; one that mixes Latin with letters that look like it is warned of.
#[gpui::test]
fn the_card_shows_the_name_accept_commits(cx: &mut TestAppContext) {
    let (program, analysis, mut overlay) = crate::code_view::tests::sample_program();
    let caller = crate::app_view::tests::CALLER;
    let hostile = format!("x) to 'IsLicenseValid'{}", "\u{200b}".repeat(230));
    overlay.names = [(caller, hostile)].into_iter().collect();
    let loaded = crate::app_view::tests::loaded_of(program, analysis, overlay);
    let (_app, thread, fake, model, cx) = chatting(Some(loaded), cx);
    thread.update(cx, |t, cx| t.send("Name it".to_owned(), cx));
    cx.run_until_parked();
    let names = ["log_flush", "log\u{3164}flush", "IsLicenseV\u{0430}lid"];
    for (ix, name) in names.iter().enumerate() {
        let args = json!({ "address": format!("{caller:#x}"), "name": name, "dry_run": false });
        fake.send_last_event(&model, call(&ix.to_string(), "set_name", args));
    }
    fake.end_last(&model);
    cx.run_until_parked();
    let said = answers(&fake);
    assert!(said[1].contains("do not show"), "{}", said[1]);
    let cards: Vec<Vec<String>> = thread.read_with(cx, |t, _| {
        t.proposals()
            .iter()
            .map(|p| {
                crate::chat::card_lines(p)
                    .into_iter()
                    .map(|(l, _)| l)
                    .collect()
            })
            .collect()
    });
    assert_eq!(cards.len(), 2, "{cards:?}");
    assert!(
        cards[0].contains(&"becomes: log_flush".to_owned()),
        "{:?}",
        cards[0]
    );
    assert!(
        cards[0].iter().all(|l| !l.contains('\u{200b}')),
        "{:?}",
        cards[0]
    );
    assert!(
        cards[0]
            .iter()
            .any(|l| l.starts_with("now: x) to 'IsLicenseValid'\\u{200b}"))
    );
    assert!(
        cards[1].iter().any(|l| l.starts_with("warning:")),
        "{:?}",
        cards[1]
    );
    assert!(cards[0].iter().all(|l| !l.starts_with("warning:")));
}

/// Every card state has a way out: two proposals of one name to two functions leave the
/// second stale, planned again it is refused, and Reject still clears it, so a later
/// proposal is the one shown and can be accepted.
#[gpui::test]
fn a_refused_card_never_wedges_the_queue(cx: &mut TestAppContext) {
    let (app, thread, fake, model, cx) = chatting(None, cx);
    let rows = first_two(&app, cx);
    thread.update(cx, |t, cx| t.send("Name them".to_owned(), cx));
    cx.run_until_parked();
    for (id, at, name) in [("1", rows.0, "chat_same"), ("2", rows.1, "chat_same")] {
        let args = json!({ "address": format!("{at:#x}"), "name": name, "dry_run": false });
        fake.send_last_event(&model, call(id, "set_name", args));
    }
    fake.end_last(&model);
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.accept(0, cx));
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.accept(1, cx));
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.plan_again(1, cx));
    cx.run_until_parked();
    assert!(
        matches!(verdicts_of(&thread, cx)[1], Verdict::Refused(_)),
        "{:?}",
        verdicts_of(&thread, cx)
    );
    thread.update(cx, |t, cx| t.reject(1, cx));
    assert_eq!(thread.read_with(cx, |t, _| t.head()), None);
    thread.update(cx, |t, cx| t.send("Again".to_owned(), cx));
    cx.run_until_parked();
    let args =
        json!({ "address": format!("{:#x}", rows.1), "name": "chat_other", "dry_run": false });
    fake.send_last_event(&model, call("3", "set_name", args));
    fake.end_last(&model);
    cx.run_until_parked();
    assert_eq!(thread.read_with(cx, |t, _| t.head()), Some(2));
    thread.update(cx, |t, cx| t.accept(2, cx));
    cx.run_until_parked();
    assert_eq!(verdicts_of(&thread, cx)[2], Verdict::Accepted);
}
