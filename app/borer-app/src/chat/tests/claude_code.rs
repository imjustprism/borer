//! The Claude Code turn against a fake child: recorded stream lines fed through the pipes a
//! real `claude` would hold, what the app writes back, and the child's end.

use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};

use futures::TryStreamExt as _;
use futures::channel::mpsc;
use futures::io::{AsyncWrite, BufReader};
use gpui::{Entity, TestAppContext, VisualTestContext};
use serde_json::{Value, json};

use super::super::claude_code::Session;
use super::super::providers::Offered;
use super::super::thread::{Entry, Fault, Ran, Thread, Verdict};
use super::{behind, chatting};

/// What the app wrote to the fake child's input.
type Written = Arc<Mutex<Vec<u8>>>;

/// Where a test writes the fake child's output, one chunk of bytes at a time.
type Out = mpsc::UnboundedSender<std::io::Result<Vec<u8>>>;

/// The fake child's input: keeps what is written.
struct Sink(Written);

impl AsyncWrite for Sink {
    fn poll_write(
        self: Pin<&mut Self>,
        _: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Poll::Ready(Ok(buf.len()))
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Ready(Ok(()))
    }

    fn poll_close(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

/// An input that takes nothing, as a child that stopped reading.
struct Stuck;

impl AsyncWrite for Stuck {
    fn poll_write(
        self: Pin<&mut Self>,
        _: &mut Context<'_>,
        _: &[u8],
    ) -> Poll<std::io::Result<usize>> {
        Poll::Pending
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Pending
    }

    fn poll_close(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        Poll::Pending
    }
}

/// Whether the fake child was dropped, as the real one is killed.
#[derive(Clone, Default)]
struct Flag(Arc<AtomicBool>);

impl Flag {
    /// Returns whether it was raised.
    fn get(&self) -> bool {
        self.0.load(Ordering::SeqCst)
    }
}

/// The fake child itself: raises its flag when dropped, and ends its output then when it
/// holds it.
struct Child {
    /// Raised when it drops.
    flag: Flag,
    /// Its output, held open until it drops; `None` once it has ended.
    _out: Option<Out>,
}

impl Drop for Child {
    fn drop(&mut self) {
        self.flag.0.store(true, Ordering::SeqCst);
    }
}

/// How the fake child's output goes on after its lines.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Then {
    /// It ends, as a child that exits.
    Ends,
    /// It hangs until the child is dropped.
    Hangs,
}

/// Returns `lines`, each ended by a line break, as one chunk of the fake child's output.
fn chunk(lines: &[String]) -> Vec<u8> {
    lines
        .iter()
        .map(|l| format!("{l}\n"))
        .collect::<String>()
        .into_bytes()
}

/// Returns a session over a fake child holding `child`'s flag, writing what the test sends
/// on the returned output, and what the app writes to it.
fn fake_session(flag: &Flag, hangs: bool, cx: &mut VisualTestContext) -> (Session, Out, Written) {
    let (out, output) = mpsc::unbounded();
    let from = BufReader::new(output.into_async_read());
    let written = Written::default();
    let child = Box::new(Child {
        flag: flag.clone(),
        _out: hangs.then(|| out.clone()),
    });
    let executor = cx.executor();
    let session = Session::over(
        from,
        Sink(written.clone()),
        child,
        Some("sonnet"),
        &executor,
    );
    (session, out, written)
}

/// Returns a thread over the sample talking to Claude Code's model `sonnet` through a fake
/// child, what the app writes to it, and whether it was killed.
///
/// The child writes the lines `script` gives for the sample's first function, then goes
/// on as `then`.
fn with_child(
    script: impl FnOnce(u64) -> Vec<String>,
    then: Then,
    cx: &mut TestAppContext,
) -> (Entity<Thread>, Written, Flag, &mut VisualTestContext) {
    let (app, thread, fake, model, cx) = chatting(None, cx);
    let entry = app
        .binary
        .read_with(cx, |b, _| b.loaded().unwrap().initial_rows.rows[0].entry);
    let killed = Flag::default();
    let (session, out, written) = fake_session(&killed, then == Then::Hangs, cx);
    out.unbounded_send(Ok(chunk(&script(entry)))).unwrap();
    drop(out);
    let chosen = behind(&fake, &model, (Offered::ClaudeCode, "claude"), "sonnet");
    thread.update(cx, |t, cx| {
        t.choose(chosen, cx);
        t.agree(cx);
        t.claude = Some(session);
    });
    (thread, written, killed, cx)
}

/// Returns Claude Code's control request `id` carrying an MCP call of `tool` with `args`.
fn tool_call(id: &str, tool: &str, args: &Value) -> String {
    json!({"type":"control_request","request_id":id,"request":{"subtype":"mcp_message","server_name":"borer","message":{"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":tool,"arguments":args}}}}).to_string()
}

/// Returns a reply of the model holding `text`.
fn says(text: &str) -> String {
    json!({"type":"assistant","message":{"role":"assistant","content":[{"type":"text","text":text}]},"parent_tool_use_id":null}).to_string()
}

/// The line Claude Code ends a turn well with.
const DONE: &str = r#"{"type":"result","subtype":"success","is_error":false,"result":"ok"}"#;

/// The line Claude Code starts a session with.
const INIT: &str = r#"{"type":"system","subtype":"init","session_id":"s","mcp_servers":[{"name":"borer","status":"connected"}]}"#;

/// Returns each line the app wrote, as JSON.
fn lines_of(written: &Written) -> Vec<Value> {
    let bytes = written.lock().unwrap();
    std::str::from_utf8(&bytes)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect()
}

/// A turn sends the person's message, answers Claude Code's read call with the thread's own
/// tool, fenced, refuses a permission prompt, streams the reply and keeps the child for the
/// next turn.
#[gpui::test]
fn a_read_call_is_answered_and_the_reply_streams(cx: &mut TestAppContext) {
    let ask = r#"{"type":"control_request","request_id":"p1","request":{"subtype":"can_use_tool","tool_name":"Bash","input":{}}}"#;
    let lines = [
        INIT.to_owned(),
        tool_call("r1", "functions", &json!({})),
        ask.to_owned(),
        says("It has functions."),
        DONE.to_owned(),
    ];
    let (thread, written, killed, cx) = with_child(|_| lines.to_vec(), Then::Ends, cx);
    thread.update(cx, |t, cx| t.send("What is here?".to_owned(), cx));
    cx.run_until_parked();
    let (entries, ran, kept, running) = thread.read_with(cx, |t, _| {
        let ran = (0..t.entries().len())
            .find_map(|ix| t.call_at(ix))
            .map(|c| (c.name.clone(), c.ran.clone()));
        (
            t.entries().to_vec(),
            ran,
            t.claude.is_some(),
            t.is_running(),
        )
    });
    assert!(!running && kept && !killed.get());
    assert_eq!(
        entries.last(),
        Some(&Entry::Model("It has functions.".to_owned()))
    );
    let (name, ran) = ran.unwrap();
    assert_eq!(name, "functions");
    assert!(matches!(ran, Ran::Answered { .. }), "{ran:?}");
    let wrote = lines_of(&written);
    assert_eq!(wrote[0]["type"], "user");
    assert_eq!(wrote[0]["message"]["content"], "What is here?");
    let answer = &wrote[1]["response"];
    assert_eq!(answer["request_id"], "r1");
    let result = &answer["response"]["mcp_response"]["result"];
    assert_eq!(result["isError"], false);
    let text = result["content"][0]["text"].as_str().unwrap();
    assert!(text.starts_with(super::super::thread::FENCE_OPEN), "{text}");
    assert_eq!(wrote[2]["response"]["subtype"], "error");
    assert_eq!(wrote[2]["response"]["request_id"], "p1");
}

/// An edit Claude Code asks to apply only plans: it waits as the app's proposal, nothing
/// is written, and Claude Code is told it was proposed.
#[gpui::test]
fn an_edit_waits_as_a_proposal(cx: &mut TestAppContext) {
    let script = |entry: u64| {
        let applying =
            json!({ "address": format!("{entry:#x}"), "name": "cc_named", "dry_run": false });
        vec![tool_call("r1", "set_name", &applying), DONE.to_owned()]
    };
    let (thread, written, _, cx) = with_child(script, Then::Ends, cx);
    thread.update(cx, |t, cx| t.send("Name the entry".to_owned(), cx));
    cx.run_until_parked();
    let verdicts: Vec<Verdict> = thread.read_with(cx, |t, _| {
        t.proposals().iter().map(|p| p.verdict.clone()).collect()
    });
    assert_eq!(verdicts, [Verdict::Waiting]);
    let wrote = lines_of(&written);
    let result = &wrote[1]["response"]["response"]["mcp_response"]["result"];
    let text = result["content"][0]["text"].as_str().unwrap();
    assert!(text.contains("proposed, not applied"), "{text}");
}

/// Stop kills the child of a turn that hangs, and the next message says Claude Code starts
/// over.
#[gpui::test]
fn stop_kills_the_child(cx: &mut TestAppContext) {
    let (thread, _, killed, cx) = with_child(|_| vec![INIT.to_owned()], Then::Hangs, cx);
    thread.update(cx, |t, cx| t.send("Look".to_owned(), cx));
    cx.run_until_parked();
    assert!(thread.read_with(cx, |t, _| t.is_running()) && !killed.get());
    thread.update(cx, Thread::stop);
    cx.run_until_parked();
    assert!(killed.get());
    assert!(thread.read_with(cx, |t, _| !t.is_running() && t.claude.is_none()));
}

/// Returns the banner and its kind a turn ends with when the fake child writes `lines` and
/// ends, after asserting the child was dropped.
fn banner(lines: Vec<String>, cx: &mut TestAppContext) -> (String, Option<Fault>) {
    let (thread, _, killed, cx) = with_child(|_| lines, Then::Ends, cx);
    thread.update(cx, |t, cx| t.send("Look".to_owned(), cx));
    cx.run_until_parked();
    let (said, fault, kept) = thread.read_with(cx, |t, _| {
        let at = t.entries().len() - 1;
        (t.entries()[at].clone(), t.fault_at(at), t.claude.is_some())
    });
    assert!(killed.get() && !kept);
    let Entry::Error(said) = said else {
        panic!("no banner: {said:?}")
    };
    (said, fault)
}

/// A child that ends mid-turn ends the turn as a provider's error banner.
#[gpui::test]
fn a_crash_is_an_error_banner(cx: &mut TestAppContext) {
    let (said, fault) = banner(vec![INIT.to_owned(), says("half")], cx);
    assert!(said.contains("ended before the turn did"), "{said}");
    assert_eq!(fault, Some(Fault::Provider));
}

/// A line that does not read ends the turn as an error banner, never a panic.
#[gpui::test]
fn garbage_is_an_error_banner(cx: &mut TestAppContext) {
    let (said, fault) = banner(vec!["{not json".to_owned()], cx);
    assert!(said.contains("does not read"), "{said}");
    assert_eq!(fault, Some(Fault::Provider));
}

/// A turn Claude Code reports failed, as one with no sign-in, is a banner with its reason.
#[gpui::test]
fn a_failed_turn_says_why(cx: &mut TestAppContext) {
    let failed = r#"{"type":"result","is_error":true,"result":"Not logged in"}"#;
    let (said, fault) = banner(vec![failed.to_owned()], cx);
    assert!(said.contains("Not logged in"), "{said}");
    assert_eq!(fault, Some(Fault::Provider));
}

/// A line Claude Code writes after its turn's end is dropped when the next turn starts, so
/// a stray `result` cannot end the next turn before its reply.
#[gpui::test]
fn a_stray_line_after_a_turn_is_dropped(cx: &mut TestAppContext) {
    let (_app, thread, fake, model, cx) = chatting(None, cx);
    let killed = Flag::default();
    let (session, out, written) = fake_session(&killed, true, cx);
    let chosen = behind(&fake, &model, (Offered::ClaudeCode, "claude"), "sonnet");
    thread.update(cx, |t, cx| {
        t.choose(chosen, cx);
        t.agree(cx);
        t.claude = Some(session);
    });
    let first = [says("one"), DONE.to_owned(), DONE.to_owned(), says("stray")];
    out.unbounded_send(Ok(chunk(&first))).unwrap();
    thread.update(cx, |t, cx| t.send("First".to_owned(), cx));
    cx.run_until_parked();
    thread.update(cx, |t, cx| t.send("Second".to_owned(), cx));
    cx.run_until_parked();
    out.unbounded_send(Ok(chunk(&[says("two"), DONE.to_owned()])))
        .unwrap();
    cx.run_until_parked();
    let entries = thread.read_with(cx, |t, _| t.entries().to_vec());
    assert_eq!(
        entries.last(),
        Some(&Entry::Model("two".to_owned())),
        "{entries:?}"
    );
    assert!(
        !entries.iter().any(|e| matches!(e, Entry::Error(_))),
        "{entries:?}"
    );
    assert!(!entries.contains(&Entry::Model("stray".to_owned())));
    assert!(!killed.get());
    assert_eq!(lines_of(&written).len(), 2);
}

/// A child that stops reading its input ends the turn after the read wait, as a child that
/// goes silent does, and is killed.
#[gpui::test]
fn a_child_that_stops_reading_ends_the_turn(cx: &mut TestAppContext) {
    let (_app, thread, fake, model, cx) = chatting(None, cx);
    let killed = Flag::default();
    let (out, output) = mpsc::unbounded();
    let child = Box::new(Child {
        flag: killed.clone(),
        _out: Some(out),
    });
    let from = BufReader::new(output.into_async_read());
    let session = Session::over(from, Stuck, child, Some("sonnet"), &cx.executor());
    let chosen = behind(&fake, &model, (Offered::ClaudeCode, "claude"), "sonnet");
    thread.update(cx, |t, cx| {
        t.choose(chosen, cx);
        t.agree(cx);
        t.claude = Some(session);
    });
    thread.update(cx, |t, cx| t.send("Look".to_owned(), cx));
    cx.run_until_parked();
    assert!(thread.read_with(cx, |t, _| t.is_running()));
    cx.executor()
        .advance_clock(super::super::thread::READ_TIMEOUT);
    cx.run_until_parked();
    let last = thread.read_with(cx, |t, _| t.entries().last().cloned());
    let Some(Entry::Error(said)) = last else {
        panic!("no banner: {last:?}")
    };
    assert!(said.contains("no word from Claude Code"), "{said}");
    assert!(killed.get());
}
