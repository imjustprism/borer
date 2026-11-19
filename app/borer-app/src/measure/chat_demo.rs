//! The chat demo, `--chat-demo [binary]`: a canned conversation for screenshots.
//!
//! A scripted model, sending nothing anywhere, answers the chat panel docked over the open
//! binary (default notepad). The demo walks every state the panel draws: the empty thread,
//! the picker open, the agreement notice, a turn running, a tool call opened, each card
//! kind and state, an error, and a long thread. Each state on screen is announced as
//! `CHAT_STAGE <name>` and held a while ([`super::stage::stage`]), so a caller can capture
//! the window; then `CHAT_DONE`, and the app quits.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use futures::channel::oneshot;
use futures::{FutureExt as _, StreamExt as _, future::BoxFuture};
use gpui::{AsyncApp, AsyncWindowContext, Entity, WeakEntity};
use language_model::{
    LanguageModel, LanguageModelClient, LanguageModelCompletionError, LanguageModelCompletionEvent,
    LanguageModelCompletionStream, LanguageModelRequest, LanguageModelToolUse,
    LanguageModelToolUseInput, StopReason,
};
use serde_json::{Value, json};

use super::stage::{poll, stage};
use super::{Harness, say};
use crate::chat::ChatPanel;
use crate::chat::providers::{Endpoint, Offered, listed};
use crate::chat::thread::{Chosen, Entry, Thread, Verdict};

/// The word this demo's stages are said with.
const CHAT: &str = "CHAT";

/// Turns of the long thread, after the cards.
const LONG_TURNS: usize = 10;

/// One canned reply of the scripted model.
enum Reply {
    /// Events streamed at once.
    Now(Vec<LanguageModelCompletionEvent>),
    /// Events streamed, then a wait for the demo's word, then the rest.
    Held(
        Vec<LanguageModelCompletionEvent>,
        oneshot::Receiver<()>,
        Vec<LanguageModelCompletionEvent>,
    ),
    /// A provider error.
    Fails(&'static str),
}

/// A model that answers each request with the next of its canned replies.
struct Scripted {
    /// The replies left, in order; an empty reply ends a turn.
    replies: Mutex<VecDeque<Reply>>,
}

impl LanguageModelClient for Scripted {
    fn stream_completion(
        &self,
        _model: &LanguageModel,
        _request: LanguageModelRequest,
        _cx: &AsyncApp,
    ) -> BoxFuture<'static, Result<LanguageModelCompletionStream, LanguageModelCompletionError>>
    {
        let reply = self.replies.lock().ok().and_then(|mut r| r.pop_front());
        let stream = match reply {
            None => futures::stream::empty().boxed(),
            Some(Reply::Now(events)) => futures::stream::iter(events.into_iter().map(Ok)).boxed(),
            Some(Reply::Held(before, word, after)) => {
                let after = futures::stream::once(word)
                    .flat_map(move |_| futures::stream::iter(after.clone().into_iter().map(Ok)));
                futures::stream::iter(before.into_iter().map(Ok))
                    .chain(after)
                    .boxed()
            }
            Some(Reply::Fails(said)) => {
                let err = LanguageModelCompletionError::Other(anyhow::anyhow!(said));
                return async move { Err(err) }.boxed();
            }
        };
        async move { Ok(stream) }.boxed()
    }
}

/// Returns streamed `text` in a few chunks.
fn chunks(text: &str) -> Vec<LanguageModelCompletionEvent> {
    text.split_inclusive(' ')
        .map(|w| LanguageModelCompletionEvent::Text(w.to_owned()))
        .collect()
}

/// Returns the calls `uses` and the stop that ends a reply.
fn calls(uses: &[(&str, &str, Value)]) -> Vec<LanguageModelCompletionEvent> {
    let mut events: Vec<_> = uses
        .iter()
        .map(|(id, name, args)| {
            LanguageModelCompletionEvent::ToolUse(LanguageModelToolUse {
                id: (*id).into(),
                name: (*name).into(),
                raw_input: args.to_string(),
                input: LanguageModelToolUseInput::Json(args.clone()),
                is_input_complete: true,
                thought_signature: None,
            })
        })
        .collect();
    let stop = if uses.is_empty() {
        StopReason::EndTurn
    } else {
        StopReason::ToolUse
    };
    events.push(LanguageModelCompletionEvent::Stop(stop));
    events
}

/// Returns a reply of streamed `text`, then the calls `uses`.
fn reply(text: &str, uses: &[(&str, &str, Value)]) -> Reply {
    let mut events = chunks(text);
    events.extend(calls(uses));
    Reply::Now(events)
}

impl Harness {
    /// Runs the chat demo once the binary is open.
    ///
    /// # Arguments
    ///
    /// * `window` - The harness's window.
    /// * `cx` - Harness context.
    pub(super) fn chat_demo(&mut self, window: &gpui::Window, cx: &mut gpui::Context<'_, Self>) {
        let exit = self.exit.clone();
        self.task = Some(cx.spawn_in(window, async move |this, cx| {
            if let Err(err) = demo(&this, cx).await {
                *exit.borrow_mut() = Some(err.context("chat demo"));
            }
            cx.update(|_, cx| cx.quit()).unwrap_or(());
        }));
    }
}

/// Waits until `done` holds of the thread, polling.
///
/// # Errors
///
/// When it still does not hold after a minute of polls ([`poll`]).
async fn until(
    thread: &Entity<Thread>,
    cx: &mut AsyncApp,
    done: impl Fn(&Thread) -> bool,
) -> anyhow::Result<()> {
    poll("the chat's settling", cx, |cx| {
        thread.read_with(cx, |t, _| done(t)).then_some(())
    })
    .await
}

/// Sends `text` and waits for the turn to end.
///
/// # Errors
///
/// When the turn never ends.
async fn ask(text: &str, thread: &Entity<Thread>, cx: &mut AsyncApp) -> anyhow::Result<()> {
    thread.update(cx, |t, cx| t.send(text.to_owned(), cx));
    until(thread, cx, |t| !t.is_running()).await
}

/// Returns the scripted model's replies after the first turn, in order: a rename, a batch,
/// a comment and a type, two renames of one name, an error, and the long thread's turns.
///
/// # Arguments
///
/// * `entry` - The entry point's address.
/// * `others` - Three more functions' addresses.
fn canned(entry: &str, others: &[String]) -> Vec<Reply> {
    let mut replies = vec![
        reply(
            "The entry point only sets up the runtime, so I'll propose a plain name for it.",
            &[(
                "3",
                "set_name",
                json!({ "address": entry, "name": "crt_startup", "dry_run": false }),
            )],
        ),
        reply("Nothing changes until you accept it.", &[]),
        reply(
            "Three helpers it calls, named in one batch.",
            &[(
                "4",
                "set_name",
                json!({ "names": [
                    format!("{}=init_heap", others[0]),
                    format!("{}=parse_command_line", others[1]),
                    format!("{}=register_window_class", others[2]),
                ], "dry_run": false }),
            )],
        ),
        reply("Proposed as one card.", &[]),
        reply(
            "A comment on the entry, and a struct for the window state it builds.",
            &[
                (
                    "5",
                    "set_comment",
                    json!({ "address": entry, "comment": "runs once before WinMain; sets up the heap and the command line", "dry_run": false }),
                ),
                (
                    "6",
                    "set_type",
                    json!({ "type": "struct WindowState { void *hwnd; int width; int height; };", "dry_run": false }),
                ),
            ],
        ),
        reply("Both wait for you.", &[]),
        reply(
            "Two candidates for the same name.",
            &[
                (
                    "7",
                    "set_name",
                    json!({ "address": others[0], "name": "main_loop", "dry_run": false }),
                ),
                (
                    "8",
                    "set_name",
                    json!({ "address": others[1], "name": "main_loop", "dry_run": false }),
                ),
            ],
        ),
        reply("Accept the one you believe.", &[]),
        Reply::Fails("overloaded_error: the provider is overloaded, try again shortly"),
    ];
    replies.extend((0..LONG_TURNS).map(|n| {
        reply(
            &format!(
                "Step {n}: `{}` reads its argument through `GetCommandLineW` and splits it on spaces; nothing here touches the network.",
                others[n % others.len()]
            ),
            &[],
        )
    }));
    replies
}

/// Returns the first turn's reply, held after its first words until the demo's word, and
/// its answer once the tools ran: a triage and a decompile, then a reply with code.
///
/// # Arguments
///
/// * `entry` - The entry point's address.
/// * `word` - What releases the held reply.
fn first_turn(entry: &str, word: oneshot::Receiver<()>) -> [Reply; 2] {
    [
        Reply::Held(
            chunks("Let me triage it first, then read the entry point. "),
            word,
            calls(&[
                ("1", "query", json!({ "uri": "borer://triage" })),
                ("2", "decompile", json!({ "address": entry })),
            ]),
        ),
        reply(
            "This is a small GUI program. The entry point sets up the C runtime, reads the command line and hands it to `WinMain`:\n```c\nint crt_startup(void) {\n    init_heap();\n    return WinMain(GetModuleHandleW(NULL), NULL, GetCommandLineW(), SW_SHOWDEFAULT);\n}\n```\nNothing in the triage points at packing or anti-analysis.",
            &[],
        ),
    ]
}

/// Accepts the first of the two newest cards, then the second, which goes stale, and plans
/// it again, which the engine refuses: the name is taken now. Says the stale and the refused
/// stage on the way.
///
/// # Errors
///
/// When a verdict never comes.
async fn refuse_second(thread: &Entity<Thread>, cx: &mut AsyncApp) -> anyhow::Result<()> {
    let ids: Vec<usize> = thread.read_with(cx, |t, _| t.proposals().iter().map(|p| p.id).collect());
    let (first, second) = (ids[ids.len() - 2], ids[ids.len() - 1]);
    let has = |id: usize, want: fn(&Verdict) -> bool| {
        move |t: &Thread| t.proposal(id).is_some_and(|p| want(&p.verdict))
    };
    thread.update(cx, |t, cx| t.accept(first, cx));
    until(thread, cx, has(first, |v| *v == Verdict::Accepted)).await?;
    thread.update(cx, |t, cx| t.accept(second, cx));
    until(thread, cx, has(second, |v| *v == Verdict::Stale)).await?;
    stage(CHAT, "stale", cx).await?;
    thread.update(cx, |t, cx| t.plan_again(second, cx));
    until(
        thread,
        cx,
        has(second, |v| matches!(v, Verdict::Refused(_))),
    )
    .await?;
    stage(CHAT, "refused", cx).await
}

/// Waits for the binary and returns its entry and three more functions' addresses.
///
/// # Errors
///
/// When the window is gone, nothing opens, or it has fewer than four functions.
async fn addresses(
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<(String, Vec<String>)> {
    let found = poll("the binary", cx, |cx| {
        this.update(cx, |h, cx| {
            let loaded = h.binary.read(cx).loaded()?;
            let rows = &loaded.initial_rows.rows;
            let entry = loaded.program.entry.or(rows.first().map(|r| r.entry))?;
            let others: Vec<String> = rows
                .iter()
                .skip(1)
                .take(3)
                .map(|r| format!("{:#x}", r.entry))
                .collect();
            Some((format!("{entry:#x}"), others))
        })
        .ok()
        .flatten()
    })
    .await;
    let (entry, others) = found?;
    anyhow::ensure!(others.len() == 3, "fewer than four functions");
    Ok((entry, others))
}

/// Shows the empty thread, then the picker open over a listed scripted model, which it
/// picks; returns that model.
///
/// # Errors
///
/// When the window is gone or stdout fails.
async fn pick(
    panel: &Entity<ChatPanel>,
    replies: Vec<Reply>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    stage(CHAT, "empty", cx).await?;
    let scripted = Arc::new(Scripted {
        replies: Mutex::new(replies.into_iter().collect()),
    });
    panel.update_in(cx, |panel, window, cx| {
        let endpoint = Endpoint::of(Offered::Anthropic, cx);
        let model = |id: &str, name: &str| Chosen {
            client: scripted.clone(),
            model: listed(&endpoint, id, name.to_owned(), 200_000),
            endpoint: endpoint.clone(),
        };
        let models = vec![
            model("claude-demo", "Claude (scripted demo)"),
            model("claude-demo-small", "Claude small (scripted demo)"),
        ];
        let chosen = models[0].clone();
        panel.offer_listed(Offered::Anthropic, models, window, cx);
        panel.thread().update(cx, |t, cx| t.choose(chosen, cx));
        panel.picker().show(window, cx);
    })?;
    stage(CHAT, "picker", cx).await?;
    panel.update(cx, |panel, cx| panel.picker().hide(cx));
    Ok(())
}

/// Plays the first turn: the agreement, the turn running, its end, and its decompile call
/// opened.
///
/// # Errors
///
/// When the window is gone, the turn never ends, or stdout fails.
async fn first(
    panel: &Entity<ChatPanel>,
    word: oneshot::Sender<()>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    let thread = panel.read_with(cx, |p, _| p.thread().clone());
    thread.update(cx, |t, cx| {
        t.send("What does this binary do?".to_owned(), cx);
    });
    stage(CHAT, "agreement", cx).await?;
    thread.update(cx, Thread::agree);
    until(&thread, cx, |t| t.entries().len() > 1).await?;
    stage(CHAT, "running", cx).await?;
    word.send(())
        .map_err(|()| anyhow::anyhow!("the turn was gone"))?;
    until(&thread, cx, |t| !t.is_running()).await?;
    stage(CHAT, "turn", cx).await?;
    panel.update(cx, |panel, cx| {
        let ix = panel
            .thread()
            .read(cx)
            .entries()
            .iter()
            .enumerate()
            .find_map(|(ix, e)| {
                let call = panel.thread().read(cx).call_at(ix)?;
                (matches!(e, Entry::Tool(_)) && call.name == "decompile").then_some(ix)
            });
        if let Some(ix) = ix {
            panel.toggle_call(ix, cx);
        }
    });
    stage(CHAT, "tool_open", cx).await
}

/// Plays the cards: a rename waiting and focused, a batch under the accepted rename, a
/// comment with a type queued behind it, a stale and a refused rename, then an error and a
/// long thread.
///
/// # Errors
///
/// When the window is gone, a turn or a verdict never comes, or stdout fails.
async fn cards(panel: &Entity<ChatPanel>, cx: &mut AsyncWindowContext) -> anyhow::Result<()> {
    let thread = panel.read_with(cx, |p, _| p.thread().clone());
    let decide = |thread: &Entity<Thread>, accept: bool, cx: &mut AsyncWindowContext| {
        thread.update(cx, |t, cx| {
            while let Some(id) = t.head() {
                if accept {
                    t.accept(id, cx);
                    break;
                }
                t.reject(id, cx);
            }
        });
    };
    ask("Name the entry point.", &thread, cx).await?;
    panel.update_in(cx, |panel, window, cx| panel.show_head(window, cx))?;
    stage(CHAT, "set_name", cx).await?;
    decide(&thread, true, cx);
    until(&thread, cx, |t| t.head().is_none()).await?;
    ask("Name the helpers it calls.", &thread, cx).await?;
    stage(CHAT, "batch", cx).await?;
    decide(&thread, false, cx);
    ask("Document the entry and its window state.", &thread, cx).await?;
    stage(CHAT, "comment_type", cx).await?;
    decide(&thread, false, cx);
    ask("Which one is the main loop?", &thread, cx).await?;
    refuse_second(&thread, cx).await?;
    decide(&thread, false, cx);
    ask("What else does it call?", &thread, cx).await?;
    stage(CHAT, "error", cx).await?;
    for n in 0..LONG_TURNS {
        ask(&format!("And step {n}?"), &thread, cx).await?;
    }
    stage(CHAT, "long", cx).await
}

/// Plays the canned conversation stage by stage.
///
/// # Errors
///
/// When the window is gone, the binary never opens, a turn never ends, or stdout fails.
async fn demo(this: &WeakEntity<Harness>, cx: &mut AsyncWindowContext) -> anyhow::Result<()> {
    let (entry, others) = addresses(this, cx).await?;
    let panel = this.update_in(cx, |h, window, cx| {
        h.workspace
            .update(cx, |w, cx| w.focus_panel::<ChatPanel>(window, cx))
    })?;
    let panel = panel.ok_or_else(|| anyhow::anyhow!("no chat panel"))?;
    let (word, held) = oneshot::channel();
    let mut replies: Vec<Reply> = first_turn(&entry, held).into();
    replies.extend(canned(&entry, &others));
    pick(&panel, replies, cx).await?;
    first(&panel, word, cx).await?;
    cards(&panel, cx).await?;
    say("CHAT_DONE")
}
