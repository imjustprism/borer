//! The Claude Code demo, `--claude-code-demo [binary]`: one short real turn through the
//! Claude Code installed on this machine, for an end-to-end check and its screenshots.
//!
//! It picks Claude Code in the chat docked over the open binary (default notepad), waits
//! for its models, shows the picker (`CHAT_STAGE picker`), agrees to send, sends [`ASKED`],
//! and once the turn ends shows it (`CHAT_STAGE turn`), then says `CHAT_DONE`. Unlike every
//! other demo it sends a message off the machine, through Claude Code's own sign-in.

use gpui::{AsyncWindowContext, WeakEntity};

use super::chat_demo::{addresses, docked, until};
use super::stage::{poll, stage};
use super::{Harness, say};
use crate::chat::providers::Offered;
use crate::chat::thread::Thread;

/// The word this demo's stages are said with.
const CHAT: &str = "CHAT";

/// What the demo asks: one read of the binary and a reply of a few words.
const ASKED: &str = "Read borer://triage with the query tool once, then answer in at most eight words: what is this binary?";

/// Plays the turn stage by stage.
///
/// # Errors
///
/// When the window is gone, the binary never opens, Claude Code is not on `PATH`, lists no
/// model, or its turn never ends, or stdout fails.
pub(super) async fn demo(
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    addresses(this, cx).await?;
    let panel = docked(this, cx)?;
    poll("a claude program on PATH", cx, |_| {
        Offered::on_offer()
            .contains(&Offered::ClaudeCode)
            .then_some(())
    })
    .await?;
    panel.update(cx, |panel, cx| panel.pick(Offered::ClaudeCode, cx));
    let first = poll("Claude Code's models", cx, |cx| {
        panel.read_with(cx, |panel, _| match panel.listed() {
            Ok(models) => models.first().map(|m| Ok(m.model.id.0.to_string())),
            Err(why) => Some(Err(anyhow::anyhow!("{why}"))),
        })
    })
    .await??;
    panel.update_in(cx, |panel, window, cx| {
        panel.choose_model(&first, cx);
        panel.picker().show(window, cx);
    })?;
    stage(CHAT, "picker", cx).await?;
    panel.update(cx, |panel, cx| panel.picker().hide(cx));
    let thread = panel.read_with(cx, |p, _| p.thread().clone());
    thread.update(cx, |t, cx| t.send(ASKED.to_owned(), cx));
    thread.update(cx, Thread::agree);
    until(&thread, cx, |t| t.entries().len() > 2 && !t.is_running()).await?;
    for entry in thread.read_with(cx, |t, _| t.entries().to_vec()) {
        eprintln!("CHAT_ENTRY {entry:?}");
    }
    stage(CHAT, "turn", cx).await?;
    say("CHAT_DONE")
}
