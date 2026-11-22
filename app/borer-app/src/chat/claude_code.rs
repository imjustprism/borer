//! The chat's turns run through the Claude Code installed on this machine: its `claude`
//! program in its stream-JSON mode ([`borer_front::claude_code`]), with its own sign-in.
//!
//! borer never reads Claude Code's settings, credentials or tokens: the app finds `claude`
//! on `PATH` by its file name alone ([`program`]), starts it, and speaks its protocol over
//! the child's standard input and output. Claude Code runs the agent loop and talks to its
//! own service; borer's tools reach it as an MCP server the app serves in-process over the
//! same pipes, answering each call with the thread's own tools ([`super::thread::answer_call`]),
//! so an edit only plans and waits as the app's proposal, its reads see the person's
//! names, and its answers are fenced and cut as they are for any provider. No built-in tool
//! of Claude Code is offered and every permission prompt is denied ([`args`]).
//!
//! One child serves a thread across its turns, so Claude Code keeps the conversation
//! without saving it to disk (`--no-session-persistence`); Stop, a new thread, another
//! binary or another model drops it, which kills it, and the next message starts a new
//! Claude Code conversation that the thread says does not see the earlier turns. A child
//! that ends, writes a line that does not read or goes silent ends the turn as an error.
//! Its standard error is discarded; nothing of it reaches the app's standard output.

use std::any::Any;
use std::path::{Path, PathBuf};
use std::sync::{Arc, LazyLock};

use anyhow::Context as _;
use borer_engine::text::one_line;
use borer_front::claude_code::{
    Event, LINE_MAX, Mcp, TURN_MAX_BYTES, answered, args, initialize, mcp, read, refuse, respond,
    user,
};
use futures::future::BoxFuture;
use futures::io::{AsyncBufRead, AsyncBufReadExt as _, AsyncReadExt as _, AsyncWrite};
use futures::{AsyncWriteExt as _, FutureExt as _};
use gpui::{AsyncApp, WeakEntity};
use language_model::{
    LanguageModel, LanguageModelClient, LanguageModelCompletionError,
    LanguageModelCompletionStream, LanguageModelRequest, LanguageModelToolUse,
    LanguageModelToolUseInput,
};
use serde_json::{Value, json};

use super::providers::{Endpoint, listed};
use super::thread::{
    Chosen, Entry, Fault, SYSTEM, Spend, Thread, answer_call, fenced, step, within,
};

/// Who the turn waits on, as a silence or a failure names it.
const WHO: &str = "Claude Code";

/// The id the app's `initialize` request goes under.
const LISTING: &str = "borer-models";

/// The context window the picker records for a Claude Code model, which manages its own.
const WINDOW: u64 = 200_000;

/// Returns the `claude` program on `PATH`, looked up once by file name alone: the native
/// installer's `claude.exe` on Windows, `claude` elsewhere. A `claude.cmd` alone is not
/// found, so no Claude Code row is offered for it. Nothing of Claude Code's is read to find
/// it.
pub(crate) fn program() -> Option<&'static Path> {
    static FOUND: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
        let name = if cfg!(windows) {
            "claude.exe"
        } else {
            "claude"
        };
        std::env::split_paths(&std::env::var_os("PATH")?)
            .map(|dir| dir.join(name))
            .find(|path| {
                borer_engine::program::checked_metadata(path)
                    .ok()
                    .flatten()
                    .is_some_and(|meta| meta.is_file())
            })
    });
    FOUND.as_deref()
}

/// A running Claude Code and the pipes the app speaks to it over.
pub(crate) struct Session {
    /// Its standard input.
    to: Box<dyn AsyncWrite + Unpin>,
    /// Its standard output.
    from: Box<dyn AsyncBufRead + Unpin>,
    /// What `--model` it was started with, `None` for its own choice.
    model: Option<String>,
    /// The child, killed when dropped.
    _child: Box<dyn Any>,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session")
            .field("model", &self.model)
            .finish_non_exhaustive()
    }
}

impl Session {
    /// Starts `program` with the chat's flags ([`args`]) in the system's temporary folder.
    ///
    /// # Errors
    ///
    /// Returns that it did not start, or gave no pipe.
    fn start(program: &str, model: Option<&str>) -> anyhow::Result<Self> {
        let mut child = util::command::new_command(program)
            .args(args(model, &SYSTEM))
            .current_dir(std::env::temp_dir())
            .stdin(util::command::Stdio::piped())
            .stdout(util::command::Stdio::piped())
            .stderr(util::command::Stdio::null())
            .kill_on_drop(true)
            .spawn()
            .with_context(|| format!("Claude Code did not start from {}", one_line(program)))?;
        let to = child
            .stdin
            .take()
            .context("Claude Code gave no input pipe")?;
        let from = child
            .stdout
            .take()
            .context("Claude Code gave no output pipe")?;
        Ok(Self::over(
            futures::io::BufReader::new(from),
            to,
            Box::new(child),
            model,
        ))
    }

    /// Returns a session over the pipes `from` and `to`; dropping it drops `child`.
    pub(crate) fn over(
        from: impl AsyncBufRead + Unpin + 'static,
        to: impl AsyncWrite + Unpin + 'static,
        child: Box<dyn Any>,
        model: Option<&str>,
    ) -> Self {
        Self {
            to: Box::new(to),
            from: Box::new(from),
            model: model.map(str::to_owned),
            _child: child,
        }
    }

    /// Writes `line` and flushes it.
    ///
    /// # Errors
    ///
    /// Returns that Claude Code no longer reads.
    async fn write(&mut self, line: &str) -> anyhow::Result<()> {
        let wrote = self.to.write_all(line.as_bytes()).await;
        wrote
            .and(self.to.flush().await)
            .context("Claude Code stopped reading; it may have ended")
    }

    /// Reads the next line, at most [`LINE_MAX`] bytes and the `left` bytes the turn has.
    ///
    /// # Errors
    ///
    /// Returns that Claude Code ended, wrote too much, or wrote what is not UTF-8.
    async fn line(&mut self, left: &mut usize) -> anyhow::Result<String> {
        let cap = LINE_MAX.min(*left);
        let mut line = Vec::new();
        (&mut self.from)
            .take(u64::try_from(cap.saturating_add(1)).unwrap_or(u64::MAX))
            .read_until(b'\n', &mut line)
            .await?;
        anyhow::ensure!(
            !line.is_empty(),
            "Claude Code ended before the turn did; the next message starts a new Claude Code conversation"
        );
        anyhow::ensure!(
            line.len() <= cap,
            "Claude Code wrote more than {cap} bytes in a line or {TURN_MAX_BYTES} in a turn; the turn ended"
        );
        *left = left.saturating_sub(line.len());
        let line = String::from_utf8(line).context("Claude Code wrote a line that is not UTF-8")?;
        Ok(line.trim_end().to_owned())
    }

    /// Reads the next line Claude Code writes and what it means, within [`within`]'s wait.
    ///
    /// # Errors
    ///
    /// Returns that it went silent, ended, or wrote a line that does not read.
    async fn next(&mut self, left: &mut usize, cx: &AsyncApp) -> anyhow::Result<Event> {
        let line = within(cx, WHO, self.line(left)).await??;
        read(&line).map_err(anyhow::Error::msg)
    }
}

/// Starts Claude Code at `endpoint` and returns the models it offers, each ready to run a
/// turn; it is killed once it has answered. Nothing is sent to a model.
///
/// # Errors
///
/// Returns that it did not start, went silent, refused, or listed nothing.
pub(crate) async fn models(endpoint: Endpoint, cx: &AsyncApp) -> anyhow::Result<Vec<Chosen>> {
    let mut session = Session::start(&endpoint.url, None)?;
    session.write(&initialize(LISTING)).await?;
    let mut left = TURN_MAX_BYTES;
    let models = loop {
        match session.next(&mut left, cx).await? {
            Event::Answered {
                request,
                models,
                error,
            } if request == LISTING => match error {
                Some(why) => anyhow::bail!("Claude Code refused to start: {}", one_line(&why)),
                None => break models,
            },
            Event::Mcp { request, message } => {
                let reply = match mcp(&message) {
                    Mcp::Reply(reply) => reply,
                    Mcp::Call { id, .. } => answered(&id, "no turn runs", true),
                };
                session
                    .write(&respond(&request, &json!({ "mcp_response": reply })))
                    .await?;
            }
            Event::Ask { request } => session.write(&refuse(&request, REFUSED)).await?,
            Event::Done(Err(why)) => anyhow::bail!("Claude Code: {}", one_line(&why)),
            Event::Text(_) | Event::Answered { .. } | Event::Done(Ok(())) | Event::Other => {}
        }
    };
    anyhow::ensure!(!models.is_empty(), "Claude Code listed no model");
    let client: Arc<dyn LanguageModelClient> = Arc::new(Itself);
    Ok(models
        .into_iter()
        .map(|m| {
            let name = if m.display_name.is_empty() {
                m.value.clone()
            } else {
                m.display_name
            };
            Chosen {
                client: client.clone(),
                model: listed(&endpoint, &m.value, name, WINDOW),
                endpoint: endpoint.clone(),
            }
        })
        .collect())
}

/// What Claude Code is told of a request the app does not serve.
const REFUSED: &str = "borer-app answers only its own MCP server's messages";

/// Runs the thread's turn through Claude Code until its turn ends.
///
/// It sends the person's newest message to the thread's Claude Code, started with
/// `chosen`'s model when none runs with it, and serves its tool calls.
///
/// Its reply's text streams into the thread; each tool call runs through the thread's own
/// tools within the turn's budgets ([`answer_call`]), a spent budget ending the turn and the
/// child. The child returns to the thread for the next turn only when its turn ends well.
///
/// # Errors
///
/// Returns that Claude Code did not start, ended, went silent, wrote a line that does not
/// read or reported a failure, or that the thread closed or stopped the turn.
pub(crate) async fn run_turn(
    this: &WeakEntity<Thread>,
    chosen: &Chosen,
    generation: u64,
    cx: &mut AsyncApp,
) -> anyhow::Result<()> {
    let model = Some(chosen.model.id.0.as_ref());
    let (kept, said, earlier) = step(this, generation, cx, |thread, _| {
        let said = thread.entries().iter().rev().find_map(|e| {
            if let Entry::Person(text) = e {
                Some(text.clone())
            } else {
                None
            }
        });
        let earlier = thread
            .entries()
            .iter()
            .filter(|e| matches!(e, Entry::Person(_)))
            .count()
            > 1;
        (thread.claude.take(), said, earlier)
    })?;
    let mut session = match kept.filter(|s| s.model.as_deref() == model) {
        Some(session) => session,
        None => {
            if earlier {
                step(this, generation, cx, |thread, cx| {
                    let said = "a new Claude Code conversation: it does not see the earlier turns";
                    thread.note(said.to_owned(), cx);
                })?;
            }
            Session::start(&chosen.endpoint.url, model)?
        }
    };
    session.write(&user(&said.unwrap_or_default())).await?;
    let mut spend = step(this, generation, cx, |thread, _| {
        Spend::new(thread.budget())
    })?;
    let mut left = TURN_MAX_BYTES;
    loop {
        match session.next(&mut left, cx).await? {
            Event::Text(text) => step(this, generation, cx, |t, cx| t.stream_text(&text, cx))?,
            Event::Mcp { request, message } => {
                let reply = match mcp(&message) {
                    Mcp::Reply(reply) => reply,
                    Mcp::Call { id, name, args } => {
                        let call = tool_use(&id, name, args);
                        let (failed, text) =
                            answer_call(this, generation, &call, chosen, &mut spend, cx).await?;
                        answered(&id, &fenced(&text), failed)
                    }
                };
                session
                    .write(&respond(&request, &json!({ "mcp_response": reply })))
                    .await?;
                if let Some(why) = spend.spent() {
                    return step(this, generation, cx, |thread, cx| {
                        thread.fail(Fault::Spent, format!("the turn ended: {why}"));
                        cx.notify();
                    });
                }
            }
            Event::Ask { request } => session.write(&refuse(&request, REFUSED)).await?,
            Event::Done(Ok(())) => break,
            Event::Done(Err(why)) => anyhow::bail!("Claude Code: {}", one_line(&why)),
            Event::Answered { .. } | Event::Other => {}
        }
    }
    step(this, generation, cx, |thread, _| {
        thread.claude = Some(session);
    })
}

/// Returns Claude Code's call of the tool `name` with `args`, under the JSON-RPC `id`, as the
/// thread's tools take a model's call.
fn tool_use(id: &Value, name: String, args: Value) -> LanguageModelToolUse {
    LanguageModelToolUse {
        id: id.to_string().into(),
        name: name.into(),
        raw_input: args.to_string(),
        input: LanguageModelToolUseInput::Json(args),
        is_input_complete: true,
        thought_signature: None,
    }
}

/// The client a Claude Code model's [`Chosen`] holds: Claude Code runs its turns itself
/// ([`run_turn`]), so a request sent through it is refused.
struct Itself;

impl LanguageModelClient for Itself {
    fn stream_completion(
        &self,
        _model: &LanguageModel,
        _request: LanguageModelRequest,
        _cx: &AsyncApp,
    ) -> BoxFuture<'static, Result<LanguageModelCompletionStream, LanguageModelCompletionError>>
    {
        let why = anyhow::anyhow!("Claude Code runs its turns itself; nothing was sent");
        futures::future::ready(Err(why.into())).boxed()
    }
}
