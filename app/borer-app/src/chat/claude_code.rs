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
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::Context as _;
use borer_engine::text::one_line;
use borer_front::claude_code::{
    ANSWERS_MAX, Event, LINE_MAX, Mcp, TESTED, TURN_MAX_BYTES, answered, args, initialize, mcp,
    read, refuse, respond, user,
};
use futures::channel::mpsc;
use futures::io::{AsyncBufRead, AsyncBufReadExt as _, AsyncRead, AsyncReadExt as _, AsyncWrite};
use futures::{AsyncWriteExt as _, SinkExt as _, StreamExt as _};
use gpui::{AsyncApp, BackgroundExecutor, Task, WeakEntity};
use language_model::{LanguageModelToolUse, LanguageModelToolUseInput};
use serde_json::{Value, json};

use super::providers::{Endpoint, KEPT_FROM_CLAUDE_CODE, listed};
use super::thread::{
    Chosen, Entry, Fault, Runs, SYSTEM, Spend, Thread, answer_call, fenced, step, within,
};

/// Who the turn waits on, as a silence or a failure names it.
const WHO: &str = "Claude Code";

/// The id the app's `initialize` request goes under.
const LISTING: &str = "borer-models";

/// The context window the picker records for a Claude Code model, which manages its own.
const WINDOW: u64 = 200_000;

/// The file name looked for on `PATH`: the native installer's `claude.exe` on Windows (a
/// `claude.cmd` alone is not found, so no Claude Code row is offered for it), `claude`
/// elsewhere.
const NAME: &str = if cfg!(windows) {
    "claude.exe"
} else {
    "claude"
};

/// What [`probe`] found, once it ran.
static FOUND: OnceLock<Option<PathBuf>> = OnceLock::new();

/// Returns the absolute path of the `claude` program [`probe`] found on `PATH`; `None` before
/// it ran or when it found none. Nothing of Claude Code's is read to find it.
pub(crate) fn program() -> Option<&'static Path> {
    FOUND.get()?.as_deref()
}

/// Looks for the `claude` program on `PATH` once, by file name alone ([`find`]).
///
/// It first removes the working folders earlier sessions left ([`sweep`]); later calls do
/// nothing. It touches the disk, so it runs off the UI thread.
pub(crate) fn probe() {
    FOUND.get_or_init(|| {
        sweep(&folders());
        find(&std::env::var_os("PATH")?, NAME)
    });
}

/// Returns the folder under the app's data folder that holds each session's working folder.
fn folders() -> PathBuf {
    paths::data_dir().join("claude-code")
}

/// Removes every folder in `root`, as sessions leave them when their child had not yet
/// exited as they dropped; one still in use stays.
fn sweep(root: &Path) {
    if borer_engine::program::unusable_path(root).is_some() {
        return;
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "the app's own folder, past unusable_path"
    )]
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        std::fs::remove_dir_all(entry.path()).unwrap_or(());
    }
}

/// A session's own working folder, made empty for it and removed when it drops, so no
/// `CLAUDE.md` or `.claude` folder of a shared place reaches Claude Code.
#[derive(Debug)]
struct Folder(PathBuf);

impl Folder {
    /// Makes a new empty folder in `root`, named by this process and a count.
    ///
    /// # Errors
    ///
    /// Returns that the folder could not be made.
    fn new(root: &Path) -> anyhow::Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir = root.join(format!("{}-{n}", std::process::id()));
        std::fs::create_dir_all(root)
            .and_then(|()| std::fs::create_dir(&dir))
            .with_context(|| format!("no working folder for Claude Code at {}", dir.display()))?;
        Ok(Self(dir))
    }
}

impl Drop for Folder {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap_or(());
    }
}

/// Returns the first file named `name` in the absolute folders of the `PATH` value `path`.
///
/// Relative and empty entries are skipped, so the working folder never supplies the
/// program, and the path returned is the one spawned, never looked up again.
fn find(path: &std::ffi::OsStr, name: &str) -> Option<PathBuf> {
    std::env::split_paths(path)
        .filter(|dir| dir.is_absolute())
        .map(|dir| dir.join(name))
        .find(|file| {
            borer_engine::program::checked_metadata(file)
                .ok()
                .flatten()
                .is_some_and(|meta| meta.is_file())
        })
}

/// One line as the reader heard it ([`hear`]): its length in bytes and what it means, or
/// why reading stopped.
type Heard = (usize, anyhow::Result<Event>);

/// Most lines the reader holds read ahead of the turn.
const AHEAD: usize = 8;

/// A running Claude Code, the pipe the app writes to it over, and the lines its reader
/// heard.
pub(crate) struct Session {
    /// Its standard input.
    to: Box<dyn AsyncWrite + Unpin + Send>,
    /// What the reader heard of its standard output, in order.
    lines: mpsc::Receiver<Heard>,
    /// What `--model` it was started with, `None` for its own choice.
    model: Option<String>,
    /// Reads and parses its standard output on the background executor; dropped, it stops.
    _reader: Task<()>,
    /// The child, killed when dropped.
    _child: Box<dyn Any + Send>,
    /// Its working folder, removed after the child is dropped; `None` for a fake child.
    _folder: Option<Folder>,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session")
            .field("model", &self.model)
            .finish_non_exhaustive()
    }
}

impl Session {
    /// Starts the `claude` program [`probe`] found with the chat's flags ([`args`]) in a
    /// new working folder of its own ([`Folder`]), off the UI thread.
    ///
    /// # Errors
    ///
    /// Returns that no `claude` was found, or that it did not start or gave no pipe.
    async fn start(model: Option<String>, cx: &AsyncApp) -> anyhow::Result<Self> {
        let executor = cx.background_executor();
        let spawning = executor.clone();
        executor
            .spawn(async move { Self::spawn(model.as_deref(), &spawning) })
            .await
    }

    /// Spawns the child [`Self::start`] starts; it creates a process and a folder, so it is
    /// called on the background executor.
    ///
    /// # Errors
    ///
    /// Returns that no `claude` was found, or that it did not start or gave no pipe.
    fn spawn(model: Option<&str>, executor: &BackgroundExecutor) -> anyhow::Result<Self> {
        let program = program().with_context(|| format!("no {NAME} was found on PATH"))?;
        let folder = Folder::new(&folders())?;
        let mut command = util::command::new_command(program);
        command.args(args(model, &SYSTEM)).current_dir(&folder.0);
        for var in KEPT_FROM_CLAUDE_CODE {
            command.env_remove(var);
        }
        let mut child = command
            .stdin(util::command::Stdio::piped())
            .stdout(util::command::Stdio::piped())
            .stderr(util::command::Stdio::piped())
            .kill_on_drop(true)
            .spawn()
            .with_context(|| {
                let at = one_line(&program.display().to_string());
                format!("Claude Code did not start from {at}")
            })?;
        let to = child
            .stdin
            .take()
            .context("Claude Code gave no input pipe")?;
        let from = child
            .stdout
            .take()
            .context("Claude Code gave no output pipe")?;
        let err = child
            .stderr
            .take()
            .context("Claude Code gave no error pipe")?;
        let said = executor.spawn(tail(err));
        let from = futures::io::BufReader::new(from);
        Ok(Self {
            _folder: Some(folder),
            ..Self::with(from, to, Box::new(child), model, executor, said)
        })
    }

    /// Returns a session over the pipes `from` and `to`, whose reader runs on `executor`;
    /// dropping it drops `child`. The child says nothing on its error pipe.
    #[cfg(test)]
    pub(crate) fn over(
        from: impl AsyncBufRead + Unpin + Send + 'static,
        to: impl AsyncWrite + Unpin + Send + 'static,
        child: Box<dyn Any + Send>,
        model: Option<&str>,
        executor: &BackgroundExecutor,
    ) -> Self {
        let said = futures::future::ready(String::new());
        Self::with(from, to, child, model, executor, said)
    }

    /// Returns a session as `Session::over` does, whose child's error pipe ends with `said`,
    /// told when its output ends.
    fn with(
        from: impl AsyncBufRead + Unpin + Send + 'static,
        to: impl AsyncWrite + Unpin + Send + 'static,
        child: Box<dyn Any + Send>,
        model: Option<&str>,
        executor: &BackgroundExecutor,
        said: impl Future<Output = String> + Send + 'static,
    ) -> Self {
        let (heard, lines) = mpsc::channel(AHEAD);
        Self {
            to: Box::new(to),
            lines,
            model: model.map(str::to_owned),
            _reader: executor.spawn(hear(from, heard, said)),
            _child: child,
            _folder: None,
        }
    }

    /// Returns the session with every line it wrote before this turn dropped, so a line it
    /// wrote after its last turn's end never counts in the next; `None` when it ended since.
    fn drained(mut self) -> Option<Self> {
        loop {
            match self.lines.try_recv() {
                Ok((_, Ok(_))) => {}
                Ok((_, Err(_))) | Err(mpsc::TryRecvError::Closed) => return None,
                Err(mpsc::TryRecvError::Empty) => return Some(self),
            }
        }
    }

    /// Writes `line` and flushes it, within [`within`]'s wait.
    ///
    /// # Errors
    ///
    /// Returns that Claude Code no longer reads, or took nothing in that time.
    async fn write(&mut self, line: &str, cx: &AsyncApp) -> anyhow::Result<()> {
        let to = &mut self.to;
        let wrote = within(cx, WHO, async move {
            let wrote = to.write_all(line.as_bytes()).await;
            wrote.and(to.flush().await)
        });
        wrote
            .await?
            .context("Claude Code stopped reading; it may have ended")
    }

    /// Returns what the next line Claude Code wrote means, within [`within`]'s wait, taking
    /// its bytes from the `left` the turn has.
    ///
    /// # Errors
    ///
    /// Returns that it went silent or ended, that the turn read more than
    /// [`TURN_MAX_BYTES`], or why the line did not read ([`hear`]).
    async fn next(&mut self, left: &mut usize, cx: &AsyncApp) -> anyhow::Result<Event> {
        let (len, heard) = within(cx, WHO, self.lines.next()).await?.context(ENDED)?;
        *left = left.checked_sub(len).with_context(|| {
            format!("Claude Code wrote more than {TURN_MAX_BYTES} bytes in a turn; the turn ended")
        })?;
        heard
    }
}

/// What the person is told when Claude Code ends before its turn does.
const ENDED: &str =
    "Claude Code ended before the turn did; the next message starts a new Claude Code conversation";

/// Most bytes kept of what Claude Code writes to its error pipe: the last ones.
const TAIL: usize = 1024;

/// Returns the last [`TAIL`] bytes Claude Code wrote to its error pipe `err`, read until it
/// ends, so the pipe never fills and nothing of it reaches the app's own output.
async fn tail(mut err: impl AsyncRead + Unpin) -> String {
    let (mut kept, mut buf) = (Vec::new(), [0u8; 4096]);
    while let Ok(n @ 1..) = err.read(&mut buf).await {
        kept.extend_from_slice(buf.get(..n).unwrap_or_default());
        kept.drain(..kept.len().saturating_sub(TAIL));
    }
    String::from_utf8_lossy(&kept).into_owned()
}

/// Returns why the turn ended when Claude Code's output ended, from what it said last on its
/// error pipe: an older Claude Code that refuses a flag is named as such.
fn ended(said: &str) -> anyhow::Error {
    let said = one_line(said.trim());
    if said.contains("unknown option") {
        anyhow::anyhow!(
            "this Claude Code does not take the flags borer-app passes; borer-app was checked with Claude Code {TESTED}, so update it (claude update); it said: {said}"
        )
    } else if said.is_empty() {
        anyhow::anyhow!(ENDED)
    } else {
        anyhow::anyhow!("{ENDED}; it said: {said}")
    }
}

/// Reads Claude Code's standard output line by line and sends what each means to the session.
///
/// Each line is at most [`LINE_MAX`] bytes. It stops when the output ends, a line does not
/// read or the session drops; at the end of the output it says why from `said`, the end of
/// the error pipe ([`ended`]).
async fn hear(
    mut from: impl AsyncBufRead + Unpin,
    mut heard: mpsc::Sender<Heard>,
    said: impl Future<Output = String>,
) {
    let mut said = Some(said);
    loop {
        let mut line = Vec::new();
        let cap = u64::try_from(LINE_MAX.saturating_add(1)).unwrap_or(u64::MAX);
        let read_line = (&mut from).take(cap).read_until(b'\n', &mut line).await;
        let said = match read_line {
            Err(why) => Err(anyhow::Error::new(why).context("Claude Code's output broke")),
            Ok(0) => Err(ended(&match said.take() {
                Some(said) => said.await,
                None => String::new(),
            })),
            Ok(_) if line.len() > LINE_MAX => Err(anyhow::anyhow!(
                "Claude Code wrote a line over {LINE_MAX} bytes; the turn ended"
            )),
            Ok(_) => std::str::from_utf8(&line)
                .context("Claude Code wrote a line that is not UTF-8")
                .and_then(|text| read(text.trim_end()).map_err(anyhow::Error::msg)),
        };
        let last = said.is_err();
        if heard.send((line.len(), said)).await.is_err() || last {
            return;
        }
    }
}

/// Starts Claude Code at `endpoint` and returns the models it offers, each ready to run a
/// turn; it is killed once it has answered. Nothing is sent to a model.
///
/// # Errors
///
/// Returns that it did not start, went silent, refused, or listed nothing.
pub(crate) async fn models(endpoint: Endpoint, cx: &AsyncApp) -> anyhow::Result<Vec<Chosen>> {
    let mut session = Session::start(None, cx).await?;
    session.write(&initialize(LISTING), cx).await?;
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
                    .write(&respond(&request, &json!({ "mcp_response": reply })), cx)
                    .await?;
            }
            Event::Ask { request } => session.write(&refuse(&request, REFUSED), cx).await?,
            Event::Done(Err(why)) => anyhow::bail!("Claude Code: {}", one_line(&why)),
            Event::Text(_) | Event::Answered { .. } | Event::Done(Ok(())) | Event::Other => {}
        }
    };
    anyhow::ensure!(!models.is_empty(), "Claude Code listed no model");
    Ok(models
        .into_iter()
        .map(|m| {
            let name = if m.display_name.is_empty() {
                m.value.clone()
            } else {
                m.display_name
            };
            Chosen {
                runs: Runs::ClaudeCode,
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
    let kept = kept.filter(|s| s.model.as_deref() == model);
    let mut session = match kept.and_then(Session::drained) {
        Some(session) => session,
        None => {
            if earlier {
                step(this, generation, cx, |thread, cx| {
                    let said = "a new Claude Code conversation: it does not see the earlier turns";
                    thread.note(said.to_owned(), cx);
                })?;
            }
            Session::start(model.map(str::to_owned), cx).await?
        }
    };
    session.write(&user(&said.unwrap_or_default()), cx).await?;
    let mut spend = step(this, generation, cx, |thread, _| {
        Spend::new(room(thread.budget()))
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
                    .write(&respond(&request, &json!({ "mcp_response": reply })), cx)
                    .await?;
                if let Some(why) = spend.spent() {
                    return step(this, generation, cx, |thread, cx| {
                        thread.fail(Fault::Spent, format!("the turn ended: {why}"));
                        cx.notify();
                    });
                }
            }
            Event::Ask { request } => session.write(&refuse(&request, REFUSED), cx).await?,
            Event::Done(Ok(())) => break,
            Event::Done(Err(why)) => anyhow::bail!("Claude Code: {}", one_line(&why)),
            Event::Answered { .. } | Event::Other => {}
        }
    }
    step(this, generation, cx, |thread, _| {
        thread.claude = Some(session);
    })
}

/// Returns the bytes of tool answers a turn sends Claude Code: the byte `budget`, never more
/// than [`ANSWERS_MAX`], so no echoed answer outgrows a line, even with no budget.
fn room(budget: Option<usize>) -> Option<usize> {
    Some(budget.map_or(ANSWERS_MAX, |budget| budget.min(ANSWERS_MAX)))
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

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::ffi::OsString;

    /// Only absolute `PATH` folders are searched: `.`, an empty entry and a relative folder
    /// that hold the file are skipped, and the absolute path found is what is returned.
    #[test]
    fn only_absolute_path_entries_are_searched() {
        let here = std::env::current_dir().unwrap();
        let relative = format!("..{}borer-app", std::path::MAIN_SEPARATOR);
        let path = std::env::join_paths([".", "", relative.as_str()]).unwrap();
        assert_eq!(super::find(&path, "Cargo.toml"), None);
        let mut with_absolute = path;
        with_absolute.push(OsString::from(if cfg!(windows) { ";" } else { ":" }));
        with_absolute.push(here.as_os_str());
        let found = super::find(&with_absolute, "Cargo.toml").unwrap();
        assert!(found.is_absolute());
        assert_eq!(found, here.join("Cargo.toml"));
    }

    /// The reader parses each line apart from the UI thread and stops at the first that does
    /// not read: here one over [`super::LINE_MAX`] bytes, after a line it heard.
    #[test]
    fn the_reader_parses_lines_and_stops_at_a_long_one() {
        let done = r#"{"type":"result","subtype":"success","is_error":false}"#;
        let long = "x".repeat(super::LINE_MAX + 10);
        let out = format!("{done}\n{long}\n{done}\n");
        let (heard, lines) = futures::channel::mpsc::channel(4);
        let from = futures::io::BufReader::new(futures::io::Cursor::new(out.into_bytes()));
        futures::executor::block_on(super::hear(from, heard, async { String::new() }));
        let said: Vec<_> = futures::executor::block_on_stream(lines).collect();
        assert_eq!(said.len(), 2);
        assert!(matches!(&said[0].1, Ok(super::Event::Done(Ok(())))));
        let why = format!("{:#}", said[1].1.as_ref().unwrap_err());
        assert!(why.contains("over"), "{why}");
    }

    /// An older Claude Code that refuses a flag is named as too old, with the version checked;
    /// another end says what it said last, and a silent one says it ended.
    #[test]
    fn an_end_says_why() {
        let old = format!(
            "{:#}",
            super::ended("error: unknown option '--safe-mode'\n")
        );
        assert!(
            old.contains(super::TESTED) && old.contains("--safe-mode"),
            "{old}"
        );
        let other = format!("{:#}", super::ended("boom"));
        assert!(
            other.contains("ended before") && other.contains("boom"),
            "{other}"
        );
        assert_eq!(format!("{:#}", super::ended("")), super::ENDED);
        let long = "y".repeat(10_000);
        let kept = futures::executor::block_on(super::tail(futures::io::Cursor::new(long)));
        assert_eq!(kept.len(), super::TAIL);
    }

    /// A turn's tool answers are capped below what an echoed line may hold, with no byte
    /// budget as with one larger than the cap.
    #[test]
    fn answers_stay_below_a_line() {
        assert_eq!(super::room(None), Some(super::ANSWERS_MAX));
        assert_eq!(super::room(Some(usize::MAX)), Some(super::ANSWERS_MAX));
        assert_eq!(super::room(Some(10)), Some(10));
        assert!(super::ANSWERS_MAX.saturating_mul(6) < super::LINE_MAX);
    }

    /// A session's working folder is new and empty, gone once it drops, and a folder left
    /// behind is swept.
    #[test]
    fn a_working_folder_is_private_and_removed() {
        let root = std::env::temp_dir().join(format!("borer-cc-test-{}", std::process::id()));
        let (one, two) = (
            super::Folder::new(&root).unwrap(),
            super::Folder::new(&root).unwrap(),
        );
        assert_ne!(one.0, two.0);
        let is_dir = |p: &std::path::Path| {
            borer_engine::program::checked_metadata(p)
                .unwrap()
                .is_some_and(|m| m.is_dir())
        };
        assert!(is_dir(&one.0) && is_dir(&two.0));
        let gone = one.0.clone();
        drop(one);
        assert!(!is_dir(&gone));
        drop(two);
        let left = root.join("left");
        std::fs::create_dir(&left).unwrap();
        super::sweep(&root);
        assert!(!is_dir(&left));
        std::fs::remove_dir_all(&root).unwrap();
    }
}
