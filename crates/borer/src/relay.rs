//! The process an MCP host launches: a relay that keeps the host's pipes
//! for the whole session and runs the server behind them as a worker.
//!
//! A host takes the end of the process it launched for the end of the
//! server and starts a fresh one, with nothing loaded. So `reload` replaces
//! the worker, never this process: the relay starts the worker (this same
//! binary, marked by [`WORKER`]), copies the host's lines to it and its
//! lines back, and when the worker ends with [`HAND_OVER`] it starts the
//! binary at the path the host launched again, marked by [`RESUME`], so a
//! build installed there since is the one that takes over. Any other end of
//! a worker ends the relay with the same code: the host sees the server end
//! as it would without the relay.
//!
//! The relay reads one thing from a line: whether it is the `reload` call.
//! Once it has passed that call on it reads nothing more from the host until
//! the worker has ended, which the worker does after answering the call and
//! every request before it; what the host sends meanwhile waits in the
//! relay's buffer for the next worker, so no request is lost or answered
//! twice. The session's state crosses in a file the worker writes and the
//! next one reads; the relay holds none of it.
//!
//! Every worker is tied to the relay ([`borer_live::Tether`]): when the host
//! kills the relay, the worker ends with it, even in the middle of a
//! request it would otherwise have run to the end for no one.

use std::io::{BufRead as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::{ChildStdin, Command, Stdio};
use std::thread::JoinHandle;

use anyhow::Context as _;
use rmcp::model::{ClientJsonRpcMessage, ClientRequest};

/// The environment variable that makes the binary a worker; its value is
/// the file the worker writes the session's state to when it hands over.
pub(crate) const WORKER: &str = "BORER_WORKER";

/// The environment variable set on a worker that takes over; its value is
/// the file holding the state of the worker before it.
pub(crate) const RESUME: &str = "BORER_RESUME";

/// The exit code of a worker that answered `reload` and every request
/// before it and wrote the session's state: the relay starts the next one.
pub(crate) const HAND_OVER: i32 = 75;

/// The exit code the relay ends with for a worker that ended without one
/// (killed by a signal) or could not be waited for.
const NO_CODE: i32 = 1;

/// A running worker.
#[derive(Debug)]
struct Worker {
    /// The pipe the host's lines go down. It stays open until the worker has
    /// ended, unless the host closed the session: a worker whose input
    /// closes stops serving before it has answered.
    stdin: ChildStdin,
    /// The thread copying the worker's output to the host; it returns only
    /// when the worker handed over ([`Worker::start`]).
    pump: JoinHandle<()>,
}

impl Worker {
    /// Starts the binary as a worker, and a thread copying its standard
    /// output to this process's.
    ///
    /// The thread ends with the worker. A worker that handed over ends just
    /// the thread; any other end of it ends this process with the worker's
    /// code, at once, so the host sees the server end even while the relay
    /// waits on the host for its next line. The thread closes its end of the
    /// worker's output before waiting, so a worker still writing to a host
    /// that has gone fails rather than blocks. The worker writes its
    /// diagnostics to this process's standard error.
    ///
    /// # Arguments
    ///
    /// * `exe` - The binary, at the path the host launched.
    /// * `state` - The file the worker writes the session's state to when it
    ///   hands over.
    /// * `resume` - The state to take over from, for a worker that follows
    ///   one that handed over; `None` for the first.
    /// * `tether` - What ends the worker with this process, `None` when
    ///   there is none; a worker that cannot be tied is said on standard
    ///   error and served untied.
    ///
    /// # Errors
    ///
    /// When the binary cannot be started.
    fn start(
        exe: &Path,
        state: &Path,
        resume: Option<&Path>,
        tether: Option<&borer_live::Tether>,
    ) -> anyhow::Result<Worker> {
        let mut cmd = Command::new(exe);
        cmd.env(WORKER, state)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        match resume {
            Some(file) => cmd.env(RESUME, file),
            None => cmd.env_remove(RESUME),
        };
        let mut child = cmd
            .spawn()
            .with_context(|| format!("starting the server {}", exe.display()))?;
        if let Some(tether) = tether
            && let Err(e) = tether.tie(&child)
        {
            eprintln!("borer: the server will not end with this process: {e}");
        }
        let stdin = child
            .stdin
            .take()
            .context("the server's input is not piped")?;
        let mut out = child
            .stdout
            .take()
            .context("the server's output is not piped")?;
        let pump = std::thread::spawn(move || {
            let mut stdout = std::io::stdout().lock();
            if let Err(e) = std::io::copy(&mut out, &mut stdout).and_then(|_| stdout.flush()) {
                eprintln!("borer: relaying the server's output: {e}");
            }
            drop(out);
            let code = match child.wait() {
                Ok(status) => status.code().unwrap_or(NO_CODE),
                Err(e) => {
                    eprintln!("borer: waiting for the server: {e}");
                    NO_CODE
                }
            };
            if code != HAND_OVER {
                std::process::exit(code);
            }
        });
        Ok(Worker { stdin, pump })
    }
}

/// Waits for a worker's output to end, which is when the worker has ended.
///
/// # Arguments
///
/// * `pump` - The thread copying the worker's output ([`Worker::pump`]).
///
/// # Errors
///
/// When that thread failed. A worker that ended other than by handing over
/// never gets here: that thread ends the relay.
fn ended(pump: JoinHandle<()>) -> anyhow::Result<()> {
    pump.join()
        .map_err(|_| anyhow::anyhow!("the thread relaying the server's output failed"))
}

/// Tells whether a line from the host is the `reload` call.
///
/// The line is read as the worker's transport reads it, as rmcp's
/// [`ClientJsonRpcMessage`], so the two agree on which line ends the worker:
/// a call the relay took for `reload` that the worker refused would hold the
/// host's lines for good.
///
/// # Arguments
///
/// * `line` - One line from the host, newline included.
fn is_reload(line: &[u8]) -> bool {
    matches!(
        serde_json::from_slice::<ClientJsonRpcMessage>(line),
        Ok(ClientJsonRpcMessage::Request(r))
            if matches!(&r.request, ClientRequest::CallToolRequest(c) if c.params.name == "reload")
    )
}

/// Relays the host's session to a worker, and starts the next worker each
/// time one hands over, until the host closes the session.
///
/// # Errors
///
/// When the binary cannot be started or the host's input fails. A worker
/// that ends other than by handing over ends this process with its own
/// exit code ([`Worker::start`]).
pub(crate) fn run() -> anyhow::Result<()> {
    let exe = std::env::args_os()
        .next()
        .map_or_else(std::env::current_exe, |a| Ok(PathBuf::from(a)))?;
    let state = std::env::temp_dir().join(format!("borer-resume-{}.json", std::process::id()));
    let tether = borer_live::Tether::new()
        .inspect_err(|e| eprintln!("borer: the server will not end with this process: {e}"))
        .ok();
    let mut worker = Worker::start(&exe, &state, None, tether.as_ref())?;
    let mut host = std::io::stdin().lock();
    let mut line = Vec::new();
    loop {
        line.clear();
        if host.read_until(b'\n', &mut line)? == 0 {
            drop(worker.stdin);
            return ended(worker.pump);
        }
        if let Err(e) = worker
            .stdin
            .write_all(&line)
            .and_then(|()| worker.stdin.flush())
        {
            ended(worker.pump)?;
            return Err(e).context("the server stopped reading without handing over");
        }
        if is_reload(&line) {
            ended(worker.pump)?;
            worker = Worker::start(&exe, &state, Some(&state), tether.as_ref())?;
        }
    }
}
