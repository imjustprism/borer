//! The hand-over of a session from one worker to the next on `reload`:
//! the state carried across and the transport that waits for the reply.

use std::collections::HashSet;
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use rmcp::RoleServer;
use rmcp::model::{ClientNotification, InitializeRequestParams, JsonRpcMessage, RequestId};
use rmcp::service::{RxJsonRpcMessage, TxJsonRpcMessage};
use rmcp::transport::Transport;
use rmcp::transport::async_rw::AsyncRwTransport;

use crate::relay;
use crate::state::{RawLoad, lock};

/// What the worker taking over resumes from, written by the one handing
/// over to the file the relay names.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct Resume {
    /// What the client sent at initialize, for the next worker to serve the
    /// session with.
    pub(crate) peer_info: Option<InitializeRequestParams>,
    /// The loaded file with its names and comments, for the next worker to
    /// load again; `None` when nothing was loaded.
    pub(crate) project: Option<borer::project::ProjectFile>,
    /// Whether the loaded file's companion PDB applied (`load_binary`'s
    /// `pdb`), for the next worker to load it the same way.
    pub(crate) pdb: Option<bool>,
    /// The `entry_file_offset` the file was loaded with, for the next
    /// worker to load it the same way.
    pub(crate) entry_file_offset: Option<u64>,
    /// The raw layout the file was mapped by, for the next worker to map
    /// it the same way; absent from the state of a worker built before it.
    #[serde(default)]
    pub(crate) raw: RawLoad,
}

impl Resume {
    /// Writes the state to `file` and ends this worker with
    /// [`relay::HAND_OVER`], which the relay answers by starting the next
    /// one. A state that cannot be written is said on stderr; the next
    /// worker then serves the session without it.
    ///
    /// # Arguments
    ///
    /// * `file` - The file the relay named ([`relay::WORKER`]).
    pub(crate) fn hand_over(&self, file: &Path) -> ! {
        if let Err(e) = serde_json::to_vec(self)
            .map_err(std::io::Error::other)
            .and_then(|json| write_fresh(file, &json))
        {
            eprintln!(
                "borer: the session's state does not survive the reload ({}): {e}",
                file.display()
            );
        }
        std::process::exit(relay::HAND_OVER)
    }

    /// Reads the state the worker before this one wrote, and removes the
    /// file.
    ///
    /// # Arguments
    ///
    /// * `file` - The file the relay named ([`relay::RESUME`]).
    ///
    /// # Errors
    ///
    /// When the file cannot be read or does not parse.
    pub(crate) fn take(file: &Path) -> Result<Resume, String> {
        let json = std::fs::read(file).map_err(|e| format!("read {}: {e}", file.display()))?;
        if let Err(e) = std::fs::remove_file(file) {
            eprintln!("borer: remove {}: {e}", file.display());
        }
        serde_json::from_slice(&json).map_err(|e| format!("parse {}: {e}", file.display()))
    }
}

/// Writes a file that must not exist yet, never through a link.
///
/// The state file lives in the relay's private directory
/// ([`relay::state_dir`]) and the worker taking over removes it once read,
/// so one already there was put there by someone else.
///
/// # Arguments
///
/// * `file` - The file.
/// * `bytes` - What it holds.
///
/// # Errors
///
/// When anything is already at `file`, or the write fails.
fn write_fresh(file: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let mut out = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(file)?;
    std::io::Write::write_all(&mut out, bytes)
}

/// The hand-over to the next worker, shared between the server, which asks
/// for it from `reload`, and the transport, which carries it out once
/// nothing is in flight.
///
/// The relay passes this worker no request after the reload call, so the
/// worker ends once the reload reply and the replies to every request
/// before it have been written ([`HandOverTransport`]): none of those is
/// lost, and whatever the client sends after the call goes to the next
/// worker.
#[derive(Debug, Default)]
pub(crate) struct HandOver {
    /// The bookkeeping, under one lock.
    pub(crate) state: Mutex<HandOverState>,
}

/// What [`HandOver`] keeps.
#[derive(Debug, Default)]
pub(crate) struct HandOverState {
    /// The requests read and not yet answered or cancelled.
    pub(crate) in_flight: HashSet<RequestId>,
    /// The state to hand over once nothing is in flight; set by `reload`.
    pub(crate) pending: Option<Resume>,
}

impl HandOver {
    /// Notes a request read.
    ///
    /// # Arguments
    ///
    /// * `id` - The request's id.
    pub(crate) fn asked(&self, id: RequestId) {
        lock(&self.state).in_flight.insert(id);
    }

    /// Notes a request answered or cancelled, and hands over, ending this
    /// worker, when that leaves nothing in flight behind a scheduled reload.
    ///
    /// # Arguments
    ///
    /// * `id` - The request's id.
    /// * `file` - Where the state goes ([`relay::WORKER`]).
    pub(crate) fn answered(&self, id: &RequestId, file: &Path) {
        let mut s = lock(&self.state);
        s.in_flight.remove(id);
        if s.in_flight.is_empty()
            && let Some(resume) = s.pending.take()
        {
            resume.hand_over(file);
        }
    }

    /// Schedules the hand-over for when nothing is in flight.
    ///
    /// The reload call is itself in flight until its reply is written, so
    /// the hand-over always follows that reply ([`Self::answered`]).
    ///
    /// # Arguments
    ///
    /// * `resume` - What the next worker resumes from.
    pub(crate) fn schedule(&self, resume: Resume) {
        lock(&self.state).pending = Some(resume);
    }
}

/// The stdio transport with the hand-over wired in.
///
/// It notes each request read and each reply written, and hands over once
/// the reload reply and every earlier one are out. Each reply written also
/// hands the memory its request freed back to the system
/// ([`borer_live::release_free_memory`]), so a worker waiting for its next
/// request holds only what it uses.
pub(crate) struct HandOverTransport {
    /// The line-framed transport over standard input and output.
    pub(crate) inner: AsyncRwTransport<RoleServer, tokio::io::Stdin, tokio::io::Stdout>,
    /// The shared bookkeeping.
    pub(crate) hand_over: Arc<HandOver>,
    /// The file the state goes to on a hand-over ([`relay::WORKER`]).
    pub(crate) state: Arc<Path>,
}

impl HandOverTransport {
    /// A transport over this process's standard handles.
    ///
    /// # Arguments
    ///
    /// * `hand_over` - The server's hand-over state.
    /// * `state` - The file the state goes to on a hand-over.
    pub(crate) fn new(hand_over: Arc<HandOver>, state: PathBuf) -> HandOverTransport {
        HandOverTransport {
            inner: AsyncRwTransport::new(tokio::io::stdin(), tokio::io::stdout()),
            hand_over,
            state: state.into(),
        }
    }
}

impl Transport<RoleServer> for HandOverTransport {
    type Error = std::io::Error;

    fn send(
        &mut self,
        item: TxJsonRpcMessage<RoleServer>,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send + 'static {
        let answered = match &item {
            JsonRpcMessage::Response(r) => Some(r.id.clone()),
            JsonRpcMessage::Error(e) => e.id.clone(),
            JsonRpcMessage::Request(_) | JsonRpcMessage::Notification(_) => None,
        };
        let send = self.inner.send(item);
        let hand_over = Arc::clone(&self.hand_over);
        let state = Arc::clone(&self.state);
        async move {
            send.await?;
            if let Some(id) = answered {
                hand_over.answered(&id, &state);
                borer_live::release_free_memory();
            }
            Ok(())
        }
    }

    async fn receive(&mut self) -> Option<RxJsonRpcMessage<RoleServer>> {
        let msg = self.inner.receive().await?;
        match &msg {
            JsonRpcMessage::Request(r) => self.hand_over.asked(r.id.clone()),
            JsonRpcMessage::Notification(n) => {
                if let ClientNotification::CancelledNotification(c) = &n.notification
                    && let Some(id) = &c.params.request_id
                {
                    self.hand_over.answered(id, &self.state);
                }
            }
            JsonRpcMessage::Response(_) | JsonRpcMessage::Error(_) => {}
        }
        Some(msg)
    }

    fn close(&mut self) -> impl Future<Output = Result<(), Self::Error>> + Send {
        self.inner.close()
    }
}

/// Ends the process quietly, and successfully, when the reader of stdout
/// has gone (`borer functions x.exe | head`), which the print macros report
/// by panicking.
///
/// Every other panic still reaches the default hook.
#[expect(
    clippy::exit,
    reason = "a closed stdout ends a CLI pipe; there is no caller left to answer"
)]
pub(crate) fn end_quietly_when_stdout_closes() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let message = info
            .payload()
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| info.payload().downcast_ref::<&str>().copied())
            .unwrap_or("");
        if message.starts_with("failed printing to stdout") {
            std::process::exit(0);
        }
        default(info);
    }));
}

#[cfg(test)]
mod tests {
    use super::write_fresh;
    use crate::relay::state_dir;

    /// Each session's state directory is fresh and its own, and the state
    /// file is never written over what is already there or through a link.
    ///
    /// # Panics
    ///
    /// When two sessions share a directory, or a planted file or link is
    /// written through.
    #[test]
    fn the_state_lives_in_a_fresh_directory_and_a_fresh_file() {
        let base = std::env::temp_dir().join(format!("borer-state-{}", std::process::id()));
        std::fs::create_dir_all(&base).expect("a temp dir");
        let one = state_dir(&base).expect("a directory");
        let two = state_dir(&base).expect("another");
        assert_ne!(one, two);
        let file = one.join("resume.json");
        write_fresh(&file, b"{}").expect("a fresh file");
        assert!(
            write_fresh(&file, b"{}").is_err(),
            "an existing file is kept"
        );
        let victim = base.join("victim.txt");
        std::fs::write(&victim, b"untouched").expect("written");
        let link = two.join("resume.json");
        #[cfg(unix)]
        let linked = std::os::unix::fs::symlink(&victim, &link).is_ok();
        #[cfg(windows)]
        let linked = std::os::windows::fs::symlink_file(&victim, &link).is_ok();
        if linked {
            assert!(write_fresh(&link, b"{}").is_err(), "a link is not followed");
        }
        assert_eq!(std::fs::read(&victim).expect("read"), b"untouched");
        std::fs::remove_dir_all(&base).expect("cleans up");
    }
}
