//! Running one request off the transport's threads, a few at a time, under
//! the deadline it stops at.
//!
//! A tool or a resource read is synchronous engine work that can take
//! minutes, so it runs on a blocking thread, and at most
//! [`REQUESTS_MAX`] of them at once: more requests wait for a permit
//! instead of each taking a core and memory. Each runs with a
//! [`Cancel`] the gate raises when the request's deadline passes
//! (`BORER_DEADLINE_SECS`, [`DEADLINE_DEFAULT`] unless set, `0` for none);
//! the engine's long loops (the decompile pipeline, the emulators, the
//! sweeps over callers and decoders) then stop at their next check, and
//! the answer ends with [`Gate::note`] saying it is partial. The deadline
//! only decides whether an answer finishes, never what a finished one
//! says: every other cap is a count. The client's cancel
//! (`notifications/cancelled`) raises the same flag, and a request it
//! stops answers nothing: no partial text goes out as an answer.

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use borer_engine::cancel::Cancel;
use rmcp::ErrorData;
use tokio::sync::Semaphore;

use crate::errors::err_internal;

/// The environment variable naming the per-request deadline, in seconds.
pub(crate) const DEADLINE_ENV: &str = "BORER_DEADLINE_SECS";

/// The deadline when the environment names none.
const DEADLINE_DEFAULT: Duration = Duration::from_mins(5);

/// Most requests the engine works on at once.
const REQUESTS_MAX: usize = 2;

/// What a request the client cancelled answers, which rmcp drops.
const CALLED_OFF: &str = "the client cancelled the request, so it stopped and answers nothing";

/// The permits requests run under, and the deadline each is given.
#[derive(Debug, Clone)]
pub(crate) struct Gate {
    /// One permit per request running.
    permits: Arc<Semaphore>,
    /// How long a request runs, `None` for no limit.
    deadline: Option<Duration>,
}

impl Default for Gate {
    /// A gate with [`REQUESTS_MAX`] permits and [`DEADLINE_DEFAULT`].
    fn default() -> Self {
        Gate::with_deadline(Some(DEADLINE_DEFAULT))
    }
}

/// What a request answered, and whether its deadline cut it.
#[derive(Debug)]
pub(crate) struct Ran<R> {
    /// The request's own answer.
    pub(crate) answer: R,
    /// Whether the deadline passed while it ran, so its answer may be
    /// partial.
    pub(crate) cut: bool,
}

impl Gate {
    /// A gate whose requests are given `deadline`.
    ///
    /// # Arguments
    ///
    /// * `deadline` - How long a request runs, `None` for no limit.
    ///
    /// # Returns
    ///
    /// The gate, with [`REQUESTS_MAX`] permits.
    pub(crate) fn with_deadline(deadline: Option<Duration>) -> Self {
        Gate {
            permits: Arc::new(Semaphore::new(REQUESTS_MAX)),
            deadline,
        }
    }

    /// The gate the environment configures: `BORER_DEADLINE_SECS` seconds,
    /// `0` for no limit, [`DEADLINE_DEFAULT`] when it is unset or not a
    /// number (said on stderr).
    ///
    /// # Returns
    ///
    /// The gate.
    pub(crate) fn from_env() -> Self {
        let Ok(text) = std::env::var(DEADLINE_ENV) else {
            return Self::default();
        };
        match text.trim().parse::<u64>() {
            Ok(0) => Self::with_deadline(None),
            Ok(secs) => Self::with_deadline(Some(Duration::from_secs(secs))),
            Err(_) => {
                eprintln!(
                    "borer: {DEADLINE_ENV}={} is not a number of seconds; using {}",
                    borer_engine::text::one_line(&text),
                    DEADLINE_DEFAULT.as_secs()
                );
                Self::default()
            }
        }
    }

    /// Says how a cut answer was cut, for its last line.
    ///
    /// # Returns
    ///
    /// The note, naming the deadline and the variable that sets it.
    pub(crate) fn note(&self) -> String {
        let secs = self.deadline.map_or(0, |d| d.as_secs());
        format!(
            "# stopped: time limit: the request ran past {secs}s and stopped there, so the answer above is partial; ask for less (one function, a filter, a page) or raise {DEADLINE_ENV}"
        )
    }

    /// Runs one request on a blocking thread once a permit is free, with
    /// its cancel flag raised when the deadline passes or the client
    /// cancels it; a request the client cancels while it waits for its
    /// permit never runs.
    ///
    /// # Arguments
    ///
    /// * `stop` - Ends when the client cancels the request (the request
    ///   context's token, `RequestContext::ct`).
    /// * `work` - The request.
    ///
    /// # Returns
    ///
    /// Its answer, and whether the deadline cut it.
    ///
    /// # Errors
    ///
    /// Internal error when the client cancelled the request, so its
    /// answer, whole or not, is dropped; when the permits are closed; or
    /// when the work panicked past every guard.
    pub(crate) async fn run<R: Send + 'static>(
        &self,
        stop: impl Future<Output = ()> + Send + 'static,
        work: impl FnOnce() -> R + Send + 'static,
    ) -> Result<Ran<R>, ErrorData> {
        let mut stop = Box::pin(stop);
        let _permit = tokio::select! {
            biased;
            () = &mut stop => return Err(err_internal(CALLED_OFF)),
            permit = self.permits.acquire() => {
                permit.map_err(|e| err_internal(format!("the request queue closed: {e}")))?
            }
        };
        let cancel = Cancel::new();
        let timer = self.deadline.map(|after| {
            let cancel = cancel.clone();
            tokio::spawn(async move {
                tokio::time::sleep(after).await;
                cancel.raise();
            })
        });
        let called_off = Cancel::new();
        let watch = {
            let (cancel, called_off) = (cancel.clone(), called_off.clone());
            tokio::spawn(async move {
                stop.await;
                called_off.raise();
                cancel.raise();
            })
        };
        let flag = cancel.clone();
        let answer = tokio::task::spawn_blocking(move || flag.within(work)).await;
        if let Some(timer) = timer {
            timer.abort();
        }
        watch.abort();
        if called_off.is_raised() {
            return Err(err_internal(CALLED_OFF));
        }
        let answer = answer.map_err(|e| err_internal(format!("the request faulted: {e}")))?;
        Ok(Ran {
            answer,
            cut: cancel.is_raised(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Gate;
    use borer_engine::emulate::{Emulator, Limit, Stop};
    use borer_engine::program::{Arch, Program, Section};
    use std::time::Duration;

    /// A request past its deadline stops its emulation at the time limit
    /// and says it was cut; one within it is not.
    ///
    /// # Panics
    ///
    /// When the emulation runs to its budget past the deadline, or a quick
    /// request is said to be cut.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_request_past_its_deadline_stops_at_the_time_limit() {
        let text = Section::mapped(".text", 0x1000, 0, 2, false, true);
        let spin = || {
            let p = Program::raw(
                vec![0xeb, 0xfe],
                Arch::X86_64,
                0,
                Some(0x1000),
                vec![text.clone()],
            );
            move || {
                let mut emu = Emulator::new(&p, usize::MAX).expect("an emulator");
                emu.run(0x1000).stop
            }
        };
        let gate = Gate::with_deadline(Some(Duration::from_millis(50)));
        let ran = gate
            .run(std::future::pending(), spin())
            .await
            .expect("the request answers");
        assert_eq!(ran.answer, Stop::Limit(Limit::Time));
        assert_eq!(ran.answer.to_string(), "stopped: time limit");
        assert!(ran.cut);
        assert!(gate.note().starts_with("# stopped: time limit"));
        let quick = gate
            .run(std::future::pending(), || 7)
            .await
            .expect("the request answers");
        assert_eq!((quick.answer, quick.cut), (7, false));
    }

    /// A request the client cancels while it runs answers an error, not
    /// what it had so far.
    ///
    /// Its emulation stops at the check the deadline stops it at, though
    /// the gate gives it no deadline.
    ///
    /// # Panics
    ///
    /// When the cancelled request answers, or runs to its budget.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_request_the_client_cancels_stops_and_answers_nothing() {
        let text = Section::mapped(".text", 0x1000, 0, 2, false, true);
        let p = Program::raw(vec![0xeb, 0xfe], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let (began, started) = tokio::sync::oneshot::channel();
        let (cancel, cancelled) = tokio::sync::oneshot::channel::<()>();
        let gate = Gate::with_deadline(None);
        let stop = async move {
            let _ = cancelled.await;
        };
        let ran = tokio::spawn(async move {
            gate.run(stop, move || {
                let mut emu = Emulator::new(&p, usize::MAX).expect("an emulator");
                let _ = began.send(());
                emu.run(0x1000).stop
            })
            .await
        });
        started.await.expect("the request starts");
        cancel.send(()).expect("the request waits");
        let refused = ran
            .await
            .expect("the request ends")
            .expect_err("a cancelled request answers nothing");
        assert!(refused.message.contains("client cancelled"), "{refused:?}");
    }

    /// A request the client cancels while it waits for a permit never
    /// runs, so a cancelled edit changes nothing.
    ///
    /// # Panics
    ///
    /// When the cancelled request runs or answers.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_request_cancelled_in_the_queue_never_runs() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, Ordering};
        let gate = Gate::with_deadline(None);
        let (free, freed) = tokio::sync::watch::channel(false);
        let busy: Vec<_> = (0..super::REQUESTS_MAX)
            .map(|_| {
                let (gate, mut freed) = (gate.clone(), freed.clone());
                tokio::spawn(async move {
                    gate.run(std::future::pending(), move || {
                        tokio::runtime::Handle::current()
                            .block_on(freed.wait_for(|f| *f))
                            .map(|_| ())
                    })
                    .await
                })
            })
            .collect();
        while gate.permits.available_permits() > 0 {
            tokio::task::yield_now().await;
        }
        let ran = Arc::new(AtomicBool::new(false));
        let edit = Arc::clone(&ran);
        let refused = gate
            .run(std::future::ready(()), move || {
                edit.store(true, Ordering::SeqCst);
            })
            .await
            .expect_err("a cancelled request answers nothing");
        assert!(refused.message.contains("client cancelled"), "{refused:?}");
        assert!(!ran.load(Ordering::SeqCst), "the cancelled request ran");
        free.send(true).expect("the busy requests wait");
        for request in busy {
            let done = request.await.expect("the busy request ends");
            assert!(done.is_ok_and(|r| r.answer.is_ok()));
        }
    }

    /// Returns a server holding one function at `0x1000`, `mov eax, 1; ret`.
    fn one_function() -> crate::BorerServer {
        let code = vec![0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3];
        let text = Section::mapped(".text", 0x1000, 0, 6, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        }
    }

    /// Reads whose deadline passes before they decompile answer promptly
    /// that the decompile stopped and end with the note, and leave nothing
    /// behind: the next read answers whole, as a fresh server does.
    ///
    /// The work waits for the gate's flag before it reads, so the deadline
    /// has passed whatever the machine's speed.
    ///
    /// # Panics
    ///
    /// When the cut answer lacks the stop or the note, or the next read
    /// differs from a fresh server's.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_read_past_its_deadline_says_it_stopped_and_keeps_nothing() {
        let server = one_function();
        let gate = Gate::with_deadline(Some(Duration::ZERO));
        let reader = server.clone();
        let ran = gate
            .run(std::future::pending(), move || {
                while !borer_engine::cancel::Cancel::raised() {
                    std::thread::yield_now();
                }
                ["function", "decompile"].map(|r| reader.read_uri(&format!("borer://{r}/0x1000")))
            })
            .await
            .expect("the request answers");
        assert!(ran.cut);
        let [summary, text] = ran.answer.map(|read| read.expect("the read answers").1);
        assert!(text.contains("// stopped: time limit"), "{text}");
        for cut in [summary, text] {
            assert!(
                cut.contains("# stopped: time limit: the request ran past"),
                "{cut}"
            );
        }
        let whole = server
            .resource_text("borer://function/0x1000")
            .expect("reads");
        assert!(!whole.contains("stopped"), "{whole}");
        assert_eq!(
            whole,
            one_function()
                .resource_text("borer://function/0x1000")
                .expect("reads")
        );
    }
}
