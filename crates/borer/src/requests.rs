//! Running one request off the transport's threads, a few at a time, under
//! the deadline its emulation stops at.
//!
//! A tool or a resource read is synchronous engine work that can take
//! minutes, so it runs on a blocking thread, and at most
//! [`REQUESTS_MAX`] of them at once: more requests wait for a permit
//! instead of each taking a core and memory. Each runs with a
//! [`Cancel`] the gate raises when the request's deadline passes
//! (`BORER_DEADLINE_SECS`, [`DEADLINE_DEFAULT`] unless set, `0` for none);
//! the emulators the request runs then stop at their next step boundary
//! with `stopped: time limit`, and the answer says so. Only emulation
//! stops: the deadline is the one input to an answer that is not the
//! question, and every other cap is a count.

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

/// The permits requests run under, and the deadline each is given.
#[derive(Debug, Clone)]
pub(crate) struct Gate {
    /// One permit per request running.
    permits: Arc<Semaphore>,
    /// How long a request's emulation runs, `None` for no limit.
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
    /// Whether the deadline passed while it ran, so an emulation in it
    /// may have stopped at the time limit.
    pub(crate) cut: bool,
}

impl Gate {
    /// A gate whose requests are given `deadline`.
    ///
    /// # Arguments
    ///
    /// * `deadline` - How long a request's emulation runs, `None` for no
    ///   limit.
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
            "# stopped: time limit: the request ran past {secs}s and its emulation stopped there; {DEADLINE_ENV} sets the limit"
        )
    }

    /// Runs one request on a blocking thread once a permit is free, with
    /// its cancel flag raised when the deadline passes.
    ///
    /// # Arguments
    ///
    /// * `work` - The request.
    ///
    /// # Returns
    ///
    /// Its answer, and whether the deadline cut it.
    ///
    /// # Errors
    ///
    /// Internal error when the permits are closed or the work panicked
    /// past every guard.
    pub(crate) async fn run<R: Send + 'static>(
        &self,
        work: impl FnOnce() -> R + Send + 'static,
    ) -> Result<Ran<R>, ErrorData> {
        let _permit = self
            .permits
            .acquire()
            .await
            .map_err(|e| err_internal(format!("the request queue closed: {e}")))?;
        let cancel = Cancel::new();
        let timer = self.deadline.map(|after| {
            let cancel = cancel.clone();
            tokio::spawn(async move {
                tokio::time::sleep(after).await;
                cancel.raise();
            })
        });
        let flag = cancel.clone();
        let answer = tokio::task::spawn_blocking(move || flag.within(work)).await;
        if let Some(timer) = timer {
            timer.abort();
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
        let ran = gate.run(spin()).await.expect("the request answers");
        assert_eq!(ran.answer, Stop::Limit(Limit::Time));
        assert_eq!(ran.answer.to_string(), "stopped: time limit");
        assert!(ran.cut);
        assert!(gate.note().starts_with("# stopped: time limit"));
        let quick = gate.run(|| 7).await.expect("the request answers");
        assert_eq!((quick.answer, quick.cut), (7, false));
    }
}
