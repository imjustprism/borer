//! Progress is a fact about the work, never about the answer: an ordinal
//! position (phase k of n, items done of total), never a time.
//!
//! A front end makes a [`Progress`], runs the work under it
//! ([`Progress::within`]) and polls [`Progress::snapshot`] from another thread;
//! the engine calls nothing back. No answer reads it, so it changes none, and
//! with nothing in force every hook is one thread-local read.
//!
//! The progress in force is per thread, the way the cancel flag is
//! ([`crate::cancel`]), and the threads the engine spawns for its sweeps
//! take it along ([`crate::analysis::reads::Handle`]): the workers of
//! [`crate::analysis::striped`] and of the decompile and export queues, a
//! decompile's own stack and the pass run beside discovery. Discovery's
//! walk lanes do not: they only walk, and run no sweep, mark no phase and
//! spawn no thread. A job runs its phases from a
//! plan, a const list of their names ([`Plan`]): each mark of a planned
//! [`crate::timing::Phases`] moves the progress on to the next phase.

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

thread_local! {
    /// The progress in force on this thread, innermost
    /// [`Progress::within`] last.
    static IN_FORCE: RefCell<Option<Progress>> = const { RefCell::new(None) };
}

#[cfg(test)]
thread_local! {
    /// The phases entered on this thread, in order, for the tests to read.
    static SEEN: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

/// A job whose phases a [`Progress`] reports, by the plan they run in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Plan {
    /// Analyzing a program ([`crate::analysis::COMPUTE_PHASES`]).
    Compute,
}

impl Plan {
    /// Every plan, each at its [`Plan::id`].
    const ALL: [Self; 1] = [Self::Compute];

    /// Returns the plan's slot in [`Plan::ALL`].
    const fn id(self) -> u16 {
        match self {
            Self::Compute => 0,
        }
    }

    /// Returns the names of the plan's phases, in the order they run.
    pub(crate) const fn names(self) -> &'static [&'static str] {
        match self {
            Self::Compute => crate::analysis::COMPUTE_PHASES,
        }
    }
}

/// What the work under a [`Progress`] wrote, for [`Progress::snapshot`].
///
/// A phase is entered by clearing [`State::items`] and then storing
/// [`State::phase`], both with release, so a reader that loads the phase,
/// the items and the phase again with acquire and sees one phase twice
/// holds that phase's items, or the cleared ones of the phase after it.
#[derive(Debug, Default)]
struct State {
    /// The phase running: its plan's [`Plan::id`] in the high 16 bits, its
    /// index plus one in the low 16; 0 before any phase.
    phase: AtomicU32,
    /// The sweep running or last run: its items in the high 32 bits, the
    /// ones done in the low 32.
    items: AtomicU64,
}

/// What the work running under it has reached, for a front end to poll.
#[derive(Debug, Clone, Default)]
pub struct Progress(Arc<State>);

/// A phase of a job: its place in the job's plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Phase {
    /// The phase's place in its plan, from 0.
    pub index: u16,
    /// How many phases the plan has.
    pub of: u16,
    /// The phase's name in its plan.
    pub name: &'static str,
}

/// Where the work under a [`Progress`] was when it was polled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Snapshot {
    /// The phase running or last run; `None` before any job ran one.
    pub phase: Option<Phase>,
    /// Items the sweep running or last run has finished.
    pub done: u64,
    /// Items that sweep has; 0 before any sweep in the phase.
    pub total: u64,
}

impl Progress {
    /// Makes a progress no work has run under.
    ///
    /// # Returns
    ///
    /// The progress; clones share it.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Runs `f` with this progress in force on this thread.
    ///
    /// # Arguments
    ///
    /// * `f` - The work to report.
    ///
    /// # Returns
    ///
    /// What `f` returns; the progress in force before is in force again
    /// after.
    pub fn within<R>(&self, f: impl FnOnce() -> R) -> R {
        crate::cancel::in_force(&IN_FORCE, Some(self.clone()), f)
    }

    /// Reads where the work under this progress is, from any thread,
    /// without a lock.
    ///
    /// The phase is read before and after the items, and the read is taken
    /// again while a phase was entered in between, so a phase is never
    /// paired with the items of the phase before ([`State`]).
    ///
    /// # Returns
    ///
    /// The phase and the sweep's items; [`Snapshot::default`] before any
    /// work ran under it. Should the phase move on [`SNAPSHOT_TRIES`]
    /// reads running, the phase last read with no items.
    #[must_use]
    pub fn snapshot(&self) -> Snapshot {
        let mut phase = self.0.phase.load(Ordering::Acquire);
        for _ in 0..SNAPSHOT_TRIES {
            let items = self.0.items.load(Ordering::Acquire);
            let again = self.0.phase.load(Ordering::Acquire);
            if again == phase {
                return Snapshot {
                    phase: phase_of(phase),
                    done: u64::from(crate::num::lo32(items)),
                    total: items >> 32,
                };
            }
            phase = again;
        }
        Snapshot {
            phase: phase_of(phase),
            ..Snapshot::default()
        }
    }

    /// The progress in force on this thread.
    ///
    /// # Returns
    ///
    /// The progress, or `None` outside every [`Progress::within`].
    pub(crate) fn current() -> Option<Self> {
        IN_FORCE.with(|c| c.borrow().clone())
    }

    /// Runs `f` under a progress taken from another thread, or under none.
    ///
    /// # Arguments
    ///
    /// * `progress` - The progress [`Progress::current`] read there.
    /// * `f` - The work.
    ///
    /// # Returns
    ///
    /// What `f` returns.
    pub(crate) fn carried<R>(progress: Option<&Self>, f: impl FnOnce() -> R) -> R {
        crate::cancel::in_force(&IN_FORCE, progress.cloned(), f)
    }
}

/// Most reads [`Progress::snapshot`] takes of a phase that keeps moving.
const SNAPSHOT_TRIES: usize = 16;

/// Reads a packed phase ([`State::phase`]) back.
///
/// # Arguments
///
/// * `packed` - The plan's id and the index plus one.
///
/// # Returns
///
/// The phase; `None` for 0 or a plan or index no plan has.
fn phase_of(packed: u32) -> Option<Phase> {
    let plan = *Plan::ALL.get(usize::from(crate::num::lo16(u64::from(packed >> 16))))?;
    let index = crate::num::lo16(u64::from(packed)).checked_sub(1)?;
    let names = plan.names();
    Some(Phase {
        index,
        of: u16::try_from(names.len()).unwrap_or(u16::MAX),
        name: names.get(usize::from(index)).copied()?,
    })
}

/// Moves the progress in force, if any, to a phase of `plan`, its sweep's
/// items cleared: they counted the phase before.
///
/// # Arguments
///
/// * `plan` - The job's plan.
/// * `index` - The phase now running, its place in the plan.
pub(crate) fn enter(plan: Plan, index: usize) {
    let Some(progress) = Progress::current() else {
        return;
    };
    let Ok(at) = u16::try_from(index.saturating_add(1)) else {
        return;
    };
    let packed = (u32::from(plan.id()) << 16) | u32::from(at);
    progress.0.items.store(0, Ordering::Release);
    progress.0.phase.store(packed, Ordering::Release);
    #[cfg(test)]
    SEEN.with(|s| s.borrow_mut().extend(plan.names().get(index)));
}

#[cfg(test)]
mod tests;
