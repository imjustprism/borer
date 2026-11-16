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
//! [`crate::timing::Phases`] moves the progress on to the next phase. A
//! job run inside another's phase (the load inside an open) reports its
//! own phases while it runs, and the outer job's next mark takes the
//! report back.
//!
//! A sweep over items ([`crate::analysis::striped`],
//! [`crate::analysis::decompile::decompile_all`], the export and the
//! check of every function) reports its items done of its total
//! ([`Sweep`]); each worker adds its share every [`TALLY_EVERY`] items
//! ([`Tally`]), so the count lags the work by at most that many a worker
//! and is whole when the sweep returns. Only the outermost sweep reports: one started
//! while another runs under the same progress, on any thread (a sweep in a
//! worker of a sweep, or one beside it), is not counted, so the total
//! never jumps to an inner sweep's. Entering a phase clears the count.
//!
//! A [`Workers`] in force caps the threads each sweep spreads over
//! ([`cores`]), taken along the same way; discovery is handed the capped
//! count for its walk lanes. The thread count changes no answer, only how
//! soon it comes.

use std::cell::RefCell;
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

thread_local! {
    /// The progress in force on this thread, innermost
    /// [`Progress::within`] last.
    static IN_FORCE: RefCell<Option<Progress>> = const { RefCell::new(None) };
}

thread_local! {
    /// The worker cap in force on this thread, innermost
    /// [`Workers::within`] last.
    static WORKERS: RefCell<Option<Workers>> = const { RefCell::new(None) };
}

#[cfg(test)]
thread_local! {
    /// The phases entered on this thread, in order, for the tests to read.
    static SEEN: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

/// A job whose phases a [`Progress`] reports, by the plan they run in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Plan {
    /// Opening a binary ([`crate::session::OPEN_PHASES`]).
    Open,
    /// Loading a file's bytes ([`crate::program::LOAD_PHASES`]).
    Load,
    /// Analyzing a program ([`crate::analysis::COMPUTE_PHASES`]).
    Compute,
}

impl Plan {
    /// Every plan, each at its [`Plan::id`].
    const ALL: [Self; 3] = [Self::Open, Self::Load, Self::Compute];

    /// Returns the plan's slot in [`Plan::ALL`].
    const fn id(self) -> u16 {
        match self {
            Self::Open => 0,
            Self::Load => 1,
            Self::Compute => 2,
        }
    }

    /// Returns the names of the plan's phases, in the order they run.
    pub(crate) const fn names(self) -> &'static [&'static str] {
        match self {
            Self::Open => crate::session::OPEN_PHASES,
            Self::Load => crate::program::LOAD_PHASES,
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
#[repr(align(64))]
struct State {
    /// The phase running: its plan's [`Plan::id`] in the high 16 bits, its
    /// index plus one in the low 16; 0 before any phase.
    phase: AtomicU32,
    /// The sweep running or last run: its items in the high 32 bits, the
    /// ones done in the low 32.
    items: AtomicU64,
    /// Sweeps running under the progress, on every thread.
    sweeps: AtomicU32,
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

/// A sweep's report of its items to the progress in force when it began.
#[derive(Debug)]
pub(crate) struct Sweep {
    /// The progress the sweep runs under; `None` outside every
    /// [`Progress::within`].
    state: Option<Arc<State>>,
    /// Whether its items are the ones reported: it began while no other
    /// sweep ran under the progress, and its total fits the count.
    counted: bool,
}

impl Sweep {
    /// Starts a sweep of `total` items under the progress in force.
    ///
    /// # Arguments
    ///
    /// * `total` - How many items the sweep runs.
    ///
    /// # Returns
    ///
    /// The sweep, which reports until it is dropped.
    pub(crate) fn start(total: usize) -> Self {
        let state = Progress::current().map(|p| p.0);
        let counted = state.as_ref().is_some_and(|s| {
            let outermost = s.sweeps.fetch_add(1, Ordering::Relaxed) == 0;
            let Some(total) = u32::try_from(total).ok().filter(|_| outermost) else {
                return false;
            };
            s.items.store(u64::from(total) << 32, Ordering::Release);
            true
        });
        Self { state, counted }
    }

    /// Counts `n` items of the sweep done, when its items are the ones
    /// reported.
    ///
    /// # Arguments
    ///
    /// * `n` - The items just finished; the sweep's finished items never
    ///   pass its total.
    pub(crate) fn add(&self, n: u64) {
        if let Some(s) = self.state.as_ref().filter(|_| self.counted) {
            s.items.fetch_add(n, Ordering::Release);
        }
    }

    /// Starts one worker's count of its items.
    ///
    /// # Returns
    ///
    /// The worker's tally, which adds what it holds when dropped.
    pub(crate) fn tally(&self) -> Tally<'_> {
        Tally {
            sweep: self,
            held: 0,
        }
    }
}

/// Items a worker counts before it adds them to its sweep's.
const TALLY_EVERY: u64 = 64;

/// One worker's items done of a [`Sweep`], added to the sweep's every
/// [`TALLY_EVERY`] items and when dropped, so the workers of a counted
/// sweep do not take turns at one cache line for every item.
#[derive(Debug)]
pub(crate) struct Tally<'s> {
    /// The sweep the items are of.
    sweep: &'s Sweep,
    /// Items finished and not yet added, below [`TALLY_EVERY`].
    held: u64,
}

impl Tally<'_> {
    /// Counts one item done.
    pub(crate) fn one(&mut self) {
        if self.sweep.counted {
            self.held += 1;
            if self.held == TALLY_EVERY {
                self.sweep.add(self.held);
                self.held = 0;
            }
        }
    }
}

impl Drop for Tally<'_> {
    /// Adds the items held to the sweep's.
    fn drop(&mut self) {
        if self.held > 0 {
            self.sweep.add(self.held);
        }
    }
}

impl Drop for Sweep {
    /// Ends the sweep, so the next one under its progress may be counted.
    fn drop(&mut self) {
        if let Some(s) = &self.state {
            s.sweeps.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

/// Most threads one sweep spreads over, for the work under
/// [`Workers::within`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Workers(pub NonZeroUsize);

impl Workers {
    /// Runs `f` with this cap in force on this thread.
    ///
    /// # Arguments
    ///
    /// * `f` - The work to cap.
    ///
    /// # Returns
    ///
    /// What `f` returns; the cap in force before is in force again after.
    pub fn within<R>(self, f: impl FnOnce() -> R) -> R {
        crate::cancel::in_force(&WORKERS, Some(self), f)
    }

    /// The cap in force on this thread.
    ///
    /// # Returns
    ///
    /// The cap, or `None` outside every [`Workers::within`].
    pub(crate) fn current() -> Option<Self> {
        WORKERS.with(|c| *c.borrow())
    }

    /// Runs `f` under a cap taken from another thread, or under none.
    ///
    /// # Arguments
    ///
    /// * `workers` - The cap [`Workers::current`] read there.
    /// * `f` - The work.
    ///
    /// # Returns
    ///
    /// What `f` returns.
    pub(crate) fn carried<R>(workers: Option<Self>, f: impl FnOnce() -> R) -> R {
        crate::cancel::in_force(&WORKERS, workers, f)
    }
}

/// Returns the threads a sweep may spread over: the cores this process may
/// run on, at most the [`Workers`] in force, at least one.
pub(crate) fn cores() -> usize {
    let cores = std::thread::available_parallelism().map_or(1, NonZeroUsize::get);
    Workers::current().map_or(cores, |Workers(most)| cores.min(most.get()))
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
