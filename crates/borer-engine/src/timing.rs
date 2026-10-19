//! Wall-clock phase marks and decompile step totals behind `BORER_TIMING`,
//! for profiling a load, an analysis or a sweep without a profiler.
//!
//! The engine never prints: its outputs are answers. The one exception is
//! this knob, inert unless the environment variable is set, which writes
//! one stderr line per marked phase so the seconds of a big binary's first
//! answer can be split into their parts. The decompile pipeline's steps
//! ([`Step`]) add their time to process-wide totals instead, which
//! [`step_times`] renders; with the knob off a [`Lap`] holds no clock and
//! adds nothing. Nothing either keeps is part of any answer, so
//! determinism of output is untouched.

use std::sync::atomic::{AtomicU64, Ordering};

/// Tells whether `BORER_TIMING` is set in the environment, read once.
fn on() -> bool {
    /// The answer, cached for the process's life.
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("BORER_TIMING").is_some())
}

/// One stderr line per [`Phases::mark`], when `BORER_TIMING` is set.
///
/// Constructed once at the top of the pass being measured; each mark names
/// the phase that just ended and restarts the clock, so the lines sum to
/// the whole pass.
#[derive(Debug)]
pub(crate) struct Phases(Option<std::time::Instant>);

impl Phases {
    /// Starts the clock, or stays inert when timing is off.
    ///
    /// # Returns
    ///
    /// The mark holder for one pass.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time printed to stderr behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn new() -> Self {
        Self(on().then(std::time::Instant::now))
    }

    /// Prints the time since the last mark and restarts the clock.
    ///
    /// # Arguments
    ///
    /// * `name` - The phase that just ended.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time printed to stderr behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn mark(&mut self, name: &str) {
        if let Some(t0) = self.0 {
            eprintln!("borer timing: {name} {:?}", t0.elapsed());
            self.0 = Some(std::time::Instant::now());
        }
    }
}

impl Default for Phases {
    /// A mark holder, timing still decided by the environment.
    fn default() -> Self {
        Self::new()
    }
}

/// A step of the decompile pipeline whose time [`Lap`] adds up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Step {
    /// Decoding the blocks, the calling shape and register liveness.
    Decode,
    /// The two dataflow rounds of the lifter.
    Lift,
    /// Structuring and emitting the body.
    Structure,
    /// The text passes run to a fixpoint (`cleanup_settled`).
    Cleanup,
    /// What follows the passes: folds, types, the header.
    Header,
    /// Naming fields through their class.
    NameFields,
    /// The finishing rewrites of the text (`polish`).
    Polish,
    /// Writing the tables the text reads inline (`inline_tables`).
    InlineTables,
    /// Declaring the vector variables (`vector::declare`).
    Vectors,
    /// Defining the helpers the text calls (`helper::declare`).
    Helpers,
    /// The check of a decompile answer against the machine (`replay`).
    Replay,
}

impl Step {
    /// Every step, in pipeline order, each at its slot in [`TOTALS`].
    const ALL: [Self; 11] = [
        Self::Decode,
        Self::Lift,
        Self::Structure,
        Self::Cleanup,
        Self::Header,
        Self::NameFields,
        Self::Polish,
        Self::InlineTables,
        Self::Vectors,
        Self::Helpers,
        Self::Replay,
    ];

    /// The step's name in the report.
    const fn name(self) -> &'static str {
        match self {
            Self::Decode => "decode",
            Self::Lift => "lift",
            Self::Structure => "structure/emit",
            Self::Cleanup => "cleanup_passes",
            Self::Header => "header",
            Self::NameFields => "name_fields",
            Self::Polish => "polish",
            Self::InlineTables => "inline_tables",
            Self::Vectors => "vector_declare",
            Self::Helpers => "helper_declare",
            Self::Replay => "replay",
        }
    }

    /// The step's slot in [`TOTALS`], its place in [`Step::ALL`].
    const fn slot(self) -> usize {
        match self {
            Self::Decode => 0,
            Self::Lift => 1,
            Self::Structure => 2,
            Self::Cleanup => 3,
            Self::Header => 4,
            Self::NameFields => 5,
            Self::Polish => 6,
            Self::InlineTables => 7,
            Self::Vectors => 8,
            Self::Helpers => 9,
            Self::Replay => 10,
        }
    }
}

/// Per step, the nanoseconds spent and the times it ran, summed over every
/// thread of the process. Written only while `BORER_TIMING` is set and
/// read only by [`step_times`]; no answer reads it.
static TOTALS: [(AtomicU64, AtomicU64); Step::ALL.len()] =
    [const { (AtomicU64::new(0), AtomicU64::new(0)) }; Step::ALL.len()];

/// A stopwatch over consecutive steps: each [`Lap::end`] adds the time
/// since the last one to a step's total. It holds no clock when timing is
/// off, so an end is one branch.
#[derive(Debug)]
pub(crate) struct Lap(Option<std::time::Instant>);

impl Lap {
    /// Starts the watch, or stays inert when timing is off.
    ///
    /// # Returns
    ///
    /// The watch.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time kept behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn new() -> Self {
        Self(on().then(std::time::Instant::now))
    }

    /// Adds the time since the last end to `step` and restarts the watch.
    ///
    /// # Arguments
    ///
    /// * `step` - The step that just ended.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time kept behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn end(&mut self, step: Step) {
        let Some(t0) = self.0 else { return };
        let now = std::time::Instant::now();
        let nanos = u64::try_from(now.duration_since(t0).as_nanos()).unwrap_or(u64::MAX);
        if let Some((total, count)) = TOTALS.get(step.slot()) {
            total.fetch_add(nanos, Ordering::Relaxed);
            count.fetch_add(1, Ordering::Relaxed);
        }
        self.0 = Some(now);
    }
}

/// Runs `f` and adds its time to `step`.
///
/// # Arguments
///
/// * `step` - The step `f` is.
/// * `f` - The work.
///
/// # Returns
///
/// What `f` returns.
pub(crate) fn timed<T>(step: Step, f: impl FnOnce() -> T) -> T {
    let mut lap = Lap::new();
    let out = f();
    lap.end(step);
    out
}

/// Renders the decompile step totals so far, one row per step that ran.
///
/// The totals are summed over every thread, so on a parallel sweep they
/// add up to more than the wall time; the shares say where the work goes.
///
/// # Returns
///
/// A table with a `#` header: step, runs, total milliseconds, mean
/// microseconds a run and share of the total; `None` when `BORER_TIMING`
/// is not set.
#[must_use]
pub fn step_times() -> Option<String> {
    use std::fmt::Write as _;
    if !on() {
        return None;
    }
    let rows: Vec<(Step, u64, u64)> = Step::ALL
        .iter()
        .filter_map(|s| {
            let (total, count) = TOTALS.get(s.slot())?;
            let n = count.load(Ordering::Relaxed);
            (n > 0).then(|| (*s, total.load(Ordering::Relaxed), n))
        })
        .collect();
    let all = crate::num::as_f64(rows.iter().map(|r| r.1).sum::<u64>().max(1));
    let mut out = String::from("# step\truns\ttotal_ms\tmean_us\tshare_pct\n");
    for (s, nanos, n) in rows {
        let ns = crate::num::as_f64(nanos);
        let _ = writeln!(
            out,
            "{}\t{n}\t{:.1}\t{:.1}\t{:.1}",
            s.name(),
            ns / 1e6,
            ns / crate::num::as_f64(n) / 1e3,
            ns * 100.0 / all,
        );
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::{Lap, Step, step_times, timed};

    /// A lap holds a clock only while timing is on, a timed step hands back
    /// what it ran, and the report is there exactly when timing is on and
    /// then names the step.
    ///
    /// # Panics
    ///
    /// When the watch or the report ignores the knob.
    #[test]
    fn steps_are_timed_only_behind_the_knob() {
        let on = std::env::var_os("BORER_TIMING").is_some();
        assert_eq!(Lap::new().0.is_some(), on);
        assert_eq!(timed(Step::Polish, || 7), 7);
        let report = step_times();
        assert_eq!(report.is_some(), on);
        if let Some(r) = report {
            assert!(r.starts_with("# step\t"), "{r}");
            assert!(r.contains("\npolish\t"), "{r}");
        }
    }
}
