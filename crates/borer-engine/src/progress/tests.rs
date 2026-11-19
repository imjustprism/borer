//! Tests of the progress in force: the phases a job's plan runs, and that
//! work outside a progress leaves it untouched.

use std::num::NonZeroUsize;

use super::{Plan, Progress, SEEN, Snapshot, Workers};
use crate::analysis::{Analysis, COMPUTE_PHASES};
use crate::program::{Arch, Program, Section};

/// Builds an x64 program of one function: `xor eax, eax; ret` at 0x1000.
fn program() -> Program {
    let mut bytes = vec![0xcc; 0x100];
    bytes[..3].copy_from_slice(&[0x31, 0xc0, 0xc3]);
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text])
}

/// The analysis under a progress runs exactly its plan's phases, in order,
/// and the last snapshot is the plan's last phase.
///
/// # Panics
///
/// When a phase is missed, repeated or out of order, or the last one is
/// not the plan's last.
#[test]
fn the_analysis_runs_its_plan_in_order() {
    SEEN.with(|s| s.borrow_mut().clear());
    let progress = Progress::new();
    progress.within(|| Analysis::compute(&program()));
    assert_eq!(SEEN.with(|s| s.borrow().clone()), COMPUTE_PHASES);
    let last = progress.snapshot().phase.expect("a phase ran");
    assert_eq!(usize::from(last.index) + 1, usize::from(last.of));
    assert_eq!(usize::from(last.of), COMPUTE_PHASES.len());
    assert_eq!(Some(&last.name), COMPUTE_PHASES.last());
}

/// An analysis under a cancel flag raised before it began stops as its
/// first phase ends: no later phase runs, and it hands back no analysis.
///
/// # Panics
///
/// When a phase runs past the raised flag, or an analysis is handed back.
#[test]
fn a_raised_flag_ends_the_analysis_with_its_first_phase() {
    SEEN.with(|s| s.borrow_mut().clear());
    let (progress, flag) = (Progress::new(), crate::cancel::Cancel::new());
    flag.raise();
    let cut = progress.within(|| {
        flag.within(|| Analysis::try_compute_with(&program(), std::sync::Arc::default()))
    });
    assert!(cut.is_none());
    assert_eq!(SEEN.with(|s| s.borrow().clone()), COMPUTE_PHASES[..1]);
}

/// A progress never put in force reads nothing, while another runs work
/// on another thread and one more on this thread runs none.
///
/// # Panics
///
/// When work reaches a progress it did not run under.
#[test]
fn work_reaches_only_the_progress_it_runs_under() {
    let (idle, busy, beside) = (Progress::new(), Progress::new(), Progress::new());
    std::thread::scope(|scope| {
        scope.spawn(|| busy.within(|| Analysis::compute(&program())));
        scope.spawn(|| beside.within(|| ()));
        drop(Analysis::compute(&program()));
    });
    assert_eq!(idle.snapshot(), Snapshot::default());
    assert_eq!(beside.snapshot(), Snapshot::default());
    let phase = busy.snapshot().phase.expect("a phase ran");
    assert_eq!(Some(&phase.name), COMPUTE_PHASES.last());
    assert!(Progress::current().is_none());
}

/// A panic caught inside a progress's scope leaves no progress in force on
/// the thread.
///
/// # Panics
///
/// When the progress outlives its scope.
#[test]
fn a_caught_panic_leaves_nothing_in_force() {
    let progress = Progress::new();
    let caught = std::panic::catch_unwind(|| progress.within(|| panic!("the work fails")));
    assert!(caught.is_err());
    assert!(Progress::current().is_none());
}

/// A mark that names no phase of the plan, or not the one running, is a
/// defect the debug build stops at.
///
/// # Panics
///
/// Always, at the mark out of its plan.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of its plan")]
fn a_mark_out_of_its_plan_is_a_defect() {
    let progress = Progress::new();
    progress.within(|| {
        let mut phases = crate::timing::Phases::planned(Plan::Compute);
        phases.mark("analysis naming");
    });
}

/// Returns a cap of `n` threads, at least one.
///
/// # Arguments
///
/// * `n` - The threads.
fn cap(n: usize) -> Workers {
    Workers(NonZeroUsize::new(n).unwrap_or(NonZeroUsize::MIN))
}

/// A striped map over 1,000 items under a cap one below the machine's
/// cores runs on exactly that many threads.
///
/// # Panics
///
/// When the map spreads past the cap, or not over the cores it may take.
#[test]
fn a_cap_bounds_the_threads_a_sweep_runs_on() {
    let items: Vec<usize> = (0..1000).collect();
    let seen = std::sync::Mutex::new(Vec::new());
    let machine = std::thread::available_parallelism().map_or(1, NonZeroUsize::get);
    let most = machine.saturating_sub(1).max(1);
    cap(most).within(|| {
        crate::analysis::striped(&items, |_| {
            let mut seen = seen.lock().expect("no item panics");
            let here = std::thread::current().id();
            if !seen.contains(&here) {
                seen.push(here);
            }
        })
    });
    assert_eq!(seen.lock().expect("no item panicked").len(), most);
}

/// A progress takes no parallelism from a sweep.
///
/// A striped sweep under a progress spreads over as many threads as the
/// same sweep without one, and a decompile sweep reads as many cores under
/// it; the bench's processor-time ratio cannot see either.
///
/// # Panics
///
/// When the sweep under the progress runs on fewer threads, or reads fewer
/// cores.
#[test]
fn a_progress_takes_no_threads_from_a_sweep() {
    let items: Vec<usize> = (0..1000).collect();
    let spread = || {
        let seen = std::sync::Mutex::new(Vec::new());
        crate::analysis::striped(&items, |_| {
            let mut seen = seen.lock().expect("no item panics");
            let here = std::thread::current().id();
            if !seen.contains(&here) {
                seen.push(here);
            }
        });
        (
            seen.into_inner().expect("no item panicked").len(),
            super::cores(),
        )
    };
    let plain = spread();
    let under = Progress::new().within(spread);
    assert_eq!(
        under, plain,
        "threads and cores under a progress, and without"
    );
}

/// Every thread a sweep spawns works under the progress and the cap of the
/// thread that started it: four threads mapped under a cap of one each
/// read the cap of one, on any machine.
///
/// # Panics
///
/// When a worker runs without the progress or past the cap.
#[test]
fn the_threads_a_sweep_spawns_take_the_progress_and_the_cap_along() {
    let items: Vec<usize> = (0..1000).collect();
    let progress = Progress::new();
    let seen = progress.within(|| {
        cap(1).within(|| {
            crate::analysis::striped_on(
                4,
                &items,
                || std::thread::current().id(),
                |&id, _| (id, Progress::current().is_some(), super::cores()),
            )
        })
    });
    let mut threads: Vec<_> = seen.iter().map(|s| s.0).collect();
    threads.dedup();
    assert!(threads.len() > 1, "the map ran on one thread");
    assert!(
        seen.iter()
            .all(|&(_, carried, cores)| carried && cores == 1)
    );
    assert!(Workers::current().is_none());
}

/// A panic caught inside a cap's scope leaves no cap in force on the
/// thread.
///
/// # Panics
///
/// When the cap outlives its scope.
#[test]
fn a_caught_panic_leaves_no_cap_in_force() {
    let caught = std::panic::catch_unwind(|| cap(2).within(|| panic!("the work fails")));
    assert!(caught.is_err());
    assert!(Workers::current().is_none());
}

/// A sweep whose items each run a sweep of their own counts only its own
/// items, inline and across the cores.
///
/// # Panics
///
/// When an inner sweep's items reach the count.
#[test]
fn only_the_outermost_sweep_is_counted() {
    let items: Vec<usize> = (0..300).collect();
    for workers in [1, 16] {
        let progress = Progress::new();
        progress.within(|| {
            cap(workers).within(|| {
                crate::analysis::striped(&items, |_| crate::analysis::striped(&items[..10], |x| *x))
            })
        });
        let last = progress.snapshot();
        assert_eq!((last.done, last.total), (300, 300), "{workers} workers");
    }
}
