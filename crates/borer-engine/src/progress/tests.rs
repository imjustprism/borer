//! Tests of the progress in force: the phases a job's plan runs, and that
//! work outside a progress leaves it untouched.

use super::{Plan, Progress, SEEN, Snapshot};
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
