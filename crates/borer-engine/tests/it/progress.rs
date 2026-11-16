//! The progress a front end polls while the engine works.
//!
//! A sweep's items reach their total and never count back, two progresses keep
//! apart, opening a binary ends on its plan's last phase, and no answer moves
//! for a progress or a worker cap in force.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::num::NonZeroUsize;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use borer_engine::analysis::decompile::decompile_all;
use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::Program;
use borer_engine::progress::{Phase, Progress, Workers};
use borer_engine::session::{Form, Open, Pdb, open};

use crate::common::fixture;

/// Returns a cap of `n` threads, at least one.
///
/// # Arguments
///
/// * `n` - The threads.
fn cap(n: usize) -> Workers {
    Workers(NonZeroUsize::new(n).unwrap_or(NonZeroUsize::MIN))
}

/// Runs `work` under `progress` while another thread polls it, and returns
/// what `work` returned and how often the count of items done went down.
///
/// # Arguments
///
/// * `progress` - The progress the work reports to.
/// * `work` - The work.
///
/// # Returns
///
/// What `work` returned, and the polls that saw the count lower than the
/// one before or past its total.
#[expect(
    clippy::expect_used,
    reason = "a poller that panicked has already failed the test"
)]
fn polled<R>(progress: &Progress, work: impl FnOnce() -> R) -> (R, usize) {
    let finished = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let poller = scope.spawn(|| {
            let (mut last, mut back) = (0, 0);
            while !finished.load(Ordering::Relaxed) {
                let now = progress.snapshot();
                back += usize::from(now.done < last || now.done > now.total);
                last = now.done;
                std::thread::yield_now();
            }
            back
        });
        let out = progress.within(work);
        finished.store(true, Ordering::Relaxed);
        (out, poller.join().expect("the poller ends"))
    })
}

/// A decompile sweep under a progress counts every function once, on one
/// worker and on sixteen, and the count polled from another thread never
/// goes down nor past the total.
#[test]
fn a_decompile_sweep_counts_every_function_once() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let n = u64::try_from(entries.len()).expect("fits");
    for workers in [1, 16] {
        let progress = Progress::new();
        let (texts, back) = polled(&progress, || {
            cap(workers).within(|| decompile_all(&p, &a, &o, &entries))
        });
        assert_eq!(texts.len(), entries.len());
        let last = progress.snapshot();
        assert_eq!((last.done, last.total), (n, n), "{workers} workers");
        assert_eq!(back, 0, "{workers} workers: the count went back");
    }
}

/// Two front ends polling two progresses on two threads each see their own
/// work's count, and a third never put in force sees none.
#[test]
fn concurrent_progresses_keep_their_own_counts() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let (left, right, idle) = (Progress::new(), Progress::new(), Progress::new());
    std::thread::scope(|scope| {
        scope.spawn(|| left.within(|| decompile_all(&p, &a, &o, &entries)));
        scope.spawn(|| right.within(|| decompile_all(&p, &a, &o, &entries[..1])));
    });
    let n = u64::try_from(entries.len()).expect("fits");
    assert_eq!((left.snapshot().done, left.snapshot().total), (n, n));
    assert_eq!((right.snapshot().done, right.snapshot().total), (1, 1));
    assert_eq!(idle.snapshot(), borer_engine::progress::Snapshot::default());
}

/// Loading a file under a progress ends on the load's last phase, and
/// opening one ends on the open's, after the load's phases ran inside it.
#[test]
fn loading_and_opening_end_on_their_plans_last_phase() {
    let bytes = crate::carve::tiny_pe();
    let progress = Progress::new();
    progress
        .within(|| Program::from_bytes("tiny.exe".into(), bytes.clone()))
        .expect("the PE loads");
    let load = progress.snapshot().phase.expect("a load phase ran");
    assert_eq!((load.name, load.index + 1), ("load clr", load.of));
    let dir = std::env::temp_dir().join(format!("borer-progress-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temp dir");
    let binary = dir.join("tiny.exe");
    std::fs::write(&binary, &bytes).expect("the binary is written");
    let how = Open {
        max_file: u64::MAX,
        form: Form::Headers(Pdb::Off),
        named: Arc::default(),
        dirs: Vec::new(),
    };
    progress
        .within(|| open(&binary, &how))
        .expect("the binary opens");
    std::fs::remove_dir_all(&dir).ok();
    let want = Phase {
        index: 1,
        of: 2,
        name: "open packs",
    };
    assert_eq!(progress.snapshot().phase, Some(want));
}

/// Exporting and checking every function under a progress count the
/// functions of the export's and the check's own sweeps, not an inner
/// sweep's items or the check's parts.
#[test]
fn the_export_and_the_check_count_their_functions() {
    use borer_engine::analysis::decompile::export::{Library, export};
    use borer_engine::analysis::decompile::verify::verify;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let progress = Progress::new();
    let hoisted = progress
        .within(|| export(&p, &a, &o, Library::Include, None, &mut |_| Ok(())))
        .expect("exports");
    let s = progress.snapshot();
    let rendered = u64::try_from(hoisted.written + hoisted.failed).expect("fits");
    assert!(
        rendered > 0 && s.total >= rendered && s.done == s.total,
        "{s:?}"
    );
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    drop(progress.within(|| verify(&p, &a, &entries, 1)));
    let n = u64::try_from(entries.len()).expect("fits");
    let s = progress.snapshot();
    assert_eq!((s.done, s.total), (n, n));
}

/// The analysis, the triage and every function's text read the same bytes
/// with nothing in force and under a progress at one worker and at
/// sixteen.
#[test]
fn no_answer_moves_under_a_progress_or_a_cap() {
    let p = fixture();
    let o = Overlay::default();
    let answers = || {
        let a = Analysis::compute(&p);
        let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
        (
            render::triage_tsv(&p, &a, &o),
            decompile_all(&p, &a, &o, &entries),
        )
    };
    let alone = answers();
    for workers in [1, 16] {
        let progress = Progress::new();
        let under = progress.within(|| cap(workers).within(answers));
        assert!(under == alone, "{workers} workers: an answer moved");
    }
}
