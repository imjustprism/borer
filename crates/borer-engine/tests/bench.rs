//! Timing harness for the paths whole-binary work runs through.
//!
//! `BORER_BENCH=path/to/bin cargo test -p borer-engine --release --test bench -- --ignored --nocapture`
//!
//! The dogfood sweep reports a wall time, but its spread across identical
//! runs is wide enough to hide a small change: 6.7s to 9.4s on one machine
//! for the same binary. Each figure here is the best of several passes over
//! a fixed slice of the program, which is the number a change has to move.

#![expect(clippy::disallowed_methods, reason = "a timing harness measures time")]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile_all;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;
use std::time::{Duration, Instant};

/// Passes taken; the fastest is reported.
const PASSES: usize = 5;

/// Functions decompiled per pass, from the start of the program.
const SLICE: usize = 2000;

/// Returns the fastest of `PASSES` runs of `f`.
///
/// # Arguments
///
/// * `f` - The work to time.
fn best<T>(mut f: impl FnMut() -> T) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..PASSES {
        let t = Instant::now();
        let out = f();
        let d = t.elapsed();
        drop(out);
        best = best.min(d);
    }
    best
}

/// Reports the best time for analysis and for decompiling a fixed slice.
#[test]
#[ignore = "set BORER_BENCH to a binary path to run this harness"]
fn timings() {
    let path = std::env::var("BORER_BENCH").expect("BORER_BENCH env var");
    let program = Program::load(std::path::Path::new(&path)).expect("load");
    let analysis = best(|| Analysis::compute(&program));
    let a = Analysis::compute(&program);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().take(SLICE).map(|f| f.entry).collect();
    let decompile = best(|| decompile_all(&program, &a, &o, &entries));
    let per = decompile.as_nanos() / entries.len().max(1) as u128;
    println!("binary:     {path}");
    println!(
        "functions:  {} total, {} timed",
        a.functions.len(),
        entries.len()
    );
    println!(
        "analysis:   {:.1} ms (best of {PASSES})",
        analysis.as_secs_f64() * 1e3
    );
    println!(
        "decompile:  {:.1} ms for {} functions, {} ns each (best of {PASSES})",
        decompile.as_secs_f64() * 1e3,
        entries.len(),
        per
    );
}
