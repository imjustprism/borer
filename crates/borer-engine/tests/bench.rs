//! Timing harness for the paths whole-binary work runs through.
//!
//! `BORER_BENCH=path/to/bin cargo test -p borer-engine --release --test bench -- --ignored --nocapture`
//!
//! `BORER_ISO=bin1;bin2 cargo test -p borer-engine --release --test bench iso -- --ignored --nocapture`
//! measures the ISO C check of a decompile answer against the answer itself
//! ([`iso_check_cost`]).
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

use borer_engine::analysis::decompile::{decompile_all, decompile_named, step_times, text_check};
use borer_engine::analysis::render::{Verdict, check_generated, check_generated_iso};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::usize_f64;
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

/// Functions [`iso_check_cost`] samples per binary, evenly by entry.
const ISO_SAMPLE: usize = 300;

/// Inputs the ISO check runs per function: the small set a single
/// `decompile` answer would pay for.
const ISO_INPUTS: usize = 8;

/// Steps each side of one input is given.
const ISO_STEPS: usize = 20_000;

/// The seed the inputs are drawn from.
const ISO_SEED: u64 = 1;

/// Returns the value at a percentile of sorted durations.
///
/// # Arguments
///
/// * `sorted` - The durations, ascending.
/// * `q` - The percentile, 0 to 100.
fn percentile(sorted: &[Duration], q: usize) -> Duration {
    sorted
        .get((sorted.len() * q / 100).min(sorted.len().saturating_sub(1)))
        .copied()
        .unwrap_or_default()
}

/// What the verdicts of one check over many functions add up to.
#[derive(Debug, Default)]
struct Tally {
    /// Functions whose every input agreed.
    agree: usize,
    /// Functions with at least one input that differs.
    differ: usize,
    /// Functions with no difference and at least one unchecked input.
    unchecked: usize,
    /// Functions the check could not run on (a float parameter, no text).
    skipped: usize,
    /// Inputs that agreed, differed, or were unchecked.
    inputs: [usize; 3],
    /// Reasons, by their words up to the first backtick or digit.
    why: std::collections::BTreeMap<String, usize>,
}

impl Tally {
    /// Adds one function's check.
    ///
    /// # Arguments
    ///
    /// * `r` - The rows the check gave, or why it did not run.
    fn add(&mut self, r: &Result<Vec<(String, Verdict)>, String>) {
        let class = |s: &str| {
            s.split(|c: char| c == '`' || c.is_ascii_digit())
                .next()
                .unwrap_or("")
                .to_owned()
        };
        let Ok(rows) = r else {
            self.skipped += 1;
            return;
        };
        let (mut d, mut u) = (false, false);
        for (_, v) in rows {
            match v {
                Verdict::Agrees => self.inputs[0] += 1,
                Verdict::Differs(_, what) => {
                    self.inputs[1] += 1;
                    d = true;
                    *self
                        .why
                        .entry(format!("differs: {}", class(what)))
                        .or_default() += 1;
                }
                Verdict::Unchecked(_, what) => {
                    self.inputs[2] += 1;
                    u = true;
                    *self
                        .why
                        .entry(format!("unchecked: {}", class(what)))
                        .or_default() += 1;
                }
            }
        }
        match (d, u) {
            (true, _) => self.differ += 1,
            (false, true) => self.unchecked += 1,
            (false, false) => self.agree += 1,
        }
    }

    /// Prints the tally under a label.
    ///
    /// # Arguments
    ///
    /// * `label` - Which check it is.
    fn print(&self, label: &str) {
        let checked = self.agree + self.differ;
        println!(
            "{label}: functions agree {} differ {} unchecked {} skipped {}; agreement {:.1}% of checked; inputs agree {} differ {} unchecked {}",
            self.agree,
            self.differ,
            self.unchecked,
            self.skipped,
            100.0 * usize_f64(self.agree) / usize_f64(checked.max(1)),
            self.inputs[0],
            self.inputs[1],
            self.inputs[2]
        );
        let mut top: Vec<(&usize, &String)> = self.why.iter().map(|(k, n)| (n, k)).collect();
        top.sort_unstable_by(|x, y| y.cmp(x));
        for (n, r) in top.iter().take(8) {
            println!("  {n:>5}  {r}");
        }
    }
}

/// Measures the ISO C check of a function's text against the decompile
/// answer it would check, on an even sample of each binary.
///
/// Per sampled function, one at a time on one thread: the decompile answer
/// (`decompile_named` and its replay check, `text_check`, both cold), then
/// the ISO check over [`ISO_INPUTS`] generated inputs, then today's
/// machine-mode check over the same inputs for comparison. Each check
/// reads the memoized text, so its time is the evaluator and emulator runs
/// alone. It reports the p50 of each, the ISO check's p50 as a share of
/// the decompile p50, and the agreement of both modes; with `BORER_TIMING`
/// set, the decompile step totals too.
#[test]
#[ignore = "set BORER_ISO to binary paths separated by ';' to run this harness"]
fn iso_check_cost() {
    let paths = std::env::var("BORER_ISO").expect("BORER_ISO env var");
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let program = Program::load(std::path::Path::new(path)).expect("load");
        let a = Analysis::compute(&program);
        let o = Overlay::default();
        let all: Vec<u64> = a
            .functions
            .iter()
            .filter(|f| f.thunk.is_none() && f.funclet.is_none())
            .map(|f| f.entry)
            .collect();
        let stride = (all.len() / ISO_SAMPLE).max(1);
        let entries: Vec<u64> = all
            .iter()
            .step_by(stride)
            .take(ISO_SAMPLE)
            .copied()
            .collect();
        let (mut dec, mut iso, mut machine) = (Vec::new(), Vec::new(), Vec::new());
        let (mut iso_tally, mut machine_tally) = (Tally::default(), Tally::default());
        for &e in &entries {
            let t = Instant::now();
            let text = decompile_named(&program, &a, &o, e);
            let check = text_check(&program, &a, &o, e);
            dec.push(t.elapsed());
            drop((text, check));
            let t = Instant::now();
            let r = check_generated_iso(&program, &a, &o, e, ISO_INPUTS, ISO_SEED, ISO_STEPS);
            iso.push(t.elapsed());
            iso_tally.add(&r);
            let t = Instant::now();
            let r = check_generated(&program, &a, &o, e, ISO_INPUTS, ISO_SEED, ISO_STEPS);
            machine.push(t.elapsed());
            machine_tally.add(&r);
        }
        let ms = |d: Duration| d.as_secs_f64() * 1e3;
        let iso_mean = iso.iter().sum::<Duration>() / u32::try_from(iso.len().max(1)).unwrap_or(1);
        for v in [&mut dec, &mut iso, &mut machine] {
            v.sort_unstable();
        }
        let (d50, i50) = (percentile(&dec, 50), percentile(&iso, 50));
        println!("binary: {path}");
        println!("functions: {} sampled of {}", entries.len(), all.len());
        println!(
            "decompile answer: p50 {:.2} ms, p90 {:.2} ms",
            ms(d50),
            ms(percentile(&dec, 90))
        );
        println!(
            "iso check ({ISO_INPUTS} inputs, {ISO_STEPS} steps): p50 {:.2} ms, p90 {:.2} ms, mean {:.2} ms; p50 = {:.1}% of decompile p50",
            ms(i50),
            ms(percentile(&iso, 90)),
            ms(iso_mean),
            100.0 * i50.as_secs_f64() / d50.as_secs_f64().max(1e-9)
        );
        println!(
            "machine-mode check: p50 {:.2} ms, p90 {:.2} ms",
            ms(percentile(&machine, 50)),
            ms(percentile(&machine, 90))
        );
        iso_tally.print("iso");
        machine_tally.print("machine");
    }
    if let Some(steps) = step_times() {
        print!("{steps}");
    }
}
