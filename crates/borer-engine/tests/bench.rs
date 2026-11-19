//! Timing harness for the paths whole-binary work runs through.
//!
//! `BORER_BENCH=path/to/bin cargo test -p borer-engine --release --test bench -- --ignored --nocapture`
//!
//! `BORER_ISO=bin1;bin2 cargo test -p borer-engine --release --test bench iso -- --ignored --nocapture`
//! measures the ISO C check of a decompile answer against the answer itself
//! ([`iso_check_cost`]).
//!
//! `BORER_BISECT=bin1;bin2 cargo test -p borer-engine --release --test bench bisect -- --ignored --nocapture`
//! finds the first text pass that breaks each function the ISO check
//! rejects ([`bisect_passes`]).
//!
//! `BORER_REPAIR=bin1;bin2 cargo test -p borer-engine --release --test bench repair -- --ignored --nocapture`
//! runs the full repair search on every function and reports how often it
//! runs, what it costs and what it repairs ([`repair_search`]).
//!
//! `BORER_LATENCY=bin1;bin2 cargo test -p borer-engine --release --test bench latency -- --ignored --nocapture`
//! times one cold `decompile` answer per sampled function as the MCP tool
//! gives it, under the binary's name tables, and hashes every answer
//! ([`mcp_latency`]).
//!
//! `BORER_CALLTREE=path/to/bin cargo test -p borer-engine --release --test bench call_tree -- --ignored --nocapture`
//! times one level of the call tree for every function ([`call_tree`]).
//!
//! `BORER_LISTING=bin1;bin2 cargo test -p borer-engine --release --test bench listing -- --ignored --nocapture`
//! reads every answer as a listing, holds its stated places to mapped
//! addresses and times its classification against its read ([`listing`]).
//!
//! `timings` also holds each function's cold decompile to a p95 and a
//! maximum ([`DECOMPILE_P95_MS`], [`DECOMPILE_MAX_MS`]), the bars the
//! notepad of the golden corpus is measured against, and reading that text
//! as a view to its own ([`VIEW_P95_US`], [`VIEW_MAX_MS`]).
//!
//! The dogfood sweep reports a wall time, but its spread across identical
//! runs is wide enough to hide a small change: 6.7s to 9.4s on one machine
//! for the same binary. Each figure here is the best of several passes over
//! a fixed slice of the program, which is the number a change has to move.

#![expect(clippy::print_stdout, reason = "it reports on stdout")]
#![expect(clippy::disallowed_methods, reason = "a timing harness measures time")]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::decompile::{
    Detail, answer, decompile, decompile_all, decompile_named, step_times, text_check,
};
use borer_engine::analysis::render::{
    Bisected, Budget, Evidence, Grade, Repair, Verdict, bisect_iso, check_generated,
    check_generated_iso, repair_iso,
};
use borer_engine::analysis::{Analysis, EnumSource, Overlay, name_of};
use borer_engine::num::{as_f64, usize_f64};
use borer_engine::program::Program;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

#[path = "common/drawn.rs"]
#[expect(
    dead_code,
    reason = "the bench lays out graphs and checks none of them"
)]
mod drawn;

/// `PROCESS_POWER_THROTTLING_STATE`, as `SetProcessInformation` reads it.
#[cfg(windows)]
#[repr(C)]
struct Throttling {
    /// The structure's version, 1.
    version: u32,
    /// The throttling kinds the call sets.
    control: u32,
    /// Which of them are on.
    state: u32,
}

#[cfg(windows)]
#[expect(unsafe_code, reason = "the bench opts out of throttling as borer does")]
#[link(name = "kernel32")]
unsafe extern "system" {
    /// Returns the pseudo-handle naming this process.
    fn GetCurrentProcess() -> *mut core::ffi::c_void;
    /// Sets a fact of a process; nonzero on success.
    fn SetProcessInformation(
        process: *mut core::ffi::c_void,
        class: i32,
        info: *const core::ffi::c_void,
        size: u32,
    ) -> i32;
}

/// Keeps the bench at full speed as `borer_live::run_at_full_speed` keeps
/// borer, so Windows does not slow it a few seconds in on a busy machine
/// and the passes timed later are not timed at another clock.
fn run_at_full_speed() {
    #[cfg(windows)]
    {
        /// `ProcessPowerThrottling`, the class of fact set.
        const POWER_THROTTLING: i32 = 4;
        /// `PROCESS_POWER_THROTTLING_EXECUTION_SPEED`.
        const EXECUTION_SPEED: u32 = 1;
        let state = Throttling {
            version: 1,
            control: EXECUTION_SPEED,
            state: 0,
        };
        let size = u32::try_from(size_of::<Throttling>()).unwrap_or(0);
        #[expect(unsafe_code, reason = "the bench opts out of throttling as borer does")]
        // SAFETY: the pointer and length describe `state`, which outlives
        // the call, and the pseudo-handle names this process.
        let set = unsafe {
            SetProcessInformation(
                GetCurrentProcess(),
                POWER_THROTTLING,
                core::ptr::from_ref(&state).cast(),
                size,
            )
        };
        assert_ne!(
            set, 0,
            "SetProcessInformation refused the throttling opt-out"
        );
    }
}

/// Timed rounds of analysis, each one run without a progress and one under
/// one ([`paired`]).
const ANALYSIS_ROUNDS: usize = 24;

/// Timed rounds of the decompile slice, as [`ANALYSIS_ROUNDS`]: as many
/// runs a side as the five passes timed before the rounds were paired.
const DECOMPILE_ROUNDS: usize = 5;

/// Most the least processor time under a progress may be of the least
/// without one ([`progress_ratio`]).
///
/// The counting is a thread-local read a sweep and an add every 64 items a
/// worker, so anything past the passes' spread is a regression.
const REPORTED_RATIO: f64 = 1.10;

/// Functions decompiled per pass, from the start of the program.
const SLICE: usize = 2000;

/// What one run cost.
#[derive(Debug, Clone, Copy)]
struct Run {
    /// Its wall-clock time.
    wall: Duration,
    /// The processor time every thread of the process spent on it, in the
    /// ticks of [`borer_live::process_cpu_ticks`].
    cpu: u64,
}

/// Returns the processor ticks this process has spent so far.
#[expect(
    clippy::expect_used,
    reason = "a bench that cannot read processor time cannot hold its bar"
)]
fn cpu_ticks() -> u64 {
    borer_live::process_cpu_ticks().expect("the processor time this process spent")
}

/// Returns what one run of `f` cost, its output dropped after the clocks
/// stop.
///
/// # Arguments
///
/// * `f` - The work to time.
fn timed<T>(f: &mut impl FnMut() -> T) -> Run {
    let (t, cpu) = (Instant::now(), cpu_ticks());
    let out = f();
    let run = Run {
        wall: t.elapsed(),
        cpu: cpu_ticks().saturating_sub(cpu),
    };
    drop(out);
    run
}

/// Returns the costs of `rounds` rounds of `plain` and `under`, after one
/// untimed round of each.
///
/// The untimed round builds what the first run would build alone (the
/// memos of a fresh analysis). `plain` runs first in even rounds and second
/// in odd ones (A B B A), so the two sides run side by side and load on the
/// machine falls on both alike, not on one block of runs.
///
/// # Arguments
///
/// * `rounds` - How many timed rounds to run.
/// * `plain` - The work without a progress.
/// * `under` - The same work under a progress.
///
/// # Returns
///
/// Each timed round's run without the progress and under it, in order.
fn paired<T>(
    rounds: usize,
    mut plain: impl FnMut() -> T,
    mut under: impl FnMut() -> T,
) -> Vec<(Run, Run)> {
    timed(&mut plain);
    timed(&mut under);
    (0..rounds)
        .map(|i| {
            if i % 2 == 0 {
                let p = timed(&mut plain);
                (p, timed(&mut under))
            } else {
                let u = timed(&mut under);
                (timed(&mut plain), u)
            }
        })
        .collect()
}

/// Returns the least cost without a progress and the least under one.
///
/// # Arguments
///
/// * `rounds` - Each round's cost without a progress and under one.
///
/// # Returns
///
/// The two least costs; `None` for no rounds.
fn bests<T: Ord + Copy>(rounds: &[(T, T)]) -> Option<(T, T)> {
    let plain = rounds.iter().map(|r| r.0).min()?;
    let under = rounds.iter().map(|r| r.1).min()?;
    Some((plain, under))
}

/// Returns the least processor time under a progress over the least
/// without one, and whether it is within [`REPORTED_RATIO`].
///
/// Processor time leaves out the time the process waited for a processor,
/// which is most of what load on the machine adds to a run's wall time.
/// What load still adds (shared caches and cores) only ever adds, so each
/// side's least run is the nearest its floor: a spike on either side moves
/// no minimum while one run of that side ran clear of it, and a progress
/// that costs more raises the floor of every run under it.
///
/// It cannot see a cost that waits rather than computes, or one on the
/// thread the others wait for, or a sweep that spreads over fewer threads
/// under a progress. The last is held by a test of the progress module
/// (`a_progress_takes_no_threads_from_a_sweep`); the first two are held by
/// nothing here, and the wall ratio [`reported`] prints beside this one is
/// where a person sees them. No wall bar is asserted: load on the machine
/// moves the wall ratio as far as a sweep run on one thread does.
///
/// # Arguments
///
/// * `rounds` - Each round's processor ticks without a progress and under
///   one.
///
/// # Returns
///
/// The ratio and whether it is at most [`REPORTED_RATIO`]; no rounds read
/// as an infinite ratio, past it.
fn progress_ratio(rounds: &[(u64, u64)]) -> (f64, bool) {
    let ratio = bests(rounds).map_or(f64::INFINITY, |(plain, under)| {
        as_f64(under) / as_f64(plain)
    });
    (ratio, ratio <= REPORTED_RATIO)
}

/// Holds [`progress_ratio`] to its purpose on made-up rounds.
///
/// A progress that costs nothing passes beside rounds a spike hit on
/// either side. A progress that costs 13% fails though one plain run
/// spiked (where the smallest or the mean per-round ratio would pass), and
/// one that costs 12% under noise fails (where the median or the mean
/// per-round ratio would pass).
#[test]
fn a_spiked_round_passes_and_a_dearer_progress_fails() {
    let ms = |p: u64, u: u64| (p, u);
    let mut spiked = vec![ms(290, 300); 8];
    spiked.extend([ms(292, 705), ms(705, 300)]);
    assert!(progress_ratio(&spiked).1, "{:?}", progress_ratio(&spiked));
    let mut floored = vec![ms(290, 328); 9];
    floored.push(ms(705, 328));
    assert!(
        !progress_ratio(&floored).1,
        "{:?}",
        progress_ratio(&floored)
    );
    let noisy = [
        ms(1430, 1520),
        ms(1350, 1530),
        ms(1400, 1520),
        ms(1360, 1530),
        ms(1410, 1520),
        ms(1380, 1530),
    ];
    assert!(!progress_ratio(&noisy).1, "{:?}", progress_ratio(&noisy));
    assert!(!progress_ratio(&[]).1);
}

/// Times analysis and the decompile slice in rounds beside the same work
/// under a progress, prints their best times, and returns what went past
/// [`REPORTED_RATIO`].
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which the slice is decompiled against.
/// * `o` - User names and comments.
/// * `entries` - The slice.
///
/// # Returns
///
/// One message per side whose time under a progress went past the bar;
/// empty when both held.
fn reported(p: &Program, a: &Analysis, o: &Overlay, entries: &[u64]) -> Vec<String> {
    let progress = borer_engine::progress::Progress::new();
    let analysis = paired(
        ANALYSIS_ROUNDS,
        || Analysis::compute(p),
        || progress.within(|| Analysis::compute(p)),
    );
    let all = paired(
        DECOMPILE_ROUNDS,
        || decompile_all(p, a, o, entries),
        || progress.within(|| decompile_all(p, a, o, entries)),
    );
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    let wall = |rounds: &[(Run, Run)]| -> Vec<(Duration, Duration)> {
        rounds.iter().map(|(p, u)| (p.wall, u.wall)).collect()
    };
    let (plain, watched) = bests(&wall(&analysis)).unwrap_or_default();
    let (whole, swept) = bests(&wall(&all)).unwrap_or_default();
    println!(
        "analysis:   {:.1} ms (best of {ANALYSIS_ROUNDS})",
        ms(plain)
    );
    println!(
        "decompile:  {:.1} ms for {} functions, {} ns each (best of {DECOMPILE_ROUNDS})",
        ms(whole),
        entries.len(),
        whole.as_nanos() / entries.len().max(1) as u128
    );
    println!(
        "reported:   analysis {:.1} ms, decompile {:.1} ms under a progress (best of {ANALYSIS_ROUNDS} and {DECOMPILE_ROUNDS}, run beside the plain ones)",
        ms(watched),
        ms(swept)
    );
    [("analysis", &analysis), ("decompile", &all)]
        .into_iter()
        .filter_map(|(what, rounds)| {
            let cpu: Vec<(u64, u64)> = rounds.iter().map(|(p, u)| (p.cpu, u.cpu)).collect();
            let (ratio, within) = progress_ratio(&cpu);
            let (p, u) = bests(&wall(rounds)).unwrap_or_default();
            println!(
                "ratio:      {what} {ratio:.3} in processor time under a progress (at most {REPORTED_RATIO}), {:.3} in wall time (not held)",
                u.as_secs_f64() / p.as_secs_f64()
            );
            (!within).then(|| {
                format!("{what} under a progress spent {ratio:.3} times the processor time it spent without, past {REPORTED_RATIO}")
            })
        })
        .collect()
}

/// The p95 of one function's cold decompile, in milliseconds, that
/// [`timings`] holds an optimized build to.
///
/// Notepad measured 7 ms (2026-10-20, `--profile sweep`); the bar leaves
/// room for a slower machine, not for a slower engine.
const DECOMPILE_P95_MS: u128 = 25;

/// The slowest one function's cold decompile may be, in milliseconds.
///
/// Notepad's slowest measured 1.7 s, at 0x140013154.
const DECOMPILE_MAX_MS: u128 = 5000;

/// The p95 of reading one function's text as a view ([`view_of`]), in
/// microseconds, that [`timings`] holds an optimized build to.
///
/// It times `view_of` alone, on the plain `decompile` text and outside any
/// memo build: what the kept view
/// ([`view`](borer_engine::analysis::decompile::view::view)) adds, the
/// answer's header lines and the noting of the reads of the build that
/// keeps it, is not in it.
const VIEW_P95_US: u128 = 2000;

/// The slowest one function's view may take to read, in milliseconds.
const VIEW_MAX_MS: u128 = 100;

/// The slowest one function's control-flow graph may take to lay out, in
/// milliseconds, cut graphs included, that [`timings`] holds every
/// function of the binary to ([`layouts`]).
const LAYOUT_WORST_MS: u128 = 100;

/// Reports the best time for analysis and for decompiling a fixed slice,
/// then each function of the slice cold and alone.
///
/// Analysis and the slice are each timed beside the same work under a
/// progress and held to [`REPORTED_RATIO`] of it ([`reported`]); each
/// function's p50, p95 and slowest are held to [`DECOMPILE_P95_MS`] and
/// [`DECOMPILE_MAX_MS`].
///
/// Also times reading each text so made as a view, held to
/// [`VIEW_P95_US`] and [`VIEW_MAX_MS`], and laying out every function's
/// control-flow graph, held to [`LAYOUT_WORST_MS`] ([`layouts`]).
#[test]
#[ignore = "set BORER_BENCH to a binary path to run this harness"]
fn timings() {
    run_at_full_speed();
    let path = std::env::var("BORER_BENCH").expect("BORER_BENCH env var");
    let program = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&program);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().take(SLICE).map(|f| f.entry).collect();
    println!("binary:     {path}");
    println!(
        "functions:  {} total, {} timed",
        a.functions.len(),
        entries.len()
    );
    let past = reported(&program, &a, &o, &entries);
    assert!(past.is_empty(), "{}", past.join("; "));
    let cold = Analysis::compute(&program);
    let mut texts = Vec::with_capacity(entries.len());
    let mut each: Vec<(Duration, u64)> = entries
        .iter()
        .map(|&e| {
            let t = Instant::now();
            let text = decompile(&program, &cold, &o, e);
            let took = t.elapsed();
            texts.extend(text.map(|text| (e, text)));
            (took, e)
        })
        .collect();
    each.sort_unstable();
    let times: Vec<Duration> = each.iter().map(|&(t, _)| t).collect();
    let (p95, (max, slowest)) = (
        percentile(&times, 95),
        each.last().copied().unwrap_or_default(),
    );
    println!(
        "each:       p50 {:?}, p95 {p95:?}, max {max:?} at {slowest:#x}",
        percentile(&times, 50)
    );
    let mut views: Vec<(Duration, u64)> = texts
        .iter()
        .map(|(e, text)| {
            let t = Instant::now();
            let v = view_of(&program, &cold, &o, *e, text);
            let took = t.elapsed();
            drop(v);
            (took, *e)
        })
        .collect();
    views.sort_unstable();
    let view_times: Vec<Duration> = views.iter().map(|&(t, _)| t).collect();
    let (view_p95, (view_max, view_slowest)) = (
        percentile(&view_times, 95),
        views.last().copied().unwrap_or_default(),
    );
    println!(
        "view:       p50 {:?}, p95 {view_p95:?}, max {view_max:?} at {view_slowest:#x}",
        percentile(&view_times, 50)
    );
    assert!(p95.as_millis() <= DECOMPILE_P95_MS, "decompile p95 {p95:?}");
    assert!(
        max.as_millis() <= DECOMPILE_MAX_MS,
        "decompiling {slowest:#x} took {max:?}"
    );
    assert!(view_p95.as_micros() <= VIEW_P95_US, "view p95 {view_p95:?}");
    assert!(
        view_max.as_millis() <= VIEW_MAX_MS,
        "reading {view_slowest:#x} as a view took {view_max:?}"
    );
    let (worst, at) = layouts(&program, &cold, &o);
    assert!(
        worst.as_millis() <= LAYOUT_WORST_MS,
        "laying out {at:#x} took {worst:?}"
    );
}

/// Returns the slowest graph layout and the entry of its function.
///
/// It times [`layout`](borer_engine::analysis::render::layout) alone over
/// every function's control-flow graph and prints the layouts at p50, p95
/// and worst.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `o` - User names and comments.
fn layouts(p: &Program, a: &Analysis, o: &Overlay) -> (Duration, u64) {
    let mut took: Vec<(Duration, u64)> = a
        .functions
        .iter()
        .filter_map(|f| {
            let g = borer_engine::analysis::render::cfg(p, a, o, f.entry).ok()?;
            let graph = drawn::graph_of(&g, f.entry);
            let t = Instant::now();
            let drawn = borer_engine::analysis::render::layout(&graph);
            let elapsed = t.elapsed();
            drop(drawn);
            Some((elapsed, f.entry))
        })
        .collect();
    took.sort_unstable();
    let times: Vec<Duration> = took.iter().map(|&(t, _)| t).collect();
    let worst = took.last().copied().unwrap_or_default();
    println!(
        "layout:     {} graphs, p50 {:?}, p95 {:?}, max {:?} at {:#x}",
        took.len(),
        percentile(&times, 50),
        percentile(&times, 95),
        worst.0,
        worst.1
    );
    worst
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
    why: BTreeMap<String, usize>,
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

/// Inputs [`bisect_passes`] runs per function.
const BISECT_INPUTS: usize = 64;

/// Bisects the text passes of each function whose text the ISO check
/// rejects, and counts the functions each pass breaks.
///
/// `BORER_BISECT` names the binaries, separated by `;`; `BORER_BISECT_NAMES`,
/// when set, the functions to check by name, separated by `,` (all others
/// are skipped); `BORER_BISECT_SHOW`, when set, prints the texts before
/// and after each breaking pass. One row per function the check rejects: the binary, the
/// name, then `pass <name>` and whether leaving it out alone repairs the
/// function (`alone`, `with-others`, or `unchecked` where the text without
/// it left every input unchecked), with the counterexample input, the line
/// and what differs; or `before-passes` when the text differs with every
/// pass left out. The table after the rows counts functions per first
/// breaking pass.
#[test]
#[ignore = "set BORER_BISECT to binary paths separated by ';' to run this harness"]
fn bisect_passes() {
    let paths = std::env::var("BORER_BISECT").expect("BORER_BISECT env var");
    let names = std::env::var("BORER_BISECT_NAMES").ok();
    let wanted: Option<Vec<&str>> = names.as_deref().map(|n| n.split(',').collect());
    let show = std::env::var_os("BORER_BISECT_SHOW").is_some();
    let mut table: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let (mut agree, mut skipped) = (0usize, 0usize);
    let t = Instant::now();
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let program = Program::load(std::path::Path::new(path)).expect("load");
        let a = Analysis::compute(&program);
        let o = Overlay::default();
        let bin = std::path::Path::new(path)
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        for f in a
            .functions
            .iter()
            .filter(|f| f.thunk.is_none() && f.funclet.is_none())
        {
            let name = name_of(&a, &o, f.entry);
            if wanted.as_ref().is_some_and(|w| !w.contains(&name.as_str())) {
                continue;
            }
            match bisect_iso(
                &program,
                &a,
                &o,
                f.entry,
                BISECT_INPUTS,
                ISO_SEED,
                ISO_STEPS,
            ) {
                Err(_) | Ok(Bisected::Unchecked(_)) => skipped += 1,
                Ok(Bisected::Agrees(_)) => agree += 1,
                Ok(Bisected::Unbisected(c)) => {
                    table.entry("(before passes)".to_owned()).or_default().0 += 1;
                    println!(
                        "{bin}\t{name}\tbefore-passes\t-\t{}\t{}\t{}",
                        c.input, c.line, c.why
                    );
                }
                Ok(Bisected::Unplaced { at, .. }) => {
                    table.entry("(unplaced)".to_owned()).or_default().0 += 1;
                    println!(
                        "{bin}\t{name}\tunplaced\t-\t{}\t{}\t{}",
                        at.input, at.line, at.why
                    );
                }
                Ok(Bisected::Broke {
                    pass,
                    at,
                    alone,
                    texts,
                    ..
                }) => {
                    if show {
                        println!("--- before {}\n{}", pass.name(), texts.0);
                        println!("--- after {}\n{}", pass.name(), texts.1);
                    }
                    let repairs = alone.grade();
                    let row = table.entry(pass.name().to_owned()).or_default();
                    row.0 += 1;
                    row.1 += usize::from(repairs == Grade::Agrees);
                    println!(
                        "{bin}\t{name}\tpass {}\t{}\t{}\t{}\t{}",
                        pass.name(),
                        match repairs {
                            Grade::Agrees => "alone",
                            Grade::Differs => "with-others",
                            Grade::Unchecked => "unchecked",
                        },
                        at.input,
                        at.line,
                        at.why
                    );
                }
            }
        }
    }
    println!(
        "# agree {agree}, skipped {skipped}, {:.1}s",
        t.elapsed().as_secs_f64()
    );
    println!("# first breaking pass\tfunctions\trepaired by leaving it out alone");
    let mut rows: Vec<(&String, &(usize, usize))> = table.iter().collect();
    rows.sort_by(|x, y| y.1.0.cmp(&x.1.0).then(x.0.cmp(y.0)));
    for (pass, (n, alone)) in rows {
        println!("{pass}\t{n}\t{alone}");
    }
}

/// Runs the full repair search ([`Budget::FULL`]) on every function of each
/// binary and reports how often it runs and what it costs.
///
/// `BORER_REPAIR` names the binaries, separated by `;`. One row per
/// function whose text disagrees: the binary, the name, `repaired` with the
/// sites the agreeing rendering moved, or `disagrees` with the note the
/// answer carries (`-` for none); then the renderings tried with their
/// evidence. The summary counts the functions the search ran on, the
/// repaired and the noted ones, and the time and checks per search, beside
/// the time of the first check every function pays.
#[test]
#[ignore = "set BORER_REPAIR to binary paths separated by ';' to run this harness"]
fn repair_search() {
    let paths = std::env::var("BORER_REPAIR").expect("BORER_REPAIR env var");
    let (mut agree, mut repaired, mut left, mut noted) = (0usize, 0usize, 0usize, 0usize);
    let (mut first, mut searched, mut checks) = (Vec::new(), Vec::new(), 0usize);
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let program = Program::load(std::path::Path::new(path)).expect("load");
        let a = Analysis::compute(&program);
        let o = Overlay::default();
        let bin = std::path::Path::new(path)
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        for f in a
            .functions
            .iter()
            .filter(|f| f.thunk.is_none() && f.funclet.is_none())
        {
            drop(decompile_named(&program, &a, &o, f.entry));
            let t = Instant::now();
            let r = repair_iso(&program, &a, &o, f.entry, Budget::FULL);
            let spent = t.elapsed();
            let name = name_of(&a, &o, f.entry);
            let frame = borer_engine::analysis::protos::frame_base(&program);
            let tried = |t: &[borer_engine::analysis::render::Tried]| {
                t.iter()
                    .map(|x| {
                        let sites: Vec<String> = x.sites.iter().map(|s| s.name(frame)).collect();
                        let ev = match &x.evidence {
                            Evidence::Tested(n) => format!("tested x{n}"),
                            Evidence::Refuted(c) => format!("refuted: {}", c.why),
                            Evidence::Unchecked => "unchecked".to_owned(),
                        };
                        format!("[{}: {ev}]", sites.join(" + "))
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            };
            match &r {
                Repair::Agrees => {
                    agree += 1;
                    first.push(spent);
                    continue;
                }
                Repair::Repaired {
                    moved, tried: t, ..
                } => {
                    repaired += 1;
                    let sites: Vec<String> = moved.iter().map(|s| s.name(frame)).collect();
                    println!("{bin}	{name}	repaired	{}	{}", sites.join(" + "), tried(t));
                }
                Repair::Disagrees { at, tried: t, .. } => {
                    left += 1;
                    noted += usize::from(r.note().is_some());
                    println!(
                        "{bin}	{name}	disagrees	{}	{} | {}",
                        r.note().unwrap_or_else(|| "-".to_owned()),
                        at.why,
                        tried(t)
                    );
                }
            }
            checks += r.checks();
            searched.push(spent);
        }
    }
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    let runs = searched.len();
    let total = runs + first.len();
    for v in [&mut first, &mut searched] {
        v.sort_unstable();
    }
    println!(
        "# {total} functions: {agree} agree, the search ran on {runs} ({:.1}%): {repaired} repaired, {left} still disagree ({noted} noted)",
        100.0 * usize_f64(runs) / usize_f64(total.max(1))
    );
    println!(
        "# first check: p50 {:.2} ms, p90 {:.2} ms; search: p50 {:.2} ms, p90 {:.2} ms, max {:.2} ms, {:.1} checks each",
        ms(percentile(&first, 50)),
        ms(percentile(&first, 90)),
        ms(percentile(&searched, 50)),
        ms(percentile(&searched, 90)),
        ms(searched.last().copied().unwrap_or_default()),
        usize_f64(checks) / usize_f64(runs.max(1))
    );
}

/// Functions [`mcp_latency`] samples per binary, evenly by entry, unless
/// `BORER_LATENCY_SAMPLE` names another count.
const LATENCY_SAMPLE: usize = 150;

/// Times one cold `decompile` answer per sampled function, the one the MCP
/// tool gives ([`answer`]), and hashes every answer so a speedup can be
/// shown to change no byte.
///
/// The answer is asked under the names the tool reads, the binary's own
/// name tables among them ([`EnumSource::Binary`]), before the tool pages
/// it.
///
/// `BORER_LATENCY` names the binaries, separated by `;`, and
/// `BORER_LATENCY_SAMPLE` how many functions to sample from each
/// ([`LATENCY_SAMPLE`] by default). Per binary it
/// prints the p50, p95 and mean of an answer, the first answer's time
/// (the one that finds the memo cold), and one hash over every
/// answer in entry order; with `BORER_LATENCY_OUT` set to a directory it
/// writes each answer's hash there, one `<entry>\t<hash>` line per
/// function. With `BORER_TIMING` set it prints the decompile step totals.
#[test]
#[ignore = "set BORER_LATENCY to binary paths separated by ';' to run this harness"]
fn mcp_latency() {
    use std::fmt::Write as _;
    use std::hash::{DefaultHasher, Hash, Hasher};
    let paths = std::env::var("BORER_LATENCY").expect("BORER_LATENCY env var");
    let out_dir = std::env::var_os("BORER_LATENCY_OUT");
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let program = Program::load(std::path::Path::new(path)).expect("load");
        let a = Analysis::compute(&program);
        let o = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        let all: Vec<u64> = a
            .functions
            .iter()
            .filter(|f| f.thunk.is_none() && f.funclet.is_none())
            .map(|f| f.entry)
            .collect();
        let sample = std::env::var("BORER_LATENCY_SAMPLE")
            .ok()
            .and_then(|n| n.parse::<usize>().ok())
            .unwrap_or(LATENCY_SAMPLE)
            .max(1);
        let stride = (all.len() / sample).max(1);
        let entries: Vec<u64> = all.iter().step_by(stride).take(sample).copied().collect();
        let mut times = Vec::with_capacity(entries.len());
        let mut whole = DefaultHasher::new();
        let mut rows = String::new();
        for &e in &entries {
            let t = Instant::now();
            let text = answer(&program, &a, &o, e, Detail::Full).unwrap_or_default();
            times.push(t.elapsed());
            let mut h = DefaultHasher::new();
            text.hash(&mut h);
            text.hash(&mut whole);
            writeln!(rows, "{e:#x}\t{:016x}", h.finish()).expect("write");
        }
        if let Some(dir) = &out_dir {
            let name = std::path::Path::new(path)
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default();
            std::fs::write(std::path::Path::new(dir).join(format!("{name}.tsv")), &rows)
                .expect("write hashes");
        }
        let ms = |d: Duration| d.as_secs_f64() * 1e3;
        let mean = times.iter().sum::<Duration>() / u32::try_from(times.len().max(1)).unwrap_or(1);
        let first = times.first().copied().unwrap_or_default();
        times.sort_unstable();
        println!(
            "latency\t{path}\t{}\tp50 {:.3}\tp95 {:.3}\tmean {:.3}\tfirst {:.3}\thash {:016x}",
            entries.len(),
            ms(percentile(&times, 50)),
            ms(percentile(&times, 95)),
            ms(mean),
            ms(first),
            whole.finish()
        );
    }
    if let Some(steps) = step_times() {
        print!("{steps}");
    }
}

/// Times one level of the call tree ([`call_children`]) for every
/// function of `BORER_CALLTREE`, at every
/// [`Level`](borer_engine::analysis::render::Level), and prints each
/// level's p95 and slowest.
///
/// Each level is timed on a fresh analysis, so the level with virtual
/// calls, which decompiles its node, finds the memo cold.
#[test]
#[ignore = "set BORER_CALLTREE to a binary path to run this harness"]
fn call_tree() {
    use borer_engine::analysis::render::{Level, call_children};
    let path = std::env::var("BORER_CALLTREE").expect("BORER_CALLTREE env var");
    let program = Program::load(std::path::Path::new(&path)).expect("load");
    let o = Overlay::default();
    for level in [Level::Callees, Level::Callers, Level::CalleesAndVirtuals] {
        let a = Analysis::compute(&program);
        let mut times: Vec<Duration> = a
            .functions
            .iter()
            .map(|f| {
                let t = Instant::now();
                let edges = call_children(&program, &a, &o, f.entry, level);
                let d = t.elapsed();
                drop(edges);
                d
            })
            .collect();
        times.sort_unstable();
        println!(
            "call tree	{level:?}	{} functions	p95 {:.3} ms	max {:.3} ms",
            times.len(),
            percentile(&times, 95).as_secs_f64() * 1e3,
            times.last().copied().unwrap_or_default().as_secs_f64() * 1e3
        );
    }
}

/// Reads every answer the catalog names as a listing on each binary of
/// `BORER_LISTING`.
///
/// Every stated place is held to a mapped address, an empty mark or a
/// file offset, and what the read and the classification cost is printed.
/// Per binary a line per answer: its rows, whether it names columns, the
/// stated place cells (addresses, empty marks), its first read and the
/// best of three classifications in microseconds, and the columns and
/// words no place states whose every filled cell is a mapped `0x` address,
/// for a statement to add. The last line sums the place cells.
#[test]
#[ignore = "set BORER_LISTING to binary paths separated by ';' to run this harness"]
fn listing() {
    use borer_engine::analysis::{hex_prefixed, parse_addr};
    use borer_engine::answer::catalog::{RESOURCE_TEMPLATES, RESOURCES, example, resource_name};
    use borer_engine::answer::{Page, listing, names, read};
    use borer_engine::table::{classify, columns_of};
    let paths = std::env::var("BORER_LISTING").expect("BORER_LISTING env var");
    let o = Overlay::default();
    let best = |f: &dyn Fn()| {
        (0..3)
            .map(|_| {
                let t = Instant::now();
                f();
                t.elapsed()
            })
            .min()
            .unwrap_or_default()
    };
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let p = Program::load(std::path::Path::new(path)).expect("load");
        let a = Analysis::compute(&p);
        let mapped = |cell: &str| {
            hex_prefixed(cell) && parse_addr(cell).is_some_and(|va| p.section_at(va).is_some())
        };
        let (mut places, mut empty) = (0usize, 0usize);
        let uris = RESOURCES
            .iter()
            .map(|r| r.0.to_owned())
            .chain(RESOURCE_TEMPLATES.iter().map(|t| example(t.2, Some(&p))))
            .filter(|uri| names().any(|n| n == resource_name(uri)));
        for uri in uris {
            let page = Page::whole(&uri);
            let cold = Instant::now();
            drop(read(&p, Some(&a), &o, &uri, page));
            let read_time = cold.elapsed();
            let Ok(l) = listing(&p, Some(&a), &o, &uri) else {
                println!("{path}\t{uri}\trefused");
                continue;
            };
            let (mut here, mut marks) = (0usize, 0usize);
            for row in 0..l.len() {
                for &at in l.places() {
                    match l.place(row, at) {
                        Some(va) => {
                            assert!(p.section_at(va).is_some(), "{uri} row {row}: {va:#x}");
                            here += 1;
                        }
                        None => {
                            let cell = l.cell(row, at).unwrap_or_default();
                            assert!(
                                EMPTY_MARKS.contains(&cell) || cell.starts_with("off="),
                                "{uri} row {row}: {cell}"
                            );
                            marks += 1;
                        }
                    }
                }
            }
            places += here;
            empty += marks;
            let (unstated, words) = unstated(&l, &mapped);
            let text = l.spell();
            let classify_time = best(&|| drop(columns_of(&classify(text))));
            println!(
                "{path}\t{uri}\t{} rows\t{}\t{here} places\t{marks} marks\tread {}us\tclassify {}us\tunstated {unstated:?} {words:?}",
                l.len(),
                if l.columns().is_some() {
                    "tab"
                } else {
                    "lines"
                },
                read_time.as_micros(),
                classify_time.as_micros()
            );
        }
        println!("{path}\ttotal\t{places} place cells\t{empty} empty marks");
    }
}

/// The cells [`listing`] counts as empty: what the renderers write where a
/// place column holds no address.
const EMPTY_MARKS: [&str; 2] = ["", "-"];

/// Returns the columns and the first four words of a listing that no place
/// states and whose every filled cell is a mapped `0x` address, for a
/// statement to add.
///
/// # Arguments
///
/// * `l` - The listing.
/// * `mapped` - Whether a cell is a `0x` address a section maps.
fn unstated<'l>(
    l: &'l borer_engine::answer::Listing,
    mapped: &dyn Fn(&str) -> bool,
) -> (Vec<&'l str>, Vec<usize>) {
    use borer_engine::answer::Place;
    let columns: Vec<&str> = l.columns().map_or(Vec::new(), |names| {
        names
            .iter()
            .enumerate()
            .filter(|(i, name)| {
                !l.places()
                    .iter()
                    .any(|at| matches!(at, Place::Column(c) if *c == name.as_str()))
                    && (0..l.len()).any(|r| {
                        l.fields(r)
                            .is_some_and(|f| f.get(*i).is_some_and(|c| !c.is_empty()))
                    })
                    && (0..l.len()).all(|r| {
                        l.fields(r)
                            .and_then(|f| f.get(*i).copied())
                            .is_none_or(|c| EMPTY_MARKS.contains(&c) || mapped(c))
                    })
            })
            .map(|(_, name)| name.as_str())
            .collect()
    });
    let words: Vec<usize> = (0..4)
        .filter(|n| {
            l.columns().is_none()
                && !l.places().contains(&Place::Word(*n))
                && !l.is_empty()
                && (0..l.len()).all(|r| {
                    l.fields(r)
                        .and_then(|f| f.first().and_then(|line| line.split_whitespace().nth(*n)))
                        .is_some_and(|w| EMPTY_MARKS.contains(&w) || mapped(w))
                })
        })
        .collect();
    (columns, words)
}
