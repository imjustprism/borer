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
//! builds it, and hashes every answer ([`mcp_latency`]).
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

use borer_engine::analysis::decompile::{
    checked_header, decompile_all, decompile_named, step_times, text_check, warnings, with_header,
};
use borer_engine::analysis::render::{
    Bisected, Budget, Evidence, INCOMPLETE_NOTE, Repair, Verdict, answered, bisect_iso,
    check_generated, check_generated_iso, next_steps, repair_iso,
};
use borer_engine::analysis::{Analysis, Overlay, name_of};
use borer_engine::num::usize_f64;
use borer_engine::program::Program;
use std::collections::BTreeMap;
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
/// function, with the counterexample input, the line and what differs; or
/// `before-passes` when the text differs with every pass left out. The
/// table after the rows counts functions per first breaking pass.
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
                Err(_) => skipped += 1,
                Ok(Bisected::Agrees) => agree += 1,
                Ok(Bisected::Unbisected(c)) => {
                    table.entry("(before passes)".to_owned()).or_default().0 += 1;
                    println!(
                        "{bin}\t{name}\tbefore-passes\t-\t{}\t{}\t{}",
                        c.input, c.line, c.why
                    );
                }
                Ok(Bisected::Broke {
                    pass,
                    at,
                    alone,
                    texts,
                }) => {
                    if show {
                        println!("--- before {}\n{}", pass.name(), texts.0);
                        println!("--- after {}\n{}", pass.name(), texts.1);
                    }
                    let row = table.entry(pass.name().to_owned()).or_default();
                    row.0 += 1;
                    row.1 += usize::from(alone);
                    println!(
                        "{bin}\t{name}\tpass {}\t{}\t{}\t{}\t{}",
                        pass.name(),
                        if alone { "alone" } else { "with-others" },
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
            let tried = |t: &[borer_engine::analysis::render::Tried]| {
                t.iter()
                    .map(|x| {
                        let sites: Vec<String> = x.sites.iter().map(|s| s.name()).collect();
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
                    let sites: Vec<String> = moved.iter().map(|s| s.name()).collect();
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

/// Builds one `decompile` answer the way the MCP tool does.
///
/// That is the names the repair search renders it under ([`answered`]),
/// then the check line, the incomplete note, the warnings and the next
/// steps over the text, then the text.
///
/// # Arguments
///
/// * `program` - The image.
/// * `a` - Its analysis.
/// * `user` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The answer, empty when the function does not decompile.
fn mcp_answer(program: &Program, a: &Analysis, user: &Overlay, entry: u64) -> String {
    let (o, differs) = answered(program, a, user, entry);
    let o = &o;
    let mut lines: Vec<String> = checked_header(program, a, o, entry)
        .into_iter()
        .chain(
            a.incomplete
                .then(|| format!("//{}", INCOMPLETE_NOTE.trim_start_matches('#'))),
        )
        .collect();
    lines.extend(
        decompile_named(program, a, o, entry)
            .and_then(|text| warnings(program, a, o, entry, &text, differs.as_deref())),
    );
    lines.extend(
        next_steps(program, a, o, entry)
            .iter()
            .map(|step| format!("// next: {step}")),
    );
    let header = (!lines.is_empty()).then(|| lines.join("\n"));
    decompile_named(program, a, o, entry)
        .map(|text| with_header(&text, header.as_deref()))
        .unwrap_or_default()
}

/// Times one cold `decompile` answer per sampled function, as the MCP tool
/// builds it, and hashes every answer so a speedup can be shown to change
/// no byte.
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
        let o = Overlay::default();
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
            let answer = mcp_answer(&program, &a, &o, e);
            times.push(t.elapsed());
            let mut h = DefaultHasher::new();
            answer.hash(&mut h);
            answer.hash(&mut whole);
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
