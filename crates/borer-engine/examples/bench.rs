//! Engine benchmark: load, analyze and decompile one binary, single-threaded,
//! and print the timings on stdout.
//!
//! ```text
//! cargo run --release --example bench -- <binary>                  everything
//! cargo run --release --example bench -- <binary> --sample <file>  functions listed in <file>
//! cargo run --release --example bench -- <binary> --pick <n>       print n entry addresses
//! ```
//!
//! `--sample` takes one hex address per line (with or without `0x`) and
//! decompiles the function containing each, so one fixed set can be timed
//! across commits. `--pick` prints `n` evenly spaced function entries (at
//! least twenty instructions each) to make such a set.
//! Output lines are `key=value` pairs so a script can parse them.

#![expect(clippy::disallowed_methods, reason = "a benchmark measures time")]

use std::error::Error;
use std::time::Instant;

use borer_engine::analysis::{Analysis, Overlay, decompile::decompile};
use borer_engine::program::Program;

/// Parses a hex address with or without a `0x` prefix.
///
/// # Arguments
///
/// * `text` - The address text.
fn parse_hex(text: &str) -> Option<u64> {
    let t = text.trim();
    let t = t.strip_prefix("0x").unwrap_or(t);
    u64::from_str_radix(t, 16).ok()
}

/// Runs the benchmark described by the command line.
///
/// # Errors
///
/// When the binary or the sample file cannot be read, or the arguments are
/// not understood.
fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(path) = args.first() else {
        return Err("usage: bench <binary> [--sample <file> | --pick <n>]".into());
    };
    let t0 = Instant::now();
    let program = Program::load(std::path::Path::new(path))?;
    let load_ms = t0.elapsed().as_millis();
    let t1 = Instant::now();
    let analysis = Analysis::compute(&program);
    let analysis_ms = t1.elapsed().as_millis();
    println!("load_ms={load_ms}");
    println!("analysis_ms={analysis_ms}");
    println!("functions={}", analysis.functions.len());
    println!("incomplete={}", analysis.incomplete);

    let mode = args.get(1).map(String::as_str);
    if mode == Some("--pick") {
        let n: usize = args.get(2).ok_or("--pick needs a count")?.parse()?;
        let eligible: Vec<u64> = analysis
            .functions
            .iter()
            .filter(|f| f.instr_count >= 20)
            .map(|f| f.entry)
            .collect();
        let step = (eligible.len() / n.max(1)).max(1);
        for entry in eligible.iter().step_by(step).take(n) {
            println!("{entry:x}");
        }
        return Ok(());
    }

    let targets: Vec<u64> = if mode == Some("--sample") {
        let file = args.get(2).ok_or("--sample needs a file")?;
        std::fs::read_to_string(file)?
            .lines()
            .filter_map(parse_hex)
            .filter_map(|va| analysis.function_at(va).map(|f| f.entry))
            .collect()
    } else {
        analysis.functions.iter().map(|f| f.entry).collect()
    };
    let overlay = Overlay::default();
    let t2 = Instant::now();
    let (mut ok, mut failed, mut bytes, mut lines) = (0usize, 0usize, 0usize, 0usize);
    for entry in &targets {
        match decompile(&program, &analysis, &overlay, *entry) {
            Some(text) => {
                ok += 1;
                bytes += text.len();
                lines += text.lines().count();
            }
            None => failed += 1,
        }
    }
    let ms = t2.elapsed().as_millis();
    println!(
        "decompile n={} ok={ok} failed={failed} ms={ms} bytes={bytes} lines={lines}",
        targets.len()
    );
    Ok(())
}
