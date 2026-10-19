//! Golden sweep: hashes every function's decompile across a set of binaries,
//! to prove a refactor of the emitter leaves the text byte-identical.
//!
//! ```text
//! BORER_GOLDEN="a.exe;b.dll" BORER_GOLDEN_OUT=after.tsv \
//!   BORER_GOLDEN_BASE=before.tsv cargo test --test golden -- --ignored --nocapture
//! ```
//!
//! Each row of the output is `binary`, `entry`, the hash of the
//! [`decompile_all`] text and the hash of the [`decompile_named_all`] text,
//! tab-separated, in address order. With `BORER_GOLDEN_BASE` set, the sweep
//! compares its rows with that file and fails on the first rows that
//! differ. `BORER_GOLDEN_DUMP` names a directory that receives every text,
//! one file per binary, to diff a function the hashes flag.
//!
//! The binaries must be the same bytes before and after: the server binary
//! the gate sweeps is rebuilt by every change, so copy it once and sweep
//! the copy.

#![expect(clippy::disallowed_methods, reason = "the sweep reports its own time")]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{
    Analysis, Overlay,
    decompile::{decompile_all, decompile_named_all},
};
use borer_engine::program::Program;
use std::fmt::Write as _;

/// Returns the 64-bit FNV-1a hash of a text, or 0 for no text.
///
/// # Arguments
///
/// * `text` - A decompile result.
fn fnv(text: Option<&str>) -> u64 {
    /// The FNV-1a 64-bit offset basis.
    const BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    /// The FNV-1a 64-bit prime.
    const PRIME: u64 = 0x0100_0000_01b3;
    text.map_or(0, |t| {
        t.bytes()
            .fold(BASIS, |h, b| (h ^ u64::from(b)).wrapping_mul(PRIME))
    })
}

/// Hashes every function of every `BORER_GOLDEN` binary and compares the
/// rows with `BORER_GOLDEN_BASE` when it is set.
#[test]
#[ignore = "set BORER_GOLDEN to binary paths to run this sweep"]
fn every_function_decompiles_to_the_recorded_bytes() {
    let paths = std::env::var("BORER_GOLDEN").expect("BORER_GOLDEN env var");
    let dump = std::env::var("BORER_GOLDEN_DUMP").ok();
    let mut rows = String::new();
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let p = Program::load_with(std::path::Path::new(path), false).expect("load");
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
        let t0 = std::time::Instant::now();
        let plain = decompile_all(&p, &a, &o, &entries);
        let plain_t = t0.elapsed();
        let t1 = std::time::Instant::now();
        let named = decompile_named_all(&p, &a, &o, &entries);
        let named_t = t1.elapsed();
        let name = std::path::Path::new(path)
            .file_name()
            .map_or_else(|| path.to_owned(), |n| n.to_string_lossy().into_owned());
        println!(
            "{name}: {} functions, decompile-all {plain_t:?}, named {named_t:?}",
            entries.len()
        );
        let mut texts = String::new();
        for ((entry, one), two) in entries.iter().zip(&plain).zip(&named) {
            writeln!(
                rows,
                "{name}\t{entry:#x}\t{:016x}\t{:016x}",
                fnv(one.as_deref()),
                fnv(two.as_deref())
            )
            .expect("write to a string");
            if dump.is_some() {
                writeln!(
                    texts,
                    "===== {entry:#x}\n{}\n===== named\n{}",
                    one.as_deref().unwrap_or(""),
                    two.as_deref().unwrap_or("")
                )
                .expect("write to a string");
            }
        }
        if let Some(dir) = &dump {
            std::fs::write(std::path::Path::new(dir).join(format!("{name}.txt")), texts)
                .expect("write the dump");
        }
    }
    if let Ok(out) = std::env::var("BORER_GOLDEN_OUT") {
        std::fs::write(out, &rows).expect("write the rows");
    }
    let Ok(base) = std::env::var("BORER_GOLDEN_BASE") else {
        return;
    };
    let base = std::fs::read_to_string(base).expect("read the base rows");
    let differ: Vec<String> = base
        .lines()
        .zip(rows.lines())
        .filter(|(a, b)| a != b)
        .map(|(a, b)| format!("{a}  ->  {b}"))
        .collect();
    assert_eq!(
        base.lines().count(),
        rows.lines().count(),
        "the sweep found a different set of functions"
    );
    assert!(
        differ.is_empty(),
        "{} functions differ, first: {:#?}",
        differ.len(),
        differ.iter().take(20).collect::<Vec<_>>()
    );
}
