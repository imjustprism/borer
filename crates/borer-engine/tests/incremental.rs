//! Incremental replay: what one rename costs the next decompiles.
//!
//! ```text
//! BORER_INCREMENTAL=path/to/bin cargo test -p borer-engine --release \
//!   --test incremental -- --ignored --nocapture
//! ```
//!
//! Decompiles a slice of the binary the way the server's `decompile_batch`
//! does, renames one function, and decompiles the slice again, twice: once
//! letting go of every result read under the old names
//! ([`Derived::forget_names_but`], what a rename did before results kept
//! their read-sets) and once carrying the results whose reads miss the
//! rename ([`Derived::moved`]). It does so for several functions of the
//! slice, prints the builds and the time of each replay, and fails when
//! the two replays' texts differ by a byte.

#![expect(clippy::disallowed_methods, reason = "the replay reports its own time")]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::{Analysis, Derived, EnumSource, Overlay};
use borer_engine::program::Program;
use std::time::{Duration, Instant};

/// Functions in the replayed slice.
const SLICE: usize = 200;

/// Functions of the slice renamed, one at a time.
const RENAMES: usize = 8;

/// How the analysis lets go of results after the rename.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Every result read under the old names goes.
    Forget,
    /// Results whose reads miss the rename are carried over.
    Carry,
}

/// What one replay measured.
#[derive(Debug)]
struct Replay {
    /// The slice's texts after the rename.
    texts: Vec<Option<String>>,
    /// Results built by the replay after the rename.
    builds: u64,
    /// Time the replay after the rename took.
    replay: Duration,
}

/// Decompiles `entries` under `before`, applies the rename `after` by
/// `mode`, and decompiles them again.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, whose memo is emptied first.
/// * `entries` - The slice.
/// * `before` - The overlay before the rename.
/// * `after` - The overlay after it.
/// * `mode` - How results are let go.
fn replay(
    p: &Program,
    a: &mut Analysis,
    entries: &[u64],
    before: &Overlay,
    after: &Overlay,
    mode: Mode,
) -> Replay {
    a.derived = Derived::default();
    for &e in entries {
        decompile_named(p, a, before, e);
    }
    match mode {
        Mode::Forget => a.derived.forget_names_but(after),
        Mode::Carry => a.derived.moved(a, before, after),
    }
    let start = a.derived.builds();
    let t = Instant::now();
    let texts = entries
        .iter()
        .map(|&e| decompile_named(p, a, after, e))
        .collect();
    Replay {
        texts,
        builds: a.derived.builds() - start,
        replay: t.elapsed(),
    }
}

/// Replays a slice of `BORER_INCREMENTAL` across renames of several of its
/// functions both ways and reports the builds and times.
#[test]
#[ignore = "set BORER_INCREMENTAL to a binary path to run this replay"]
fn a_rename_rebuilds_only_what_read_the_name() {
    let path = std::env::var("BORER_INCREMENTAL").expect("BORER_INCREMENTAL env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let mut a = Analysis::compute(&p);
    let step = (a.functions.len() / SLICE).max(1);
    let entries: Vec<u64> = a
        .functions
        .iter()
        .step_by(step)
        .take(SLICE)
        .map(|f| f.entry)
        .collect();
    let before = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let warm = Instant::now();
    for &e in &entries {
        decompile_named(&p, &a, &before, e);
    }
    let warm = warm.elapsed();
    let stats = a.derived.read_stats();
    println!(
        "{path}: {} functions, slice of {}: {} builds in {warm:?}, {} item bytes; read-sets of {} results: {} keys, {} bytes, {} read every name",
        a.functions.len(),
        entries.len(),
        a.derived.builds(),
        a.derived.item_bytes(),
        stats.results,
        stats.keys,
        stats.bytes,
        stats.names_whole
    );
    let callers = |target: u64| {
        a.xrefs_to(target)
            .iter()
            .filter(|r| r.from_entry.is_some_and(|e| entries.contains(&e)))
            .count()
    };
    let most_called = entries
        .iter()
        .copied()
        .max_by_key(|&e| (callers(e), std::cmp::Reverse(e)))
        .expect("a function");
    let targets: Vec<(u64, usize)> = std::iter::once(most_called)
        .chain(
            entries
                .iter()
                .copied()
                .step_by(SLICE / RENAMES)
                .take(RENAMES - 1),
        )
        .map(|t| (t, callers(t)))
        .collect();
    let (mut forget_builds, mut carry_builds) = (0, 0);
    let (mut forget_time, mut carry_time) = (Duration::ZERO, Duration::ZERO);
    for (target, refs) in targets {
        let mut after = before.clone();
        after.names.insert(target, "renamed_by_replay".to_owned());
        let forget = replay(&p, &mut a, &entries, &before, &after, Mode::Forget);
        let carry = replay(&p, &mut a, &entries, &before, &after, Mode::Carry);
        println!(
            "  rename {target:#x} ({refs} references from the slice): forget {} builds in {:?}, carry {} builds in {:?}",
            forget.builds, forget.replay, carry.builds, carry.replay
        );
        let differ: Vec<String> = forget
            .texts
            .iter()
            .zip(&carry.texts)
            .zip(&entries)
            .filter(|((f, c), _)| f != c)
            .map(|(_, e)| format!("{e:#x}"))
            .collect();
        assert!(
            differ.is_empty(),
            "renaming {target:#x}: texts differ at {differ:?}"
        );
        forget_builds += forget.builds;
        carry_builds += carry.builds;
        forget_time += forget.replay;
        carry_time += carry.replay;
    }
    let per = |d: Duration| d / u32::try_from(RENAMES * SLICE).expect("fits");
    println!(
        "  over {RENAMES} renames: forget {forget_builds} builds, {:?} a decompile; carry {carry_builds} builds, {:?} a decompile",
        per(forget_time),
        per(carry_time)
    );
}
