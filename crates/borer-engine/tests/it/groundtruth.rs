//! Ground-truth fidelity: decompile the compiler-emitted `check_serial` from
//! the crackme example and verify the pseudo-C matches the source shape.
//!
//! The function is located by its final-comparison constant: the optimizer
//! folds const-slice reads, so the marker string has no stable xref
//! (documented known gap).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay, decompile::decompile, render::run_tsv};
use borer_engine::program::Program;
use borer_engine::search::{find_bytes, parse_pattern};

/// Finds the crackme, the `borer-fixtures` example that `cargo test
/// --workspace` builds unoptimized (the workspace profile pins that package
/// to level 0, the code shape this test checks).
///
/// The examples sit beside this test binary's own directory
/// (`<target>/debug/deps/` holds the test, `<target>/debug/examples/` the
/// examples), so the search follows wherever cargo put the build, a
/// `CARGO_TARGET_DIR` included.
///
/// # Returns
///
/// The path of `crackme.exe` or `crackme-<hash>.exe`, or `None` when the
/// examples directory is missing.
fn crackme_exe() -> Option<std::path::PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?.parent()?.join("examples");
    let rd = std::fs::read_dir(dir.as_path()).ok()?;
    let mut hits: Vec<std::path::PathBuf> = rd.filter_map(|e| e.ok().map(|x| x.path())).collect();
    hits.sort();
    hits.into_iter().find(|p| {
        let n = p
            .file_name()
            .map(|x| x.to_string_lossy().to_string())
            .unwrap_or_default();
        (n == "crackme.exe" || n.starts_with("crackme-")) && n.ends_with(".exe")
    })
}

/// The decompiled `check_serial` keeps the shape of its source.
///
/// It returns the `== 0xdeadbeef` comparison, structures the loop, keeps the
/// `^=` accumulation, shows the checked `i * 4` as an overflow test, leaks no
/// unknown flags or temporaries, and keeps bare copies (debug codegen) to a
/// minority of the body. A constant load (`x = 5;`) is not a copy.
#[test]
#[cfg_attr(
    not(debug_assertions),
    ignore = "the crackme's shape is that of its dev build; a release build links it with LTO"
)]
#[cfg_attr(
    all(debug_assertions, not(windows)),
    ignore = "the crackme's shape is that of its Windows x64 dev build"
)]
fn decompiled_serial_check_matches_source_shape() {
    let Some(exe) = crackme_exe() else {
        panic!("crackme example not built; run cargo build -p borer-fixtures --examples");
    };
    // INVARIANT: the dev build's PDB sits beside the exe and its names are
    // not the dev-shape facts these tests pin.
    let p = Program::load_with(&exe, false).expect("load crackme");
    let a = Analysis::compute(&p);

    let pat = parse_pattern("b8 ef be ad de").expect("pattern");
    let hits = find_bytes(&p, &pat, 0).hits;
    let va = hits
        .iter()
        .find_map(|h| h.va)
        .expect("deadbeef compare present");
    let f = a
        .function_at(va)
        .expect("compare lands inside a discovered function");

    let out = decompile(&p, &a, &Overlay::default(), f.entry).expect("decompile");

    assert!(
        out.lines()
            .any(|l| l.trim().starts_with("return ") && l.contains("== 0xdeadbeef")),
        "final comparison not returned:
{out}"
    );
    assert!(
        out.contains("while (1) {") || out.contains("for ("),
        "loop not structured:
{out}"
    );
    assert!(
        out.lines().any(|l| l.contains(" ^= ")),
        "xor accumulation missing:
{out}"
    );
    assert!(
        out.contains("mulhi64(") || out.contains("smulo64("),
        "overflow check missing:
{out}"
    );
    assert!(
        !out.contains("FLAGS_UNKNOWN") && !out.contains("tmp_"),
        "unknown flags or temporaries leaked:
{out}"
    );
    let body: Vec<&str> = out
        .lines()
        .filter(|l| {
            let t = l.trim();
            !t.starts_with("//") && !t.starts_with("uint") && !t.is_empty()
        })
        .collect();
    let copies = body
        .iter()
        .filter(|l| {
            l.trim()
                .strip_suffix(';')
                .and_then(|s| s.split_once(" = "))
                .is_some_and(|(a, b)| {
                    let ident = |s: &str| {
                        !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    };
                    let literal = b.strip_prefix("0x").unwrap_or(b);
                    ident(a) && ident(b) && !literal.chars().all(|c| c.is_ascii_digit())
                })
        })
        .count();
    assert!(
        copies * 100 <= body.len() * 26,
        "too many bare copies ({copies} of {}):
{out}",
        body.len()
    );
}

/// A run of `check_serial` answers what the binary computes on each key.
///
/// Its decompiled text is read to the end of every path the keys take: each
/// row says whether the text agrees or where it differs, never that a line
/// could not be read.
#[test]
#[cfg_attr(
    not(debug_assertions),
    ignore = "the crackme's shape is that of its dev build; a release build links it with LTO"
)]
#[cfg_attr(
    all(debug_assertions, not(windows)),
    ignore = "the crackme's shape is that of its Windows x64 dev build"
)]
fn the_serial_check_runs_and_its_text_is_read() {
    let Some(exe) = crackme_exe() else {
        panic!("crackme example not built; run cargo build -p borer-fixtures --examples");
    };
    // INVARIANT: the dev build's PDB sits beside the exe and its names are
    // not the dev-shape facts these tests pin.
    let p = Program::load_with(&exe, false).expect("load crackme");
    let a = Analysis::compute(&p);
    let pat = parse_pattern("b8 ef be ad de").expect("pattern");
    let va = find_bytes(&p, &pat, 0)
        .hits
        .iter()
        .find_map(|h| h.va)
        .expect("deadbeef compare present");
    let entry = a.function_at(va).expect("a function").entry;
    let o = Overlay::default();
    let out = run_tsv(&p, &a, &o, &format!("{entry:#x}/0;1;0xdeadbeef")).expect("runs");
    let rows: Vec<Vec<&str>> = out
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| l.split('\t').collect())
        .collect();
    assert_eq!(rows.len(), 3, "{out}");
    for row in &rows {
        assert_eq!(row.get(1..3), Some(&["0", "returned"][..]), "{out}");
        let text = row.last().copied().unwrap_or("");
        assert!(
            text == "agrees" || text.starts_with("differs@L"),
            "the text was not read to the end: {out}"
        );
    }
    assert_eq!(
        out,
        run_tsv(&p, &a, &o, &format!("{entry:#x}/0;1;0xdeadbeef")).expect("runs")
    );
}
