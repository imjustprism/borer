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

/// The identifiers outside every generic argument list of a name, without
/// the words the two Rust name spellings differ in (`{closure#0}` and
/// `closure$0`, `impl$2`, `{shim:vtable#0}`).
///
/// # Arguments
///
/// * `name` - A demangled name.
/// * `outer` - Whether to leave out what sits between angle brackets.
fn name_words(name: &str, outer: bool) -> Vec<&str> {
    /// Words one spelling has and the other does not.
    const NOISE: &[&str] = &[
        "closure",
        "closure_env",
        "impl",
        "enum2",
        "tuple",
        "ref",
        "ref_mut",
        "slice2",
        "str",
        "dyn",
        "as",
        "mut",
        "shim",
        "vtable",
        "__rustc",
        "_",
    ];
    let mut depth = 0usize;
    let mut out = Vec::new();
    let mut start = None;
    for (i, c) in name.char_indices().chain([(name.len(), ' ')]) {
        let ident = c.is_ascii_alphanumeric() || c == '_';
        if ident && start.is_none() {
            start = Some(i);
        }
        if !ident && let Some(from) = start.take() {
            let w = &name[from..i];
            if (!outer || depth == 0)
                && !NOISE.contains(&w)
                && !w.bytes().all(|b| b.is_ascii_digit())
            {
                out.push(w);
            }
        }
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    out
}

/// Reads the public function names a PDB gives each address.
///
/// # Arguments
///
/// * `path` - The PDB.
/// * `base` - The image base its addresses are relative to.
///
/// # Returns
///
/// The names by address, or `None` when the PDB does not read.
fn pdb_publics(
    path: &std::path::Path,
    base: u64,
) -> Option<std::collections::BTreeMap<u64, Vec<String>>> {
    use pdb::FallibleIterator;
    let mut pdb = pdb::PDB::open(std::fs::File::open(path).ok()?).ok()?;
    let map = pdb.address_map().ok()?;
    let globals = pdb.global_symbols().ok()?;
    let mut out: std::collections::BTreeMap<u64, Vec<String>> = std::collections::BTreeMap::new();
    let mut it = globals.iter();
    while let Some(s) = it.next().ok()? {
        if let Ok(pdb::SymbolData::Public(p)) = s.parse()
            && p.function
            && let Some(rva) = p.offset.to_rva(&map)
        {
            out.entry(base + u64::from(rva.0))
                .or_default()
                .push(p.name.to_string().into_owned());
        }
    }
    Some(out)
}

/// The shipped Rust set names the standard library's functions in a Rust
/// program built by the toolchain it was read from, and every name it
/// gives is the one the program's PDB has there.
///
/// The crackme is loaded without its PDB, so nothing names its functions
/// but the set; loaded with it, the PDB says what each entry is, under
/// every name it gives the address (`rust_begin_unwind` is the link name
/// of `std::panicking::panic_handler`). Two
/// spellings of one function (the set's v0 names demangled, the PDB's
/// MSVC-style ones) agree on the last word outside every argument list,
/// and every outer word of the PDB's name is among the set's words.
#[test]
#[cfg_attr(
    not(debug_assertions),
    ignore = "the crackme is built by the dev profile with the pinned toolchain the set was read from"
)]
#[cfg_attr(
    all(debug_assertions, not(windows)),
    ignore = "the shipped Rust set is for Windows x64"
)]
fn the_shipped_rust_set_names_the_crackme_as_its_pdb_does() {
    use borer_engine::analysis::NameSource;
    let Some(exe) = crackme_exe() else {
        panic!("crackme example not built; run cargo build -p borer-fixtures --examples");
    };
    let bare = Program::load_with(&exe, false).expect("load crackme");
    let a = Analysis::compute(&bare);
    let truth = Analysis::compute(&Program::load(&exe).expect("load crackme with its PDB"));
    let publics = pdb_publics(&exe.with_extension("pdb"), bare.image_base).expect("the PDB reads");
    let named: Vec<(u64, String)> = a
        .functions
        .iter()
        .filter(|f| f.name_source == NameSource::Library)
        .filter_map(|f| Some((f.entry, f.name.clone()?)))
        .collect();
    assert!(named.len() >= 100, "{} named", named.len());
    let wrong: Vec<String> = named
        .iter()
        .filter_map(|(entry, got)| {
            let wants: Vec<String> = truth
                .function(*entry)
                .and_then(|f| f.name.clone())
                .into_iter()
                .chain(
                    publics
                        .get(entry)
                        .into_iter()
                        .flatten()
                        .map(|n| borer_engine::search::demangled_name(n)),
                )
                .collect();
            let og = name_words(got, true);
            let agree = wants.iter().any(|want| {
                let ow = name_words(want, true);
                og.last().is_some()
                    && og.last() == ow.last()
                    && (ow.iter().all(|w| name_words(got, false).contains(w))
                        || og.iter().all(|w| name_words(want, false).contains(w)))
            });
            (!agree).then(|| format!("{entry:#x}: {got} where the PDB says {}", wants.join(" | ")))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
