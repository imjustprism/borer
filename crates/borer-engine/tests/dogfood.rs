//! Dogfood sweep: decompile every discovered function in a real binary and
//! count failures. Run explicitly:
//!
//! ```text
//! BORER_DOGFOOD=path/to/bin cargo test --test dogfood -- --ignored --nocapture
//! ```
//!
//! Besides "did it produce text", every function's text must be well formed:
//! each `goto L_x;` has its label in the same function, braces balance
//! (string literals excluded), and every callee the analysis found is named
//! somewhere in the text. All three were real bugs once (blocks skipped by
//! the old address-order driver; a cleanup pass with stale indices; a
//! register-to-register `movss` that killed the vector under it and, with
//! it, the call that had loaded it).

#![expect(
    clippy::disallowed_methods,
    reason = "the sweeps report and bound their own time"
)]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{
    Analysis, Overlay, decompile::decompile, decompile::decompile_all,
    decompile::decompile_named_all, name_of, render,
};
use borer_engine::program::Program;
use std::collections::BTreeSet;

mod common;
#[path = "common/gotos.rs"]
mod gotos;

use gotos::{dangling_gotos, without_strings};

/// Returns the net brace depth of the text with string literals blanked out.
///
/// # Arguments
///
/// * `text` - Pseudo-C text.
fn brace_imbalance(text: &str) -> i64 {
    without_strings(text).chars().fold(0i64, |d, c| match c {
        '{' => d + 1,
        '}' => d - 1,
        _ => d,
    })
}

/// Lists the callees whose name the text never says.
///
/// A call in the code and not in the text is code the reader never sees.
/// Two things are not that: a function whose header says it left unreachable
/// blocks out, and the smart-pointer accessors borer folds into the
/// expression that reads through them.
///
/// # Arguments
///
/// * `analysis` - The program's analysis.
/// * `overlay` - The names in force.
/// * `callees` - The function's callees.
/// * `text` - Its pseudo-C.
///
/// # Returns
///
/// The names that are missing, at most a few.
/// Lists the `local_N`/`arg_N` slot names a code line uses but no
/// declaration line declares.
///
/// A stack slot named in the body must be declared, or the text is not valid
/// C. Names in `//` comment lines (the escape note) do not count, since they
/// are not code.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
///
/// # Returns
///
/// The undeclared slot names, without duplicates.
fn undeclared_slots(text: &str) -> Vec<String> {
    let is_slot = |w: &str| {
        w.split_once('_').is_some_and(|(head, digits)| {
            matches!(head, "local" | "home" | "arg")
                && !digits.is_empty()
                && digits.bytes().all(|b| b.is_ascii_hexdigit())
        })
    };
    let tokens = |line: &str| {
        line.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .filter(|w| is_slot(w))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    let mut declared: BTreeSet<String> = BTreeSet::new();
    let mut used: BTreeSet<String> = BTreeSet::new();
    for line in text.lines() {
        let t = line.trim_start();
        if t.starts_with("//") {
            continue;
        }
        let decl = matches!(
            t.split_whitespace().next(),
            Some(w) if w.starts_with("uint") || w.starts_with("int") || w == "float"
                || w == "double" || w == "bool" || w == "char" || w == "void"
        ) && t.ends_with(';')
            && !t.contains('=')
            && !t.contains('(');
        for w in tokens(line) {
            if decl {
                declared.insert(w);
            } else {
                used.insert(w);
            }
        }
    }
    used.difference(&declared).cloned().collect()
}

/// `sub_` names run straight into an identifier, outside strings: a pass that
/// dropped the parentheses of a call leaves `sub_140de64a8rdi`, which is no
/// C and names no function.
///
/// The deliberate `__rdx` suffix a second result renders under is the one
/// glued shape that names a function on purpose.
fn glued_names(text: &str) -> Vec<String> {
    let body = without_strings(text);
    let mut out: Vec<String> = body
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|w| {
            w.strip_prefix("sub_").is_some_and(|rest| {
                let hex = rest.chars().take_while(char::is_ascii_hexdigit).count();
                let tail = rest.get(hex..).unwrap_or("");
                let numbered = tail
                    .strip_prefix('_')
                    .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()));
                hex > 0 && !tail.is_empty() && !numbered && tail != "__rdx"
            })
        })
        .map(str::to_owned)
        .collect();
    out.sort();
    out.dedup();
    out
}

/// Lift-pass temporaries (`tmp_` with an id at or above `1 << 30`) that leaked
/// into the text; the `polish` pass should renumber every one, so any here is a
/// regression.
fn leaked_temps(text: &str) -> Vec<String> {
    const LIFT_TMP_BASE: u64 = 1 << 30;
    let mut out: Vec<String> = text
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter_map(|w| {
            let digits = w.strip_prefix("tmp_")?;
            let id: u64 = digits.parse().ok()?;
            (id >= LIFT_TMP_BASE).then(|| w.to_owned())
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

fn missing_calls(
    analysis: &Analysis,
    overlay: &Overlay,
    function: &borer_engine::analysis::Function,
    text: &str,
) -> Vec<String> {
    if text.contains("unreachable blocks omitted") {
        return Vec::new();
    }
    let mut out = Vec::new();
    for c in &function.callees {
        // Two functions can overlap: a compiler gives the tail of one its own
        // unwind entry, so an address is both a block of the outer function
        // and an entry of its own. A jump to it is internal control flow
        // there, which the renderer spells as a `goto` and elides when the
        // block follows, so no name is expected in the text.
        if function.blocks.iter().any(|b| b.start == *c) {
            continue;
        }
        let name = name_of(analysis, overlay, *c);
        // A frame helper is inlined: the prologue builds the caller's frame
        // and the epilogue tears it down, and neither is a call the text
        // shows.
        if name.contains("operator ")
            || matches!(
                name.as_str(),
                "__SEH_prolog4" | "__EH_prolog3" | "__SEH_epilog4" | "__EH_epilog3"
            )
        {
            continue;
        }
        let bare = name
            .rsplit("::")
            .next()
            .unwrap_or(&name)
            .rsplit('!')
            .next()
            .unwrap_or(&name);
        if !text.contains(bare) && !text.contains(&format!("{c:#x}")) {
            out.push(name);
        }
    }
    out
}

/// Decompiles every function of the `BORER_DOGFOOD` binary, prints timings
/// and the first failures, and requires zero failures and well-formed text.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_same_binary_answers_the_same_bytes_twice() {
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    // Two analyses of one program, in one process, so the addresses the
    // allocator hands out differ between them. A map keyed on a pointer, or
    // iterated in hash order, answers differently here and nowhere else.
    let first = Analysis::compute(&p);
    let second = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        first.functions.len(),
        second.functions.len(),
        "function discovery is not deterministic"
    );
    let entry = p
        .entry
        .unwrap_or_else(|| first.functions.first().map_or(0, |f| f.entry));
    // One case per renderer family, so a difference names the renderer.
    let cases: Vec<(&str, String, String)> = vec![
        ("binary_info", p.summary(), p.summary()),
        (
            "functions",
            render::functions_tsv(&first, &o, None, render::FunctionOrder::Address, 0, 100).2,
            render::functions_tsv(&second, &o, None, render::FunctionOrder::Address, 0, 100).2,
        ),
        (
            "crypto",
            render::crypto_tsv(&p, &first, &o, 0, 200),
            render::crypto_tsv(&p, &second, &o, 0, 200),
        ),
        (
            "decompile",
            decompile(&p, &first, &o, entry).unwrap_or_default(),
            decompile(&p, &second, &o, entry).unwrap_or_default(),
        ),
        (
            "why",
            render::why_tsv(&p, &first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::why_tsv(&p, &second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "layout",
            render::layout_tsv(&p, &first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::layout_tsv(&p, &second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "taint",
            render::taint_tsv(&p, &first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::taint_tsv(&p, &second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "oracle",
            render::oracle_tsv(&p, &first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::oracle_tsv(&p, &second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "emulate",
            render::emulate_tsv(&p, &first, &o, &format!("{entry:#x},steps=20000"))
                .unwrap_or_else(|e| e),
            render::emulate_tsv(&p, &second, &o, &format!("{entry:#x},steps=20000"))
                .unwrap_or_else(|e| e),
        ),
        (
            "hidden",
            render::hidden_strings_tsv(&p, &first, &o, ""),
            render::hidden_strings_tsv(&p, &second, &o, ""),
        ),
        (
            "triage",
            render::triage_tsv(&p, &first, &o),
            render::triage_tsv(&p, &second, &o),
        ),
    ];
    for (name, one, two) in cases {
        if one == two {
            continue;
        }
        let at = one
            .lines()
            .zip(two.lines())
            .position(|(a, b)| a != b)
            .unwrap_or(0);
        panic!(
            "{name} is not deterministic, first difference at line {}:
  {}
  {}",
            at + 1,
            one.lines().nth(at).unwrap_or(""),
            two.lines().nth(at).unwrap_or("")
        );
    }
}

#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn decompile_every_function() {
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    let t0 = std::time::Instant::now();
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let analysis_t = t0.elapsed();
    let t1 = std::time::Instant::now();

    let (mut ok, mut empty, mut failed) = (0usize, 0usize, 0usize);
    let mut first_failures: Vec<u64> = Vec::new();
    let mut malformed: Vec<String> = Vec::new();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_all(&p, &a, &Overlay::default(), &entries);
    for (f, r) in a.functions.iter().zip(texts) {
        match r {
            Some(t) if t.lines().count() > 2 => {
                ok += 1;
                let missing = dangling_gotos(&t);
                let depth = brace_imbalance(&t);
                let calls = missing_calls(&a, &Overlay::default(), f, &t);
                let undeclared = undeclared_slots(&t);
                let leaked = leaked_temps(&t);
                let glued = glued_names(&t);
                if (!missing.is_empty()
                    || depth != 0
                    || !calls.is_empty()
                    || !undeclared.is_empty()
                    || !leaked.is_empty()
                    || !glued.is_empty())
                    && malformed.len() < 10
                {
                    malformed.push(format!(
                        "{:#x}: dangling gotos {missing:?}, brace depth {depth}, calls not in the text {calls:?}, undeclared {undeclared:?}, leaked temps {leaked:?}, glued names {glued:?}",
                        f.entry
                    ));
                }
            }
            Some(_) => empty += 1,
            None => {
                failed += 1;
                if first_failures.len() < 10 {
                    first_failures.push(f.entry);
                }
            }
        }
    }
    println!(
        "binary: {}\nfunctions: {} (analysis {:?}, decompile-all {:?})\nok={} stubs={} failed={}\nfirst failures: {:x?}\nmalformed: {malformed:?}",
        path,
        a.functions.len(),
        analysis_t,
        t1.elapsed(),
        ok,
        empty,
        failed,
        first_failures
    );
    assert_eq!(failed, 0, "functions that failed to decompile");
    assert!(malformed.is_empty(), "malformed output: {malformed:?}");
}

/// Decompiles every function of the `BORER_DOGFOOD_A64` binary and
/// requires well-formed text.
///
/// As [`decompile_every_function`] does for an x86 build: no function
/// fails, no `goto` dangles, braces balance and every callee is named.
///
/// For an arm64 build of any program (a C library linked for
/// `aarch64-linux-gnu`, a Mach-O, a PE); it prints the tally of each
/// defect over the whole binary.
#[test]
#[ignore = "set BORER_DOGFOOD_A64 to an arm64 binary path to run this sweep"]
fn decompile_every_arm64_function() {
    let path = std::env::var("BORER_DOGFOOD_A64").expect("BORER_DOGFOOD_A64 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let started = std::time::Instant::now();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_all(&p, &a, &Overlay::default(), &entries);
    let took = started.elapsed();
    let (mut ok, mut failed, mut gotos, mut braces, mut unnamed) = (0usize, 0, 0, 0, 0);
    let mut first: Vec<String> = Vec::new();
    for (f, r) in a.functions.iter().zip(texts) {
        let Some(t) = r else {
            failed += 1;
            continue;
        };
        ok += 1;
        let missing = dangling_gotos(&t);
        let depth = brace_imbalance(&t);
        let calls = missing_calls(&a, &Overlay::default(), f, &t);
        gotos += usize::from(!missing.is_empty());
        braces += usize::from(depth != 0);
        unnamed += usize::from(!calls.is_empty());
        if (!missing.is_empty() || depth != 0 || !calls.is_empty()) && first.len() < 10 {
            first.push(format!(
                "{:#x}: dangling gotos {missing:?}, brace depth {depth}, calls not in the text {calls:?}",
                f.entry
            ));
        }
    }
    eprintln!(
        "binary: {path}\nfunctions: {} decompiled {ok} failed {failed} in {took:.1?}\nwith dangling gotos {gotos}, unbalanced braces {braces}, a callee unnamed {unnamed}\nfirst: {first:#?}",
        a.functions.len()
    );
    assert_eq!(failed, 0, "functions that failed to decompile");
    assert!(first.is_empty(), "malformed output: {first:#?}");
}

/// Replays the text of every function of the `BORER_DOGFOOD_A64` binary
/// against the arm64 machine and requires every claim it makes to hold.
///
/// As [`the_text_agrees_with_the_emulator_on_every_block`] does for an
/// x86 build; it prints the tally and the share of blocks checked.
#[test]
#[ignore = "set BORER_DOGFOOD_A64 to an arm64 binary path to run this sweep"]
fn the_arm64_text_agrees_with_the_machine_on_every_block() {
    use borer_engine::analysis::decompile::replay::{replay, replay_tsv};
    let path = std::env::var("BORER_DOGFOOD_A64").expect("BORER_DOGFOOD_A64 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none())
        .map(|f| f.entry)
        .collect();
    let started = std::time::Instant::now();
    let r = replay(&p, &a, &entries, 1);
    let took = started.elapsed();
    let text = replay_tsv(&r);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    for d in r.wrong().iter().take(40) {
        eprintln!(
            "ROW\t{:#x}\t{:#x}\t{:#x}\t{}\t{}\t{:#x}\t{:#x}\t{}\t{}",
            d.function, d.block, d.at, d.claim, d.place, d.text, d.machine, d.bits, d.expr
        );
    }
    let share = borer_engine::num::usize_f64(r.checked) * 100.0
        / borer_engine::num::usize_f64(r.blocks.max(1));
    eprintln!(
        "# {share:.1}% of blocks checked, {} disagreements; replay took {took:.1?}",
        r.wrong().len()
    );
    assert!(r.checked > 0, "{text}");
    assert!(r.wrong().is_empty(), "{} disagreements", r.wrong().len());
}

/// Decompiles every function of the `BORER_DOGFOOD` binary the way the
/// tools do, with the fields, results and asserted names, and requires
/// the same well-formed text as [`decompile_every_function`].
///
/// The naming passes rewrite lines after the structurer is done, so a
/// rename that glues names, loses a label or unbalances a brace shows
/// only here.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn decompile_every_function_named() {
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let t1 = std::time::Instant::now();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_named_all(&p, &a, &o, &entries);
    let (mut ok, mut failed) = (0usize, 0usize);
    let mut malformed: Vec<String> = Vec::new();
    for (f, r) in a.functions.iter().zip(texts) {
        let Some(t) = r else {
            failed += 1;
            continue;
        };
        ok += 1;
        let missing = dangling_gotos(&t);
        let depth = brace_imbalance(&t);
        let calls = missing_calls(&a, &o, f, &t);
        let undeclared = undeclared_slots(&t);
        let leaked = leaked_temps(&t);
        let glued = glued_names(&t);
        let quoted = t
            .lines()
            .find(|l| l.trim_start().starts_with("//") && l.contains('"'))
            .map(str::to_owned);
        if (!missing.is_empty()
            || depth != 0
            || !calls.is_empty()
            || !undeclared.is_empty()
            || !leaked.is_empty()
            || !glued.is_empty()
            || quoted.is_some())
            && malformed.len() < 10
        {
            malformed.push(format!(
                "{:#x}: dangling gotos {missing:?}, brace depth {depth}, calls not in the text {calls:?}, undeclared {undeclared:?}, leaked temps {leaked:?}, glued names {glued:?}, quoted header {quoted:?}",
                f.entry
            ));
        }
    }
    println!(
        "binary: {path}
functions: {} (decompile-named-all {:?})
ok={ok} failed={failed}
malformed: {malformed:?}",
        a.functions.len(),
        t1.elapsed(),
    );
    assert_eq!(failed, 0, "functions that failed to decompile");
    assert!(malformed.is_empty(), "malformed output: {malformed:?}");
}

/// Every fixture function's text is well formed, headers included.
///
/// The dogfood sweep runs only when a binary is named, so this holds the
/// same invariants over the fixture on every run, plus one the sweep cannot
/// state as cheaply: no header line carries a double quote. A quote in a
/// comment leaves any reader that tracks string literals inside one, and a
/// header that repeated an assert's quotes reached a real binary before
/// anything caught it.
#[test]
fn every_fixture_function_is_well_formed() {
    let p = common::fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_all(&p, &a, &o, &entries);
    let mut malformed: Vec<String> = Vec::new();
    for (entry, text) in entries.iter().zip(texts) {
        let Some(text) = text else { continue };
        let missing = dangling_gotos(&text);
        let depth = brace_imbalance(&text);
        let quoted = text
            .lines()
            .find(|l| l.trim_start().starts_with("//") && l.contains('"'));
        if !missing.is_empty() || depth != 0 || quoted.is_some() {
            malformed.push(format!(
                "{entry:#x}: dangling {missing:?}, depth {depth}, quoted header {quoted:?}"
            ));
        }
    }
    assert!(malformed.is_empty(), "malformed: {malformed:?}");
}

/// The integrity helpers accept well-formed text, flag a dangling goto, ignore
/// `goto L_` and braces inside string literals, and count unbalanced braces.
#[test]
fn integrity_helpers_catch_the_known_shapes() {
    assert_eq!(
        dangling_gotos("goto L_1;\nL_1:\nreturn;\n"),
        Vec::<String>::new()
    );
    assert_eq!(
        dangling_gotos("if (x) goto L_2;\nL_1:\n"),
        vec!["L_2".to_owned()]
    );
    assert_eq!(
        dangling_gotos("f(\"goto L_\", 5);\nreturn;\n"),
        Vec::<String>::new()
    );
    assert_eq!(brace_imbalance("if (a) {\n  f(\"}\");\n}\n"), 0);
    assert_eq!(brace_imbalance("while (1) {\n  if (b) {\n}\n"), 1);
}

/// Checks the lifter against the emulator on every block of the
/// `BORER_DOGFOOD` binary and requires them to agree on every register,
/// stack slot, store and branch.
///
/// A lifting bug reads as plausible C, and the emulator runs the real
/// instructions, so a disagreement names one block and one fact the
/// pseudo-C is wrong about, or an instruction the emulator gets wrong, which
/// `emulate`, `solve` and the unpacker rest on. When the gate verified 40
/// functions, a whole binary held 303 disagreements; when it compared
/// registers alone, a store of a wrong value or a branch on the wrong
/// condition passed every block.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_lifter_agrees_with_the_emulator_on_every_block() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let started = std::time::Instant::now();
    let v = verify(&p, &a, &entries, 1);
    let took = started.elapsed();
    let text = verify_tsv(&v);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    eprintln!("# verify took {took:.1?}");
    assert!(v.checked > 0, "{text}");
    assert!(v.mismatches.is_empty(), "{text}");
}

/// Checks the arm64 lifter against the arm64 machine on every block of the
/// `BORER_DOGFOOD_A64` binary and requires them to agree on every register,
/// `v` register, stack slot, store and branch.
///
/// The arm64 counterpart of the sweep above, for an arm64 build of any
/// program (a C library linked for `aarch64-linux-gnu`, a Mach-O, a PE);
/// it prints the tally and the share of blocks the check compared.
#[test]
#[ignore = "set BORER_DOGFOOD_A64 to an arm64 binary path to run this sweep"]
fn the_arm64_lifter_agrees_with_the_emulator_on_every_block() {
    use borer_engine::analysis::decompile::verify_a64::{verify, verify_tsv};
    let path = std::env::var("BORER_DOGFOOD_A64").expect("BORER_DOGFOOD_A64 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let started = std::time::Instant::now();
    let v = verify(&p, &a, &entries, 1);
    let took = started.elapsed();
    let text = verify_tsv(&v);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    let share = borer_engine::num::usize_f64(v.checked) * 100.0
        / borer_engine::num::usize_f64(v.blocks.max(1));
    eprintln!("# {share:.1}% of blocks checked; verify took {took:.1?}");
    assert!(v.checked > 0, "{text}");
    assert!(v.mismatches.is_empty(), "{text}");
}

/// Replays the text of every function of the `BORER_DOGFOOD` binary
/// against the emulator and requires every claim it makes to hold.
///
/// Each block's statements, as the emission recorded them, run from three
/// states built through the lifter's own relation between machine and
/// text; at every successor the relation must hold again, the branch must
/// go the machine's way, a call must pass what the machine passes and a
/// return hand back what it does. It prints the tally, why blocks went
/// unchecked, the share of blocks checked, how long one function's replay
/// takes, and a row per disagreement (`BORER_DOGFOOD_SEED` picks the
/// states, 1 by default); lane roughness (values that differ only above
/// the low 32 bits, a narrow-width claim) is counted apart and not failed
/// on.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_text_agrees_with_the_emulator_on_every_block() {
    use borer_engine::analysis::decompile::replay::{Replayed, replay_function, replay_tsv};
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    let seed: u64 = std::env::var("BORER_DOGFOOD_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && f.funclet.is_none())
        .map(|f| f.entry)
        .collect();
    let threads = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let started = std::time::Instant::now();
    let mut each: Vec<(u64, std::time::Duration, Replayed)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let (p, a, entries) = (&p, &a, &entries);
                scope.spawn(move || {
                    entries
                        .iter()
                        .skip(t)
                        .step_by(threads)
                        .map(|&e| {
                            let t0 = std::time::Instant::now();
                            let r = replay_function(p, a, e, seed);
                            (e, t0.elapsed(), r)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("a replay thread"))
            .collect()
    });
    let took = started.elapsed();
    each.sort_by_key(|(e, ..)| *e);
    let mut times: Vec<(std::time::Duration, u64)> =
        each.iter().map(|(e, t, _)| (*t, *e)).collect();
    times.sort_unstable();
    let mut total = Replayed::default();
    for (_, _, r) in each {
        total.merge(r);
    }
    let text = replay_tsv(&total);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    for d in &total.disagreements {
        eprintln!(
            "ROW\t{:#x}\t{:#x}\t{:#x}\t{}\t{}\t{:#x}\t{:#x}\t{}\t{}\t{}",
            d.function, d.block, d.at, d.claim, d.place, d.text, d.machine, d.bits, d.lane, d.expr
        );
    }
    let at = |q: usize| {
        times
            .get(times.len() * q / 100)
            .copied()
            .unwrap_or_default()
    };
    let worst = times.last().copied().unwrap_or_default();
    let flagged: BTreeSet<u64> = total.wrong().iter().map(|d| d.function).collect();
    eprintln!(
        "binary: {path}\nfunctions: {}, flagged {}; blocks checked {} of {}; replay {took:.1?}\none function: p50 {:.1?}, p90 {:.1?}, p99 {:.1?}, most {:.1?} at {:#x}",
        total.functions,
        flagged.len(),
        total.checked,
        total.blocks,
        at(50).0,
        at(90).0,
        at(99).0,
        worst.0,
        worst.1
    );
    assert!(total.checked > 0, "{text}");
    assert!(
        total.wrong().is_empty(),
        "{} disagreements",
        total.wrong().len()
    );
}

/// Runs every small function of the `BORER_DOGFOOD` binary on inputs its
/// signature types, in the emulator and through its final text as C, and
/// requires the two to agree on every input.
///
/// The replay above checks each statement as the lifter emitted it; what
/// the passes after it do to the text (merging chains, typing, layouts,
/// polish) only a run of the final text sees. Functions of at most
/// `BORER_DOGFOOD_SMALL` instructions (40 by default) are run on
/// `BORER_DOGFOOD_INPUTS` inputs each (4), generated from
/// `BORER_DOGFOOD_SEED` (1), each side given `BORER_DOGFOOD_STEPS` steps
/// (20000). An input the binary does not return from, or the text holds a
/// line this cannot run, is unchecked and counted by reason; each
/// difference prints as a row: the entry, the input, the line and what
/// differs.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_final_text_agrees_with_the_emulator_on_small_functions() {
    use borer_engine::analysis::render::{Verdict, check_generated};
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    let knob = |name: &str, default: usize| {
        std::env::var(name)
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(default)
    };
    let (small, inputs, steps) = (
        knob("BORER_DOGFOOD_SMALL", 40),
        knob("BORER_DOGFOOD_INPUTS", 4),
        knob("BORER_DOGFOOD_STEPS", 20_000),
    );
    let seed = u64::try_from(knob("BORER_DOGFOOD_SEED", 1)).unwrap_or(1);
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && f.funclet.is_none() && f.instr_count <= small)
        .map(|f| f.entry)
        .collect();
    let threads = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let started = std::time::Instant::now();
    type Each = (
        u64,
        std::time::Duration,
        Result<Vec<(String, Verdict)>, String>,
    );
    let mut each: Vec<Each> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let (p, a, o, entries) = (&p, &a, &o, &entries);
                scope.spawn(move || {
                    entries
                        .iter()
                        .skip(t)
                        .step_by(threads)
                        .map(|&e| {
                            let t0 = std::time::Instant::now();
                            let r = check_generated(p, a, o, e, inputs, seed, steps);
                            (e, t0.elapsed(), r)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("a run thread"))
            .collect()
    });
    let took = started.elapsed();
    each.sort_by_key(|(e, ..)| *e);
    let (mut agree, mut differ, mut unchecked) = (0usize, 0usize, 0usize);
    let mut skipped: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut why: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut flagged: BTreeSet<u64> = BTreeSet::new();
    for (e, _, r) in &each {
        match r {
            Err(reason) => {
                let class = reason
                    .split_once(' ')
                    .map_or(reason.as_str(), |(_, rest)| rest);
                *skipped.entry(class.to_owned()).or_default() += 1;
            }
            Ok(rows) => {
                for (args, v) in rows {
                    match v {
                        Verdict::Agrees => agree += 1,
                        Verdict::Differs(line, what) => {
                            differ += 1;
                            flagged.insert(*e);
                            eprintln!("DIFF	{e:#x}	{args}	L{line}	{what}");
                        }
                        Verdict::Unchecked(_, reason) => {
                            unchecked += 1;
                            let class: String = reason
                                .split(|c: char| c == '`' || c.is_ascii_digit())
                                .next()
                                .unwrap_or("")
                                .to_owned();
                            *why.entry(class).or_default() += 1;
                        }
                    }
                }
            }
        }
    }
    let mut times: Vec<(std::time::Duration, u64)> =
        each.iter().map(|(e, t, _)| (*t, *e)).collect();
    times.sort_unstable();
    let at = |q: usize| {
        times
            .get(times.len() * q / 100)
            .copied()
            .unwrap_or_default()
    };
    let worst = times.last().copied().unwrap_or_default();
    let mut reasons: Vec<(usize, String)> = why.into_iter().map(|(k, n)| (n, k)).collect();
    reasons.sort_unstable_by(|x, y| y.cmp(x));
    for (n, r) in reasons.iter().take(12) {
        eprintln!("UNCHECKED	{n}	{r}");
    }
    for (r, n) in &skipped {
        eprintln!("SKIPPED	{n}	{r}");
    }
    eprintln!(
        "binary: {path}
functions of at most {small} instructions: {}, {inputs} inputs each, {steps} steps a run
inputs: agree {agree}, differ {differ} (in {} functions), unchecked {unchecked}; skipped functions {}
run {took:.1?}; one function: p50 {:.1?}, p90 {:.1?}, p99 {:.1?}, most {:.1?} at {:#x}",
        entries.len(),
        flagged.len(),
        skipped.values().sum::<usize>(),
        at(50).0,
        at(90).0,
        at(99).0,
        worst.0,
        worst.1
    );
    assert!(agree > 0, "nothing was checked");
    assert_eq!(
        differ,
        0,
        "{differ} inputs differ in {} functions",
        flagged.len()
    );
}

/// Checks the text of every function of the `BORER_DOGFOOD` binary against
/// the graph its structurer was handed and requires each to agree.
///
/// Every path the text claims must be a path of the binary and every path
/// of the binary one the text claims, up to calls, returns and labels.
///
/// Each disagreement prints as one line (`entry`, the side holding the
/// path the other lacks, where, the step, what the other side could do
/// instead), followed by the tally, why functions went unchecked, the time
/// the checks took beside the time the texts took, and how long one
/// function's check takes, each checked a second time alone to hold the
/// verdict to the first.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_structure_agrees_with_the_cfg_on_every_function() {
    use borer_engine::analysis::decompile::traces::{
        Structure, check, check_all, decompile_with_cfg_all,
    };
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    // INVARIANT: the sweeps pin the engine's own dev-shape facts, and the
    // dev build's PDB sits beside the corpus binary.
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let t0 = std::time::Instant::now();
    let texts = decompile_with_cfg_all(&p, &a, &o, &entries);
    let decompiled = t0.elapsed();
    let t1 = std::time::Instant::now();
    let verdicts = check_all(&p, &a, &o, &entries, &texts);
    let checked = t1.elapsed();
    let mut each: Vec<(std::time::Duration, u64)> = Vec::new();
    for ((e, t), v) in entries.iter().zip(&texts).zip(&verdicts) {
        let Some((text, live)) = t else { continue };
        let t2 = std::time::Instant::now();
        let again = check(&p, &a, &o, *e, text, live);
        each.push((t2.elapsed(), *e));
        assert_eq!(Some(&again), v.as_ref(), "{e:#x}: a second check disagrees");
    }
    each.sort_unstable();
    let at = |q: usize| each.get(each.len() * q / 100).copied().unwrap_or_default();
    let worst = each.last().copied().unwrap_or_default();
    let (mut agree, mut flags) = (0usize, Vec::new());
    let mut unchecked: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for (e, v) in entries.iter().zip(&verdicts) {
        match v {
            Some(Structure::Agrees) => agree += 1,
            Some(Structure::Disagrees(d)) => flags.push(format!(
                "{e:#x}\t{:?}\t{:#x}\t{}\t{}",
                d.side,
                d.at,
                d.step,
                d.other.join("; ")
            )),
            Some(Structure::Unchecked(why)) => {
                eprintln!("UNCHECKED\t{e:#x}\t{why}");
                *unchecked.entry(why).or_default() += 1;
            }
            None => *unchecked.entry("no text").or_default() += 1,
        }
    }
    for f in &flags {
        eprintln!("FLAG\t{f}");
    }
    eprintln!(
        "binary: {path}\nfunctions: {}, agree {agree}, disagree {}, unchecked {unchecked:?}\ndecompile {decompiled:.1?}, check {checked:.1?}\none check: p50 {:.1?}, p99 {:.1?}, most {:.1?} at {:#x}",
        entries.len(),
        flags.len(),
        at(50).0,
        at(99).0,
        worst.0,
        worst.1
    );
    assert!(flags.is_empty(), "{} functions disagree", flags.len());
}
