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

use borer_engine::analysis::decompile::verify::Verified;
use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::{
    Analysis, Overlay,
    decompile::{
        Swept, declarations_end, decompile, decompile_all, decompile_named_all,
        decompile_swept_all, virtual_callees,
    },
    name_of, render,
};
use borer_engine::program::{Program, SymbolKind};
use borer_engine::view::{Kind, Ref, View};
use std::collections::BTreeSet;
use std::sync::{LazyLock, OnceLock};

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
/// are not code. A function pointer declaration, `uint64_t (*arg_20)(...)`,
/// declares the name inside its `(*...)`. A `static inline` function the
/// unit defines on one line is a scope of its own: the slots it names must
/// be declared in its body, and its body declares nothing for the function
/// the text is about.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
///
/// # Returns
///
/// The undeclared slot names, without duplicates.
fn undeclared_slots(text: &str) -> Vec<String> {
    let mut declared: BTreeSet<String> = BTreeSet::new();
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut out: BTreeSet<String> = BTreeSet::new();
    for line in text.lines() {
        let t = line.trim_start();
        if t.starts_with("//") {
            continue;
        }
        if t.starts_with("static inline ") {
            let body = t.split_once('{').map_or("", |(_, b)| b);
            let (mut own, mut reads) = (BTreeSet::new(), BTreeSet::new());
            for stmt in body.split(['{', '}']).flat_map(|s| s.split_inclusive(';')) {
                slots_of(stmt.trim(), &mut own, &mut reads);
            }
            out.extend(reads.difference(&own).cloned());
            continue;
        }
        slots_of(t, &mut declared, &mut used);
    }
    out.extend(used.difference(&declared).cloned());
    out.into_iter().collect()
}

/// Sorts the slot names of one line or statement into those it declares
/// and those it uses.
///
/// # Arguments
///
/// * `t` - The line or statement, trimmed.
/// * `declared` - Receives the names a declaration declares.
/// * `used` - Receives the names anything else uses.
fn slots_of(t: &str, declared: &mut BTreeSet<String>, used: &mut BTreeSet<String>) {
    let is_slot = |w: &str| {
        w.split_once('_').is_some_and(|(head, digits)| {
            matches!(head, "local" | "home" | "arg")
                && !digits.is_empty()
                && digits.bytes().all(|b| b.is_ascii_hexdigit())
        })
    };
    let decl = matches!(
        t.split_whitespace().next().map(|w| w.trim_end_matches('*')),
        Some(w) if w.starts_with("uint") || w.starts_with("int")
            || matches!(w, "float" | "double" | "bool" | "char" | "void" | "FILE")
    ) && t.ends_with(';')
        && !t.contains('=')
        && (!t.contains('(') || t.contains("(*"));
    let declared_name = t
        .split_once("(*")
        .and_then(|(_, rest)| rest.split_once(')'))
        .map(|(name, _)| name);
    for w in t
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|w| is_slot(w))
    {
        if decl && declared_name.is_none_or(|n| n == w) {
            declared.insert(w.to_owned());
        } else {
            used.insert(w.to_owned());
        }
    }
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

/// The callees of `function` its text names nowhere, but the frame helpers
/// and the ARM32 division helpers, which the text prints as the operator
/// they compute.
///
/// A clone's dotted name (`f.constprop.0`) counts under the C identifier
/// the text spells it as (`f_constprop_0`).
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
        if function.blocks.iter().any(|b| b.start == *c) {
            continue;
        }
        let name = name_of(analysis, overlay, *c);
        if name.contains("operator ")
            || matches!(
                name.as_str(),
                "__SEH_prolog4"
                    | "__EH_prolog3"
                    | "__SEH_epilog4"
                    | "__EH_epilog3"
                    | "__aeabi_idiv"
                    | "__aeabi_uidiv"
                    | "__aeabi_idivmod"
                    | "__aeabi_uidivmod"
                    | "__rt_sdiv"
                    | "__rt_udiv"
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
        if !text.contains(bare)
            && !text.contains(&bare.replace(['.', '$', '@'], "_"))
            && !text.contains(&format!("{c:#x}"))
        {
            out.push(name);
        }
    }
    out
}

/// The `BORER_DOGFOOD` binary, loaded and analyzed once for every sweep
/// over it, with what more than one sweep reads built once on first use.
///
/// The sweeps run side by side in one process; each of them loading,
/// analyzing and decompiling the binary afresh did the same work up to
/// three times over, which no sweep checks.
struct Corpus {
    /// The binary's path, as the variable names it.
    path: String,
    /// The binary.
    program: Program,
    /// Its analysis.
    analysis: Analysis,
    /// How long the analysis took.
    took: std::time::Duration,
    /// Every function's texts ([`decompile_swept_all`]), in function order.
    swept: OnceLock<Vec<Option<Swept>>>,
    /// The lifter checked against the emulator on every block.
    verified: OnceLock<Verified>,
}

impl Corpus {
    /// Returns every function's entry, in address order.
    fn entries(&self) -> Vec<u64> {
        self.analysis.functions.iter().map(|f| f.entry).collect()
    }

    /// Returns every function's texts, decompiling them on the first call.
    fn swept(&self) -> &[Option<Swept>] {
        self.swept.get_or_init(|| {
            decompile_swept_all(
                &self.program,
                &self.analysis,
                &Overlay::default(),
                &self.entries(),
            )
        })
    }

    /// Returns the lifter's check against the emulator on every block,
    /// running it on the first call.
    fn verified(&self) -> &Verified {
        self.verified.get_or_init(|| {
            borer_engine::analysis::decompile::verify::verify(
                &self.program,
                &self.analysis,
                &self.entries(),
                1,
            )
        })
    }
}

/// The `BORER_DOGFOOD` binary, read on first use.
#[expect(
    clippy::expect_used,
    reason = "a sweep whose binary does not load has nothing to check"
)]
static CORPUS: LazyLock<Corpus> = LazyLock::new(|| {
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    let started = std::time::Instant::now();
    let program = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let analysis = Analysis::compute(&program);
    Corpus {
        path,
        program,
        analysis,
        took: started.elapsed(),
        swept: OnceLock::new(),
        verified: OnceLock::new(),
    }
});

/// Analyzes the `BORER_DOGFOOD` binary a second time and requires every
/// renderer to answer the same bytes from both analyses.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_same_binary_answers_the_same_bytes_twice() {
    let c = &*CORPUS;
    let p = &c.program;
    let first = &c.analysis;
    let second = &Analysis::compute(p);
    let o = Overlay::default();
    assert_eq!(
        first.functions.len(),
        second.functions.len(),
        "function discovery is not deterministic"
    );
    let entry = p
        .entry
        .unwrap_or_else(|| first.functions.first().map_or(0, |f| f.entry));
    let cases: Vec<(&str, String, String)> = vec![
        ("binary_info", p.summary(), p.summary()),
        (
            "functions",
            render::function_rows(first, &o, None, render::FunctionOrder::Address, 0, 100).spell(),
            render::function_rows(second, &o, None, render::FunctionOrder::Address, 0, 100).spell(),
        ),
        (
            "crypto",
            render::crypto_tsv(p, first, &o, 0, 200),
            render::crypto_tsv(p, second, &o, 0, 200),
        ),
        (
            "decompile",
            decompile(p, first, &o, entry).unwrap_or_default(),
            decompile(p, second, &o, entry).unwrap_or_default(),
        ),
        (
            "why",
            render::why_tsv(p, first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::why_tsv(p, second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "layout",
            render::layout_tsv(p, first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::layout_tsv(p, second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "taint",
            render::taint_tsv(p, first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::taint_tsv(p, second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "oracle",
            render::oracle_tsv(p, first, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
            render::oracle_tsv(p, second, &o, &format!("{entry:#x}")).unwrap_or_else(|e| e),
        ),
        (
            "emulate",
            render::emulate_tsv(p, first, &o, &format!("{entry:#x},steps=20000"))
                .unwrap_or_else(|e| e),
            render::emulate_tsv(p, second, &o, &format!("{entry:#x},steps=20000"))
                .unwrap_or_else(|e| e),
        ),
        (
            "hidden",
            render::hidden_strings_tsv(p, first, &o, ""),
            render::hidden_strings_tsv(p, second, &o, ""),
        ),
        (
            "triage",
            render::triage_tsv(p, first, &o),
            render::triage_tsv(p, second, &o),
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
    let c = &*CORPUS;
    let (path, a, analysis_t) = (&c.path, &c.analysis, c.took);
    let t1 = std::time::Instant::now();

    let (mut ok, mut empty, mut failed) = (0usize, 0usize, 0usize);
    let mut first_failures: Vec<u64> = Vec::new();
    let mut malformed: Vec<String> = Vec::new();
    let mut unsettled: Vec<String> = Vec::new();
    let texts = c
        .swept()
        .iter()
        .map(|s| s.as_ref().map(|s| (&s.text, &s.settle)));
    for (f, r) in a.functions.iter().zip(texts) {
        if let Some((_, settle)) = &r
            && settle.spent()
            && unsettled.len() < 10
        {
            unsettled.push(format!(
                "{:#x}: {} of {} passes, still changing: {:?}",
                f.entry, settle.passes, settle.fuel, settle.churn
            ));
        }
        match r.map(|(t, _)| t) {
            Some(t) if t.lines().count() > 2 => {
                ok += 1;
                let missing = dangling_gotos(t);
                let depth = brace_imbalance(t);
                let calls = missing_calls(a, &Overlay::default(), f, t);
                let undeclared = undeclared_slots(t);
                let leaked = leaked_temps(t);
                let glued = glued_names(t);
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
    assert!(
        unsettled.is_empty(),
        "cleanup spent its pass budget: {unsettled:?}"
    );
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
    assert_eq!(
        r.functions,
        entries.len(),
        "functions left out of the replay"
    );
    assert!(r.checked > 0, "{text}");
    assert!(r.wrong().is_empty(), "{} disagreements", r.wrong().len());
}

/// Decompiles every function of the `BORER_DOGFOOD_A32` binary and
/// requires well-formed text.
///
/// As [`decompile_every_arm64_function`] does for an arm64 build, for an
/// ARM32 build of any program (an `armv7a-linux-gnueabihf` ELF, A32 or
/// T32, or a `thumbv7-windows` PE); it prints the tally of each defect
/// over the whole binary.
#[test]
#[ignore = "set BORER_DOGFOOD_A32 to an ARM32 binary path to run this sweep"]
fn decompile_every_arm32_function() {
    let path = std::env::var("BORER_DOGFOOD_A32").expect("BORER_DOGFOOD_A32 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let started = std::time::Instant::now();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_all(&p, &a, &Overlay::default(), &entries);
    let took = started.elapsed();
    let (mut ok, mut failed, mut asm) = (0usize, 0usize, 0usize);
    let mut first: Vec<String> = Vec::new();
    for (f, r) in a.functions.iter().zip(texts) {
        let Some(t) = r else {
            failed += 1;
            continue;
        };
        ok += 1;
        asm += t.matches("/* asm").count();
        let missing = dangling_gotos(&t);
        let depth = brace_imbalance(&t);
        let calls = missing_calls(&a, &Overlay::default(), f, &t);
        if (!missing.is_empty() || depth != 0 || !calls.is_empty()) && first.len() < 10 {
            first.push(format!(
                "{:#x}: dangling gotos {missing:?}, brace depth {depth}, calls not in the text {calls:?}",
                f.entry
            ));
        }
    }
    eprintln!(
        "binary: {path}
functions: {} decompiled {ok} failed {failed} in {took:.1?}, {asm} asm lines
first: {first:#?}",
        a.functions.len()
    );
    assert_eq!(failed, 0, "functions that failed to decompile");
    assert!(first.is_empty(), "malformed output: {first:#?}");
}

/// Checks the ARM32 lifter against the ARM32 machine on every block of
/// the `BORER_DOGFOOD_A32` binary and requires them to agree on every
/// register, VFP register, stack slot, store and branch.
///
/// The ARM32 counterpart of
/// [`the_arm64_lifter_agrees_with_the_emulator_on_every_block`]; it prints
/// the tally and the share of blocks the check compared.
#[test]
#[ignore = "set BORER_DOGFOOD_A32 to an ARM32 binary path to run this sweep"]
fn the_arm32_lifter_agrees_with_the_emulator_on_every_block() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let path = std::env::var("BORER_DOGFOOD_A32").expect("BORER_DOGFOOD_A32 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let v = verify(&p, &a, &entries, 1);
    let text = verify_tsv(&v);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    let share = borer_engine::num::usize_f64(v.checked) * 100.0
        / borer_engine::num::usize_f64(v.blocks.max(1));
    eprintln!("# {share:.1}% of blocks checked");
    assert_eq!(
        v.functions,
        entries.len(),
        "functions left out of the check"
    );
    assert!(v.checked > 0, "{text}");
    assert!(v.mismatches.is_empty(), "{text}");
}

/// Replays the text of every function of the `BORER_DOGFOOD_A32` binary
/// against the ARM32 machine and requires every claim it makes to hold.
///
/// As [`the_arm64_text_agrees_with_the_machine_on_every_block`] does for
/// an arm64 build.
#[test]
#[ignore = "set BORER_DOGFOOD_A32 to an ARM32 binary path to run this sweep"]
fn the_arm32_text_agrees_with_the_machine_on_every_block() {
    use borer_engine::analysis::decompile::replay::{replay, replay_tsv};
    let path = std::env::var("BORER_DOGFOOD_A32").expect("BORER_DOGFOOD_A32 env var");
    let p = Program::load(std::path::Path::new(&path)).expect("load");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none())
        .map(|f| f.entry)
        .collect();
    let r = replay(&p, &a, &entries, 1);
    let text = replay_tsv(&r);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    assert_eq!(
        r.functions,
        entries.len(),
        "functions left out of the replay"
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
    let c = &*CORPUS;
    let (path, a) = (&c.path, &c.analysis);
    let o = Overlay::default();
    let t1 = std::time::Instant::now();
    let texts = c
        .swept()
        .iter()
        .map(|s| s.as_ref().and_then(|s| s.named.as_ref()));
    let (mut ok, mut failed) = (0usize, 0usize);
    let mut malformed: Vec<String> = Vec::new();
    for (f, r) in a.functions.iter().zip(texts) {
        let Some(t) = r else {
            failed += 1;
            continue;
        };
        ok += 1;
        let missing = dangling_gotos(t);
        let depth = brace_imbalance(t);
        let calls = missing_calls(a, &o, f, t);
        let undeclared = undeclared_slots(t);
        let leaked = leaked_temps(t);
        let glued = glued_names(t);
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

/// Returns each function's text as the sweep rendered it, named where it
/// has a named one ([`Swept::named`], else [`Swept::text`]).
///
/// # Arguments
///
/// * `c` - The corpus.
fn swept_texts(c: &Corpus) -> Vec<(u64, &str)> {
    c.analysis
        .functions
        .iter()
        .zip(c.swept())
        .filter_map(|(f, s)| {
            let s = s.as_ref()?;
            Some((f.entry, s.named.as_deref().unwrap_or(&s.text)))
        })
        .collect()
}

/// Returns a hash of each text's view, on `threads` threads taking the
/// texts from one queue: a hash of every token's line, end, kind and link
/// in order, the view's canonical dump.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `texts` - Each function's entry and text.
/// * `threads` - How many threads read the views.
#[expect(
    clippy::expect_used,
    reason = "a worker thread that panics fails the sweep"
)]
fn view_dumps(p: &Program, a: &Analysis, texts: &[(u64, &str)], threads: usize) -> Vec<u64> {
    use std::hash::{DefaultHasher, Hash, Hasher};
    let next = std::sync::atomic::AtomicUsize::new(0);
    let dump = |entry: u64, text: &str| {
        let mut out = String::new();
        if let Some(v) = view_of(p, a, &Overlay::default(), entry, text) {
            for i in 0..v.lines() {
                for (span, kind, link) in v.tokens(i) {
                    out.push_str(&format!("{i}\t{}\t{kind:?}\t{link:?}\n", span.end));
                }
            }
        }
        let mut h = DefaultHasher::new();
        out.hash(&mut h);
        h.finish()
    };
    let mut each: Vec<(usize, u64)> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&(entry, text)) = texts.get(k) else {
                            return done;
                        };
                        done.push((k, dump(entry, text)));
                    }
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|w| w.join().expect("a view thread"))
            .collect()
    });
    each.sort_unstable();
    each.into_iter().map(|(_, h)| h).collect()
}

/// Every function's view of the `BORER_DOGFOOD` binary reads the same
/// tokens on one thread and on every core, and again in one process.
///
/// The views read the sweep's texts ([`swept_texts`]): on the corpus's
/// analysis on one thread, on a fresh analysis whose memo the threads fill
/// as they race, and on the first analysis again.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_view_reads_the_same_at_any_thread_count() {
    let c = &*CORPUS;
    let texts = swept_texts(c);
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let once = view_dumps(&c.program, &c.analysis, &texts, 1);
    let fresh = Analysis::compute(&c.program);
    let wide = view_dumps(&c.program, &fresh, &texts, cores);
    let again = view_dumps(&c.program, &c.analysis, &texts, 1);
    let differ = |other: &[u64]| {
        texts
            .iter()
            .zip(once.iter().zip(other))
            .filter(|(_, (x, y))| x != y)
            .map(|((e, _), _)| format!("{e:#x}"))
            .take(10)
            .collect::<Vec<_>>()
    };
    println!("{} views read on 1 and {cores} threads", texts.len());
    assert!(
        differ(&wide).is_empty(),
        "across threads: {:?}",
        differ(&wide)
    );
    assert!(
        differ(&again).is_empty(),
        "in one process: {:?}",
        differ(&again)
    );
}

/// Spells a function's or an import's name as a text does: without its
/// module prefix, the `.`, `$` and `@` of a C name turned to `_`, a
/// qualified name kept whole.
///
/// # Arguments
///
/// * `name` - The name.
fn spelled(name: &str) -> String {
    let name = borer_engine::analysis::bare_name(name);
    if name.contains("::") || name.contains('(') {
        name.to_owned()
    } else {
        name.replace(['.', '$', '@'], "_")
    }
}

/// Returns how many discovered functions and imports go by each spelling:
/// an import once, however many slots it has, and a stub that only jumps
/// through an import's slot as that import.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
fn spellings(p: &Program, a: &Analysis) -> std::collections::BTreeMap<String, usize> {
    let o = Overlay::default();
    let mut by = std::collections::BTreeMap::new();
    let imports: BTreeSet<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| s.name.as_str())
        .collect();
    let functions = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none())
        .map(|f| spelled(&name_of(a, &o, f.entry)));
    let imports = imports
        .into_iter()
        .map(|n| spelled(&borer_engine::search::demangled_name(n)));
    for name in functions.chain(imports) {
        *by.entry(name).or_insert(0) += 1;
    }
    by
}

/// Returns the ids a view ships that the function's facts, read here apart
/// from the view, do not bear out.
///
/// A `static inline` line is the function its own name links to; every
/// other line is the function the text is of. A function id must be the
/// function, a callee or the function a callee's stub is bound to, a
/// reference target, or a virtual callee; an import's slot an import's,
/// and referenced or jumped through by a stub the function calls; a
/// label's address a block's start; a global's address mapped and
/// referenced; a variable the function's, defined on its signature, a
/// declaration or its `static inline` line; a type defined on a line that
/// spells it.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `entry` - The function the view is of.
/// * `v` - The view.
/// * `text` - The text it read.
fn unborne(p: &Program, a: &Analysis, entry: u64, v: &View, text: &str) -> Vec<String> {
    let decls = declarations_end(text).unwrap_or(0);
    let targets =
        |f: u64| -> BTreeSet<u64> { a.refs_from(f).into_iter().map(|(t, _)| t).collect() };
    let main = targets(entry);
    let mut virtuals: Option<Vec<u64>> = None;
    let mut bad = Vec::new();
    for i in 0..v.lines() {
        let line = v.line(i).unwrap_or_default();
        let tokens: Vec<_> = v.tokens(i).collect();
        let scope = if line.starts_with("static inline ") {
            let named = tokens.iter().find(|(_, kind, _)| *kind == Kind::Function);
            named.and_then(|(.., link)| {
                if let Some(Ref::Function(g)) = link {
                    Some(*g)
                } else {
                    None
                }
            })
        } else {
            Some(entry)
        };
        let f = scope.and_then(|s| a.function(s));
        let inline = scope
            .filter(|s| *s != entry)
            .map(targets)
            .unwrap_or_default();
        let referenced = |at: u64| match scope {
            Some(s) if s == entry => main.contains(&at),
            Some(_) => inline.contains(&at),
            None => false,
        };
        for (span, _, link) in &tokens {
            let Some(r) = link else { continue };
            let ok = match r {
                Ref::Function(e) => {
                    Some(*e) == scope
                        || f.is_some_and(|f| {
                            f.callees.contains(e)
                                || f.callees
                                    .iter()
                                    .any(|c| a.function(*c).and_then(|g| g.bound) == Some(*e))
                        })
                        || referenced(*e)
                        || (scope == Some(entry)
                            && virtuals
                                .get_or_insert_with(|| {
                                    virtual_callees(p, a, &Overlay::default(), entry)
                                })
                                .contains(e))
                }
                Ref::Import(s) => {
                    let stub = f.is_some_and(|f| {
                        f.callees
                            .iter()
                            .any(|c| a.function(*c).and_then(|g| g.thunk) == Some(*s))
                    });
                    (referenced(*s) || stub)
                        && p.symbols
                            .iter()
                            .any(|y| y.kind == SymbolKind::Import && y.addr == *s)
                }
                Ref::Address(va) => f.is_some_and(|f| f.blocks.iter().any(|b| b.start == *va)),
                Ref::Global(va) => {
                    let mapped = p.section_at(*va).is_some()
                        || p.zero_fill_at(*va).is_some()
                        || p.in_headers(*va)
                        || (p.format == borer_engine::program::BinaryFormat::Pe
                            && *va == p.image_base);
                    mapped && referenced(*va)
                }
                Ref::String(va) => p.section_at(*va).is_some() && referenced(*va),
                Ref::Field { .. } => true,
                Ref::Variable { function, name } => {
                    Some(*function) == scope
                        && v.definition(r).is_some_and(|d| {
                            v.line(d).is_some_and(|l| {
                                let declares = l.starts_with("// signature: ")
                                    || l.starts_with("static inline ")
                                    || d < decls;
                                declares
                                    && l.split(|c: char| !c.is_alphanumeric() && c != '_')
                                        .any(|w| w == &**name)
                            })
                        })
                }
                Ref::Type(name) => v
                    .definition(r)
                    .is_some_and(|d| v.line(d).is_some_and(|l| l.contains(&**name))),
            };
            if !ok {
                bad.push(format!(
                    "{entry:#x} line {i}: {} {r:?}",
                    &line[span.clone()]
                ));
            }
        }
    }
    bad
}

/// What the sweep counts of the views: the call tokens (a name right
/// before a `(`) and the tokens of three kinds, each with how many carry
/// an id.
#[derive(Debug, Default)]
struct Census {
    /// Call tokens, and how many carry an id.
    calls: (usize, usize),
    /// Call tokens whose spelling names exactly one discovered function or
    /// import, and how many of them carry an id.
    resolvable: (usize, usize),
    /// Call tokens whose spelling names more than one.
    ambiguous: usize,
    /// Variable, label and global tokens, each with how many carry an id.
    kinds: [(usize, usize); 3],
    /// What the views counted of the names they left unlinked: the ones no
    /// fact bore out, and the ones more than one thing spells.
    counted: (usize, usize),
    /// The first resolvable call tokens without an id.
    examples: Vec<String>,
}

impl Census {
    /// Adds one function's view.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function.
    /// * `v` - Its view.
    /// * `by` - How many functions and imports go by each spelling
    ///   ([`spellings`]).
    fn add(&mut self, entry: u64, v: &View, by: &std::collections::BTreeMap<String, usize>) {
        for i in 0..v.lines() {
            let line = v.line(i).unwrap_or_default();
            let tokens: Vec<_> = v.tokens(i).collect();
            for (k, (span, kind, link)) in tokens.iter().enumerate() {
                let slot = match kind {
                    Kind::Variable => Some(0),
                    Kind::Label => Some(1),
                    Kind::Global => Some(2),
                    Kind::Space
                    | Kind::Comment
                    | Kind::Keyword
                    | Kind::Constant
                    | Kind::Mnemonic
                    | Kind::Register
                    | Kind::Type
                    | Kind::Function
                    | Kind::Field
                    | Kind::Address
                    | Kind::String
                    | Kind::Number
                    | Kind::Punct
                    | Kind::Text => None,
                };
                if let Some(s) = slot {
                    self.kinds[s].0 += 1;
                    self.kinds[s].1 += usize::from(link.is_some());
                }
                let opens = tokens
                    .get(k + 1)
                    .is_some_and(|(next, ..)| &line[next.clone()] == "(");
                if !opens || !matches!(kind, Kind::Function | Kind::Text) {
                    continue;
                }
                let word = &line[span.clone()];
                self.calls.0 += 1;
                self.calls.1 += usize::from(link.is_some());
                match by.get(word).copied().unwrap_or(0) {
                    0 => {}
                    1 => {
                        self.resolvable.0 += 1;
                        self.resolvable.1 += usize::from(link.is_some());
                        if link.is_none() && self.examples.len() < 10 {
                            self.examples.push(format!("{entry:#x} line {i}: {word}"));
                        }
                    }
                    _ => self.ambiguous += 1,
                }
            }
        }
        let counted = v.unlinked();
        self.counted.0 += counted.uncorroborated;
        self.counted.1 += counted.ambiguous;
    }
}

/// Reads every function's text of the `BORER_DOGFOOD` binary as a view,
/// checks that each spells its text and ships only corroborated ids
/// ([`unborne`]), and prints the census.
///
/// The texts are the sweep's ([`swept_texts`]), so nothing decompiles
/// twice. The census counts the call tokens that carry an id against those
/// whose spelling names exactly one discovered function or import, lists
/// the first of those left without one, and counts the variables, labels
/// and globals linked.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_view_spells_its_text_and_links_only_what_the_code_shows() {
    let c = &*CORPUS;
    let (p, a) = (&c.program, &c.analysis);
    let by = spellings(p, a);
    let (mut census, mut misspelled, mut bad) = (Census::default(), Vec::new(), Vec::new());
    let started = std::time::Instant::now();
    for (entry, text) in swept_texts(c) {
        let Some(v) = view_of(p, a, &Overlay::default(), entry, text) else {
            misspelled.push(format!("{entry:#x}: no view"));
            continue;
        };
        if v.spell() != text && misspelled.len() < 10 {
            misspelled.push(format!("{entry:#x}"));
        }
        bad.extend(unborne(p, a, entry, &v, text));
        census.add(entry, &v, &by);
    }
    let share = |(n, k): (usize, usize)| format!("{k} of {n}");
    println!(
        "binary: {}\nviews: {:?}\ncall tokens: {} linked; resolvable: {} linked; ambiguous {}\nfirst resolvable unlinked: {:?}\nvariables: {} linked; labels: {} linked; globals: {} linked\nthe views counted: {} uncorroborated, {} ambiguous",
        c.path,
        started.elapsed(),
        share(census.calls),
        share(census.resolvable),
        census.ambiguous,
        census.examples,
        share(census.kinds[0]),
        share(census.kinds[1]),
        share(census.kinds[2]),
        census.counted.0,
        census.counted.1,
    );
    assert!(
        misspelled.is_empty(),
        "views that do not spell their text: {misspelled:?}"
    );
    assert!(
        bad.is_empty(),
        "{} ids no fact bears out: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
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
    assert_eq!(
        undeclared_slots("uint64_t (*arg_20)(uint64_t);\narg_20(local_8);\n"),
        vec!["local_8".to_owned()]
    );
    let inline = "static inline uint64_t f(void *a1) { uint64_t local_8; \
                  *(uint64_t*)a1 = local_8; return a1; }\n";
    assert_eq!(
        undeclared_slots(&format!("{inline}return f(a1);\n")),
        Vec::<String>::new()
    );
    assert_eq!(
        undeclared_slots(&format!("{inline}local_8 = f(a1);\n")),
        vec!["local_8".to_owned()]
    );
    assert_eq!(
        undeclared_slots(
            "static inline uint64_t g(void *a1) { *(uint64_t*)a1 = local_8; return a1; }\n\
             uint64_t local_8;\nlocal_8 = g(a1);\n"
        ),
        vec!["local_8".to_owned()]
    );
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
    use borer_engine::analysis::decompile::verify::verify_tsv;
    let started = std::time::Instant::now();
    let v = CORPUS.verified();
    let took = started.elapsed();
    let text = verify_tsv(v);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    eprintln!("# verify took {took:.1?}");
    let functions = CORPUS.analysis.functions.len();
    assert_eq!(v.functions, functions, "functions left out of the check");
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
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
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
    assert_eq!(
        v.functions,
        entries.len(),
        "functions left out of the check"
    );
    assert!(v.checked > 0, "{text}");
    assert!(v.mismatches.is_empty(), "{text}");
}

/// Checks the lifter against the emulator on every block of the
/// `BORER_DOGFOOD` binary through MIR as well as through the expressions.
///
/// Both readings must compare the same facts and agree on every one.
/// MIR states every width the expressions leave to their reader, so a
/// lowering that changed what a value means shows here as a fact one
/// reading compares and the other does not, or as a disagreement. An
/// arm64 binary is checked against the arm64 machine.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn the_mir_agrees_with_the_emulator_as_the_expressions_do() {
    use borer_engine::analysis::decompile::verify;
    let c = &*CORPUS;
    let (p, a, entries) = (&c.program, &c.analysis, c.entries());
    let (expr, mir) = (c.verified(), verify::verify_mir(p, a, &entries, 1));
    let text = verify::verify_tsv(&mir);
    for line in text.lines().take_while(|l| l.starts_with('#')) {
        eprintln!("{line}");
    }
    assert!(mir.checked > 0, "{text}");
    assert_eq!(mir.facts, expr.facts, "{text}");
    assert!(mir.mismatches.is_empty(), "{text}");
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
    let seed: u64 = std::env::var("BORER_DOGFOOD_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let c = &*CORPUS;
    let (path, p, a) = (&c.path, &c.program, &c.analysis);
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && f.funclet.is_none())
        .map(|f| f.entry)
        .collect();
    let threads = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let started = std::time::Instant::now();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut each: Vec<(u64, std::time::Duration, Replayed)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|_| {
                let (p, a, entries, next) = (&p, &a, &entries, &next);
                scope.spawn(move || {
                    let mut done = Vec::new();
                    while let Some(&e) =
                        entries.get(next.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
                    {
                        let t0 = std::time::Instant::now();
                        let r = replay_function(p, a, e, seed);
                        done.push((e, t0.elapsed(), r));
                    }
                    done
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
/// differs. `BORER_DOGFOOD_ONLY` (`0x`-hex) narrows the sweep to one
/// entry and prints the text under test.
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
    let only = std::env::var("BORER_DOGFOOD_ONLY")
        .ok()
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok());
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && f.funclet.is_none() && f.instr_count <= small)
        .filter(|f| only.is_none_or(|e| f.entry == e))
        .map(|f| f.entry)
        .collect();
    if let Some(e) = only {
        let text = borer_engine::analysis::decompile::decompile_named(&p, &a, &o, e)
            .unwrap_or_else(|| "(no text)".to_owned());
        eprintln!("TEXT of {e:#x}:\n{text}");
    }
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
                            if only.is_some() {
                                eprintln!("UNCHECKED	{e:#x}	{args}	{reason}");
                            }
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

/// Reads every function's text of the `BORER_DOGFOOD` binary and requires
/// each value it reads to come from a line of it or be an input.
///
/// A register variable that no line sets before a read holds only what the
/// register held at entry: unless it is a parameter, the text lost the
/// value on its way ([`decompile::unset_reads`]). The per-block replay
/// cannot see it, since it rebuilds each block's inputs from the machine.
/// It prints each flagged line (`entry`, line, names, the line itself), the
/// tally by the name read (`r10`, `tmp_N`, ...), and why texts went
/// unread, the first `BORER_DOGFOOD_SHOW` rows (40) in full.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_value_the_text_reads_is_set_or_an_input() {
    use borer_engine::analysis::decompile;
    let path = std::env::var("BORER_DOGFOOD").expect("BORER_DOGFOOD env var");
    let show: usize = std::env::var("BORER_DOGFOOD_SHOW")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(40);
    let p = Program::load_with(std::path::Path::new(&path), false).expect("load");
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && f.funclet.is_none())
        .map(|f| f.entry)
        .collect();
    let texts = decompile_named_all(&p, &a, &o, &entries);
    let started = std::time::Instant::now();
    let (mut read, mut flagged) = (0usize, Vec::new());
    let mut unread: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut by_name: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (e, text) in entries.iter().zip(&texts) {
        let Some(text) = text else { continue };
        match decompile::unset_reads(&p, &a, &o, *e, text) {
            Ok(rows) => {
                read += 1;
                for (line, names) in rows {
                    for n in &names {
                        let class = n.trim_end_matches(|c: char| c.is_ascii_digit());
                        *by_name.entry(class.to_owned()).or_default() += 1;
                    }
                    let shown = text.lines().nth(line - 1).unwrap_or("").trim();
                    flagged.push(format!("{e:#x}	L{line}	{}	{shown}", names.join(",")));
                }
            }
            Err(why) => *unread.entry(why).or_default() += 1,
        }
    }
    for f in flagged.iter().take(show) {
        eprintln!("UNSET	{f}");
    }
    for (n, k) in &by_name {
        eprintln!("NAME	{k}	{n}");
    }
    for (why, k) in &unread {
        eprintln!("UNREAD	{k}	{why}");
    }
    let functions: BTreeSet<&str> = flagged
        .iter()
        .filter_map(|f| f.split('\t').next())
        .collect();
    eprintln!(
        "binary: {path}
texts read {read} of {}; lines reading an unset value {} in {} functions; check {:.1?}",
        entries.len(),
        flagged.len(),
        functions.len(),
        started.elapsed()
    );
    assert!(read > 0, "no text was read");
    assert!(
        flagged.is_empty(),
        "{} lines read a value no line sets",
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
    use borer_engine::analysis::decompile::traces::{Structure, check, check_all};
    let c = &*CORPUS;
    let (path, p, a, entries) = (&c.path, &c.program, &c.analysis, c.entries());
    let o = Overlay::default();
    let t0 = std::time::Instant::now();
    let texts: Vec<_> = c
        .swept()
        .iter()
        .map(|s| s.as_ref().and_then(|s| s.fields.as_ref()))
        .collect();
    let decompiled = t0.elapsed();
    let t1 = std::time::Instant::now();
    let verdicts = check_all(p, a, &o, &entries, &texts);
    let checked = t1.elapsed();
    let mut each: Vec<(std::time::Duration, u64)> = Vec::new();
    for ((e, t), v) in entries.iter().zip(&texts).zip(&verdicts) {
        let Some((text, live)) = t else { continue };
        let t2 = std::time::Instant::now();
        let again = check(p, a, &o, *e, text, live);
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
