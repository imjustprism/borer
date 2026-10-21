//! The analysis-then-decompile step every pseudo-C test takes, the image
//! hand-assembled code is decompiled from, and the check that the text
//! runs as the binary does.

use borer_engine::analysis::decompile::{decompile, decompile_named};
use borer_engine::analysis::render::{Verdict, check_generated};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// Decompiles one function of `p` under a fresh analysis and an empty
/// overlay.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or an empty string when decompilation fails, so an
/// assertion on the text prints what came back.
pub(crate) fn decompiled(p: &Program, entry: u64) -> String {
    let a = Analysis::compute(p);
    decompile(p, &a, &Overlay::default(), entry).unwrap_or_default()
}

/// Builds a 64-bit PE-shaped program of `code` at 0x140001000 with no
/// symbols.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
pub(crate) fn program64(code: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_1000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    p
}

/// Asserts that the text of each function agrees with the machine on
/// every block from several seeds, the replay the dogfood sweep runs.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `entries` - The functions to replay.
///
/// # Panics
///
/// When a statement disagrees with the machine, with the table.
pub(crate) fn replays_clean(p: &Program, a: &Analysis, entries: &[u64]) {
    use borer_engine::analysis::decompile::replay::{replay, replay_tsv};
    for seed in 1..=4 {
        let r = replay(p, a, entries, seed);
        assert!(r.wrong().is_empty(), "seed {seed}:\n{}", replay_tsv(&r));
    }
}

/// Runs a function's final text as C beside the binary in the emulator on
/// 64 inputs its signature types, and requires every run the binary
/// returns from to agree.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
///
/// # Returns
///
/// The final text, for the caller's own assertions.
///
/// # Panics
///
/// When a run of the text differs from the binary, or none agrees.
pub(crate) fn runs_agree(p: &Program, entry: u64) -> String {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let text = decompile_named(p, &a, &o, entry).unwrap_or_default();
    let runs = check_generated(p, &a, &o, entry, 64, 1, 20_000).unwrap_or_default();
    let differ: Vec<String> = runs
        .iter()
        .filter_map(|(args, v)| match v {
            Verdict::Differs(line, what) => Some(format!("{args}: L{line} {what}")),
            Verdict::Agrees | Verdict::Unchecked(..) => None,
        })
        .collect();
    assert!(differ.is_empty(), "{}\n{text}", differ.join("\n"));
    assert!(
        runs.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{runs:?}\n{text}"
    );
    text
}
