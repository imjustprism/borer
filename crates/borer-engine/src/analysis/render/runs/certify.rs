//! How far a function's decompilation was checked against the binary: the
//! lifted blocks replayed against the emulator and the final text run as
//! ISO C beside it, read off as one grade.

use std::fmt::Write as _;

use super::blame::function_count_steps;
use super::vectors::VERIFY_SEED;
use super::{Verdict, check_generated_iso, within_total};
use crate::analysis::decompile::text_check;
use crate::analysis::render::*;

/// Most reasons an input went unchecked the answer lists.
const REASONS_SHOWN: usize = 3;

/// Says how far a function's decompilation was checked against the binary.
///
/// Two checks are read together. The lift: the statements the lifter
/// emitted, replayed block by block against the emulator (the `checked vs
/// binary` line of `decompile`). The text: the final pseudo-C run as ISO C
/// beside the binary on inputs drawn from its signature, each input
/// agreeing, differing, or unchecked with a reason, counted apart so an
/// unchecked input never reads as agreement. The grade is `differs` when
/// either check is contradicted, `agrees` when at least one input was
/// checked and nothing was contradicted, else `unchecked`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and passes.
/// * `spec` - `<function>[,count=N][,steps=N]`: the function by address or
///   name, how many inputs (1 to 64, 64 by default) and the steps each run
///   is given (20000 by default).
///
/// # Returns
///
/// A header, a `lift` and a `text` line, the commonest reasons inputs went
/// unchecked, the first input that differs, and the `grade` line.
///
/// # Errors
///
/// When the spec does not read, names no function, or asks for more steps
/// than one request runs.
pub fn certify_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    let (entry, count, budget) = function_count_steps(a, o, spec, "certify")?;
    within_total(count, budget)?;
    let name = name_of(a, o, entry);
    let mut out = format!(
        "# certify for {name} ({entry:#x}): what of its decompilation was checked against the binary; agreement is evidence, not proof\n"
    );
    let lift = text_check(p, a, o, entry);
    let lift_wrong = match lift.as_ref() {
        Some(c) => {
            let header = c.header();
            let said = header
                .strip_prefix("// checked vs binary: ")
                .unwrap_or(&header);
            let _ = writeln!(out, "lift\t{said}");
            !c.disagree.is_empty()
        }
        None => {
            out.push_str(
                "lift\tnot checked: the function does not decompile or its code is not emulated\n",
            );
            false
        }
    };
    let runs = x86_only(p, "the text check")
        .and_then(|()| check_generated_iso(p, a, o, entry, count, VERIFY_SEED, budget));
    let (agree, differ) = match &runs {
        Ok(runs) => text_lines(&mut out, runs, budget),
        Err(why) => {
            let _ = writeln!(out, "text\tnot run: {why}");
            (0, 0)
        }
    };
    let (grade, meaning) = if lift_wrong || differ > 0 {
        (
            "differs",
            "the binary contradicts the decompilation where the lines above say",
        )
    } else if agree > 0 {
        (
            "agrees",
            "every input checked agrees and no lifted block is contradicted",
        )
    } else {
        (
            "unchecked",
            "no input was checked, so nothing is claimed of the text",
        )
    };
    let _ = writeln!(out, "grade\t{grade}\t{meaning}");
    Ok(out)
}

/// Writes the `text` line, the commonest reasons inputs went unchecked and
/// the first input that differs.
///
/// # Arguments
///
/// * `out` - The answer.
/// * `runs` - Each input's arguments and the text's verdict on it.
/// * `budget` - Steps each run was given.
///
/// # Returns
///
/// How many inputs agreed and how many differed.
fn text_lines(out: &mut String, runs: &[(String, Verdict)], budget: usize) -> (usize, usize) {
    let (mut agree, mut differ) = (0, 0);
    let mut why: BTreeMap<&str, usize> = BTreeMap::new();
    let mut first: Option<(&str, usize, &str)> = None;
    for (input, v) in runs {
        match v {
            Verdict::Agrees => agree += 1,
            Verdict::Unchecked(_, reason) => *why.entry(reason.as_str()).or_default() += 1,
            Verdict::Differs(line, what) => {
                differ += 1;
                first.get_or_insert((input.as_str(), *line, what.as_str()));
            }
        }
    }
    let unchecked = runs.len() - agree - differ;
    let _ = writeln!(
        out,
        "text\t{agree} of {} inputs agree as ISO C, {unchecked} unchecked, {differ} differ (seed {VERIFY_SEED}, {budget} steps each)",
        runs.len()
    );
    let mut reasons: Vec<(&str, usize)> = why.into_iter().collect();
    reasons.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(y.0)));
    for (reason, n) in reasons.iter().take(REASONS_SHOWN) {
        let _ = writeln!(out, "unchecked\t{n}\t{reason}");
    }
    if let Some((input, line, what)) = first {
        let _ = writeln!(out, "differs\t{input}\t{line}\t{what}");
    }
    (agree, differ)
}
