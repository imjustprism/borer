//! How far a decompilation was checked against the binary.
//!
//! The lifted blocks replayed against the emulator and the final text run
//! as ISO C beside it, read off as one grade, for one function or a page
//! of them.

use std::fmt::Write as _;

use super::blame::{BLAME_STEPS, function_count_steps, run_option};
use super::vectors::VERIFY_SEED;
use super::{Verdict, check_generated_iso, within_total};
use crate::analysis::decompile::text_check;
use crate::analysis::render::*;
use crate::text::one_line;

/// Most reasons an input went unchecked the answer lists.
const REASONS_SHOWN: usize = 3;

/// Functions a page of [`certify_many`] grades unless it says.
const PAGE_LIMIT: usize = 32;

/// Most functions one page of [`certify_many`] grades.
const PAGE_MAX: usize = 64;

/// Inputs each function of a page draws unless the spec says.
const PAGE_INPUTS: usize = 16;

/// Characters of a page row's note kept, the rest cut.
const NOTE_MAX: usize = 100;

/// Says how far a function's decompilation was checked against the binary.
///
/// Two checks are read together. The lift: the statements the lifter
/// emitted, replayed block by block against the emulator (the `checked vs
/// binary` line of `decompile`). The text: the final pseudo-C run as ISO C
/// beside the binary on inputs drawn from its signature, each input
/// agreeing, differing, or unchecked with a reason, counted apart so an
/// unchecked input never reads as agreement. The grade is `differs` when
/// either check is contradicted, `agrees` when at least one input was
/// checked and nothing was contradicted, else `unchecked`. A spec opening
/// with `*` grades a page of functions instead ([`certify_many`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and passes.
/// * `spec` - `<function>[,count=N][,steps=N]`: the function by address or
///   name, how many inputs (1 to 64, 64 by default) and the steps each run
///   is given (20000 by default); or `*[filter][,offset=N][,limit=N]
///   [,count=N][,steps=N]`.
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
    if let Some(many) = spec.trim_start().strip_prefix('*') {
        return certify_many(p, a, o, many);
    }
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
    let tally = match &runs {
        Ok(runs) => {
            let tally = Tally::of(runs);
            let _ = writeln!(
                out,
                "text\t{} of {} inputs agree as ISO C, {} unchecked, {} differ (seed {VERIFY_SEED}, {budget} steps each)",
                tally.agree,
                runs.len(),
                tally.unchecked,
                tally.differ
            );
            for (reason, n) in tally.reasons.iter().take(REASONS_SHOWN) {
                let _ = writeln!(out, "unchecked\t{n}\t{reason}");
            }
            if let Some((input, line, what)) = tally.first {
                let _ = writeln!(out, "differs\t{input}\t{line}\t{what}");
            }
            tally
        }
        Err(why) => {
            let _ = writeln!(out, "text\tnot run: {why}");
            Tally::default()
        }
    };
    let (grade, meaning) = tally.grade(lift_wrong);
    let _ = writeln!(out, "grade\t{grade}\t{meaning}");
    Ok(out)
}

/// What a text check found over its inputs.
#[derive(Debug, Default)]
struct Tally<'r> {
    /// Inputs that agree.
    agree: usize,
    /// Inputs left unchecked.
    unchecked: usize,
    /// Inputs that differ.
    differ: usize,
    /// Why inputs went unchecked, with how many, most first.
    reasons: Vec<(&'r str, usize)>,
    /// The first input that differs: its arguments, the line and what
    /// differs.
    first: Option<(&'r str, usize, &'r str)>,
}

impl<'r> Tally<'r> {
    /// Counts each input's verdict.
    ///
    /// # Arguments
    ///
    /// * `runs` - Each input's arguments and the text's verdict on it.
    fn of(runs: &'r [(String, Verdict)]) -> Self {
        let mut t = Tally::default();
        let mut why: BTreeMap<&str, usize> = BTreeMap::new();
        for (input, v) in runs {
            match v {
                Verdict::Agrees => t.agree += 1,
                Verdict::Unchecked(_, reason) => {
                    t.unchecked += 1;
                    *why.entry(reason.as_str()).or_default() += 1;
                }
                Verdict::Differs(line, what) => {
                    t.differ += 1;
                    t.first
                        .get_or_insert((input.as_str(), *line, what.as_str()));
                }
            }
        }
        t.reasons = why.into_iter().collect();
        t.reasons.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(y.0)));
        t
    }

    /// The grade and what it means: `differs` when the lift or an input is
    /// contradicted, `agrees` when an input was checked, else `unchecked`.
    ///
    /// # Arguments
    ///
    /// * `lift_wrong` - Whether the binary contradicts a lifted block.
    fn grade(&self, lift_wrong: bool) -> (&'static str, &'static str) {
        if lift_wrong || self.differ > 0 {
            (
                "differs",
                "the binary contradicts the decompilation where the lines above say",
            )
        } else if self.agree > 0 {
            (
                "agrees",
                "every input checked agrees and no lifted block is contradicted",
            )
        } else {
            (
                "unchecked",
                "no input was checked, so nothing is claimed of the text",
            )
        }
    }
}

/// Grades a page of functions as [`certify_tsv`] grades one, a row each.
///
/// The functions are those whose name holds the filter (any case), in
/// address order, from `offset`, at most `limit` ([`PAGE_LIMIT`] unless
/// the spec says, at most [`PAGE_MAX`]), each on [`PAGE_INPUTS`] inputs
/// unless the spec says. A row's note is the first lifted statement the
/// binary contradicts, then the first input that differs, else the
/// commonest reason inputs went unchecked, else why the text check did not
/// run.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and passes.
/// * `spec` - `[filter][,offset=N][,limit=N][,count=N][,steps=N]`.
///
/// # Errors
///
/// When an option does not read or is out of range, or the page asks for
/// more steps than one request runs.
fn certify_many(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    let (filter, rest) = spec_head(spec);
    let (mut count, mut budget, mut offset, mut limit) = (PAGE_INPUTS, BLAME_STEPS, 0, PAGE_LIMIT);
    for option in rest.map(str::trim) {
        if run_option(option, &mut count, &mut budget)? {
            continue;
        }
        match option.split_once('=') {
            Some(("offset", n)) => offset = parse_count(n).ok_or("offset is a count")?,
            Some(("limit", n)) => {
                limit = parse_count(n)
                    .filter(|n| (1..=PAGE_MAX).contains(n))
                    .ok_or_else(|| format!("limit is 1 to {PAGE_MAX}"))?;
            }
            _ => {
                return Err(format!(
                    "certify takes *[filter][,offset=N][,limit=N][,count=N][,steps=N]; cannot read {}",
                    one_line(option)
                ));
            }
        }
    }
    let needle = filter.to_ascii_lowercase();
    let matching: Vec<(u64, String)> = a
        .functions
        .iter()
        .map(|f| (f.entry, name_of(a, o, f.entry)))
        .filter(|(_, n)| n.to_ascii_lowercase().contains(&needle))
        .collect();
    let page = matching.get(offset..).unwrap_or_default();
    let page = page.get(..limit.min(page.len())).unwrap_or_default();
    within_total(count.saturating_mul(page.len()), budget)?;
    let x86 = x86_only(p, "the text check");
    let rows = crate::analysis::striped_with(
        page,
        1,
        || (),
        |(), (entry, name)| {
            let lift = text_check(p, a, o, *entry);
            let disagree = lift.as_ref().as_ref().and_then(|c| c.disagree.first());
            let runs = x86
                .clone()
                .and_then(|()| check_generated_iso(p, a, o, *entry, count, VERIFY_SEED, budget));
            let (tally, note) = match &runs {
                Ok(runs) => {
                    let tally = Tally::of(runs);
                    let note = tally.first.map_or_else(
                        || tally.reasons.first().map_or("", |r| r.0).to_owned(),
                        |(input, line, what)| format!("differs on {input} at line {line}: {what}"),
                    );
                    (tally, note)
                }
                Err(why) => (Tally::default(), format!("not run: {why}")),
            };
            let (grade, _) = tally.grade(disagree.is_some());
            let note = match disagree {
                Some(at) => format!("the lift disagrees with the binary at {at:#x}; {note}"),
                None => note,
            };
            let note: String = one_line(&note).chars().take(NOTE_MAX).collect();
            (
                grade,
                format!(
                    "{name}\t{entry:#x}\t{grade}\t{}\t{}\t{}\t{note}\n",
                    tally.agree, tally.unchecked, tally.differ
                ),
            )
        },
    );
    let rows: Vec<(&str, String)> = rows.into_iter().flatten().collect();
    let tally_of = |g: &str| rows.iter().filter(|(grade, _)| *grade == g).count();
    let mut out = format!(
        "# certify: {} agrees, {} unchecked, {} differs of {} functions graded, {count} inputs each (seed {VERIFY_SEED}, {budget} steps each); agreement is evidence, not proof\n# function\tentry\tgrade\tagree\tunchecked\tdiffer\tnote\n",
        tally_of("agrees"),
        tally_of("unchecked"),
        tally_of("differs"),
        rows.len()
    );
    for (_, row) in &rows {
        out.push_str(row);
    }
    let _ = writeln!(
        out,
        "# showing {} of {} functions from {offset}",
        rows.len(),
        matching.len()
    );
    Ok(out)
}
