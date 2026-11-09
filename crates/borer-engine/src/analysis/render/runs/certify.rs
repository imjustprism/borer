//! How far a decompilation was checked against the binary.
//!
//! The lifted blocks replayed against the emulator and the final text run
//! as ISO C beside it, read off as one grade, for one function or a page
//! of them.

use std::fmt::Write as _;

use super::blame::{BLAME_STEPS, function_count_steps, run_option};
use super::vectors::{VERIFY_SEED, generated_in};
use super::{NOT_MODELED_SHOWN, Outcome, Verdict, not_modeled, within_total};
use crate::analysis::decompile::interp::Mode;
use crate::analysis::decompile::text_check;
use crate::analysis::render::*;
use crate::text::one_line;

/// Most reasons an input went unchecked the answer lists.
const REASONS_SHOWN: usize = 3;

/// Block starts the answer names as never reached before the rest are
/// counted.
const NEVER_SHOWN: usize = 6;

/// Calls answered by default a page row names before the rest are counted.
const ROW_NAMES: usize = 3;

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
/// checked and nothing was contradicted, else `unchecked`. An agreement is
/// only as wide as the inputs went, so the answer says how many of the
/// function's blocks they reached and which they never did, and names the
/// calls the runs answered with the default because nothing models them:
/// the text was checked against that answer only. A spec opening with `*`
/// grades a page of functions instead ([`certify_many`]).
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
/// unchecked, the first input that differs, the `reached` line, a `not
/// modeled` line when a run rested on a call nothing models, and the
/// `grade` line.
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
        .and_then(|()| generated_in(p, a, o, entry, (count, VERIFY_SEED, budget), Mode::Iso));
    let tally = match &runs {
        Ok(runs) => {
            let tally = Tally::of(runs, &block_starts(a, entry));
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
            let _ = writeln!(out, "reached\t{}", tally.reach());
            if let Some(names) = not_modeled(runs.iter().map(|(_, x)| x), NOT_MODELED_SHOWN) {
                let _ = writeln!(
                    out,
                    "not modeled\t{names}: each did nothing and answered 0 wherever the binary or the text called it, so what follows them was checked against that answer only"
                );
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
    /// The function's blocks.
    blocks: usize,
    /// Its block starts no input's run of the binary executed, in address
    /// order.
    never: Vec<u64>,
}

impl<'r> Tally<'r> {
    /// Counts each input's verdict and the blocks the inputs reached.
    ///
    /// # Arguments
    ///
    /// * `runs` - Each input's arguments and its outcome.
    /// * `starts` - The function's block starts, in address order.
    fn of(runs: &'r [(String, Outcome)], starts: &[u64]) -> Self {
        let mut t = Tally::default();
        let mut why: BTreeMap<&str, usize> = BTreeMap::new();
        let mut reached = BTreeSet::new();
        for (input, x) in runs {
            reached.extend(x.reached.iter().copied());
            match &x.verdict {
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
        t.blocks = starts.len();
        t.never = starts
            .iter()
            .copied()
            .filter(|s| !reached.contains(s))
            .collect();
        t
    }

    /// How far the inputs reached: `N of M blocks`, and the first block
    /// starts they never reached.
    fn reach(&self) -> String {
        let mut line = format!(
            "{} of {} blocks",
            self.blocks - self.never.len(),
            self.blocks
        );
        if !self.never.is_empty() {
            let named: Vec<String> = self
                .never
                .iter()
                .take(NEVER_SHOWN)
                .map(|s| format!("{s:#x}"))
                .collect();
            let _ = write!(line, "; never reached: {}", named.join(", "));
            if self.never.len() > NEVER_SHOWN {
                let _ = write!(line, " and {} more", self.never.len() - NEVER_SHOWN);
            }
        }
        line
    }

    /// The grade and what it means: `differs` when the lift or an input is
    /// contradicted, `agrees` when an input was checked, else `unchecked`.
    /// An agreement over inputs that left blocks unreached says how many
    /// they reached.
    ///
    /// # Arguments
    ///
    /// * `lift_wrong` - Whether the binary contradicts a lifted block.
    fn grade(&self, lift_wrong: bool) -> (&'static str, String) {
        if lift_wrong || self.differ > 0 {
            (
                "differs",
                "the binary contradicts the decompilation where the lines above say".to_owned(),
            )
        } else if self.agree > 0 {
            let over = if self.never.is_empty() {
                String::new()
            } else {
                format!(
                    " (they reached {} of {} blocks)",
                    self.blocks - self.never.len(),
                    self.blocks
                )
            };
            (
                "agrees",
                format!("every input checked agrees{over} and no lifted block is contradicted"),
            )
        } else {
            (
                "unchecked",
                "no input was checked, so nothing is claimed of the text".to_owned(),
            )
        }
    }
}

/// A function's block starts, in address order; empty when no function
/// starts at `entry`.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `entry` - The function's entry.
fn block_starts(a: &Analysis, entry: u64) -> Vec<u64> {
    a.function(entry)
        .map(|f| f.blocks.iter().map(|b| b.start).collect())
        .unwrap_or_default()
}

/// Grades a page of functions as [`certify_tsv`] grades one, a row each.
///
/// The functions are those whose name holds the filter (any case), in
/// address order, from `offset`, at most `limit` ([`PAGE_LIMIT`] unless
/// the spec says, at most [`PAGE_MAX`]), each on [`PAGE_INPUTS`] inputs
/// unless the spec says. A row's note is the first lifted statement the
/// binary contradicts, then the first input that differs, else the
/// commonest reason inputs went unchecked, else why the text check did not
/// run. The two last columns say how far the inputs reached and what they
/// rested on that nothing models ([`reach_columns`]).
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
            let runs = x86.clone().and_then(|()| {
                generated_in(p, a, o, *entry, (count, VERIFY_SEED, budget), Mode::Iso)
            });
            let (tally, note) = match &runs {
                Ok(runs) => {
                    let tally = Tally::of(runs, &block_starts(a, *entry));
                    let note = tally.first.map_or_else(
                        || tally.reasons.first().map_or("", |r| r.0).to_owned(),
                        |(input, line, what)| differs_note(input, line, what),
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
                    "{name}\t{entry:#x}\t{grade}\t{}\t{}\t{}\t{note}\t{}\n",
                    tally.agree,
                    tally.unchecked,
                    tally.differ,
                    reach_columns(&runs, &tally)
                ),
            )
        },
    );
    let rows: Vec<(&str, String)> = rows.into_iter().flatten().collect();
    let tally_of = |g: &str| rows.iter().filter(|(grade, _)| *grade == g).count();
    let mut out = format!(
        "# certify: {} agrees, {} unchecked, {} differs of {} functions graded, {count} inputs each (seed {VERIFY_SEED}, {budget} steps each); agreement is evidence, not proof\n# function\tentry\tgrade\tagree\tunchecked\tdiffer\tnote\treached\tnot modeled\n",
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

/// Returns a page row's last two columns, how far its inputs went.
///
/// The first is the function's blocks the inputs reached, as
/// `reached/blocks`; the second the calls the binary's runs answered with
/// the default because nothing models them, at most [`ROW_NAMES`] named.
///
/// # Arguments
///
/// * `runs` - Each input with its outcome, or why the text check did not
///   run.
/// * `tally` - What the inputs found.
///
/// # Returns
///
/// The two columns, tab-separated; `-` for each when the check did not
/// run, and for the second when every call was modeled.
fn reach_columns(runs: &Result<Vec<(String, Outcome)>, String>, tally: &Tally<'_>) -> String {
    let Ok(runs) = runs else {
        return "-\t-".to_owned();
    };
    let names =
        not_modeled(runs.iter().map(|(_, x)| x), ROW_NAMES).unwrap_or_else(|| "-".to_owned());
    format!(
        "{}/{}\t{names}",
        tally.blocks - tally.never.len(),
        tally.blocks
    )
}

/// A page row's note for the first input that differs: the line and what
/// differs first, the input last, so the cut at [`NOTE_MAX`] drops the
/// input's bytes before the reason.
///
/// # Arguments
///
/// * `input` - The input's arguments as a row spells them, empty for none.
/// * `line` - The text's line.
/// * `what` - What differs there.
fn differs_note(input: &str, line: usize, what: &str) -> String {
    if input.is_empty() {
        format!("line {line}: {what}")
    } else {
        format!("line {line}: {what}; on {input}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A row's note says where and what differs before the input, so a
    /// long input is what the cut drops.
    ///
    /// # Panics
    ///
    /// When the note starts otherwise or keeps the input's tail.
    #[test]
    fn a_note_leads_with_the_reason() {
        let long = format!("hex:{}", "ab".repeat(80));
        let note: String = differs_note(&long, 7, "`rax` is read before any line sets it")
            .chars()
            .take(NOTE_MAX)
            .collect();
        assert!(
            note.starts_with("line 7: `rax` is read before any line sets it; on hex:"),
            "{note}"
        );
        assert_eq!(differs_note("", 3, "x"), "line 3: x");
    }
}
