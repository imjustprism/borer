//! Which cleanup pass breaks a function's text: the bisection of
//! [`bisect_iso`] read off as an answer.

use std::fmt::Write as _;

use super::vectors::VERIFY_SEED;
use super::{BUDGET_MAX, Bisected, INPUTS_MAX, bisect_iso, unchecked_rows, within_total};
use crate::analysis::decompile::Pass;
use crate::analysis::render::diff::{DIFF_FN_MAX_LINES, line_diff, render_collapsed};
use crate::analysis::render::*;
use crate::text::one_line;

/// Inputs a blame draws when the spec names no count.
const BLAME_INPUTS: usize = INPUTS_MAX;

/// Steps each run of a blame is given when the spec names none.
pub(super) const BLAME_STEPS: usize = 20_000;

/// Lines of the before-and-after diff a blame shows.
const BLAME_DIFF_LINES: usize = 60;

/// Most times a bisection runs its inputs: the full text, the text with
/// no pass, one probe per halving of [`Pass::ALL`], and the full text
/// with the blamed pass alone left out.
fn bisect_runs() -> usize {
    let halvings = Pass::ALL.len().next_power_of_two().trailing_zeros();
    3usize.saturating_add(usize::try_from(halvings).unwrap_or(usize::MAX))
}

/// Names the first text cleanup pass that breaks a function, the input it
/// differs on, and whether leaving that pass out alone repairs it.
///
/// The function's text is run as ISO C beside the binary on inputs drawn
/// from its signature ([`bisect_iso`]); the answer says when the text
/// agrees on every input it was checked on, when no input was checked and
/// why, when it differs before any pass ran, and when the check cannot run
/// (an error).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and passes.
/// * `spec` - `<function>[,count=N][,steps=N]`: the function by address or
///   name, how many inputs (1 to 64, 64 by default) and the steps each run
///   is given (20000 by default). The bisection runs the inputs up to
///   [`bisect_runs`] times, and all of them together must stay within the
///   steps one request runs.
///
/// # Returns
///
/// The answer: a header, then the verdict lines (for a text no input
/// checked, `unchecked` and how many inputs each reason left so) and the
/// capped diff of the text before and after the pass.
///
/// # Errors
///
/// For an arm program, a spec that does not read or asks for more steps
/// than one request runs, a target that names no function, or a function
/// whose text does not decompile or whose signature types no inputs.
pub fn blame_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    x86_only(p, "blame")?;
    let (entry, count, budget) = function_count_steps(a, o, spec, "blame")?;
    within_total(count.saturating_mul(bisect_runs()), budget).map_err(|_| {
        format!(
            "blame runs its {count} inputs up to {} times while it bisects, past the steps one request runs at {budget} steps each; lower steps= or count=",
            bisect_runs()
        )
    })?;
    let name = name_of(a, o, entry);
    let found = bisect_iso(p, a, o, entry, count, VERIFY_SEED, budget)
        .map_err(|why| format!("blame cannot check {name} ({entry:#x}): {why}"))?;
    Ok(blame_report(&name, entry, count, budget, &found))
}

/// Reads a `<function>[,count=N][,steps=N]` spec: the function's entry,
/// how many inputs (1 to [`INPUTS_MAX`], all of them by default) and the
/// steps each run is given ([`BLAME_STEPS`] by default).
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - The spec.
/// * `tool` - The answer's name, for a refusal.
///
/// # Errors
///
/// When the function names nothing, or an option does not read or is out
/// of range.
pub(super) fn function_count_steps(
    a: &Analysis,
    o: &Overlay,
    spec: &str,
    tool: &str,
) -> Result<(u64, usize, usize), String> {
    let (target, rest) = spec_head(spec);
    let start = locate(a, o, target).ok_or_else(|| unresolved(target))?;
    let entry = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?
        .entry;
    let (mut count, mut budget) = (BLAME_INPUTS, BLAME_STEPS);
    for option in rest.map(str::trim) {
        if !run_option(option, &mut count, &mut budget)? {
            return Err(format!(
                "{tool} takes <function>[,count=N][,steps=N]; cannot read {}",
                one_line(option)
            ));
        }
    }
    Ok((entry, count, budget))
}

/// Reads a `count=N` or `steps=N` option into what it sets.
///
/// # Arguments
///
/// * `option` - One option of a spec.
/// * `count` - How many inputs, 1 to [`INPUTS_MAX`].
/// * `budget` - The steps each run is given, 1 to [`BUDGET_MAX`].
///
/// # Returns
///
/// Whether the option was one of the two.
///
/// # Errors
///
/// When its value is out of range.
pub(super) fn run_option(
    option: &str,
    count: &mut usize,
    budget: &mut usize,
) -> Result<bool, String> {
    match option.split_once('=') {
        Some(("count", n)) => {
            *count = parse_count(n)
                .filter(|n| (1..=INPUTS_MAX).contains(n))
                .ok_or_else(|| format!("count is 1 to {INPUTS_MAX}"))?;
        }
        Some(("steps", n)) => {
            *budget = parse_count(n)
                .filter(|n| (1..=BUDGET_MAX).contains(n))
                .ok_or_else(|| format!("steps is 1 to {BUDGET_MAX}"))?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

/// Writes the answer of [`blame_tsv`] for one bisection.
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `entry` - The function's entry.
/// * `count` - How many inputs were drawn.
/// * `budget` - Steps each run was given.
/// * `found` - What the bisection found.
///
/// # Returns
///
/// The header, the verdict and, for a pass to blame, the capped diff.
fn blame_report(name: &str, entry: u64, count: usize, budget: usize, found: &Bisected) -> String {
    let mut out = format!(
        "# blame for {name} ({entry:#x}): its text run as ISO C beside the binary on {count} inputs drawn from its signature (seed {VERIFY_SEED}, {budget} steps each); an input the text leaves unchecked says nothing\n"
    );
    match found {
        Bisected::Agrees => out.push_str(
            "agrees\tno input differs, so no pass is to blame; agreement on drawn inputs is evidence, not proof\n",
        ),
        Bisected::Unchecked(reasons) => {
            out.push_str("unchecked\tno input was checked, so nothing is claimed of the text and no pass is blamed\n");
            unchecked_rows(&mut out, reasons);
        }
        Bisected::Unbisected(c) => {
            out.push_str("before-passes\tthe text differs with every cleanup pass left out, so the lift or the structure the passes start from is wrong, not a pass\n");
            let _ = writeln!(out, "differs\t{}\t{}\t{}", c.input, c.line, c.why);
        }
        Bisected::Broke {
            pass,
            at,
            alone,
            texts,
        } => {
            let _ = writeln!(
                out,
                "pass\t{}\tthe first cleanup pass whose text differs; the text with the passes before it agrees",
                pass.name()
            );
            let _ = writeln!(out, "differs\t{}\t{}\t{}", at.input, at.line, at.why);
            out.push_str(if *alone {
                "repairs\tyes: the full text with only this pass left out agrees on every input\n"
            } else {
                "repairs\tno: the full text with only this pass left out still differs, so a later pass breaks it too\n"
            });
            let before: Vec<&str> = texts.0.lines().take(DIFF_FN_MAX_LINES).collect();
            let after: Vec<&str> = texts.1.lines().take(DIFF_FN_MAX_LINES).collect();
            if texts.0.lines().count().max(texts.1.lines().count()) > DIFF_FN_MAX_LINES {
                let _ = writeln!(
                    out,
                    "# the texts run past {DIFF_FN_MAX_LINES} lines and only those are compared, so a change past them is not shown"
                );
            }
            let mut diff = String::new();
            render_collapsed(&mut diff, &line_diff(&before, &after));
            let total = diff.lines().count();
            let _ = writeln!(
                out,
                "# the text before and after {} (showing {} of {total} lines)",
                pass.name(),
                total.min(BLAME_DIFF_LINES)
            );
            for line in diff.lines().take(BLAME_DIFF_LINES) {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Bisected, blame_report};
    use crate::analysis::decompile::Pass;
    use crate::analysis::render::Counterexample;

    /// Returns a counterexample on input `5`.
    fn at() -> Counterexample {
        Counterexample {
            input: "5".to_owned(),
            line: "return x + 1;".to_owned(),
            why: "returned 6, the binary 7".to_owned(),
        }
    }

    /// A pass to blame is named with the input it differs on, whether
    /// leaving it out alone repairs the text, and the lines it changed.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn a_breaking_pass_is_named_with_its_input_and_diff() {
        let found = Bisected::Broke {
            pass: Pass::FoldTempCopies,
            at: at(),
            alone: true,
            texts: (
                "a;
b;
c;
"
                .to_owned(),
                "a;
B;
c;
"
                .to_owned(),
            ),
        };
        let text = blame_report("f", 0x1000, 8, 100, &found);
        let name = Pass::FoldTempCopies.name();
        assert!(text.contains(&format!("pass	{name}	")), "{text}");
        assert!(text.contains("differs	5	return x + 1;	returned 6, the binary 7"));
        assert!(text.contains("repairs	yes"), "{text}");
        assert!(
            text.contains(
                "  - b;
  + B;
"
            ),
            "{text}"
        );
    }

    /// A text that agrees blames nothing and says agreement is not proof;
    /// one that differs before any pass blames no pass.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn agreement_and_a_broken_start_blame_no_pass() {
        let agrees = blame_report("f", 0x1000, 8, 100, &Bisected::Agrees);
        assert!(agrees.contains("agrees	no input differs"), "{agrees}");
        assert!(agrees.contains("not proof"), "{agrees}");
        assert!(!agrees.contains("pass	"), "{agrees}");
        let before = blame_report("f", 0x1000, 8, 100, &Bisected::Unbisected(at()));
        assert!(before.contains("before-passes	"), "{before}");
        assert!(before.contains("differs	5	"), "{before}");
    }

    /// A pass that rewrites more lines than the answer shows is cut to
    /// the cap with its count.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn a_long_diff_is_capped() {
        let before: String = (0..200)
            .map(|k| {
                format!(
                    "a{k};
"
                )
            })
            .collect();
        let after: String = (0..200)
            .map(|k| {
                format!(
                    "b{k};
"
                )
            })
            .collect();
        let found = Bisected::Broke {
            pass: Pass::FoldJumps,
            at: at(),
            alone: false,
            texts: (before, after),
        };
        let text = blame_report("f", 0x1000, 8, 100, &found);
        assert!(text.contains("repairs	no"), "{text}");
        assert!(text.contains("(showing 60 of 400 lines)"), "{text}");
        assert!(text.lines().count() < 70, "{text}");
    }

    /// Texts longer than the diff compares say that a change past the
    /// compared lines is not shown.
    ///
    /// # Panics
    ///
    /// When the note is missing.
    #[test]
    fn a_text_past_the_compared_lines_says_so() {
        let long: String = (0..1600)
            .map(|k| {
                format!(
                    "x{k};
"
                )
            })
            .collect();
        let found = Bisected::Broke {
            pass: Pass::FoldJumps,
            at: at(),
            alone: true,
            texts: (
                long.clone(),
                format!(
                    "{long}y;
"
                ),
            ),
        };
        let text = blame_report("f", 0x1000, 8, 100, &found);
        assert!(text.contains("# the texts run past 1500 lines"), "{text}");
    }

    /// A text no input checked is unchecked, with how many inputs each
    /// reason left so, and is nowhere said to agree.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn a_text_no_input_checked_is_unchecked() {
        let reasons = vec![("it spins".to_owned(), 7), ("it faults".to_owned(), 1)];
        let text = blame_report("f", 0x1000, 8, 100, &Bisected::Unchecked(reasons));
        assert!(text.contains("\nunchecked\tno input was checked"), "{text}");
        assert!(
            text.ends_with("\nunchecked\t7\tit spins\nunchecked\t1\tit faults\n"),
            "{text}"
        );
        assert!(!text.contains("agree"), "{text}");
    }
}
