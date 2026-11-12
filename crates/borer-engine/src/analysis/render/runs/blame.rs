//! Which cleanup pass breaks a function's text: the bisection of
//! [`bisect_iso`] read off as an answer.

use std::fmt::Write as _;

use super::vectors::VERIFY_SEED;
use super::{
    BUDGET_MAX, Bisected, Checked, Grade, INPUTS_MAX, bisect_iso, commonest, unchecked_rows,
    within_total,
};
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
/// why, when it differs before any pass ran, when a text the bisection
/// needed left the differing input unchecked so that no pass can be named,
/// and when the check cannot run (an error).
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

/// How many of the inputs drawn a text agrees on and, when it left any
/// unchecked, how many and the commonest reason with its count: one input
/// that agrees beside 63 left unchecked is not 64 that agree.
///
/// # Arguments
///
/// * `c` - What the text's runs said.
/// * `count` - How many inputs were drawn.
fn agreed_on(c: &Checked, count: usize) -> String {
    let mut out = format!("{} of {count} inputs", c.agreed);
    let left: usize = c.unchecked.values().sum();
    if let Some((why, n)) = commonest(c.unchecked.clone()).first() {
        let _ = write!(out, ", {left} left unchecked ({n}: {why})");
    }
    out
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
        Bisected::Agrees(whole) => {
            let _ = writeln!(
                out,
                "agrees\tno input differs, so no pass is to blame; the text agrees on {}; agreement on drawn inputs is evidence, not proof",
                agreed_on(whole, count)
            );
        }
        Bisected::Unchecked(reasons) => {
            out.push_str("unchecked\tno input was checked, so nothing is claimed of the text and no pass is blamed\n");
            unchecked_rows(&mut out, reasons);
        }
        Bisected::Unbisected(c) => {
            out.push_str("before-passes\tthe text differs with every cleanup pass left out, so the lift or the structure the passes start from is wrong, not a pass\n");
            let _ = writeln!(out, "differs\t{}\t{}\t{}", c.input, c.line, c.why);
        }
        Bisected::Unplaced {
            at,
            ran,
            agreed,
            unchecked,
        } => {
            let which = match ran {
                0 => "every cleanup pass left out".to_owned(),
                n => format!("only its first {n} cleanup passes run"),
            };
            let left = match agreed {
                0 => "every input".to_owned(),
                n => format!("the input it differs on (agreeing on {n} of {count})"),
            };
            let _ = writeln!(
                out,
                "unplaced\tthe text differs, and with {which} it left {left} unchecked, which is neither agreement nor a difference, so no pass is named"
            );
            let _ = writeln!(out, "differs\t{}\t{}\t{}", at.input, at.line, at.why);
            unchecked_rows(&mut out, unchecked);
        }
        Bisected::Broke {
            pass,
            at,
            before,
            alone,
            texts,
        } => {
            let _ = writeln!(
                out,
                "pass\t{}\tthe first cleanup pass whose text differs; the text with the passes before it agrees on {}",
                pass.name(),
                agreed_on(before, count)
            );
            let _ = writeln!(out, "differs\t{}\t{}\t{}", at.input, at.line, at.why);
            let repairs = match alone.grade() {
                Grade::Agrees => format!("yes: the full text with only this pass left out agrees on {}", agreed_on(alone, count)),
                Grade::Differs => "no: the full text with only this pass left out still differs, so a later pass breaks it too".to_owned(),
                Grade::Unchecked if alone.agreed == 0 => "unchecked: the full text with only this pass left out left every input unchecked, so nothing is claimed of it".to_owned(),
                Grade::Unchecked => format!("unchecked: the full text with only this pass left out left the input the text differs on unchecked, so nothing is claimed of it; it agrees on {}", agreed_on(alone, count)),
            };
            let _ = writeln!(out, "repairs\t{repairs}");
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
    use super::super::vectors::bisected;
    use super::{Bisected, blame_report};
    use crate::analysis::decompile::{Pass, Passes};
    use crate::analysis::render::{Checked, Counterexample};

    /// Returns a counterexample on input `5`.
    fn at() -> Counterexample {
        Counterexample {
            input: "5".to_owned(),
            line: "return x + 1;".to_owned(),
            why: "returned 6, the binary 7".to_owned(),
        }
    }

    /// Returns what a text's runs said.
    ///
    /// # Arguments
    ///
    /// * `agreed` - Inputs it agreed on.
    /// * `spun` - Inputs it left unchecked, for spinning.
    /// * `differs` - Whether it differs on [`at`].
    fn ran(agreed: usize, spun: usize, differs: bool) -> Checked {
        Checked {
            differs: differs.then(at),
            differed: differs.then_some(5),
            agreed,
            unchecked: (spun > 0)
                .then(|| ("it spins".to_owned(), spun))
                .into_iter()
                .collect(),
            missed: false,
        }
    }

    /// Bisects texts that agree while fewer than `agree` passes run, check
    /// no input while fewer than `unchecked` run, and differ from there on,
    /// the full text too.
    ///
    /// The full text with one pass left out runs all but one, which no
    /// text of a bisection that ends below the last pass does.
    ///
    /// # Arguments
    ///
    /// * `agree` - Passes run in the first text that does not agree.
    /// * `unchecked` - Passes run in the first text that differs.
    /// * `alone` - What the full text with one pass left out does.
    fn found(agree: usize, unchecked: usize, alone: &Checked) -> Bisected {
        let check = |skip: Passes, _: Option<usize>| match Pass::ALL
            .iter()
            .filter(|p| skip.runs(**p))
            .count()
        {
            k if k + 1 == Pass::ALL.len() => alone.clone(),
            k if k < agree => ran(8, 0, false),
            k if k < unchecked => ran(0, 8, false),
            _ => ran(3, 0, true),
        };
        bisected(&check, &|k| format!("{k} passes"))
    }

    /// A text of the bisection no input checked places no pass, and one
    /// the blamed pass was left out of repairs nothing.
    ///
    /// Read as agreement, the texts that checked nothing put the blame on
    /// the first pass after them, the eleventh or the forty-first here,
    /// though no text before it was seen to agree, and a full text that
    /// checked nothing without that pass read as repaired. The search
    /// stops at the first such text it meets instead; with every text
    /// decided it names the pass after the last that agreed, and hands on
    /// what the text without it did.
    ///
    /// # Panics
    ///
    /// When the bisection names a pass on a text that checked nothing.
    #[test]
    fn a_probe_no_input_checked_places_no_pass() {
        let unplaced = |ran| Bisected::Unplaced {
            at: at(),
            ran,
            agreed: 0,
            unchecked: vec![("it spins".to_owned(), 8)],
        };
        let spun = ran(0, 8, false);
        assert_eq!(found(0, 10, &spun), unplaced(0));
        assert_eq!(found(4, 40, &spun), unplaced(32));
        assert_eq!(found(0, 0, &spun), Bisected::Unbisected(at()));
        for alone in [spun, ran(8, 0, false), ran(2, 0, true)] {
            let broke = Bisected::Broke {
                pass: Pass::ALL[9],
                at: at(),
                before: Box::new(ran(8, 0, false)),
                alone: Box::new(alone.clone()),
                texts: ("9 passes".to_owned(), "10 passes".to_owned()),
            };
            assert_eq!(found(10, 10, &alone), broke);
        }
    }

    /// A break no pass can be laid to shows the difference, why the text
    /// the bisection stopped at was not checked, and names no pass.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn an_unplaced_break_names_no_pass() {
        let found = |ran| Bisected::Unplaced {
            at: at(),
            ran,
            agreed: 0,
            unchecked: vec![("it spins".to_owned(), 8)],
        };
        let bare = blame_report("f", 0x1000, 8, 100, &found(0));
        assert!(
            bare.contains("\nunplaced\tthe text differs, and with every cleanup pass left out it left every input unchecked"),
            "{bare}"
        );
        assert!(
            bare.ends_with(
                "\ndiffers\t5\treturn x + 1;\treturned 6, the binary 7\nunchecked\t8\tit spins\n"
            ),
            "{bare}"
        );
        assert!(
            !bare.contains("\npass\t") && !bare.contains("\nrepairs\t"),
            "{bare}"
        );
        assert!(!bare.contains("agrees"), "{bare}");
        let mid = blame_report("f", 0x1000, 8, 100, &found(32));
        assert!(
            mid.contains("with only its first 32 cleanup passes run it left"),
            "{mid}"
        );
    }

    /// An answer that lists fewer reasons than inputs went unchecked for
    /// says how many it shows of how many; one that lists them all gives no
    /// count.
    ///
    /// # Panics
    ///
    /// When reasons are cut uncounted, or a whole list is counted.
    #[test]
    fn reasons_cut_from_an_answer_are_counted() {
        let reasons = |n: usize| -> Vec<(String, usize)> {
            (0..n).map(|i| (format!("reason {i}"), 9 - i)).collect()
        };
        let cut = blame_report("f", 0x1000, 30, 100, &Bisected::Unchecked(reasons(4)));
        assert!(
            cut.ends_with(
                "\n# unchecked: showing 3 of 4 reasons, the commonest first\nunchecked\t9\treason 0\nunchecked\t8\treason 1\nunchecked\t7\treason 2\n"
            ),
            "{cut}"
        );
        let whole = blame_report("f", 0x1000, 24, 100, &Bisected::Unchecked(reasons(3)));
        assert!(!whole.contains("showing"), "{whole}");
        assert!(whole.ends_with("\nunchecked\t7\treason 2\n"), "{whole}");
    }

    /// A text that left the input the full text differs on unchecked
    /// places no pass and repairs nothing, however many others it agrees
    /// on.
    ///
    /// The full text differs on input 5. A text of the bisection that
    /// agrees on one input and leaves 63 unchecked, 5 among them, read as
    /// agreeing: it put the blame on the pass after it, and as the text
    /// without the blamed pass it read `repairs yes`. Held to input 5 it
    /// is unchecked: the search ends there with its counts, and the
    /// repair is said to be unchecked. The full text itself is held to no
    /// input.
    ///
    /// # Panics
    ///
    /// When a pass is named or a repair claimed on such a text.
    #[test]
    fn a_text_that_skips_the_differing_input_places_and_repairs_nothing() {
        let skips = |held: Option<usize>| Checked {
            missed: held == Some(5),
            ..ran(1, 63, false)
        };
        let runs = |skip: Passes| Pass::ALL.iter().filter(|p| skip.runs(**p)).count();
        let placed = bisected(
            &|skip, held| match runs(skip) {
                k if k == Pass::ALL.len() => {
                    assert_eq!(held, None, "the full text is held to no input");
                    ran(3, 0, true)
                }
                k if k < 4 => ran(8, 0, false),
                k if k < 40 => skips(held),
                _ => ran(3, 0, true),
            },
            &|k| format!("{k} passes"),
        );
        let unplaced = Bisected::Unplaced {
            at: at(),
            ran: 32,
            agreed: 1,
            unchecked: vec![("it spins".to_owned(), 63)],
        };
        assert_eq!(placed, unplaced);
        let text = blame_report("f", 0x1000, 64, 100, &placed);
        assert!(
            text.contains("\nunplaced\tthe text differs, and with only its first 32 cleanup passes run it left the input it differs on (agreeing on 1 of 64) unchecked, "),
            "{text}"
        );
        assert!(!text.contains("\npass\t"), "{text}");
        let repaired = bisected(
            &|skip, held| match runs(skip) {
                k if k + 1 == Pass::ALL.len() => skips(held),
                k if k < 10 => ran(8, 0, false),
                _ => ran(3, 0, true),
            },
            &|k| format!("{k} passes"),
        );
        let text = blame_report("f", 0x1000, 64, 100, &repaired);
        assert!(
            text.contains("\nrepairs\tunchecked: the full text with only this pass left out left the input the text differs on unchecked, so nothing is claimed of it; it agrees on 1 of 64 inputs, 63 left unchecked (63: it spins)\n"),
            "{text}"
        );
        assert!(!text.contains("repairs\tyes"), "{text}");
    }

    /// Wherever the answer says a text agrees it says on how many of the
    /// inputs, how many it left unchecked and the commonest reason: the
    /// full text, the text before the blamed pass and the text without it.
    ///
    /// # Panics
    ///
    /// When a line that says a text agrees gives no counts.
    #[test]
    fn agreement_says_how_many_inputs_agree_and_how_many_were_left() {
        let few = ran(1, 63, false);
        let counted = "agrees on 1 of 64 inputs, 63 left unchecked (63: it spins)";
        let whole = blame_report("f", 0x1000, 64, 100, &Bisected::Agrees(few.clone()));
        assert!(
            whole.contains(&format!("; the text {counted}; ")),
            "{whole}"
        );
        let found = Bisected::Broke {
            pass: Pass::FoldJumps,
            at: at(),
            before: Box::new(few.clone()),
            alone: Box::new(few),
            texts: (String::new(), String::new()),
        };
        let broke = blame_report("f", 0x1000, 64, 100, &found);
        assert!(
            broke.contains(&format!("the passes before it {counted}\n")),
            "{broke}"
        );
        assert!(
            broke.contains(&format!(
                "\nrepairs\tyes: the full text with only this pass left out {counted}\n"
            )),
            "{broke}"
        );
        let all = blame_report("f", 0x1000, 8, 100, &Bisected::Agrees(ran(8, 0, false)));
        assert!(
            all.contains("; the text agrees on 8 of 8 inputs; "),
            "{all}"
        );
        let over = |c: &Checked| bisected(&|_, _| c.clone(), &|_| String::new());
        assert_eq!(over(&ran(1, 7, false)), Bisected::Agrees(ran(1, 7, false)));
        let spun = vec![("it spins".to_owned(), 8)];
        assert_eq!(over(&ran(0, 8, false)), Bisected::Unchecked(spun));
    }

    /// Leaving the blamed pass out repairs the text only when that text
    /// agrees: one that checked no input is said to be unchecked.
    ///
    /// # Panics
    ///
    /// When the answer says otherwise.
    #[test]
    fn a_text_that_checks_nothing_is_no_repair() {
        let found = Bisected::Broke {
            pass: Pass::FoldJumps,
            at: at(),
            before: Box::new(ran(8, 0, false)),
            alone: Box::new(ran(0, 8, false)),
            texts: (String::new(), String::new()),
        };
        let text = blame_report("f", 0x1000, 8, 100, &found);
        assert!(text.contains("\nrepairs\tunchecked: "), "{text}");
        assert!(
            !text.contains("repairs\tyes") && !text.contains("repairs\tno"),
            "{text}"
        );
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
            before: Box::new(ran(8, 0, false)),
            alone: Box::new(ran(8, 0, false)),
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
        let agrees = blame_report("f", 0x1000, 8, 100, &Bisected::Agrees(ran(8, 0, false)));
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
            before: Box::new(ran(8, 0, false)),
            alone: Box::new(ran(2, 0, true)),
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
            before: Box::new(ran(8, 0, false)),
            alone: Box::new(ran(8, 0, false)),
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
