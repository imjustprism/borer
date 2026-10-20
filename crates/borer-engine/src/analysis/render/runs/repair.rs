//! The repair search over a function's choice points.
//!
//! A function whose text disagrees with the binary is rebuilt with the
//! choice points the disagreement implicates moved to their literal
//! rendering, one move at a time within a fixed budget, and the first text
//! that agrees is kept, with every rendering tried and the evidence for or
//! against it.
//!
//! The judge is the ISO check on generated inputs ([`first_difference`]),
//! and the replay of the statements as emitted ([`text_check`]) where the
//! ISO check runs nothing (arm64, a floating parameter). The disagreement
//! is localized two ways: its line names the sites it reads (a slot's
//! variable, a `return`), and when the text with every pass left out
//! agrees, a bisection of [`Pass::ALL`] names the first pass that breaks
//! it ([`first_breaking`]). The rest of the function's sites follow. The
//! inputs, the order and the budget are functions of the function and a
//! fixed seed, so the same binary gets the same answer.

use std::cell::Cell;
use std::sync::Arc;

use super::vectors::{Checked, Counterexample, draw, first_breaking, first_difference};
use crate::analysis::decompile::{Pass, Passes, Site, choice_points, text_check};
use crate::analysis::{Analysis, Overlay};
use crate::program::Program;

/// How much one search may run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Budget {
    /// Inputs each text is checked on.
    pub inputs: usize,
    /// The inputs' seed.
    pub seed: u64,
    /// Steps each run is given, on either side.
    pub steps: usize,
    /// Most renderings tried after the text as it is.
    pub moves: usize,
}

impl Budget {
    /// One `decompile` answer: a small input set and step budget.
    pub const ANSWER: Self = Self {
        inputs: 8,
        seed: 1,
        steps: 20_000,
        moves: 8,
    };

    /// Benchmarks and tests: more inputs, the same moves.
    pub const FULL: Self = Self {
        inputs: 64,
        seed: 1,
        steps: 20_000,
        moves: 8,
    };
}

/// What a check found of one rendering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Evidence {
    /// It agreed with the binary on this many inputs and differed on none.
    Tested(usize),
    /// It differs on this input.
    Refuted(Counterexample),
    /// Nothing about it could be checked: the text does not read, or every
    /// input was left unchecked.
    Unchecked,
}

/// One rendering the search tried: the sites it moved to their literal
/// rung, and the evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tried {
    /// The sites moved, the rest at their readable rung.
    pub sites: Vec<Site>,
    /// What the check found.
    pub evidence: Evidence,
}

/// What a repair search ended with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Repair {
    /// The text agrees with the binary as it is, or nothing could be
    /// checked: nothing moved.
    Agrees,
    /// A rendering agrees.
    Repaired {
        /// The sites the agreeing text renders at their literal rung.
        moved: Vec<Site>,
        /// Every rendering tried, the agreeing one last.
        tried: Vec<Tried>,
        /// Texts checked, the first and the bisection's included.
        checks: usize,
    },
    /// No rendering within the budget agrees.
    Disagrees {
        /// Where the text as it is differs.
        at: Counterexample,
        /// Every rendering tried.
        tried: Vec<Tried>,
        /// Texts checked, the first and the bisection's included.
        checks: usize,
    },
}

impl Repair {
    /// Returns the overlay the answer's text is built under: `o` with the
    /// agreeing rendering's sites moved, or `None` when nothing moved.
    ///
    /// # Arguments
    ///
    /// * `o` - The overlay the search started from.
    #[must_use]
    pub fn rendered(&self, o: &Overlay) -> Option<Overlay> {
        let Self::Repaired { moved, .. } = self else {
            return None;
        };
        Some(moved.iter().fold(o.clone(), |u, s| s.moved(&u)))
    }

    /// Returns how many texts the search checked; one when the first agreed.
    #[must_use]
    pub fn checks(&self) -> usize {
        match self {
            Self::Agrees => 1,
            Self::Repaired { checks, .. } | Self::Disagrees { checks, .. } => *checks,
        }
    }

    /// Returns the one-line note an answer carries when its text still
    /// disagrees with the binary after the search.
    ///
    /// Only a difference in what the run leaves behind is noted: a value
    /// returned, a byte of a buffer, an import called. A text the ISO
    /// reading refuses (a register read before any line sets it) or one
    /// whose run stops short is often right where it matters, so it is not.
    ///
    /// # Returns
    ///
    /// The note, a `// warn:` item without the prefix; `None` when the text
    /// agrees, was repaired, or differs only in a way that is not noted.
    #[must_use]
    pub fn note(&self) -> Option<String> {
        let Self::Disagrees { at, tried, .. } = self else {
            return None;
        };
        let value = at.why.starts_with("the text returns ")
            && !at.why.contains("(the low 32 bits agree)")
            || at.why.contains(" after the text, ")
            || at.why.starts_with("call ");
        if !value {
            return None;
        }
        let line = if at.line.is_empty() {
            String::new()
        } else {
            format!(" at `{}`", at.line.trim_end_matches(';'))
        };
        Some(
            format!(
                "differs on {}{line}: {} ({} other rendering{} tried)",
                at.input,
                at.why,
                tried.len(),
                if tried.len() == 1 { "" } else { "s" }
            )
            .replace(';', ","),
        )
    }

    /// Returns the bytes the result holds beyond its own size.
    fn bytes(&self) -> usize {
        let tried = |t: &[Tried]| {
            t.iter()
                .map(|x| x.sites.capacity() * size_of::<Site>() + size_of::<Tried>())
                .sum::<usize>()
        };
        match self {
            Self::Agrees => 0,
            Self::Repaired {
                moved, tried: t, ..
            } => moved.capacity() * size_of::<Site>() + tried(t),
            Self::Disagrees { at, tried: t, .. } => {
                at.input.capacity() + at.line.capacity() + at.why.capacity() + tried(t)
            }
        }
    }
}

/// Tells whether a line of a text reads a choice point: a `return` the
/// return's site, a slot's variable its slot.
///
/// # Arguments
///
/// * `site` - The site.
/// * `line` - The line, trimmed.
fn implicated(site: Site, line: &str) -> bool {
    match site {
        Site::Return => line.starts_with("return "),
        Site::Slot(k) => {
            let name = format!("local_{:x}", k.unsigned_abs());
            line.match_indices(&name).any(|(i, _)| {
                let word =
                    |c: Option<char>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
                !word(line[..i].chars().next_back()) && !word(line[i + name.len()..].chars().next())
            })
        }
        Site::Pass(_) => false,
    }
}

/// The first statement the replay of a function's text does not bear out,
/// as a counterexample.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `u` - The overlay the text is built under.
/// * `entry` - The function's entry.
fn replay_refutes(p: &Program, a: &Analysis, u: &Overlay, entry: u64) -> Option<Counterexample> {
    let check = text_check(p, a, u, entry);
    let at = check.as_ref().as_ref()?.disagree.first().copied()?;
    Some(Counterexample {
        input: "the replay's states".to_owned(),
        line: String::new(),
        why: format!("the statements of {at:#x} disagree with the machine"),
    })
}

/// Searches the renderings of a function's choice points for a text that
/// agrees with the binary.
///
/// The text as `o` builds it is checked first, the replay before the ISO
/// check so the replay reads the lifter's witness the decompile keeps for
/// it; when both agree, or nothing could be checked, nothing moves. Otherwise each implicated site is moved
/// to its literal rung alone, in order (the sites the differing line reads,
/// the pass a bisection blames, the function's other sites), at most
/// `budget.moves` renderings in all, the last of them every site tried at
/// once; the first that agrees on every input it checks is kept. A move
/// agrees only if some input agreed, where the ISO check ran at all.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names; its moved sites and passes are where the search
///   starts.
/// * `entry` - The function's entry.
/// * `budget` - The inputs, steps and moves the search may take.
///
/// # Returns
///
/// What the search ended with ([`Repair`]).
#[must_use]
pub fn repair_iso(p: &Program, a: &Analysis, o: &Overlay, entry: u64, budget: Budget) -> Repair {
    let refuted = replay_refutes(p, a, o, entry);
    let drawn = draw(p, a, o, entry, budget.inputs, budget.seed).ok();
    let checks = Cell::new(1usize);
    let iso = |u: &Overlay| {
        drawn.as_ref().map_or(
            Checked {
                differs: None,
                agreed: 0,
            },
            |d| first_difference(p, a, u, entry, d, budget.steps),
        )
    };
    let base = iso(o);
    let live = base.differs.is_some() || base.agreed > 0;
    let Some(at) = base.differs.clone().or(refuted) else {
        return Repair::Agrees;
    };
    let probe = |u: &Overlay| {
        checks.set(checks.get() + 1);
        iso(u)
    };
    let judge = |u: &Overlay| {
        let refuted = replay_refutes(p, a, u, entry);
        let c = if live {
            probe(u)
        } else {
            checks.set(checks.get() + 1);
            Checked {
                differs: None,
                agreed: 0,
            }
        };
        match c.differs.or(refuted) {
            Some(c) => Evidence::Refuted(c),
            None if live && c.agreed == 0 => Evidence::Unchecked,
            None => Evidence::Tested(c.agreed),
        }
    };
    let points = choice_points(p, a, o, entry);
    let mut order: Vec<Site> = points
        .iter()
        .filter(|s| implicated(**s, &at.line))
        .copied()
        .collect();
    if base.differs.is_some() {
        let without = |skip: Passes| Overlay {
            passes: skip,
            ..o.clone()
        };
        let bare = probe(&without(Passes::after(0)));
        if bare.differs.is_none() && bare.agreed > 0 {
            let (good, _, _) = first_breaking(&|skip| probe(&without(skip)).differs);
            order.extend(Pass::ALL.get(good).map(|p| Site::Pass(*p)));
        }
    }
    for s in points {
        if !order.contains(&s) {
            order.push(s);
        }
    }
    let mut tried: Vec<Tried> = Vec::new();
    let singles = order.len().min(budget.moves);
    let mut moves: Vec<Vec<Site>> = order.iter().take(singles).map(|s| vec![*s]).collect();
    if order.len() > 1 && singles < budget.moves {
        moves.push(order.iter().take(singles).copied().collect());
    }
    for sites in moves {
        let evidence = judge(&sites.iter().fold(o.clone(), |u, s| s.moved(&u)));
        let agrees = matches!(evidence, Evidence::Tested(_));
        tried.push(Tried { sites, evidence });
        if agrees {
            return Repair::Repaired {
                moved: tried.last().map(|t| t.sites.clone()).unwrap_or_default(),
                tried,
                checks: checks.get(),
            };
        }
    }
    Repair::Disagrees {
        at,
        tried,
        checks: checks.get(),
    }
}

/// [`repair_iso`] once per overlay, function and budget, through
/// [`Analysis::derived`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, holding the memo.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `budget` - The inputs, steps and moves the search may take.
///
/// # Returns
///
/// The shared result.
#[must_use]
pub fn repaired(p: &Program, a: &Analysis, o: &Overlay, entry: u64, budget: Budget) -> Arc<Repair> {
    a.derived.get_or_build_item(
        "repair",
        o.fingerprint(),
        (entry, budget),
        || repair_iso(p, a, o, entry, budget),
        Repair::bytes,
    )
}

/// Returns the overlay one `decompile` answer renders a function under,
/// and the note it carries.
///
/// It runs the repair search with a small input set and budget
/// ([`Budget::ANSWER`]), which moves nothing when the text agrees.
///
/// A sweep (`index`, `decompile_all`, a batch) calls no such thing: its
/// texts are the readable ones, unchecked.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, holding the memo.
/// * `o` - User names.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The overlay, a copy of `o` when nothing moved, and the note
/// ([`Repair::note`]).
#[must_use]
pub fn answered(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> (Overlay, Option<String>) {
    let r = repaired(p, a, o, entry, Budget::ANSWER);
    (r.rendered(o).unwrap_or_else(|| o.clone()), r.note())
}

#[cfg(test)]
mod tests {
    use super::{Counterexample, Repair, Site, implicated};

    /// A line implicates the sites it reads, by whole names only.
    ///
    /// # Panics
    ///
    /// When the check fails.
    #[test]
    fn a_line_implicates_the_sites_it_reads() {
        assert!(implicated(Site::Return, "return a1 / -5;"));
        assert!(!implicated(Site::Return, "returned = 1;"));
        assert!(implicated(Site::Slot(-0xc), "x = local_c * 2.0f;"));
        assert!(!implicated(Site::Slot(-0xc), "x = local_c0 * 2.0f;"));
        assert!(!implicated(Site::Slot(-0xc), "x = home_local_c;"));
    }

    /// Only a text that still differs in what its run leaves behind gets a
    /// note; a refused reading, a low-bits-only result and an agreeing text
    /// get none.
    ///
    /// # Panics
    ///
    /// When the check fails.
    #[test]
    fn only_a_remaining_value_difference_is_noted() {
        let left = |why: &str| Repair::Disagrees {
            at: Counterexample {
                input: "0x10".to_owned(),
                line: "return x;".to_owned(),
                why: why.to_owned(),
            },
            tried: Vec::new(),
            checks: 1,
        };
        let noted = left("the text returns 0x1, the binary 0x2; x set at line 3").note();
        assert_eq!(
            noted.as_deref(),
            Some(
                "differs on 0x10 at `return x`: the text returns 0x1, the binary 0x2, x set at line 3 (0 other renderings tried)"
            )
        );
        assert!(
            left("as ISO C, `eax` is read before any line sets it; the binary returned")
                .note()
                .is_none()
        );
        assert!(
            left(
                "the text returns 0xfffffffffffffffd, the binary 0xfffffffd (the low 32 bits agree)"
            )
            .note()
            .is_none()
        );
        assert!(Repair::Agrees.note().is_none());
    }
}
