//! The guarded regions of a function: each `try` or `__try`, the code it
//! protects and the clauses that handle what is thrown or raised there.
//!
//! The exception metadata names them three ways. An x64 MSVC function's
//! `FuncInfo` maps instruction ranges to states and each try block to a
//! range of states and its catch handlers ([`crate::unwind`]); its scope
//! table lists each `__try`'s range with its filter or `__finally`. An
//! Itanium function's LSDA lists call-site ranges with a landing pad and
//! the types its action chain catches ([`crate::lsda`]). A 32-bit
//! function with an `_except_handler3`/`4` frame stores the index of the
//! `__try` it enters into its registration, and the scope table that index
//! names holds the filter and the handler ([`super::seh32`]).
//!
//! What the decompiler needs is the same for all of them: the ranges, the
//! clauses in the order they are tried, and for each clause the code that
//! runs it - a funclet the runtime calls, a label of the function itself
//! the runtime resumes at, or both.

use std::collections::BTreeMap;

use super::{Analysis, Function, ThrowSite};
use crate::program::Program;

/// Which construct a guard is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Dialect {
    /// C++ `try` and `catch`.
    Cxx,
    /// Structured exception handling: `__try` with `__except` or
    /// `__finally`.
    Seh,
}

/// What one clause handles.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClauseKind {
    /// `catch (decl)`: the declaration as C++ writes it (`Error &`, `int`,
    /// `...`).
    Catch(String),
    /// `__except (filter)`: the filter funclet, or `None` for
    /// `EXCEPTION_EXECUTE_HANDLER` written as the constant.
    Except(Option<u64>),
    /// `__finally`.
    Finally,
}

/// One clause of a guard and the code that runs it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Clause {
    /// What it handles.
    pub(crate) kind: ClauseKind,
    /// The funclet the runtime calls to run the clause's body, when the
    /// body is out of line.
    pub(crate) funclet: Option<u64>,
    /// The label of the function itself the runtime resumes at: an
    /// Itanium landing pad, an `__except` body, a catch's continuation.
    pub(crate) resume: Option<u64>,
    /// The selector an Itanium landing pad compares to pick this clause.
    pub(crate) selector: Option<i64>,
}

/// One guarded region.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Guard {
    /// Which construct it is.
    pub(crate) dialect: Dialect,
    /// The protected instruction ranges, half-open, sorted and disjoint.
    pub(crate) ranges: Vec<(u64, u64)>,
    /// The clauses in the order the runtime tries them; never empty.
    pub(crate) clauses: Vec<Clause>,
}

impl Guard {
    /// Tells whether the guard protects any byte of `start..end`.
    ///
    /// # Arguments
    ///
    /// * `start` - First address.
    /// * `end` - One past the last.
    ///
    /// # Returns
    ///
    /// Whether any range overlaps it.
    pub(crate) fn covers(&self, start: u64, end: u64) -> bool {
        self.ranges.iter().any(|&(s, e)| s < end && start < e)
    }
}

/// Lists the guarded regions of a function, outermost first.
///
/// The x64 tables are read once per program and kept in the analysis's
/// memo; an Itanium function's come from its throw sites, and a 32-bit
/// SEH frame's from the function's own code.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `f` - The function.
///
/// # Returns
///
/// The guards, empty for a function the metadata guards nothing in.
pub(crate) fn of(program: &Program, analysis: &Analysis, f: &Function) -> Vec<Guard> {
    let mut out = if program.is_64 && !program.headers.exception_handlers.is_empty() {
        let table = analysis
            .derived
            .get_or_build("eh_guards", (), || crate::unwind::guards(program));
        table.get(&f.entry).cloned().unwrap_or_default()
    } else if let Some(sites) = analysis.throw_sites.get(&f.entry) {
        itanium(sites)
    } else if !program.is_64 {
        super::seh32::guards(program, analysis, f)
    } else {
        Vec::new()
    };
    for clause in out
        .iter_mut()
        .flat_map(|g| g.clauses.iter_mut())
        .filter(|c| c.resume.is_none() && matches!(c.kind, ClauseKind::Catch(_)))
    {
        if let Some(funclet) = clause.funclet.and_then(|e| analysis.function(e)) {
            clause.resume = super::functions::returned_labels(program, funclet)
                .into_iter()
                .find(|&l| f.blocks.iter().any(|b| b.start == l));
        }
    }
    out.sort_by_key(|g| {
        let start = g.ranges.first().map_or(0, |r| r.0);
        let end = g.ranges.last().map_or(0, |r| r.1);
        (start, std::cmp::Reverse(end))
    });
    out
}

/// Reads the `try` regions an Itanium function's call sites declare.
///
/// The sites that share a landing pad and catch something are one `try`:
/// the pad is where every clause's code begins, and the selector it
/// compares picks the clause. A pad that only cleans up is no `try`.
///
/// # Arguments
///
/// * `sites` - The function's call sites, sorted by start.
///
/// # Returns
///
/// One guard per catching landing pad.
fn itanium(sites: &[ThrowSite]) -> Vec<Guard> {
    let mut by_pad: BTreeMap<u64, Guard> = BTreeMap::new();
    for s in sites {
        let Some(pad) = s.landing_pad else {
            continue;
        };
        if s.catches.is_empty() {
            continue;
        }
        let g = by_pad.entry(pad).or_insert_with(|| Guard {
            dialect: Dialect::Cxx,
            ranges: Vec::new(),
            clauses: s
                .catches
                .iter()
                .zip(&s.filters)
                .map(|(name, &filter)| Clause {
                    kind: ClauseKind::Catch(name.clone()),
                    funclet: None,
                    resume: Some(pad),
                    selector: Some(filter),
                })
                .collect(),
        });
        g.ranges.push((s.start, s.end));
    }
    by_pad
        .into_values()
        .map(|mut g| {
            g.ranges = merged(g.ranges);
            g
        })
        .collect()
}

/// Sorts ranges and merges the ones that touch or overlap.
///
/// # Arguments
///
/// * `ranges` - Half-open ranges in any order.
///
/// # Returns
///
/// The same addresses as sorted disjoint ranges.
pub(crate) fn merged(mut ranges: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
    ranges.sort_unstable();
    let mut out: Vec<(u64, u64)> = Vec::with_capacity(ranges.len());
    for (s, e) in ranges {
        match out.last_mut() {
            Some(last) if s <= last.1 => last.1 = last.1.max(e),
            Some(_) | None => out.push((s, e)),
        }
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{ClauseKind, Dialect, itanium, merged};
    use crate::analysis::ThrowSite;

    /// Touching and overlapping ranges merge, and the rest keep apart.
    #[test]
    fn ranges_merge_where_they_touch() {
        assert_eq!(
            merged(vec![(10, 20), (0, 5), (5, 8), (15, 30)]),
            vec![(0, 8), (10, 30)]
        );
    }

    /// The call sites that share a catching landing pad are one `try`,
    /// with a clause per caught type and its selector; a site whose pad
    /// only cleans up guards nothing.
    #[test]
    fn sites_sharing_a_pad_are_one_try() {
        let site = |start, pad, catches: &[&str], filters: &[i64]| ThrowSite {
            start,
            end: start + 5,
            landing_pad: pad,
            catches: catches.iter().map(|s| (*s).to_owned()).collect(),
            filters: filters.to_vec(),
            cleanup: false,
        };
        let sites = [
            site(0x10, Some(0x80), &["Error", "std::exception"], &[2, 1]),
            site(0x15, Some(0x80), &["Error", "std::exception"], &[2, 1]),
            site(0x30, Some(0x90), &[], &[]),
            site(0x40, None, &[], &[]),
        ];
        let guards = itanium(&sites);
        assert_eq!(guards.len(), 1, "{guards:?}");
        let g = &guards[0];
        assert_eq!(g.dialect, Dialect::Cxx);
        assert_eq!(g.ranges, vec![(0x10, 0x1a)]);
        assert_eq!(
            g.clauses
                .iter()
                .map(|c| (c.kind.clone(), c.resume, c.selector))
                .collect::<Vec<_>>(),
            vec![
                (ClauseKind::Catch("Error".to_owned()), Some(0x80), Some(2)),
                (
                    ClauseKind::Catch("std::exception".to_owned()),
                    Some(0x80),
                    Some(1)
                ),
            ]
        );
        assert!(g.covers(0x19, 0x20) && !g.covers(0x1a, 0x30));
    }
}
