//! The first members a constructor stores, which say what its class holds
//! at each offset.

use std::collections::{BTreeMap, BTreeSet};

use super::hints::receiver_class;
use super::scan::{member_class, template_args};
use super::{ClassInfo, Scan};
use crate::analysis::Analysis;

/// Marks a template's arguments in the type it holds at offset 0.
const ARGS_MARK: &str = "\u{0}";
/// Most classes followed when asking what a class holds at offset 0.
const HELD_MAX: usize = 16;

/// The classes others hold at offset 0, as their own code shows.
///
/// A method of a class hands its own `this` to a method of another,
/// neither of them a class with a table (a class with a table starts with
/// it, so what it holds at offset 0 is a base). A template's
/// instantiations hold the same kind of member, so one instantiation seen
/// holding a type built of its arguments (`Util::Dictionary<K,V>` its
/// `Util::Array<Util::KeyValuePair<K,V> >`) makes each instantiation hold
/// its own.
#[derive(Default)]
pub(super) struct FirstMembers {
    /// Class to the classes its code shows it holding at offset 0.
    pub(super) direct: BTreeMap<String, BTreeSet<String>>,
    /// Template to the type it holds at offset 0, its arguments marked
    /// ([`ARGS_MARK`]); one with instantiations that disagree has none.
    pub(super) patterns: BTreeMap<String, Option<String>>,
}

impl FirstMembers {
    /// Gathers the relation from the named members' scans.
    ///
    /// # Arguments
    ///
    /// * `analysis` - Functions and their names.
    /// * `scans` - Scans by entry.
    /// * `renames` - Names chosen by this pass.
    /// * `statics` - Class-named functions whose first argument is not `this`.
    /// * `reads` - How many arguments each function reads ([`read_counts`](super::scan::read_counts)).
    /// * `classes` - The classes the tables and descriptors name.
    pub(super) fn gather(
        analysis: &Analysis,
        scans: &BTreeMap<u64, Scan>,
        renames: &BTreeMap<u64, String>,
        statics: &BTreeSet<u64>,
        reads: &BTreeMap<u64, usize>,
        classes: &BTreeMap<String, ClassInfo>,
    ) -> Self {
        let mut held = Self::default();
        for f in &analysis.functions {
            let Some(scan) = scans.get(&f.entry) else {
                continue;
            };
            let Some((outer, true)) = member_class(f, renames, statics, scan) else {
                continue;
            };
            if classes.contains_key(outer) {
                continue;
            }
            for &(target, p) in &scan.this_calls {
                let Some(callee) = analysis.function(target) else {
                    continue;
                };
                if p != 0 || reads.get(&target).is_none_or(|&k| k == 0) {
                    continue;
                }
                let Some(inner) = receiver_class(callee, renames, statics, scans) else {
                    continue;
                };
                if inner == outer || classes.contains_key(inner) {
                    continue;
                }
                held.direct
                    .entry(outer.to_owned())
                    .or_default()
                    .insert(inner.to_owned());
            }
        }
        for (outer, inners) in &held.direct {
            let Some((template, args)) = template_args(outer) else {
                continue;
            };
            for inner in inners.iter().filter(|i| i.contains(args)) {
                let pattern = inner.replace(args, ARGS_MARK);
                held.patterns
                    .entry(template.to_owned())
                    .and_modify(|known| {
                        if known.as_ref() != Some(&pattern) {
                            *known = None;
                        }
                    })
                    .or_insert(Some(pattern));
            }
        }
        held
    }

    /// Returns the classes `outer` holds at offset 0, directly or through
    /// what those hold in turn.
    ///
    /// # Arguments
    ///
    /// * `outer` - The class.
    pub(super) fn inside(&self, outer: &str) -> BTreeSet<String> {
        let mut found = BTreeSet::new();
        let mut todo = vec![outer.to_owned()];
        while let Some(class) = todo.pop() {
            let built = template_args(&class).and_then(|(template, args)| {
                self.patterns
                    .get(template)
                    .cloned()
                    .flatten()
                    .map(|p| p.replace(ARGS_MARK, args))
            });
            let next = self
                .direct
                .get(&class)
                .into_iter()
                .flatten()
                .cloned()
                .chain(built);
            for inner in next {
                if found.len() < HELD_MAX && inner != outer && found.insert(inner.clone()) {
                    todo.push(inner);
                }
            }
        }
        found
    }

    /// Returns whether `outer` holds `inner` at offset 0.
    ///
    /// # Arguments
    ///
    /// * `outer` - The class that may hold the other.
    /// * `inner` - The class it may hold.
    pub(super) fn holds(&self, outer: &str, inner: &str) -> bool {
        outer != inner && self.inside(outer).contains(inner)
    }

    /// Drops from `candidates` each class another of them holds at offset
    /// 0: of an object and the member it starts with, the object.
    ///
    /// # Arguments
    ///
    /// * `candidates` - Classes voted for a parameter or bounding it.
    pub(super) fn outermost(&self, candidates: BTreeSet<String>) -> BTreeSet<String> {
        if candidates.len() < 2 || self.direct.is_empty() {
            return candidates;
        }
        let held: BTreeSet<String> = candidates.iter().flat_map(|c| self.inside(c)).collect();
        let outer: BTreeSet<String> = candidates
            .iter()
            .filter(|c| !held.contains(*c))
            .cloned()
            .collect();
        if outer.is_empty() { candidates } else { outer }
    }
}
