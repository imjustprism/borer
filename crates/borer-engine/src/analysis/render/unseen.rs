//! What a call or reference answer could not see: the indirect calls and
//! jumps discovery did not resolve, whose targets are no edge of the call
//! graph and no reference.

use std::sync::Arc;

use super::*;

/// Fewest calls and jumps to a target before its listing is no longer
/// short, so the note on what it could not see is left off.
pub(super) const SHORT_CALLERS: usize = 4;

/// Which functions an answer read the calls of.
#[derive(Debug, Clone, Copy)]
pub enum Reach<'a> {
    /// Every function: who calls a target may be any of them.
    Program,
    /// Only these, by entry: the functions a walk looked at.
    Walked(&'a BTreeSet<u64>),
}

/// Jumps followed from a call into a chain of trampolines before the
/// chain counts as resolved.
const TRAMPOLINE_HOPS: usize = 4;

/// Where each call or jump of one function lands, by its site.
///
/// A target that is no function but a slot in data holding a function's
/// address ([`RefKind::Table`]) lands on that function, as a call through
/// a dispatch pointer does; any other target lands where it points.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `stored` - The function each data slot holds, by the slot.
/// * `entry` - The function.
///
/// # Returns
///
/// The landing of every branch site, by site, several for a site with
/// several targets.
fn landings(a: &Analysis, stored: &BTreeMap<u64, u64>, entry: u64) -> BTreeMap<u64, Vec<u64>> {
    let mut out: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (target, s) in a.refs_from(entry) {
        if s.is_branch() {
            let lands = match a.function(target) {
                Some(_) => target,
                None => stored.get(&target).copied().unwrap_or(target),
            };
            out.entry(s.va).or_default().push(lands);
        }
    }
    out
}

/// Whether a block's call or jump reaches no target discovery resolved:
/// none leaves it, or each it has lands in a trampoline.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `b` - The block.
/// * `lands` - Where the function's branch sites land ([`landings`]).
/// * `through` - The trampolines: functions that only jump on through a
///   register.
fn blind(
    a: &Analysis,
    b: &BasicBlock,
    lands: &BTreeMap<u64, Vec<u64>>,
    through: &BTreeSet<u64>,
) -> bool {
    let reaches = lands
        .range(b.start..b.end)
        .flat_map(|(_, t)| t)
        .any(|t| !through.contains(t));
    match b.term {
        BlockTerm::Call => !reaches,
        BlockTerm::Indirect => !reaches && a.jump_tables.range(b.start..b.end).next().is_none(),
        BlockTerm::Ret
        | BlockTerm::Jmp
        | BlockTerm::Cond
        | BlockTerm::Fall
        | BlockTerm::Invalid => false,
    }
}

/// Counts, for each function, its calls and jumps that discovery resolved
/// to no target.
///
/// A trampoline is a one-block function that jumps on through a register
/// (`jmp rax`, the CFG dispatcher) or to another trampoline, directly or
/// through a pointer in data, up to [`TRAMPOLINE_HOPS`] deep; a call into
/// one goes wherever the register points, so it counts as unresolved and
/// the trampoline's own jump does not. Memoized for the analysis
/// ([`crate::analysis::Derived`]).
///
/// # Arguments
///
/// * `a` - The analysis.
///
/// # Returns
///
/// The count by function entry, functions with none left out.
fn unresolved(a: &Analysis) -> Arc<BTreeMap<u64, usize>> {
    a.derived.get_or_build("unresolved_branches", (), || {
        let stored: BTreeMap<u64, u64> = a
            .xrefs
            .iter()
            .flat_map(|(&f, sites)| sites.iter().map(move |s| (f, s)))
            .filter(|(f, s)| {
                s.kind == RefKind::Table && s.from_entry.is_none() && a.function(*f).is_some()
            })
            .map(|(f, s)| (s.va, f))
            .collect();
        let lone: Vec<_> = a
            .functions
            .iter()
            .filter_map(|f| match f.blocks.as_slice() {
                [b] if matches!(b.term, BlockTerm::Indirect | BlockTerm::Jmp) => {
                    Some((f.entry, b, landings(a, &stored, f.entry)))
                }
                _ => None,
            })
            .collect();
        let mut through = BTreeSet::new();
        for _ in 0..=TRAMPOLINE_HOPS {
            let next: BTreeSet<u64> = lone
                .iter()
                .filter(|(_, b, lands)| match b.term {
                    BlockTerm::Jmp => {
                        !lands.is_empty() && lands.values().flatten().all(|t| through.contains(t))
                    }
                    BlockTerm::Ret
                    | BlockTerm::Cond
                    | BlockTerm::Call
                    | BlockTerm::Indirect
                    | BlockTerm::Fall
                    | BlockTerm::Invalid => blind(a, b, lands, &through),
                })
                .map(|(e, _, _)| *e)
                .collect();
            if next == through {
                break;
            }
            through = next;
        }
        a.functions
            .iter()
            .filter(|f| !through.contains(&f.entry))
            .filter_map(|f| {
                let lands = landings(a, &stored, f.entry);
                let n = f
                    .blocks
                    .iter()
                    .filter(|b| blind(a, b, &lands, &through))
                    .count();
                (n > 0).then_some((f.entry, n))
            })
            .collect()
    })
}

/// Says what a call or reference answer could not see: the indirect calls
/// and jumps borer did not resolve among the functions it read, whose
/// targets are missing from the answer.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `reach` - The functions the answer read the calls of.
/// * `lead` - The comment mark the line starts with: `#`, or `%%` in a
///   mermaid graph.
///
/// # Returns
///
/// The line, newline-terminated; `None` when every call and jump there
/// was resolved.
#[must_use]
pub fn unseen_line(a: &Analysis, reach: Reach<'_>, lead: &str) -> Option<String> {
    let counts = unresolved(a);
    let (sites, functions, scope) = match reach {
        Reach::Program => (counts.values().sum(), counts.len(), "in the program"),
        Reach::Walked(walked) => walked.iter().filter_map(|e| counts.get(e)).fold(
            (0usize, 0usize, "among the functions walked"),
            |(s, f, w), n| (s + n, f + 1, w),
        ),
    };
    (sites > 0).then(|| {
        format!(
            "{lead} not seen: {sites} indirect call{} or jump{} in {functions} function{} {scope} were not resolved to a target, so what they reach is not in this answer\n",
            plural(sites),
            plural(sites),
            plural(functions)
        )
    })
}

/// Says what a call graph could not see ([`unseen_line`]), as a mermaid
/// comment.
///
/// A graph of callees misses what the unresolved calls of its drawn
/// functions reach; a graph of callers misses the callers that reach the
/// root through an unresolved call anywhere, said when the root has few
/// callers.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `walk` - Which way the graph was walked.
/// * `root_callers` - How many callers the root has.
/// * `drawn` - The graph's nodes.
///
/// # Returns
///
/// The `%%` line, or empty when there is nothing to say.
pub(super) fn graph_line(
    a: &Analysis,
    walk: Walk,
    root_callers: usize,
    drawn: &BTreeSet<u64>,
) -> String {
    let reach = match walk {
        Walk::Callers => (root_callers < SHORT_CALLERS).then_some(Reach::Program),
        Walk::Callees => Some(Reach::Walked(drawn)),
    };
    reach
        .and_then(|r| unseen_line(a, r, "%%"))
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::{Reach, unseen_line};
    use crate::analysis::Analysis;
    use crate::program::{Arch, Program, Section};
    use std::collections::BTreeSet;

    /// Returns x86-64 code at `0x1000`: a function that calls another
    /// directly and then through `rax`, and the callee.
    fn calls() -> Program {
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1014
            0xff, 0xd0, // ASM: call rax
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
            0xc3, // ASM: ret
        ];
        code.resize(0x14, 0xcc);
        code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
        let len = u64::try_from(code.len()).unwrap_or(0);
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text])
    }

    /// The call through a register is counted where it is, the direct one
    /// is not, and a walk that did not read its function says nothing.
    ///
    /// # Panics
    ///
    /// When the line is missing, miscounts or shows where it should not.
    #[test]
    fn an_unresolved_call_is_counted_where_it_was_read() {
        let p = calls();
        let a = Analysis::compute(&p);
        let line = unseen_line(&a, Reach::Program, "#").unwrap_or_default();
        assert!(
            line.starts_with("# not seen: 1 indirect call or jump in 1 function in the program"),
            "{line}"
        );
        let walked = BTreeSet::from([0x1000]);
        let line = unseen_line(&a, Reach::Walked(&walked), "%%").unwrap_or_default();
        assert!(line.starts_with("%% not seen: 1 indirect"), "{line}");
        let callee = BTreeSet::from([0x1014]);
        assert_eq!(unseen_line(&a, Reach::Walked(&callee), "#"), None);
    }

    /// A short list of callers, a call graph and a path not found each end
    /// with what borer could not see; a graph that read no unresolved call
    /// says nothing.
    ///
    /// # Panics
    ///
    /// When a line is missing or shows where it should not.
    #[test]
    fn short_call_answers_say_what_they_could_not_see() {
        use crate::analysis::Overlay;
        use crate::analysis::render::{call_path, callgraph_mermaid, xrefs_tsv};
        let p = calls();
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let callers = xrefs_tsv(&a, &o, 0x1014, 0, 60, false);
        assert!(
            callers.contains("\n# not seen: 1 indirect call"),
            "{callers}"
        );
        let count = xrefs_tsv(&a, &o, 0x1014, 0, 60, true);
        assert!(count.contains("\n# not seen: 1 indirect call"), "{count}");
        let path = call_path(&p, &a, &o, 0x1000, 0x1100, 8);
        assert!(path.contains("does not reach"), "{path}");
        assert!(path.contains("\n# not seen: 1 indirect call"), "{path}");
        let graph = callgraph_mermaid(&p, &a, &o, 0x1000, 30, false);
        assert!(graph.ends_with("is not in this answer\n"), "{graph}");
        assert!(graph.contains("\n%% not seen: 1 indirect call"), "{graph}");
        let leaf = callgraph_mermaid(&p, &a, &o, 0x1014, 30, false);
        assert!(!leaf.contains("not seen"), "{leaf}");
    }

    /// A direct call into a function that only jumps on through a register
    /// is counted at the call, as the CFG dispatcher's callers are, and the
    /// trampoline's own jump is not counted again.
    ///
    /// # Panics
    ///
    /// When the call is not counted, or the trampoline is.
    #[test]
    fn a_call_into_a_trampoline_is_unresolved() {
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
            0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x1014
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
            0xc3, // ASM: ret
        ];
        code.resize(0x14, 0xcc);
        code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
        code.resize(0x20, 0xcc);
        code.extend([0xff, 0xe0]); // ASM: jmp rax
        let len = u64::try_from(code.len()).unwrap_or(0);
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let line = unseen_line(&a, Reach::Program, "#").unwrap_or_default();
        assert!(
            line.starts_with("# not seen: 1 indirect call or jump in 1 function in the program"),
            "{line}"
        );
        let trampoline = BTreeSet::from([0x1020]);
        assert_eq!(unseen_line(&a, Reach::Walked(&trampoline), "#"), None);
    }
}
