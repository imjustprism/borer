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

/// The calls and jumps discovery resolved to no target, read once per
/// analysis ([`unresolved`]).
#[derive(Debug, Default)]
struct Unresolved {
    /// How many each function makes, by entry; functions with none and
    /// trampolines left out.
    counts: BTreeMap<u64, usize>,
    /// The trampolines: one-block functions that only jump on through a
    /// register, directly or through others.
    through: BTreeSet<u64>,
}

/// Where each call or jump of one function lands, by its site.
///
/// A target in code lands there, an import's slot on the import, and a
/// slot in data holding a function's address ([`RefKind::Table`]) on that
/// function, as a call through a dispatch pointer does. Any other target,
/// a slot filled at run time, lands nowhere: the site has no landing.
///
/// # Arguments
///
/// * `p` - The loaded image, for its code sections.
/// * `a` - The analysis.
/// * `slots` - What each import slot and function pointer in data lands
///   on, by the slot.
/// * `entry` - The function.
///
/// # Returns
///
/// The landings of every branch site, by site, empty for one that lands
/// nowhere.
fn landings(
    p: &Program,
    a: &Analysis,
    slots: &BTreeMap<u64, u64>,
    entry: u64,
) -> BTreeMap<u64, Vec<u64>> {
    let mut out: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (target, s) in a.refs_from(entry) {
        if s.is_branch() {
            let code = a.function_at(target).is_some()
                || p.section_at(target).is_some_and(|sec| sec.executable);
            let lands = if code {
                Some(target)
            } else {
                slots.get(&target).copied()
            };
            out.entry(s.va).or_default().extend(lands);
        }
    }
    out
}

/// Whether a block's call or jump reaches no target discovery resolved:
/// none leaves it, or each it has lands nowhere or in a trampoline.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `b` - The block.
/// * `lands` - Where the function's branch sites land ([`landings`]).
/// * `through` - The trampolines found so far.
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
/// (`jmp rax`, the CFG dispatcher) or a slot filled at run time, or to
/// another trampoline, directly or through a pointer in data, up to
/// [`TRAMPOLINE_HOPS`] deep. A call into one goes wherever the register
/// points, so it counts as unresolved where it is made. Memoized for the
/// analysis ([`crate::analysis::Derived`]).
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports and code sections.
/// * `a` - The analysis.
///
/// # Returns
///
/// The counts and the trampolines.
fn unresolved(p: &Program, a: &Analysis) -> Arc<Unresolved> {
    a.derived.get_or_build("unresolved_branches", (), || {
        let imports = p
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
            .map(|s| (s.addr, s.addr));
        let stored = a
            .xrefs
            .iter()
            .filter(|(f, _)| a.function(**f).is_some())
            .flat_map(|(&f, sites)| sites.iter().map(move |s| (f, s)))
            .filter(|(_, s)| s.kind == RefKind::Table && s.from_entry.is_none())
            .map(|(f, s)| (s.va, f));
        let slots: BTreeMap<u64, u64> = stored.chain(imports).collect();
        let lone: Vec<_> = a
            .functions
            .iter()
            .filter_map(|f| match f.blocks.as_slice() {
                [b] if matches!(b.term, BlockTerm::Indirect | BlockTerm::Jmp) => {
                    Some((f.entry, b, landings(p, a, &slots, f.entry)))
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
                        let mut to = lands.values().flatten().peekable();
                        to.peek().is_some() && to.all(|t| through.contains(t))
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
        let counts = a
            .functions
            .iter()
            .filter(|f| !through.contains(&f.entry))
            .filter_map(|f| {
                let lands = landings(p, a, &slots, f.entry);
                let n = f
                    .blocks
                    .iter()
                    .filter(|b| blind(a, b, &lands, &through))
                    .count();
                (n > 0).then_some((f.entry, n))
            })
            .collect();
        Unresolved { counts, through }
    })
}

/// Says what a call or reference answer could not see: the indirect calls
/// and jumps borer did not resolve among the functions it read, whose
/// targets are missing from the answer.
///
/// A trampoline's own jump counts only when the answer read none of its
/// callers, which count it where they call it.
///
/// # Arguments
///
/// * `p` - The loaded image.
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
pub fn unseen_line(p: &Program, a: &Analysis, reach: Reach<'_>, lead: &str) -> Option<String> {
    let found = unresolved(p, a);
    let own = |e: &u64, walked: &BTreeSet<u64>| {
        let callers = a.function(*e).map_or(&[][..], |f| f.callers.as_slice());
        (found.through.contains(e) && !callers.iter().any(|c| walked.contains(c))).then_some(1)
    };
    let (sites, functions, scope) = match reach {
        Reach::Program => (
            found.counts.values().sum(),
            found.counts.len(),
            "in the program",
        ),
        Reach::Walked(walked) => walked
            .iter()
            .filter_map(|e| found.counts.get(e).copied().or_else(|| own(e, walked)))
            .fold(
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

/// Appends what a call graph could not see ([`unseen_line`]) as a
/// mermaid comment.
///
/// A graph of callees misses what the unresolved calls of its drawn
/// functions reach; a graph of callers misses the callers that reach the
/// root through an unresolved call anywhere, said when the root has few
/// callers.
///
/// # Arguments
///
/// * `out` - The graph's text, which the `%%` line is appended to.
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `walk` - Which way the graph was walked.
/// * `root_callers` - How many callers the root has.
/// * `drawn` - The graph's nodes.
pub(super) fn graph_line(
    out: &mut String,
    p: &Program,
    a: &Analysis,
    walk: Walk,
    root_callers: usize,
    drawn: &BTreeSet<u64>,
) {
    let reach = match walk {
        Walk::Callers => (root_callers < SHORT_CALLERS).then_some(Reach::Program),
        Walk::Callees => Some(Reach::Walked(drawn)),
    };
    if let Some(line) = reach.and_then(|r| unseen_line(p, a, r, "%%")) {
        out.push_str(&line);
    }
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
        let line = unseen_line(&p, &a, Reach::Program, "#").unwrap_or_default();
        assert!(
            line.starts_with("# not seen: 1 indirect call or jump in 1 function in the program"),
            "{line}"
        );
        let walked = BTreeSet::from([0x1000]);
        let line = unseen_line(&p, &a, Reach::Walked(&walked), "%%").unwrap_or_default();
        assert!(line.starts_with("%% not seen: 1 indirect"), "{line}");
        let callee = BTreeSet::from([0x1014]);
        assert_eq!(unseen_line(&p, &a, Reach::Walked(&callee), "#"), None);
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
        let callers = xrefs_tsv(&p, &a, &o, 0x1014, 0, 60, false);
        assert!(
            callers.contains("\n# not seen: 1 indirect call"),
            "{callers}"
        );
        let count = xrefs_tsv(&p, &a, &o, 0x1014, 0, 60, true);
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
    /// is counted at the call, as the CFG dispatcher's callers are.
    ///
    /// The trampoline's own jump is counted only for an answer that read
    /// none of its callers.
    ///
    /// # Panics
    ///
    /// When the call is not counted, or the trampoline is counted twice or
    /// not at all.
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
        let line = unseen_line(&p, &a, Reach::Program, "#").unwrap_or_default();
        assert!(
            line.starts_with("# not seen: 1 indirect call or jump in 1 function in the program"),
            "{line}"
        );
        let alone = BTreeSet::from([0x1020]);
        let line = unseen_line(&p, &a, Reach::Walked(&alone), "#").unwrap_or_default();
        assert!(line.starts_with("# not seen: 1 indirect"), "{line}");
        let both = BTreeSet::from([0x1000, 0x1020]);
        let line = unseen_line(&p, &a, Reach::Walked(&both), "#").unwrap_or_default();
        assert!(line.starts_with("# not seen: 1 indirect"), "{line}");
    }

    /// A call through a slot in writable data that holds no function is
    /// unresolved, though discovery records the slot as its target.
    ///
    /// # Panics
    ///
    /// When the call through the empty slot is not counted.
    #[test]
    fn a_call_through_an_empty_slot_is_unresolved() {
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
            0xff, 0x15, 0xf6, 0x0f, 0x00, 0x00, // ASM: call [rip+0xff6] (0x2000)
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
            0xc3, // ASM: ret
        ];
        code.resize(0x1000, 0xcc);
        code.extend([0u8; 0x10]);
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let data = Section::mapped(".data", 0x2000, 0x1000, 0x10, true, false);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text, data]);
        let a = Analysis::compute(&p);
        let line = unseen_line(&p, &a, Reach::Program, "#").unwrap_or_default();
        assert!(line.starts_with("# not seen: 1 indirect call"), "{line}");
    }
}
