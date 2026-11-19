//! What a call or reference answer could not see: the indirect calls and
//! jumps discovery did not resolve, whose targets are no edge of the call
//! graph and no reference.

use std::sync::Arc;

use super::*;

mod form;
mod rules;
mod spell;

pub use spell::{indirect_check, indirect_tsv};

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

/// Most candidate targets one site keeps; the rest are counted in
/// [`Site::candidates_total`].
pub const CANDIDATES_MAX: usize = 8;

/// The calls and jumps discovery resolved to no target, each site with how
/// it forms its target, why it stayed unresolved and the candidates a rule
/// admits; read once per analysis ([`census`]).
#[derive(Debug, Default)]
pub struct Census {
    /// Every unresolved site outside the trampolines, in address order.
    pub sites: Vec<Site>,
    /// The trampolines: one-block functions that only jump on through a
    /// register, directly or through others. Their own jumps are counted
    /// where they are called, not as sites.
    pub through: BTreeSet<u64>,
}

/// One call or jump discovery resolved to no target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Site {
    /// The entry of the function making it.
    pub function: u64,
    /// The call or jump instruction.
    pub at: u64,
    /// How it forms its target.
    pub form: Form,
    /// Why discovery left it unresolved.
    pub why: Why,
    /// The first [`CANDIDATES_MAX`] targets a rule admits, in address
    /// order; never callers, never complete. Shared by every site the
    /// same rule and slot admit them for.
    pub candidates: Arc<[Candidate]>,
    /// How many targets the rules admit, kept or not.
    pub candidates_total: usize,
}

/// How an unresolved call or jump forms its target, as its block shows it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Form {
    /// Through a register the block does not load from memory.
    Register,
    /// Through `[R+k]`, `R` loaded from memory earlier in the block: slot
    /// `k / word` of the table `R` points at.
    VtableSlot {
        /// The slot's index.
        slot: usize,
    },
    /// Through `[R+k]`, `R` not loaded from memory in the block.
    Field {
        /// `k`, in bytes.
        offset: i64,
    },
    /// Through a slot at a fixed address.
    Global {
        /// The slot's address.
        slot: u64,
    },
    /// Through a word in memory the block ties to no object and no fixed
    /// slot: a stack slot, an indexed table, or a register loaded from
    /// one.
    Memory,
    /// Into a trampoline, through a register the block does not show or
    /// memory that is no fixed slot.
    IntoTrampoline {
        /// The trampoline's entry.
        entry: u64,
    },
    /// An indirect jump through a register, no table found.
    Jump,
}

/// Why discovery resolved an indirect call or jump to no target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Why {
    /// Nothing in the file names a target.
    NoTarget,
    /// It goes through a slot in data that holds no function in the file.
    SlotFilledAtRunTime {
        /// The slot's address.
        slot: u64,
    },
    /// It goes into a trampoline, which goes wherever a register points.
    Trampoline {
        /// The trampoline's entry.
        through: u64,
    },
    /// An indirect jump with no jump table found.
    NoJumpTable,
}

/// A function an unresolved site may reach, with the rule that admitted
/// it; never a caller of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    /// The function's entry.
    pub target: u64,
    /// The rule that admitted it.
    pub rule: Rule,
}

/// The rule that admitted a candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    /// A recovered class holds the function in the slot the site calls
    /// through.
    VtableSlot {
        /// The first class, by name, that holds it there, one allocation
        /// shared by every site it is a candidate of.
        class: Arc<str>,
    },
    /// A store into exactly the slot the site calls through writes the
    /// function's address, loaded in the store's own block.
    StoredSlot {
        /// The store's instruction.
        store: u64,
    },
}

/// Where each call or jump of one function lands, as `(site, landing)`
/// pairs in site order.
///
/// A target in code lands there, an import's slot on the import, and a
/// slot in data holding a function's address ([`RefKind::Table`]) on that
/// function, as a call through a dispatch pointer does. Any other target,
/// a slot filled at run time, lands nowhere: the site has no pair.
///
/// # Arguments
///
/// * `p` - The loaded image, for its code sections.
/// * `a` - The analysis.
/// * `slots` - What each import slot and function pointer in data lands
///   on, by the slot.
/// * `targets` - The function's branch targets ([`targets`]).
fn landings(
    p: &Program,
    a: &Analysis,
    slots: &BTreeMap<u64, u64>,
    targets: &[(u64, u64)],
) -> Vec<(u64, u64)> {
    targets
        .iter()
        .filter_map(|&(site, target)| {
            let lands = if is_code(p, a, target) {
                Some(target)
            } else {
                slots.get(&target).copied()
            };
            lands.map(|t| (site, t))
        })
        .collect()
}

/// Returns a function's call and jump sites with their targets, as
/// `(site, target)` pairs sorted by site, so a block's are one range.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `entry` - The function.
fn targets(a: &Analysis, entry: u64) -> Vec<(u64, u64)> {
    let mut out: Vec<(u64, u64)> = a
        .refs_by_function
        .get(&entry)
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .filter_map(|&(t, i)| Some((t, a.xrefs.get(&t)?.get(i)?)))
        .filter(|(_, s)| s.is_branch())
        .map(|(t, s)| (s.va, t))
        .collect();
    out.sort_unstable();
    out
}

/// Returns the pairs of a site-sorted list whose site lies in a block.
///
/// # Arguments
///
/// * `pairs` - `(site, address)` pairs sorted by site.
/// * `b` - The block.
fn within<'p>(pairs: &'p [(u64, u64)], b: &BasicBlock) -> &'p [(u64, u64)] {
    let lo = pairs.partition_point(|&(s, _)| s < b.start);
    let hi = pairs.partition_point(|&(s, _)| s < b.end);
    pairs.get(lo..hi).unwrap_or_default()
}

/// Tells whether a branch target is code: a function's or an executable
/// section's.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `target` - The target.
fn is_code(p: &Program, a: &Analysis, target: u64) -> bool {
    a.function_at(target).is_some() || p.section_at(target).is_some_and(|sec| sec.executable)
}

/// Whether a block's call or jump reaches no target discovery resolved:
/// none leaves it, or each it has lands nowhere or in a trampoline.
///
/// A direct jump is blind only when it lands in a trampoline: a tail jump
/// into the dispatcher.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `b` - The block.
/// * `lands` - Where the function's branch sites land ([`landings`]).
/// * `through` - The trampolines found so far.
fn blind(a: &Analysis, b: &BasicBlock, lands: &[(u64, u64)], through: &BTreeSet<u64>) -> bool {
    let to = within(lands, b);
    let some = !to.is_empty();
    let reaches = to.iter().any(|(_, t)| !through.contains(t));
    match b.term {
        BlockTerm::Call => !reaches,
        BlockTerm::Indirect => !reaches && a.block_table(b).is_none(),
        BlockTerm::Jmp => some && !reaches,
        BlockTerm::Ret | BlockTerm::Cond | BlockTerm::Fall | BlockTerm::Invalid => false,
    }
}

/// The blocks whose call or jump discovery resolved to no target, read
/// once per analysis ([`blind_blocks`]): what [`unseen_line`] counts, and
/// the sites [`census`] reads the forms of.
#[derive(Debug, Default)]
struct Blind {
    /// Each such block outside the trampolines: its function's entry and
    /// its index among the function's blocks, in function order.
    blocks: Vec<(u64, usize)>,
    /// The trampolines ([`Census::through`]).
    through: BTreeSet<u64>,
    /// How many blocks each function has, by entry; functions with none
    /// left out.
    counts: BTreeMap<u64, usize>,
    /// What each import slot and function pointer in data lands on, by the
    /// slot ([`landings`]).
    slots: BTreeMap<u64, u64>,
}

/// Finds, for each function, its calls and jumps that discovery resolved
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
fn blind_blocks(p: &Program, a: &Analysis) -> Arc<Blind> {
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
        let through = trampolines(p, a, &slots);
        let mut blocks = Vec::new();
        let mut counts = BTreeMap::new();
        let live = a
            .functions
            .iter()
            .take_while(|_| !crate::cancel::Cancel::raised());
        for f in live.filter(|f| !through.contains(&f.entry)) {
            let lands = landings(p, a, &slots, &targets(a, f.entry));
            let before = blocks.len();
            blocks.extend(
                f.blocks
                    .iter()
                    .enumerate()
                    .filter(|(_, b)| blind(a, b, &lands, &through))
                    .map(|(i, _)| (f.entry, i)),
            );
            if blocks.len() > before {
                counts.insert(f.entry, blocks.len() - before);
            }
        }
        Blind {
            blocks,
            through,
            counts,
            slots,
        }
    })
}

/// Returns every call and jump discovery resolved to no target, outside
/// the trampolines, with its form, why and candidates.
///
/// Built the first time it is asked for, never at load, from the blocks
/// [`unseen_line`] counts, less those ending in a direct call or jump that
/// lands in no trampoline, and memoized for the analysis
/// ([`crate::analysis::Derived`]). A build the request's cancel flag cuts
/// short stops between blocks and is not kept.
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports and code sections.
/// * `a` - The analysis.
///
/// # Returns
///
/// The census.
#[must_use]
pub fn census(p: &Program, a: &Analysis) -> Arc<Census> {
    a.derived.get_or_build("indirect_census", (), || {
        let found = blind_blocks(p, a);
        let jumps = form::jumps(p, a, &found.through);
        let mut sites = Vec::with_capacity(found.blocks.len());
        let mut of = (None, Vec::new(), Vec::new());
        let none: Arc<[Candidate]> = Arc::from([]);
        let live = found
            .blocks
            .iter()
            .take_while(|_| !crate::cancel::Cancel::raised());
        for &(entry, i) in live {
            let Some(b) = a.function(entry).and_then(|f| f.blocks.get(i)) else {
                continue;
            };
            if of.0 != Some(entry) {
                let raw = targets(a, entry);
                let lands = landings(p, a, &found.slots, &raw);
                of = (Some(entry), raw, lands);
            }
            let block = form::Block {
                targets: within(&of.1, b),
                lands: within(&of.2, b),
            };
            let Some((at, form, why)) = form::site(p, a, b, block, &found.through, &jumps) else {
                continue;
            };
            sites.push(Site {
                function: entry,
                at,
                form,
                why,
                candidates: Arc::clone(&none),
                candidates_total: 0,
            });
        }
        sites.sort_unstable_by_key(|s| (s.at, s.function));
        rules::fill(p, a, &mut sites);
        Census {
            sites,
            through: found.through.clone(),
        }
    })
}

/// Returns the trampolines: the one-block functions whose jump reaches no
/// target discovery resolved, or only other trampolines.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `slots` - What each import slot and function pointer in data lands
///   on, by the slot.
fn trampolines(p: &Program, a: &Analysis, slots: &BTreeMap<u64, u64>) -> BTreeSet<u64> {
    let lone: Vec<_> = a
        .functions
        .iter()
        .filter_map(|f| match f.blocks.as_slice() {
            [b] if matches!(b.term, BlockTerm::Indirect | BlockTerm::Jmp) => {
                Some((f.entry, b, landings(p, a, slots, &targets(a, f.entry))))
            }
            _ => None,
        })
        .collect();
    let mut through = BTreeSet::new();
    for _ in 0..=TRAMPOLINE_HOPS {
        let next: BTreeSet<u64> = lone
            .iter()
            .filter(|(_, b, lands)| blind(a, b, lands, &through))
            .map(|(e, _, _)| *e)
            .collect();
        if next == through {
            break;
        }
        through = next;
    }
    through
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
    let found = blind_blocks(p, a);
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

/// Appends the incomplete-walk warning and what a call graph could not see
/// ([`unseen_line`]) as mermaid comments.
///
/// An incomplete walk writes [`INCOMPLETE_NOTE`] under `%%`. A graph of
/// callees also notes what the unresolved calls of its drawn functions
/// reach; a graph of callers notes the callers that reach the root through
/// an unresolved call anywhere, said when the root has few callers.
///
/// # Arguments
///
/// * `out` - The graph's text, which any `%%` lines are appended to.
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
    if a.incomplete {
        let _ = writeln!(out, "%%{}", INCOMPLETE_NOTE.trim_start_matches('#'));
    }
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

    /// A tail jump into a trampoline is unresolved, as the call into it is.
    ///
    /// # Panics
    ///
    /// When the tail jump is not counted.
    #[test]
    fn a_tail_jump_into_a_trampoline_is_unresolved() {
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
            0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
            0x85, 0xc9, // ASM: test ecx,ecx
            0x74, 0x05, // ASM: je 0x1016
            0xe9, 0x0a, 0x00, 0x00, 0x00, // ASM: jmp 0x1020
            0xc3, // ASM: ret
        ];
        code.resize(0x20, 0xcc);
        code.extend([0xff, 0xe0]); // ASM: jmp rax
        let len = u64::try_from(code.len()).unwrap_or(0);
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let line = unseen_line(&p, &a, Reach::Program, "#").unwrap_or_default();
        assert!(
            line.starts_with("# not seen: 2 indirect calls or jumps in 1 function in"),
            "{line}"
        );
    }

    /// Call graphs, unreached call paths, and string-to-function reports carry
    /// [`super::super::INCOMPLETE_NOTE`] when [`Analysis::incomplete`] is set.
    ///
    /// # Panics
    ///
    /// When a complete answer warns or an incomplete answer drops the warning.
    #[test]
    fn incomplete_walks_warn_in_graphs_paths_and_strings() {
        use crate::analysis::Overlay;
        use crate::analysis::render::{
            INCOMPLETE_NOTE, Walk, call_path, callgraph, functions_by_string_tsv,
            hidden_strings_tsv,
        };
        let p = calls();
        let mut a = Analysis::compute(&p);
        let o = Overlay::default();
        let mermaid_note = format!("%%{}", INCOMPLETE_NOTE.trim_start_matches('#'));
        assert!(!callgraph(&p, &a, &o, 0x1000, 20, Walk::Callees).contains(&mermaid_note));
        assert!(!call_path(&p, &a, &o, 0x1014, 0x1000, 8).contains(INCOMPLETE_NOTE));
        assert!(!functions_by_string_tsv(&p, &a, &o, "none", 0, 20).contains(INCOMPLETE_NOTE));
        assert!(!hidden_strings_tsv(&p, &a, &o, "").contains(INCOMPLETE_NOTE));
        a.incomplete = true;
        assert!(callgraph(&p, &a, &o, 0x1000, 20, Walk::Callees).contains(&mermaid_note));
        assert!(call_path(&p, &a, &o, 0x1014, 0x1000, 8).contains(INCOMPLETE_NOTE));
        assert!(functions_by_string_tsv(&p, &a, &o, "none", 0, 20).contains(INCOMPLETE_NOTE));
        assert!(hidden_strings_tsv(&p, &a, &o, "").contains(INCOMPLETE_NOTE));
    }
}
