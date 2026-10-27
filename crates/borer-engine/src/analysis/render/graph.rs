//! Call paths, call graphs and control-flow graphs, as text and mermaid.

use super::*;

/// Most functions a reachability search will look at before giving up.
///
/// A call graph of a hundred thousand functions is still searched in a moment, so this is
/// only there so a pathological graph cannot hang a request.
pub(super) const REACH_VISITS_MAX: usize = 400_000;

/// Deepest call chain a reachability search will follow.
pub(super) const REACH_DEPTH_MAX: usize = 64;

/// Whether one function reaches another through calls, and by what chain.
///
/// "Does this code path ever get to the send, to the allocator, to this check" is the
/// question a call graph is usually opened to answer, and a rendered graph answers it badly:
/// it is capped to stay readable, so on a real binary it shows a neighbourhood rather than a
/// path, and the two functions are almost never in the same neighbourhood. The answer wanted
/// is a chain, and a chain is a few lines however large the program is.
///
/// The search is breadth-first, so the chain returned is a shortest one. There may be
/// others; this says how many functions it had to look at to find this, which is what says
/// whether "no" means no. The parent of each function on the way is kept, which is what
/// turns a visit into the chain that reached it.
///
/// The goal may be an import called through its slot with no thunk, which no function is
/// the body of: each function that calls or jumps through the slot has it as one more
/// callee, so the chain's last call is the call of the import.
///
/// # Arguments
///
/// * `p` - The loaded image, for an import's name.
/// * `a` - The analysis.
/// * `o` - The annotation overlay, for names.
/// * `from` - Entry of the function to start at.
/// * `to` - Entry of the function to look for, or an import's slot.
/// * `depth` - Longest chain to follow, capped at [`REACH_DEPTH_MAX`].
///
/// # Returns
///
/// The chain, one call per line, or a statement that none was found and how far it looked.
pub fn call_path(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    from: u64,
    to: u64,
    depth: usize,
) -> String {
    let limit = depth.clamp(1, REACH_DEPTH_MAX);
    let label = |va: u64| node_label(p, a, o, va);
    if from == to {
        return format!(
            "# {} reaches itself: it is the function asked about\n",
            label(from)
        );
    }
    let through_slot: BTreeSet<u64> = if a.function(to).is_some() {
        BTreeSet::new()
    } else {
        a.xrefs_to(to)
            .iter()
            .filter(|s| s.is_branch())
            .filter_map(|s| s.from_entry)
            .collect()
    };
    let mut came_from: BTreeMap<u64, u64> = BTreeMap::new();
    let mut frontier = vec![from];
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    seen.insert(from);
    let mut found = false;
    let mut levels = 0usize;
    'search: while !frontier.is_empty() && levels < limit && seen.len() < REACH_VISITS_MAX {
        levels += 1;
        let mut next = Vec::new();
        for cur in frontier {
            let Some(f) = a.function(cur) else { continue };
            let slot = through_slot.contains(&cur).then_some(to);
            for callee in f.callees.iter().copied().chain(slot) {
                if !seen.insert(callee) {
                    continue;
                }
                came_from.insert(callee, cur);
                if callee == to {
                    found = true;
                    break 'search;
                }
                next.push(callee);
            }
        }
        frontier = next;
    }
    if !found {
        return format!(
            "# {} does not reach {} within {levels} call(s); {} function(s) looked at\n{}",
            label(from),
            label(to),
            seen.len(),
            unseen_line(p, a, Reach::Walked(&seen), "#").unwrap_or_default()
        );
    }
    let mut chain = vec![to];
    let mut at = to;
    while let Some(&parent) = came_from.get(&at) {
        chain.push(parent);
        at = parent;
        if at == from {
            break;
        }
    }
    chain.reverse();
    let mut out = format!(
        "# {} reaches {} in {} call(s); {} function(s) looked at\n",
        label(from),
        label(to),
        chain.len() - 1,
        seen.len()
    );
    for (i, &entry) in chain.iter().enumerate() {
        let _ = writeln!(out, "{:>3}  {:#x}  {}", i, entry, label(entry));
    }
    out
}

/// Which way a call graph is walked from its root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Walk {
    /// What the root calls, transitively.
    Callees,
    /// What reaches the root, transitively.
    Callers,
}

/// Renders the callgraph under or over a function as mermaid.
///
/// [`callgraph`] with the direction as a flag.
///
/// # Arguments
///
/// * `p` - The loaded image, for the import names.
/// * `a` - The analysis.
/// * `o` - User names for the labels.
/// * `root` - The root function's entry.
/// * `max_nodes` - Most nodes in the graph, the root included.
/// * `callers` - Walk what reaches the root instead of what it calls.
///
/// # Returns
///
/// As [`callgraph`].
pub fn callgraph_mermaid(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    root: u64,
    max_nodes: usize,
    callers: bool,
) -> String {
    let walk = if callers {
        Walk::Callers
    } else {
        Walk::Callees
    };
    callgraph(p, a, o, root, max_nodes, walk)
}

/// Renders the callgraph under or over a function as mermaid.
///
/// The node budget is spent in two rounds so a wide root neither starves
/// depth nor wastes the budget: the first walks breadth-first with at most
/// [`CallGraph::FANOUT`] callees per node, which reserves nodes for what
/// the callees call; the second gives the callees held back whatever is
/// left, in the same order. An import called through its slot is a leaf,
/// drawn as a stadium and named after the import: on a framework program
/// the imports are most of what a function does.
///
/// Walking callers answers what reaches a function: an import has none and
/// a caller carries no slot name, so the targets are plain entries, and an
/// import or a data symbol, which has no body, is reached by every function
/// that references it. Such a root is labelled by its symbol, an import
/// drawn as the stadium it is everywhere else, where `sub_<hex>` named a
/// function that is not there.
///
/// The count of what is not shown is of distinct functions and imports a
/// drawn node calls (or is called by) that the graph does not hold, every
/// node's included: counting only the second round's refusals missed the
/// first round's and those of the nodes the second round added.
///
/// # Arguments
///
/// * `p` - The loaded image, for the import names.
/// * `a` - The analysis.
/// * `o` - User names for the labels.
/// * `root` - The root function's entry.
/// * `max_nodes` - Most nodes in the graph, the root included.
/// * `walk` - Which way to walk from the root.
///
/// # Returns
///
/// A `graph TD` document and a trailing `%%` count line, a mermaid
/// comment, so the whole answer parses as a diagram.
pub fn callgraph(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    root: u64,
    max_nodes: usize,
    walk: Walk,
) -> String {
    let slots: BTreeMap<u64, &str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect();
    let mut g = CallGraph {
        nodes: vec![root],
        imports: BTreeMap::new(),
        edges: Vec::new(),
        max_nodes,
        walk,
    };
    if a.function(root).is_none()
        && let Some(raw) = slots.get(&root)
    {
        let name = crate::search::demangled_name(raw);
        g.imports.insert(root, bare_name(&name).to_owned());
    }
    let targets_of = |cur: u64| -> Vec<Callee> {
        match walk {
            Walk::Callers => match a.function(cur) {
                Some(f) => f.callers.iter().map(|&c| Callee::near(c)).collect(),
                None => {
                    let mut from: Vec<Callee> = a.xrefs.get(&cur).map_or_else(Vec::new, |sites| {
                        sites
                            .iter()
                            .filter_map(|s| s.from_entry)
                            .map(Callee::near)
                            .collect()
                    });
                    from.sort_unstable();
                    from.dedup();
                    from
                }
            },
            Walk::Callees => callees_of(a, &slots, cur),
        }
    };
    let mut held: Vec<(u64, Vec<Callee>)> = Vec::new();
    let mut head = 0;
    while head < g.nodes.len() {
        let cur = g.nodes[head];
        head += 1;
        let targets = targets_of(cur);
        let split = targets.len().min(CallGraph::FANOUT);
        for t in &targets[..split] {
            g.link(cur, t);
        }
        if split < targets.len() {
            held.push((cur, targets[split..].to_vec()));
        }
    }
    for (cur, rest) in held {
        for t in rest {
            g.link(cur, &t);
        }
    }
    let drawn: BTreeSet<u64> = g.nodes.iter().copied().collect();
    let hidden: BTreeSet<u64> = g
        .nodes
        .iter()
        .flat_map(|&n| targets_of(n))
        .map(|t| t.target)
        .filter(|t| !drawn.contains(t))
        .collect();
    let mut out = String::from("graph TD\n");
    for (i, &n) in g.nodes.iter().enumerate() {
        match g.imports.get(&n) {
            Some(name) => {
                let _ = writeln!(out, "  n{i}([\"{}\"])", sanitize_label(name));
            }
            None => {
                let _ = writeln!(
                    out,
                    "  n{i}[\"{}\"]",
                    sanitize_label(&node_label(p, a, o, n))
                );
            }
        }
    }
    for (from, to) in &g.edges {
        if let (Some(i), Some(j)) = (
            g.nodes.iter().position(|n| n == from),
            g.nodes.iter().position(|n| n == to),
        ) {
            let _ = writeln!(out, "  n{i} --> n{j}");
        }
    }
    let (what, dir) = match walk {
        Walk::Callers => ("callers", "callers of the root, transitively"),
        Walk::Callees => ("callees", "callees of the root"),
    };
    let spill = if hidden.is_empty() {
        String::new()
    } else {
        format!(", {} {what} not shown", hidden.len())
    };
    let _ = writeln!(
        out,
        "%% {} nodes, {} imports ({dir}; cap {max_nodes}{spill}); use function(address) for details",
        g.nodes.len(),
        g.imports.len()
    );
    unseen::graph_line(&mut out, p, a, walk, targets_of(root).len(), &drawn);
    out
}

/// Labels a node that is not drawn as an import: its user or function
/// name, else the symbol at it (a data root walked for its callers), else
/// its address.
///
/// # Arguments
///
/// * `p` - The loaded image, for the symbols.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `n` - The node's address.
fn node_label(p: &Program, a: &Analysis, o: &Overlay, n: u64) -> String {
    if o.names.contains_key(&n) || a.function(n).is_some() {
        return name_of(a, o, n);
    }
    a.symbol_at(p, n).map_or_else(
        || format!("{n:#x}"),
        |s| bare_name(&crate::search::demangled_name(&s.name)).to_owned(),
    )
}

/// A call target and, when it is an import slot, the import's name.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Callee {
    /// A function entry, or an import slot.
    pub(super) target: u64,
    /// The import's name, without its `dll!` prefix, when `target` is a slot.
    pub(super) import: Option<String>,
}

impl Callee {
    /// A near callee: a function of the program's own.
    ///
    /// # Arguments
    ///
    /// * `target` - Its entry.
    pub(super) fn near(target: u64) -> Self {
        Self {
            target,
            import: None,
        }
    }
}

/// The callgraph under construction: its nodes in the order they were
/// reached, which import each leaf is, and its edges.
pub(super) struct CallGraph {
    /// Function entries and import slots, the root first.
    pub(super) nodes: Vec<u64>,
    /// The import name of every node that is an import slot.
    pub(super) imports: BTreeMap<u64, String>,
    /// `(from, to)` pairs in the order they were drawn.
    pub(super) edges: Vec<(u64, u64)>,
    /// Most nodes the graph may hold.
    pub(super) max_nodes: usize,
    /// Which way the walk goes. Over callers, an edge runs from the node
    /// just added into the one it was reached from: arrows still point the
    /// way calls go.
    pub(super) walk: Walk,
}

impl CallGraph {
    /// Most callees expanded per node in the first round, so one wide
    /// function cannot spend the whole node budget on its own children and
    /// leave none for depth.
    pub(super) const FANOUT: usize = 6;

    /// Draws an edge, adding the target as a node when the budget allows;
    /// a new target past the budget is left out, edge and all.
    ///
    /// # Arguments
    ///
    /// * `from` - The node the walk reached the target from.
    /// * `to` - The target: a function entry or an import slot.
    pub(super) fn link(&mut self, from: u64, to: &Callee) {
        if !self.nodes.contains(&to.target) {
            if self.nodes.len() >= self.max_nodes {
                return;
            }
            self.nodes.push(to.target);
            if let Some(n) = &to.import {
                self.imports.insert(to.target, n.clone());
            }
        }
        match self.walk {
            Walk::Callers => self.edges.push((to.target, from)),
            Walk::Callees => self.edges.push((from, to.target)),
        }
    }
}

/// Lists what a function calls: its near callees, then the imports it
/// calls or jumps to through their slots, in site order.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slots` - Import slot address to the import's raw name.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The callees, the imports named without their `dll!` prefix.
pub(super) fn callees_of(a: &Analysis, slots: &BTreeMap<u64, &str>, entry: u64) -> Vec<Callee> {
    let Some(f) = a.function(entry) else {
        return Vec::new();
    };
    let mut out: Vec<Callee> = f.callees.iter().map(|&c| Callee::near(c)).collect();
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    for (target, site) in a.refs_from(entry) {
        if !site.is_branch() {
            continue;
        }
        let Some(raw) = slots.get(&target) else {
            continue;
        };
        if seen.insert(target) {
            let name = crate::search::demangled_name(raw);
            out.push(Callee {
                target,
                import: Some(bare_name(&name).to_owned()),
            });
        }
    }
    out
}

/// Most blocks a control-flow graph draws.
pub const CFG_BLOCKS_MAX: usize = 300;

/// Renders a function's control-flow graph as mermaid.
///
/// A node is labelled by its block's start and terminator; the end is the
/// next block's start, and `function` lists the sizes. A function of more
/// than [`CFG_BLOCKS_MAX`] blocks draws that many in address order from
/// `offset`, with the edges among them, and says so on the last line: a
/// 2,900-block dispatcher drew 89 KB of mermaid at once, and the blocks
/// past the first page are read by paging. The line is a `%%` comment, so
/// the whole answer parses as a diagram.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names for the title.
/// * `entry` - The function's entry address.
/// * `offset` - Blocks to skip, in address order, before the page drawn.
///
/// # Returns
///
/// A `graph TD` document with one node per drawn block (`start term`) and
/// one edge per successor among them, then a `%% showing N of M blocks
/// from O` line when the function was cut; `None` when no function starts
/// at `entry`.
pub fn cfg_mermaid(a: &Analysis, o: &Overlay, entry: u64, offset: usize) -> Option<String> {
    let f = a.function(entry)?;
    let drawn = f
        .blocks
        .iter()
        .skip(offset)
        .take(CFG_BLOCKS_MAX)
        .collect::<Vec<_>>();
    let mut out = format!(
        "graph TD; title[\"{} CFG {} blocks\"]\n",
        sanitize_label(&name_of(a, o, entry)),
        f.blocks.len()
    );
    let index: BTreeMap<u64, usize> = drawn
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    for (i, b) in drawn.iter().enumerate() {
        let _ = writeln!(out, "  n{i}[\"{:#x} {}\"]", b.start, b.term.name());
    }
    for (i, b) in drawn.iter().enumerate() {
        for &s in &b.successors {
            if let Some(&j) = index.get(&s) {
                let _ = writeln!(out, "  n{i} --> n{j}");
            }
        }
    }
    if drawn.len() < f.blocks.len() {
        let _ = write!(
            out,
            "%% {} blocks from {offset}",
            showing(drawn.len(), f.blocks.len())
        );
        let next = offset.saturating_add(drawn.len());
        if next < f.blocks.len() {
            let _ = write!(out, "; offset={next} for the next page");
        }
        out.push('\n');
    }
    Some(out)
}
