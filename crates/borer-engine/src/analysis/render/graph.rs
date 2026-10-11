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
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - The annotation overlay, for names.
/// * `from` - Entry of the function to start at.
/// * `to` - Entry of the function to look for.
/// * `depth` - Longest chain to follow, capped at [`REACH_DEPTH_MAX`].
///
/// # Returns
///
/// The chain, one call per line, or a statement that none was found and how far it looked.
pub fn call_path(a: &Analysis, o: &Overlay, from: u64, to: u64, depth: usize) -> String {
    let limit = depth.clamp(1, REACH_DEPTH_MAX);
    if from == to {
        return format!(
            "# {} reaches itself: it is the function asked about\n",
            name_of(a, o, from)
        );
    }
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
            for &callee in &f.callees {
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
            "# {} does not reach {} within {levels} call(s); {} function(s) looked at\n",
            name_of(a, o, from),
            name_of(a, o, to),
            seen.len()
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
        name_of(a, o, from),
        name_of(a, o, to),
        chain.len() - 1,
        seen.len()
    );
    for (i, &entry) in chain.iter().enumerate() {
        let _ = writeln!(out, "{:>3}  {:#x}  {}", i, entry, name_of(a, o, entry));
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
/// that references it.
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
/// A `graph TD` document and a trailing count line.
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
    let mut held: Vec<(u64, Vec<Callee>)> = Vec::new();
    let mut head = 0;
    while head < g.nodes.len() {
        let cur = g.nodes[head];
        head += 1;
        let targets = match walk {
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
        };
        let split = targets.len().min(CallGraph::FANOUT);
        for t in &targets[..split] {
            g.link(cur, t);
        }
        if split < targets.len() {
            held.push((cur, targets[split..].to_vec()));
        }
    }
    let mut elided = 0usize;
    for (cur, rest) in held {
        for t in rest {
            if !g.link(cur, &t) {
                elided += 1;
            }
        }
    }
    let mut out = String::from("graph TD\n");
    for (i, &n) in g.nodes.iter().enumerate() {
        match g.imports.get(&n) {
            Some(name) => {
                let _ = writeln!(out, "  n{i}([\"{}\"])", sanitize_label(name));
            }
            None => {
                let _ = writeln!(out, "  n{i}[\"{}\"]", sanitize_label(&name_of(a, o, n)));
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
    let spill = if elided > 0 {
        let what = match walk {
            Walk::Callers => "callers",
            Walk::Callees => "callees",
        };
        format!(", {elided} {what} not shown")
    } else {
        String::new()
    };
    let dir = match walk {
        Walk::Callers => "callers of the root, transitively",
        Walk::Callees => "callees of the root",
    };
    let _ = writeln!(
        out,
        "# {} nodes, {} imports ({dir}; cap {max_nodes}{spill}); use function(address) for details",
        g.nodes.len(),
        g.imports.len()
    );
    out
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

    /// Draws an edge, adding the target as a node when the budget allows.
    ///
    /// # Arguments
    ///
    /// * `from` - The node the walk reached the target from.
    /// * `to` - The target: a function entry or an import slot.
    ///
    /// # Returns
    ///
    /// Whether the edge was drawn; it is not when `to` is a new node and
    /// the budget is spent.
    pub(super) fn link(&mut self, from: u64, to: &Callee) -> bool {
        if !self.nodes.contains(&to.target) {
            if self.nodes.len() >= self.max_nodes {
                return false;
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
        true
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
/// than [`CFG_BLOCKS_MAX`] blocks draws the first that many in address
/// order with the edges among them and says so on the last line: a
/// 2,900-block dispatcher drew 89 KB of mermaid at once.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names for the title.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// A `graph TD` document with one node per drawn block (`start term`) and
/// one edge per successor among them, then a `# N blocks, showing 300; the
/// rest elided` line when the function was cut; `None` when no function
/// starts at `entry`.
pub fn cfg_mermaid(a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    let f = a.function(entry)?;
    let drawn = f.blocks.get(..CFG_BLOCKS_MAX).unwrap_or(&f.blocks);
    let mut out = format!(
        "graph TD; title[\"{} CFG {} blocks\"]
",
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
    if f.blocks.len() > CFG_BLOCKS_MAX {
        let _ = writeln!(
            out,
            "# {} blocks, showing {CFG_BLOCKS_MAX}; the rest elided",
            f.blocks.len()
        );
    }
    Some(out)
}
