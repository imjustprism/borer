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
            "# {} does not reach {} within {levels} call(s); {} function(s) looked at\n{}{}",
            label(from),
            label(to),
            seen.len(),
            incomplete_line(a.incomplete),
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
    let slots = import_slots(p);
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
    let targets_of = |cur: u64| call_targets(a, &slots, cur, walk);
    let far = |targets: &[Callee]| -> Vec<u64> { targets.iter().map(|t| t.target).collect() };
    let mut reached: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut held: Vec<(u64, Vec<Callee>)> = Vec::new();
    let mut head = 0;
    while head < g.nodes.len() {
        let cur = g.nodes[head];
        head += 1;
        let mut targets = targets_of(cur);
        reached.insert(cur, far(&targets));
        let rest = targets.split_off(targets.len().min(CallGraph::FANOUT));
        for t in &targets {
            g.link(cur, t);
        }
        if !rest.is_empty() {
            held.push((cur, rest));
        }
    }
    for (cur, rest) in held {
        for t in rest {
            g.link(cur, &t);
        }
    }
    for &n in &g.nodes {
        reached.entry(n).or_insert_with(|| far(&targets_of(n)));
    }
    let drawn: BTreeSet<u64> = g.nodes.iter().copied().collect();
    let hidden: BTreeSet<u64> = reached
        .values()
        .flatten()
        .copied()
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
    let from_root = reached.get(&root).map_or(0, Vec::len);
    unseen::graph_line(&mut out, p, a, walk, from_root, &drawn);
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

/// A neighbor a call graph walk takes from a node, with the instructions
/// making the edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Callee {
    /// A function entry, or an import slot.
    pub(super) target: u64,
    /// The import's name, without its `dll!` prefix, when `target` is a slot.
    pub(super) import: Option<String>,
    /// The instructions making the edge, in address order: in the node
    /// over callees, in the caller over callers; only the calls and jumps
    /// when there are any, else the references. Empty when discovery
    /// knows the call without a site for it.
    pub(super) sites: Vec<u64>,
    /// Some site calls or jumps; when false every site only references
    /// the node (a load of an import slot or of a global, over callers).
    pub(super) called: bool,
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

/// Returns the program's import slots, each with the import's raw name.
///
/// # Arguments
///
/// * `p` - The loaded image.
pub(super) fn import_slots(p: &Program) -> BTreeMap<u64, &str> {
    p.symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect()
}

/// Returns the neighbors a call graph walk takes from one node, each with
/// the instructions making the edge: the one rule [`callgraph`] and
/// [`call_children`] both follow.
///
/// Over callees they are [`callees_of`]. Over callers they are the
/// function's callers, or, for a node with no body (an import slot, a
/// global), every function that references it, in entry order.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slots` - Import slot address to the import's raw name
///   ([`import_slots`]).
/// * `cur` - The node: a function entry, an import slot or a data address.
/// * `walk` - Which way to walk.
pub(super) fn call_targets(
    a: &Analysis,
    slots: &BTreeMap<u64, &str>,
    cur: u64,
    walk: Walk,
) -> Vec<Callee> {
    match walk {
        Walk::Callers => callers_of(a, cur),
        Walk::Callees => callees_of(a, slots, cur),
    }
}

/// Lists what reaches a node: a function's callers, each with its call
/// and jump sites naming the function, or, for a node with no body,
/// every function referencing it, with every reference.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `cur` - The node.
///
/// # Returns
///
/// The callers, in [`Function::callers`] order for a function, else by
/// entry.
fn callers_of(a: &Analysis, cur: u64) -> Vec<Callee> {
    let body = a.function(cur);
    let mut by: BTreeMap<u64, (Vec<u64>, Vec<u64>)> = BTreeMap::new();
    for s in a.xrefs_to(cur) {
        let Some(from) = s.from_entry else { continue };
        let (calls, uses) = by.entry(from).or_default();
        match (s.is_branch(), body) {
            (true, _) => calls.push(s.va),
            (false, None) => uses.push(s.va),
            (false, Some(_)) => {}
        }
    }
    let edge = |target: u64, (calls, uses): (Vec<u64>, Vec<u64>)| {
        let called = !calls.is_empty() || uses.is_empty();
        let mut sites = if calls.is_empty() { uses } else { calls };
        sites.sort_unstable();
        sites.dedup();
        Callee {
            target,
            import: None,
            sites,
            called,
        }
    };
    match body {
        Some(f) => f
            .callers
            .iter()
            .map(|&c| edge(c, by.remove(&c).unwrap_or_default()))
            .collect(),
        None => by.into_iter().map(|(c, made)| edge(c, made)).collect(),
    }
}

/// Lists what a function calls: its near callees, then the imports it
/// calls or jumps to through their slots, in site order, each with its
/// call and jump sites.
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
    let mut by: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut first: Vec<u64> = Vec::new();
    for (target, site) in a.refs_from(entry) {
        if site.is_branch() {
            let sites = by.entry(target).or_default();
            if sites.is_empty() {
                first.push(target);
            }
            sites.push(site.va);
        }
    }
    let mut out: Vec<Callee> = f
        .callees
        .iter()
        .map(|&target| Callee {
            target,
            import: None,
            sites: by.get(&target).cloned().unwrap_or_default(),
            called: true,
        })
        .collect();
    for target in first {
        if let Some(raw) = slots.get(&target) {
            let name = crate::search::demangled_name(raw);
            out.push(Callee {
                target,
                import: Some(bare_name(&name).to_owned()),
                sites: by.remove(&target).unwrap_or_default(),
                called: true,
            });
        }
    }
    out
}

/// Most edges [`call_children`] lists for one node.
pub const CALL_CHILDREN_MAX: usize = 1024;

/// Most call sites one [`CallEdge`] lists.
pub const CALL_SITES_MAX: usize = 16;

/// How a call edge is known: what the called end of the edge is.
///
/// Over callees the called end is the edge's target; over callers it is
/// the node the level was asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Via {
    /// A call or jump straight to an address of the program's own.
    Direct,
    /// A call or jump through an import slot: the called end is the slot.
    Import,
    /// A call or jump to an import thunk, `jmp [slot]` and nothing else
    /// ([`Function::thunk`]).
    Thunk {
        /// The import slot the thunk jumps through.
        slot: u64,
    },
    /// A call or jump to a linkage stub the loader binds to a function of
    /// the program's own ([`Function::bound`]): over callees the edge's
    /// target is that function, not the stub, and over callers of that
    /// function the stub's callers are its callers.
    Bound {
        /// The stub's entry, which the call instruction names.
        stub: u64,
    },
    /// A virtual call the decompiler resolved through the receiver's
    /// vtable ([`crate::analysis::decompile::virtual_calls`]), listed only
    /// for [`Level::CalleesAndVirtuals`].
    Virtual {
        /// The slot's index in the vtable.
        slot: usize,
    },
    /// References that never call or jump to a node with no body, over
    /// callers: a load of an import slot, or a use of a global.
    Data,
}

/// One edge of a level of the call tree: a function the node calls, or
/// one that calls it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEdge {
    /// The function entry or import slot at the far end of the edge.
    pub target: u64,
    /// The target's name as listings spell it: the overlay's, else the
    /// engine's, else its symbol's, else its address.
    pub name: Box<str>,
    /// How the call is known.
    pub via: Via,
    /// The instructions making the call, in address order, the first
    /// [`CALL_SITES_MAX`]: in the node over callees, in the target over
    /// callers. Each names the called end: the stub for [`Via::Bound`];
    /// for [`Via::Data`] they are the references.
    pub sites: Vec<u64>,
    /// How many instructions make the call, the ones `sites` holds
    /// included. The cross-reference index keeps at most 65,536 sites of
    /// one target, so past that it is a floor.
    pub site_count: usize,
    /// The target has no edge of its own to follow the same way: an
    /// import, a function that calls nothing, or one nothing calls.
    pub leaf: bool,
}

/// One level of the call tree, as [`call_children`] lists it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Children {
    /// The edges, by target and then first site, at most
    /// [`CALL_CHILDREN_MAX`].
    pub rows: Vec<CallEdge>,
    /// How many edges there are, the ones `rows` holds included.
    pub total: usize,
}

/// Which level of the call tree [`call_children`] lists for a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    /// What the node calls, as the cross-references show it.
    Callees,
    /// What the node calls, with the virtual calls the decompiler resolves
    /// in it ([`Via::Virtual`]): this decompiles the node, once, memoized.
    CalleesAndVirtuals,
    /// What calls the node.
    Callers,
}

impl Level {
    /// Returns the way the level walks the call graph.
    #[must_use]
    pub fn walk(self) -> Walk {
        match self {
            Level::Callees | Level::CalleesAndVirtuals => Walk::Callees,
            Level::Callers => Walk::Callers,
        }
    }
}

/// Returns one level of the call tree under or over a node: each edge,
/// how it is known and the instructions that make it.
///
/// The edges are the ones [`callgraph`] draws ([`call_targets`]), with one
/// difference: a call to a stub the loader binds to a local function
/// leads to that function, since the stub's own level would be empty, and
/// the function's callers include the stub's. The graph draws the stub.
/// Virtual calls are only listed when asked for, since finding them
/// decompiles the node; a target's `leaf` never looks for them. A tree is
/// expanded one node at a time, so a cycle is not a level's business: the
/// caller marks a node already on its path.
///
/// # Arguments
///
/// * `p` - The loaded image, for import and symbol names.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `node` - A function entry, an import slot or a data address.
/// * `level` - Whether the level lists what the node calls, with or
///   without its virtual calls, or what calls it.
///
/// # Returns
///
/// The edges by target and then first site, capped at
/// [`CALL_CHILDREN_MAX`], and how many there are; no edges for a node that
/// calls nothing, or that nothing calls.
#[must_use]
pub fn call_children(p: &Program, a: &Analysis, o: &Overlay, node: u64, level: Level) -> Children {
    let walk = level.walk();
    let slots = import_slots(p);
    let stubs = bound_stubs(a, walk);
    let mut found = tree_edges(a, &slots, &stubs, node, walk);
    if level == Level::CalleesAndVirtuals {
        let mut resolved: BTreeMap<(u64, usize), Vec<u64>> = BTreeMap::new();
        for c in crate::analysis::decompile::virtual_calls(p, a, o, node) {
            resolved.entry((c.entry, c.slot)).or_default().push(c.site);
        }
        found.extend(resolved.into_iter().map(|((entry, slot), mut sites)| {
            sites.sort_unstable();
            (entry, Via::Virtual { slot }, sites)
        }));
    }
    found.sort_unstable_by_key(|(target, via, sites)| (*target, sites.first().copied(), *via));
    let total = found.len();
    let rows = found
        .into_iter()
        .take(CALL_CHILDREN_MAX)
        .map(|(target, via, mut sites)| {
            let site_count = sites.len();
            sites.truncate(CALL_SITES_MAX);
            CallEdge {
                target,
                name: node_label(p, a, o, target).into_boxed_str(),
                via,
                sites,
                site_count,
                leaf: !has_edges(a, &slots, &stubs, target, walk),
            }
        })
        .collect();
    Children { rows, total }
}

/// Returns, over callers, each local function's entry with the entries of
/// the linkage stubs bound to it ([`Function::bound`]); over callees none
/// is needed.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `walk` - Which way the level walks.
fn bound_stubs(a: &Analysis, walk: Walk) -> BTreeMap<u64, Vec<u64>> {
    let mut out: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    if walk == Walk::Callers {
        for f in &a.functions {
            if let Some(to) = f.bound {
                out.entry(to).or_default().push(f.entry);
            }
        }
    }
    out
}

/// Returns a node's edges in the call tree: [`call_targets`] with each
/// one's far end and [`Via`], and over callers the callers of every stub
/// bound to the node.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slots` - The import slots ([`import_slots`]).
/// * `stubs` - The stubs bound to each local function ([`bound_stubs`]).
/// * `node` - The node the level is for.
/// * `walk` - Which way the level walks.
///
/// # Returns
///
/// Each edge as its target, how it is known and every site making it.
fn tree_edges(
    a: &Analysis,
    slots: &BTreeMap<u64, &str>,
    stubs: &BTreeMap<u64, Vec<u64>>,
    node: u64,
    walk: Walk,
) -> Vec<(u64, Via, Vec<u64>)> {
    let mut out: Vec<(u64, Via, Vec<u64>)> = call_targets(a, slots, node, walk)
        .into_iter()
        .map(|c| {
            let end = match walk {
                Walk::Callees => c.target,
                Walk::Callers => node,
            };
            let via = via_of(a, slots, end, c.called);
            let target = match (walk, via) {
                (Walk::Callees, Via::Bound { .. }) => {
                    crate::analysis::decompile::abi::reached(a, end)
                }
                _ => c.target,
            };
            (target, via, c.sites)
        })
        .collect();
    for &stub in stubs.get(&node).map_or(&[][..], Vec::as_slice) {
        out.extend(
            callers_of(a, stub)
                .into_iter()
                .map(|c| (c.target, Via::Bound { stub }, c.sites)),
        );
    }
    out
}

/// Tells whether a node has an edge of its own in the call tree, as
/// [`tree_edges`] would list it, without listing them.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slots` - The import slots ([`import_slots`]).
/// * `stubs` - The stubs bound to each local function ([`bound_stubs`]).
/// * `n` - The node.
/// * `walk` - Which way the level walks.
fn has_edges(
    a: &Analysis,
    slots: &BTreeMap<u64, &str>,
    stubs: &BTreeMap<u64, Vec<u64>>,
    n: u64,
    walk: Walk,
) -> bool {
    let called = |e: u64| a.function(e).is_some_and(|f| !f.callers.is_empty());
    match (walk, a.function(n)) {
        (Walk::Callees, None) => false,
        (Walk::Callees, Some(f)) => {
            !f.callees.is_empty()
                || a.refs_from(n)
                    .iter()
                    .any(|(t, s)| s.is_branch() && slots.contains_key(t))
        }
        (Walk::Callers, Some(_)) => {
            called(n) || stubs.get(&n).is_some_and(|s| s.iter().any(|&e| called(e)))
        }
        (Walk::Callers, None) => a.xrefs_to(n).iter().any(|s| s.from_entry.is_some()),
    }
}

/// Returns how a call to its called end is known.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slots` - The import slots ([`import_slots`]).
/// * `end` - The called end: a function entry, an import slot or, over
///   callers, a data address.
/// * `called` - Some site calls or jumps to `end`, rather than only
///   referencing it.
fn via_of(a: &Analysis, slots: &BTreeMap<u64, &str>, end: u64, called: bool) -> Via {
    match a.function(end) {
        Some(f) => match (f.thunk, f.bound) {
            (Some(slot), _) => Via::Thunk { slot },
            (None, Some(_)) => Via::Bound { stub: end },
            (None, None) => Via::Direct,
        },
        None if !called => Via::Data,
        None if slots.contains_key(&end) => Via::Import,
        None => Via::Direct,
    }
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
