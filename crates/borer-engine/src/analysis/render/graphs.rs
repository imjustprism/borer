//! Laid-out graphs: what every graph shares, and typed graphs past the
//! control-flow graph.
//!
//! Every graph shares its edges, what its caps left out, and the walk and
//! layout that draw it. The calls around a function and the references to
//! an address are typed values a front end draws and derives nothing from.

use super::*;

/// One edge of a laid-out graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Link<E> {
    /// The source node's index in the graph's nodes.
    pub from: usize,
    /// The target node's index in the graph's nodes.
    pub to: usize,
    /// What the edge is.
    pub kind: E,
    /// Whether the edge closes a cycle: the depth-first walk of
    /// [`back_edges`] found its target still on the walk's stack. It is
    /// drawn up the side.
    pub back: bool,
}

/// What a laid-out graph left out: some of its nodes, some of their
/// edges, or, in a control-flow graph, the rows of a block past
/// [`CFG_ROWS_MAX`] or past what [`CFG_LISTED_MAX`] leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cut {
    /// Nodes drawn.
    pub shown: usize,
    /// Nodes found, those drawn included: a function's blocks, or the
    /// nodes a walk reached.
    pub total: usize,
    /// Edges held among the drawn nodes.
    pub edges_shown: usize,
    /// Edges found, those held included.
    pub edges_total: usize,
    /// Drawn blocks cut short ([`Node::shortened`]); 0 in any other graph.
    pub shortened: usize,
}

impl Cut {
    /// Returns the cut when it left out anything.
    #[must_use]
    pub fn kept(self) -> Option<Self> {
        (self.shown < self.total || self.edges_shown < self.edges_total || self.shortened > 0)
            .then_some(self)
    }
}

/// Returns which edges close a cycle.
///
/// A depth-first walk from the root takes each node's edges out in their
/// given order, then walks again from each node it did not reach, in
/// node order; an edge to a node on the walk's stack is a back edge.
/// For a reducible graph, which compiled code almost always is, these are
/// exactly the edges whose target dominates their source; in an
/// irreducible one the walk's order picks which edge of a cycle is back.
/// Without the back edges the graph has no cycle. The walk keeps its own
/// stack, so it visits each node and edge once at any depth.
///
/// # Arguments
///
/// * `n` - The node count.
/// * `root` - The node the walk starts from.
/// * `edges` - Each edge's source and target node.
///
/// # Returns
///
/// Whether each edge is a back edge, by edge; an edge naming a node past
/// `n` is not.
fn back_edges(n: usize, root: usize, edges: &[(usize, usize)]) -> Vec<bool> {
    let mut order: Vec<usize> = (0..edges.len()).collect();
    order.sort_by_key(|&k| edges[k].0);
    let mut starts = vec![0usize; n.saturating_add(1)];
    for &(from, _) in edges {
        if let Some(s) = starts.get_mut(from.saturating_add(1)) {
            *s += 1;
        }
    }
    for i in 1..starts.len() {
        starts[i] += starts[i - 1];
    }
    let mut back = vec![false; edges.len()];
    let mut state = vec![Visit::New; n];
    let mut stack: Vec<(usize, usize)> = Vec::new();
    for r in std::iter::once(root).chain(0..n) {
        if state.get(r) != Some(&Visit::New) {
            continue;
        }
        state[r] = Visit::Open;
        stack.push((r, starts[r]));
        while let Some(top) = stack.last_mut() {
            let (v, k) = *top;
            if k >= starts[v + 1] {
                state[v] = Visit::Done;
                stack.pop();
                continue;
            }
            top.1 += 1;
            let Some(&e) = order.get(k) else { continue };
            let to = edges[e].1;
            match state.get(to) {
                Some(Visit::Open) => back[e] = true,
                Some(Visit::New) => {
                    state[to] = Visit::Open;
                    stack.push((to, starts[to]));
                }
                Some(Visit::Done) | None => {}
            }
        }
    }
    back
}

/// Where a node stands in the walk of [`back_edges`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Visit {
    /// Not reached yet.
    New,
    /// On the walk's stack.
    Open,
    /// Left, every successor walked.
    Done,
}

/// Marks a graph's back edges and lays it out top to bottom from its root
/// ([`layout()`]), each back edge up the side.
///
/// # Arguments
///
/// * `sizes` - Each node's box in text cells.
/// * `root` - The node on the top layer.
/// * `edges` - The edges; each `back` is set here.
pub(super) fn draw<E>(sizes: Vec<(u32, u32)>, root: usize, edges: &mut [Link<E>]) -> Drawing {
    let pairs: Vec<(usize, usize)> = edges.iter().map(|e| (e.from, e.to)).collect();
    let back = back_edges(sizes.len(), root, &pairs);
    for (e, &b) in edges.iter_mut().zip(&back) {
        e.back = b;
    }
    layout(&Graph {
        sizes,
        edges: pairs
            .iter()
            .zip(&back)
            .map(|(&(from, to), &b)| GraphEdge {
                from,
                to,
                route: if b { Route::Up } else { Route::Down },
            })
            .collect(),
        root,
    })
}

/// Most nodes a typed graph holds; a larger cap asked for is lowered to
/// this, and the nodes past it are counted ([`Cut`]).
pub const GRAPH_NODES_MAX: usize = 1024;

/// Most edges a typed graph holds. Every node keeps the edge the walk
/// reached it by; the other edges among the nodes are held while the list
/// has room for those, and the rest are counted ([`Cut`]).
pub const GRAPH_EDGES_MAX: usize = 4 * GRAPH_NODES_MAX;

/// Most levels a call or reference graph walks from its root; a larger
/// depth asked for is lowered to this.
pub const GRAPH_DEPTH_MAX: usize = REACH_DEPTH_MAX;

/// Rows of a node's box: its one line of text and a cell above and below.
const NODE_ROWS: u32 = 3;

/// A graph of typed nodes and edges, laid out with every edge pointing
/// down the drawing.
#[derive(Debug)]
pub struct TypedGraph<N, E> {
    /// The nodes, in address order.
    pub nodes: Vec<N>,
    /// The node the graph was asked about: in a graph of callees, at the
    /// top; of callers or references, at the bottom, what reaches it
    /// above.
    pub root: usize,
    /// The edges among the nodes, by source, then target, then kind; each
    /// points down the drawing.
    pub edges: Vec<Link<E>>,
    /// What the caps left out, when they left out anything.
    pub cut: Option<Cut>,
    /// The analysis ran out of instruction budget ([`Analysis::incomplete`]),
    /// so edges may be missing.
    pub incomplete: bool,
    /// What the graph says of the calls and jumps left unresolved that
    /// could add edges it lacks: none, how many, or why they were not
    /// counted ([`Unseen`]).
    pub unseen: Unseen,
    /// The drawing of the nodes and edges ([`TypedGraph::layout`]).
    drawing: Arc<Drawing>,
}

impl<N, E> TypedGraph<N, E> {
    /// Returns the graph laid out top to bottom.
    ///
    /// Each node is a box one row of text high and as wide as its name plus
    /// a cell on both sides, widened by the layout where it has more edges
    /// than columns ([`Drawing::sizes`]); each edge's index is its place in
    /// [`TypedGraph::edges`], and each route runs from the edge's `from` to
    /// its `to`, a back edge up the side. It is laid out once, with the
    /// graph.
    #[must_use]
    pub fn layout(&self) -> Arc<Drawing> {
        Arc::clone(&self.drawing)
    }

    /// Returns the heap bytes the node and edge lists and the drawing hold,
    /// without what each node or edge holds itself.
    fn shell_bytes(&self) -> usize {
        self.nodes.capacity() * size_of::<N>()
            + self.edges.capacity() * size_of::<Link<E>>()
            + self.drawing.bytes()
    }
}

/// What a node of a call or reference graph is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AddrKind {
    /// A function's entry.
    Function,
    /// An import's slot, which no function is the body of.
    Import,
    /// An address inside a function other than its entry, or one an
    /// executable section maps that no function holds.
    Code,
    /// An address only a section that is not executable maps: a global, or
    /// a pointer stored in data.
    Data,
    /// An address no section maps.
    Unmapped,
}

/// A node of a call or reference graph: an address and its name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AddrNode {
    /// The address.
    pub addr: u64,
    /// Its name as listings spell it: an import's name, else the
    /// overlay's, else the engine's, else its symbol's, else its address.
    pub name: Box<str>,
    /// What is there.
    pub kind: AddrKind,
    /// Whether the node has edges the graph does not hold: past the depth,
    /// the cap or [`GRAPH_EDGES_MAX`]. A node that is not open shows all
    /// its edges.
    pub open: bool,
}

/// An edge of a call or reference graph: how it is known and the
/// instructions making it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sites<K> {
    /// How the edge is known: a [`Via`] for a call, a [`RefKind`] for a
    /// reference.
    pub kind: K,
    /// The instructions making it, in address order, the first
    /// [`CALL_SITES_MAX`]; for a pointer stored in data, the word holding
    /// it. Empty for a call discovery knows without a site.
    pub sites: Vec<u64>,
    /// How many instructions make it, those `sites` holds included. The
    /// cross-reference index keeps at most 65,536 sites of one target, so
    /// past that it is a floor.
    pub site_count: usize,
}

/// One edge a walk found, before the graph's nodes are numbered.
struct Found<K> {
    /// The end the walk stood on.
    near: u64,
    /// The end the walk reached.
    far: u64,
    /// How the edge is known and its sites.
    kind: Sites<K>,
}

/// What a walk out from a root found, before the graph's nodes are
/// numbered.
struct Walked<K> {
    /// The node the walk started from.
    root: u64,
    /// The nodes held, the root among them.
    held: BTreeSet<u64>,
    /// The edges held: every edge a node was reached by, then the others
    /// among the held nodes while there is room ([`Walked::push`]).
    edges: Vec<Found<K>>,
    /// Nodes found past the depth or the cap.
    past: BTreeSet<u64>,
    /// Held nodes with an edge the graph does not hold.
    open: BTreeSet<u64>,
    /// Edges found, those held included.
    edges_total: usize,
    /// Most nodes held.
    cap: usize,
}

impl<K> Sites<K> {
    /// Returns an edge's kind with its first [`CALL_SITES_MAX`] sites and
    /// how many there are.
    ///
    /// # Arguments
    ///
    /// * `kind` - How the edge is known.
    /// * `all` - Every instruction making it, in address order.
    fn of(kind: K, all: &[u64]) -> Self {
        Self {
            kind,
            sites: all.iter().take(CALL_SITES_MAX).copied().collect(),
            site_count: all.len(),
        }
    }
}

impl<K> Walked<K> {
    /// Returns an empty walk from a root.
    ///
    /// # Arguments
    ///
    /// * `root` - The root, held.
    /// * `cap` - Most nodes to hold.
    fn new(root: u64, cap: usize) -> Self {
        Self {
            root,
            held: BTreeSet::from([root]),
            edges: Vec::new(),
            past: BTreeSet::new(),
            open: BTreeSet::new(),
            edges_total: 0,
            cap,
        }
    }

    /// Takes one edge the walk found from a held node.
    ///
    /// A far end not yet held is held when `grow` allows and the cap has
    /// room, and the edge is the one it was reached by ([`Walked::keep`]);
    /// else it is counted past the cap ([`Walked::miss`]).
    ///
    /// # Arguments
    ///
    /// * `near` - The held node the walk stands on.
    /// * `far` - The edge's other end.
    /// * `kind` - How the edge is known and its sites.
    /// * `grow` - Whether the walk may still add nodes.
    ///
    /// # Returns
    ///
    /// Whether `far` was added.
    fn push(&mut self, near: u64, far: u64, kind: Sites<K>, grow: bool) -> bool {
        let brought = !self.held.contains(&far);
        if brought && !(grow && self.held.len() < self.cap) {
            self.miss(near, far);
            return false;
        }
        self.held.insert(far);
        self.keep(near, far, kind);
        brought
    }

    /// Keeps an edge between held nodes.
    ///
    /// An edge is kept while the list leaves room for one edge per node
    /// still to come under the cap, so the list never passes
    /// [`GRAPH_EDGES_MAX`] and the edge each node is reached by, which
    /// comes with it, always fits; past that the edge is counted and both
    /// ends are open.
    ///
    /// # Arguments
    ///
    /// * `near` - The node the walk stands on.
    /// * `far` - The edge's other end.
    /// * `kind` - How the edge is known and its sites.
    fn keep(&mut self, near: u64, far: u64, kind: Sites<K>) {
        self.edges_total += 1;
        let room = self.cap.saturating_sub(self.held.len());
        if self.edges.len().saturating_add(room) >= GRAPH_EDGES_MAX {
            self.open.extend([near, far]);
            return;
        }
        self.edges.push(Found { near, far, kind });
    }

    /// Counts an edge to a node past the depth or the cap; its near end is
    /// open.
    ///
    /// # Arguments
    ///
    /// * `near` - The held node the walk stands on.
    /// * `far` - The node left out.
    fn miss(&mut self, near: u64, far: u64) {
        self.edges_total += 1;
        self.past.insert(far);
        self.open.insert(near);
    }
}

/// Returns what is at an address, as a call or reference graph names it.
///
/// # Arguments
///
/// * `p` - The loaded image, for its sections.
/// * `a` - The analysis.
/// * `imports` - The import slots among the nodes, with their names.
/// * `addr` - The address.
fn addr_kind(p: &Program, a: &Analysis, imports: &BTreeMap<u64, String>, addr: u64) -> AddrKind {
    let section = p.section_at(addr);
    if a.function(addr).is_some() {
        AddrKind::Function
    } else if imports.contains_key(&addr) {
        AddrKind::Import
    } else if a.function_at(addr).is_some() || section.is_some_and(|s| s.executable) {
        AddrKind::Code
    } else if section.is_some() {
        AddrKind::Data
    } else {
        AddrKind::Unmapped
    }
}

/// Returns a walk as a laid-out graph of addresses.
///
/// # Arguments
///
/// * `p` - The loaded image, for symbols and sections.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `imports` - The import slots among the nodes, with the names an
///   import node takes ([`CallWalk::imports`]).
/// * `w` - The walk.
/// * `walk` - Which way the walk went: over callers each edge points from
///   its far end to its near one, at the root, so the root is drawn at the
///   bottom.
/// * `unseen` - What the graph says of the calls it could not see.
fn places<K: Ord>(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    imports: &BTreeMap<u64, String>,
    w: Walked<K>,
    walk: Walk,
    unseen: Unseen,
) -> TypedGraph<AddrNode, Sites<K>> {
    let addrs: Vec<u64> = w.held.into_iter().collect();
    let nodes: Vec<AddrNode> = addrs
        .iter()
        .map(|&addr| AddrNode {
            addr,
            name: match imports.get(&addr).filter(|_| a.function(addr).is_none()) {
                Some(name) => name.as_str().into(),
                None => node_label(p, a, o, addr).into_boxed_str(),
            },
            kind: addr_kind(p, a, imports, addr),
            open: w.open.contains(&addr),
        })
        .collect();
    let index = |va: u64| addrs.binary_search(&va).ok();
    let mut edges: Vec<Link<Sites<K>>> = w
        .edges
        .into_iter()
        .filter_map(|e| {
            let (from, to) = match walk {
                Walk::Callers => (e.far, e.near),
                Walk::Callees => (e.near, e.far),
            };
            Some(Link {
                from: index(from)?,
                to: index(to)?,
                kind: e.kind,
                back: false,
            })
        })
        .collect();
    edges.sort_by(|x, y| (x.from, x.to, &x.kind).cmp(&(y.from, y.to, &y.kind)));
    let cut = Cut {
        shown: nodes.len(),
        total: nodes.len().saturating_add(w.past.len()),
        edges_shown: edges.len(),
        edges_total: w.edges_total,
        shortened: 0,
    };
    let root = index(w.root).unwrap_or(0);
    let sizes = nodes.iter().map(|n| name_box(&n.name)).collect();
    let drawing = match walk {
        Walk::Callers => draw_inward(sizes, root, &mut edges),
        Walk::Callees => draw(sizes, root, &mut edges),
    };
    TypedGraph {
        nodes,
        root,
        edges,
        cut: cut.kept(),
        incomplete: a.incomplete,
        unseen,
        drawing: Arc::new(drawing),
    }
}

/// Returns a node's box: its name's width and one row, each plus a cell on
/// both sides.
///
/// # Arguments
///
/// * `name` - The node's name.
fn name_box(name: &str) -> (u32, u32) {
    let width = name.chars().count().saturating_add(2);
    (u32::try_from(width).unwrap_or(u32::MAX), NODE_ROWS)
}

/// Lays a graph out with its root at the bottom: what points at the root
/// above it, every edge pointing down the drawing.
///
/// The edges are laid out turned round from the root ([`draw`]), then the
/// drawing is turned upside down: each node's row mirrored, each route
/// mirrored and run the other way, so it starts on its `from`'s bottom and
/// ends on its `to`'s top.
///
/// # Arguments
///
/// * `sizes` - Each node's box in text cells.
/// * `root` - The node on the bottom layer.
/// * `edges` - The edges, each pointing at the root's side; each `back`
///   is set here.
fn draw_inward<E>(sizes: Vec<(u32, u32)>, root: usize, edges: &mut [Link<E>]) -> Drawing {
    let turn = |edges: &mut [Link<E>]| {
        for e in edges {
            std::mem::swap(&mut e.from, &mut e.to);
        }
    };
    turn(edges);
    let mut d = draw(sizes, root, edges);
    turn(edges);
    let bottom = i64::from(d.size.1);
    let flip = |y: i64| i32::try_from(bottom - y).unwrap_or(i32::MAX);
    for (at, &(_, h)) in d.at.iter_mut().zip(&d.sizes) {
        at.1 = flip(i64::from(at.1) + i64::from(h));
    }
    for route in &mut d.routes {
        route.reverse();
        for point in route.iter_mut() {
            point.1 = flip(i64::from(point.1));
        }
    }
    d
}

/// Returns the heap bytes a graph of addresses holds.
///
/// # Arguments
///
/// * `g` - The graph.
fn addr_bytes<K>(g: &TypedGraph<AddrNode, Sites<K>>) -> usize {
    g.shell_bytes()
        + g.nodes.iter().map(|n| n.name.len()).sum::<usize>()
        + g.edges
            .iter()
            .map(|e| e.kind.sites.capacity() * size_of::<u64>())
            .sum::<usize>()
}

/// Returns the calls around a function as a typed graph: what it calls or
/// what calls it, each edge with how the call is known and where it is
/// made.
///
/// The walk is the mermaid graph's ([`callgraph`], [`call_walk`]): its
/// node budget spent in rounds of a few neighbours a node, a stub the
/// loader binds drawn as itself with a [`Via::Bound`] edge, an import as
/// its slot. Two things differ: the walk stops `depth` levels from the
/// root and, where the mermaid graph leaves the neighbours its second
/// round adds unexpanded, walks on from them while the depth and the cap
/// leave room; and the graph holds every call among its nodes up to
/// [`GRAPH_EDGES_MAX`]. The call tree ([`call_children`]) follows a bound
/// stub to its function instead. Edges point the way calls go: over
/// callers the root is at the bottom. Built once per root, walk, depth,
/// cap and names in force, and kept in the memo.
///
/// # Arguments
///
/// * `p` - The loaded image, for import and symbol names.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `root` - A function entry, an import slot or a data address.
/// * `walk` - Whether to walk what the root calls or what calls it.
/// * `depth` - Levels whose nodes draw their neighbours, from 1 to
///   [`GRAPH_DEPTH_MAX`]; the last level's calls among the nodes are held
///   too.
/// * `cap` - Most nodes, the root included, from 1 to
///   [`GRAPH_NODES_MAX`].
///
/// # Returns
///
/// The graph: its nodes by address, its edges by source and target, what
/// the caps left out, and what the analysis could not see.
#[must_use]
pub fn call_graph(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    root: u64,
    walk: Walk,
    depth: usize,
    cap: usize,
) -> Arc<TypedGraph<AddrNode, Sites<Via>>> {
    let depth = depth.clamp(1, GRAPH_DEPTH_MAX);
    let cap = cap.clamp(1, GRAPH_NODES_MAX);
    a.derived.get_or_build_item(
        "call graph",
        o.fingerprint(),
        (root, walk, depth, cap),
        || {
            let slots = import_slots(p);
            let budget = CallBudget {
                nodes: cap,
                depth,
                passes: usize::MAX,
            };
            let g = call_walk(p, a, root, walk, budget);
            let targets = |n: u64| g.reached.get(&n).map_or(&[][..], Vec::as_slice);
            let edge = |near: u64, c: &Callee| {
                let end = match walk {
                    Walk::Callees => c.target,
                    Walk::Callers => near,
                };
                Sites::of(via_of(a, &slots, end, c.called), &c.sites)
            };
            let mut w = Walked::new(root, g.nodes.len());
            w.held.extend(g.nodes.iter().copied());
            for (&far, &near) in &g.came_from {
                if let Some(c) = targets(near).iter().find(|c| c.target == far) {
                    w.keep(near, far, edge(near, c));
                }
            }
            for &near in &g.nodes {
                for c in targets(near) {
                    if g.came_from.get(&c.target) == Some(&near) {
                        continue;
                    }
                    if w.held.contains(&c.target) {
                        w.keep(near, c.target, edge(near, c));
                    } else {
                        w.miss(near, c.target);
                    }
                }
            }
            let drawn: BTreeSet<u64> = g.nodes.iter().copied().collect();
            let from_root = g.reached.get(&root).map_or(0, Vec::len);
            let unseen = unseen::graph_unseen(p, a, walk, from_root, &drawn);
            places(p, a, o, &g.imports, w, walk, unseen)
        },
        addr_bytes,
    )
}

/// Returns what references an address as a typed graph: the functions
/// referencing it, then what references them, a level at a time, each
/// edge with what its sites do.
///
/// A reference from no function, a pointer stored in data, comes from the
/// word holding it, a [`AddrKind::Data`] node. Every edge points at what
/// is referenced, so the target is drawn at the bottom; one function's
/// sites of one kind are one edge. Built once per address, depth, cap and
/// names in force, and kept in the memo.
///
/// # Arguments
///
/// * `p` - The loaded image, for import and symbol names.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `target` - The referenced address.
/// * `depth` - Levels whose nodes add what references them, from 1 to
///   [`GRAPH_DEPTH_MAX`]; the last level's references among the nodes are
///   held too.
/// * `cap` - Most nodes, the target included, from 1 to
///   [`GRAPH_NODES_MAX`].
///
/// # Returns
///
/// The graph: its nodes by address, its edges by source and target, what
/// the caps left out, and what the analysis could not see.
#[must_use]
pub fn xref_graph(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    target: u64,
    depth: usize,
    cap: usize,
) -> Arc<TypedGraph<AddrNode, Sites<RefKind>>> {
    let depth = depth.clamp(1, GRAPH_DEPTH_MAX);
    let cap = cap.clamp(1, GRAPH_NODES_MAX);
    a.derived.get_or_build_item(
        "xref graph",
        o.fingerprint(),
        (target, depth, cap),
        || {
            let slots = import_slots(p);
            let mut w = Walked::new(target, cap);
            let mut frontier = vec![target];
            for level in 0..=depth {
                let mut added = Vec::new();
                for near in frontier {
                    for (far, kind) in referrers(a, near) {
                        if w.push(near, far, kind, level < depth) {
                            added.push(far);
                        }
                    }
                }
                frontier = added;
            }
            let imports: BTreeMap<u64, String> = w
                .held
                .iter()
                .filter_map(|&n| Some((n, graph_name(slots.get(&n)?))))
                .collect();
            let unseen = unseen::xref_unseen(p, a, target, a.xrefs_to(target));
            places(p, a, o, &imports, w, Walk::Callers, unseen)
        },
        addr_bytes,
    )
}

/// Returns what references an address: one entry per referencing function
/// and kind of reference, a pointer in data standing as the word holding
/// it.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `at` - The referenced address.
///
/// # Returns
///
/// Each referrer with its kind and sites ([`Sites::of`]), by referrer and
/// kind.
fn referrers(a: &Analysis, at: u64) -> Vec<(u64, Sites<RefKind>)> {
    let mut by: BTreeMap<(u64, RefKind), Vec<u64>> = BTreeMap::new();
    for s in a.xrefs_to(at) {
        by.entry((s.from_entry.unwrap_or(s.va), s.kind))
            .or_default()
            .push(s.va);
    }
    by.into_iter()
        .map(|((from, kind), mut sites)| {
            sites.sort_unstable();
            sites.dedup();
            (from, Sites::of(kind, &sites))
        })
        .collect()
}
