//! Layered drawings of directed graphs on a grid of text cells.
//!
//! [`layout`] draws a graph top to bottom as Sugiyama, Tagawa and Toda
//! (1981) do: nodes on layers, long edges split at every layer they cross,
//! the order within each layer swept to fewer crossings, then each node
//! placed by the four alignments of Brandes and Kopf (2001), balanced. All
//! of it is integer arithmetic over text cells, so a graph draws to the same
//! coordinates on every host, and every step is linear or a sort in the
//! nodes and edges it is given, a fixed number of times.

use std::collections::BTreeSet;

/// Rounds of crossing reduction, each a sweep down the layers and one up.
pub const LAYOUT_ROUNDS: usize = 4;

/// Nodes [`layout`] may add per node of the graph where long edges cross
/// layers; an edge past the budget is routed down the side, as a back
/// edge is routed up it, and counted ([`Drawing::sided`]).
pub const LAYOUT_DUMMIES_PER_NODE: usize = 64;

/// Columns between two nodes side by side on a layer.
const GAP_X: i64 = 2;

/// A directed graph to lay out.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Graph {
    /// Each node's width and height, in text cells.
    pub sizes: Vec<(u32, u32)>,
    /// The edges. Without those routed up the graph should have no cycle;
    /// an edge that still points up is routed up the side too.
    pub edges: Vec<GraphEdge>,
    /// The node on the top layer, which the layers count from.
    pub root: usize,
}

/// One edge of a [`Graph`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphEdge {
    /// The source node.
    pub from: usize,
    /// The target node.
    pub to: usize,
    /// Which way the edge is laid out.
    pub route: Route,
}

/// Which way a [`GraphEdge`] is laid out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// Down the layers: the target is laid out below the source.
    Down,
    /// Up the side: a back edge, closing a cycle, left out of the layers.
    Up,
}

/// How [`layout`] routed an edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Routed {
    /// Down through the layers, split at each layer it crosses.
    Layered,
    /// Out to a column of its own right of every node, then in from the
    /// side: a back edge, a self loop, an edge that points up, or a long
    /// edge past the budget.
    Side,
    /// Not at all: the edge names a node the graph does not have.
    Missing,
}

/// Where [`layout`] put each node and edge.
///
/// Coordinates are grid lines between text cells, from the top left: a
/// node at `(x, y)` of size `(w, h)` spans the lines `x..=x + w` and
/// `y..=y + h`, so its top edge is the line `y` and its bottom edge the
/// line `y + h`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Drawing {
    /// Each node's top-left corner, by node.
    pub at: Vec<(i32, i32)>,
    /// Each node's box as drawn, by node: its size, widened where it is
    /// narrower than twice a column more than it has edges out or in, so
    /// each edge has a port column of its own on the node's layer's parity.
    pub sizes: Vec<(u32, u32)>,
    /// Each edge's path, by edge: corner points of horizontal and vertical
    /// runs from a port on its source's bottom edge to one on its target's
    /// top edge, never through a node, no horizontal run sharing a line
    /// with another edge's where they overlap. Every column a route turns
    /// down at on layer `l`, a port or an added node, is even when `l` is
    /// and odd when it is odd, so in the gap between two layers no route
    /// leaves down a column another comes in at, and no two routes share
    /// a vertical run. Empty for a missing edge.
    pub routes: Vec<Vec<(i32, i32)>>,
    /// How each edge was routed, by edge.
    pub routed: Vec<Routed>,
    /// The drawing's last grid lines across and down: every node and
    /// route point lies between the lines 0 and these.
    pub size: (u32, u32),
    /// Crossings between layers before the reduction, in input order.
    pub crossings_before: usize,
    /// Crossings between layers after it, never more than before: of the
    /// layered edges, as their runs cross between adjacent layers.
    pub crossings: usize,
    /// Long edges routed on the side because they would have taken more
    /// than [`LAYOUT_DUMMIES_PER_NODE`] added nodes per node.
    pub sided: usize,
}

impl Drawing {
    /// Returns the heap bytes the drawing holds.
    #[must_use]
    pub fn bytes(&self) -> usize {
        size_of_val(&*self.at)
            + size_of_val(&*self.routes)
            + size_of_val(&*self.routed)
            + self.routes.iter().map(|r| size_of_val(&**r)).sum::<usize>()
    }
}

/// The graph on layers, long edges split.
#[derive(Debug)]
struct Ranked {
    /// Each node's layer: the graph's nodes, then the added ones.
    layer: Vec<usize>,
    /// Each node's width in cells; an added node is one wide.
    width: Vec<i64>,
    /// Each node's neighbours on the layer above.
    up: Vec<Vec<usize>>,
    /// Each node's neighbours on the layer below.
    down: Vec<Vec<usize>>,
    /// Each edge's nodes from source to target, one a layer, or `None` for
    /// an edge routed on the side or naming no node.
    chains: Vec<Option<Vec<usize>>>,
    /// The layer count.
    layers: usize,
    /// Long edges left on the side past the budget.
    sided: usize,
}

/// Returns an `i64` coordinate as an `i32`, saturating.
///
/// # Arguments
///
/// * `x` - The coordinate.
fn narrow(x: i64) -> i32 {
    i32::try_from(x).unwrap_or(if x < 0 { i32::MIN } else { i32::MAX })
}

/// Lays a graph out on layers, top to bottom.
///
/// 1. Layers: the longest path from the root over the edges routed down;
///    the nodes the root does not reach go below, the longest path among
///    them from the first layer under the rest.
/// 2. An edge crossing layers gets one added node on each layer between,
///    up to [`LAYOUT_DUMMIES_PER_NODE`] per node of the graph.
/// 3. Crossings: [`LAYOUT_ROUNDS`] rounds of barycenter sweeps down and up,
///    ties in input order, keeping the order with the fewest.
/// 4. Columns: Brandes and Kopf's four alignments, each block packed left
///    by the longest path over its neighbours, then balanced, the
///    narrowest of the four standing in when the balance would make two
///    nodes touch.
/// 5. Routes: down from a port on the source's bottom, ports ordered by
///    where their edges go, into the gap under its layer, across on a line
///    of the gap of its own, stacked so two routes cross only where they
///    swap order, down through the added nodes,
///    across and into the target's top; an edge routed on the side goes
///    out to a column of its own right of every node and comes in across
///    the gap above the target's layer.
///
/// Its cost is a sort per layer per sweep over the nodes and added nodes,
/// so callers cap the nodes they pass.
///
/// # Arguments
///
/// * `g` - The graph; a root it does not have counts as its first node.
///
/// # Returns
///
/// The drawing; empty for a graph of no nodes.
#[must_use]
pub fn layout(g: &Graph) -> Drawing {
    let n = g.sizes.len();
    if n == 0 {
        return Drawing {
            routes: vec![Vec::new(); g.edges.len()],
            routed: vec![Routed::Missing; g.edges.len()],
            ..Drawing::default()
        };
    }
    let root = if g.root < n { g.root } else { 0 };
    let r = rank(g, layers(g, root));
    let (rows, before, after) = order(&r);
    let mut out = place(g, &r, &rows, &coordinates(&rows, &r, n));
    out.crossings_before = before;
    out.crossings = after;
    out.sided = r.sided;
    out
}

/// Returns each node's layer.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `root` - The node on the top layer, one the graph has.
fn layers(g: &Graph, root: usize) -> Vec<usize> {
    let n = g.sizes.len();
    let mut fwd = vec![Vec::new(); n];
    for e in &g.edges {
        if e.route == Route::Down && e.from != e.to && e.from < n && e.to < n {
            fwd[e.from].push(e.to);
        }
    }
    let mut reached = vec![false; n];
    reached[root] = true;
    let mut todo = vec![root];
    while let Some(u) = todo.pop() {
        for &v in &fwd[u] {
            if !reached[v] {
                reached[v] = true;
                todo.push(v);
            }
        }
    }
    let mut layer: Vec<Option<usize>> = vec![None; n];
    longest_paths(&fwd, &reached, 0, &mut layer);
    let rest: Vec<bool> = layer.iter().map(Option::is_none).collect();
    longest_paths(&fwd, &rest, below(&layer), &mut layer);
    let mut next = below(&layer);
    layer
        .into_iter()
        .map(|l| {
            l.unwrap_or_else(|| {
                next += 1;
                next - 1
            })
        })
        .collect()
}

/// Returns the first layer under every node given one.
///
/// # Arguments
///
/// * `layer` - Each node's layer, if given.
fn below(layer: &[Option<usize>]) -> usize {
    layer.iter().flatten().max().map_or(0, |&m| m + 1)
}

/// Gives the members their longest-path layers from `base`, by Kahn's
/// order over the edges among them.
///
/// A member on a cycle of those edges, possible only when the caller's
/// edges routed up miss one, keeps no layer or the one a member before it
/// gave.
///
/// # Arguments
///
/// * `fwd` - Each node's targets over the edges routed down.
/// * `member` - Which nodes to give layers.
/// * `base` - The layer of a member no other member points to.
/// * `layer` - Each node's layer, set for the members.
fn longest_paths(fwd: &[Vec<usize>], member: &[bool], base: usize, layer: &mut [Option<usize>]) {
    let mut ins = vec![0usize; fwd.len()];
    for (u, outs) in fwd.iter().enumerate() {
        if member[u] {
            for &v in outs.iter().filter(|&&v| member[v]) {
                ins[v] += 1;
            }
        }
    }
    let mut ready: Vec<usize> = (0..fwd.len())
        .filter(|&v| member[v] && ins[v] == 0)
        .collect();
    for &v in &ready {
        layer[v] = Some(base);
    }
    while let Some(u) = ready.pop() {
        let next = layer[u].map_or(base, |l| l + 1);
        for &v in fwd[u].iter().filter(|&&v| member[v]) {
            layer[v] = layer[v].max(Some(next));
            ins[v] -= 1;
            if ins[v] == 0 {
                ready.push(v);
            }
        }
    }
}

/// Splits the edges that cross layers at every layer between.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `layer` - Each node's layer.
fn rank(g: &Graph, layer: Vec<usize>) -> Ranked {
    let n = g.sizes.len();
    let layers = layer.iter().max().map_or(0, |&m| m + 1);
    let mut degree = vec![(0i64, 0i64); n];
    for e in g.edges.iter().filter(|e| e.from < n && e.to < n) {
        degree[e.from].0 += 1;
        degree[e.to].1 += 1;
    }
    let mut r = Ranked {
        layer,
        width: g
            .sizes
            .iter()
            .zip(&degree)
            .map(|(&(w, _), &(o, i))| i64::from(w).max(2 * (o.max(i) + 1)))
            .collect(),
        up: vec![Vec::new(); n],
        down: vec![Vec::new(); n],
        chains: Vec::with_capacity(g.edges.len()),
        layers,
        sided: 0,
    };
    let mut budget = LAYOUT_DUMMIES_PER_NODE.saturating_mul(n);
    for e in &g.edges {
        let (u, v) = (e.from, e.to);
        let spans = (u < n && v < n && e.route == Route::Down)
            .then(|| (r.layer[u], r.layer[v]))
            .filter(|&(lu, lv)| lv > lu);
        let Some((lu, lv)) = spans else {
            r.chains.push(None);
            continue;
        };
        if lv - lu - 1 > budget {
            r.sided += 1;
            r.chains.push(None);
            continue;
        }
        budget -= lv - lu - 1;
        let mut path = vec![u];
        for l in lu + 1..lv {
            path.push(r.layer.len());
            r.layer.push(l);
            r.width.push(1);
            r.up.push(Vec::new());
            r.down.push(Vec::new());
        }
        path.push(v);
        for w in path.windows(2) {
            r.down[w[0]].push(w[1]);
            r.up[w[1]].push(w[0]);
        }
        r.chains.push(Some(path));
    }
    r
}

/// Returns each node's place on its layer.
///
/// # Arguments
///
/// * `order` - Each layer's nodes, left to right.
/// * `total` - The node count.
fn positions(order: &[Vec<usize>], total: usize) -> Vec<usize> {
    let mut pos = vec![0; total];
    for layer in order {
        for (i, &v) in layer.iter().enumerate() {
            pos[v] = i;
        }
    }
    pos
}

/// Orders each layer to fewer crossings.
///
/// # Arguments
///
/// * `r` - The graph on layers.
///
/// # Returns
///
/// Each layer's nodes left to right, the crossings of the input order
/// (nodes, then added nodes, each by number) and of the order returned:
/// the order with the fewest of every round's, the input's included.
fn order(r: &Ranked) -> (Vec<Vec<usize>>, usize, usize) {
    let mut order = vec![Vec::new(); r.layers];
    for (v, &l) in r.layer.iter().enumerate() {
        order[l].push(v);
    }
    let mut pos = positions(&order, r.layer.len());
    let before = crossings(&order, &pos, &r.down);
    let (mut best, mut fewest) = (order.clone(), before);
    for _ in 0..LAYOUT_ROUNDS {
        for layer in order.iter_mut().skip(1) {
            sweep(layer, &mut pos, &r.up);
        }
        for layer in order.iter_mut().rev().skip(1) {
            sweep(layer, &mut pos, &r.down);
        }
        let c = crossings(&order, &pos, &r.down);
        if c < fewest {
            fewest = c;
            best.clone_from(&order);
        }
    }
    (best, before, fewest)
}

/// Sorts one layer by the mean place of each node's neighbours on the
/// layer swept from, ties by node number; a node with none keeps its own
/// place as its mean.
///
/// # Arguments
///
/// * `layer` - The layer's nodes, reordered.
/// * `pos` - Each node's place, updated for this layer.
/// * `nbrs` - Each node's neighbours on the layer swept from.
fn sweep(layer: &mut [usize], pos: &mut [usize], nbrs: &[Vec<usize>]) {
    let num = |v: usize| u128::from(crate::num::from_usize(v));
    let mut keyed: Vec<(u128, u128, usize)> = layer
        .iter()
        .map(|&v| match nbrs[v].as_slice() {
            [] => (num(pos[v]), 1, v),
            ns => (ns.iter().map(|&u| num(pos[u])).sum(), num(ns.len()), v),
        })
        .collect();
    keyed.sort_by(|a, b| (a.0 * b.1).cmp(&(b.0 * a.1)).then(a.2.cmp(&b.2)));
    for (i, (slot, &(_, _, v))) in layer.iter_mut().zip(&keyed).enumerate() {
        *slot = v;
        pos[v] = i;
    }
}

/// Counts the pairs of edges that cross between adjacent layers.
///
/// Per pair of layers the edges sorted by upper place are an inversion
/// count over their lower places, kept in a Fenwick tree.
///
/// # Arguments
///
/// * `order` - Each layer's nodes, left to right.
/// * `pos` - Each node's place on its layer.
/// * `down` - Each node's neighbours on the layer below.
fn crossings(order: &[Vec<usize>], pos: &[usize], down: &[Vec<usize>]) -> usize {
    let mut total = 0usize;
    let mut pairs = Vec::new();
    for (l, layer) in order.iter().enumerate() {
        let Some(lower) = order.get(l + 1) else { break };
        pairs.clear();
        pairs.extend(
            layer
                .iter()
                .flat_map(|&u| down[u].iter().map(move |&v| (pos[u], pos[v]))),
        );
        pairs.sort_unstable();
        let mut tree = vec![0usize; lower.len() + 1];
        for (seen, &(_, b)) in pairs.iter().enumerate() {
            let (mut i, mut at_most) = (b + 1, 0);
            while i > 0 {
                at_most += tree[i];
                i &= i - 1;
            }
            total = total.saturating_add(seen - at_most);
            let mut i = b + 1;
            while i < tree.len() {
                tree[i] += 1;
                i += i & i.wrapping_neg();
            }
        }
    }
    total
}

/// Returns the edges between layers that cross an edge between two added
/// nodes, both ways round: Brandes and Kopf's type 1 conflicts, which no
/// alignment may use, so a long edge stays straight.
///
/// # Arguments
///
/// * `order` - Each layer's nodes, left to right.
/// * `pos` - Each node's place on its layer.
/// * `r` - The graph on layers.
/// * `n` - The graph's own node count; nodes from here on were added.
fn conflicts(
    order: &[Vec<usize>],
    pos: &[usize],
    r: &Ranked,
    n: usize,
) -> BTreeSet<(usize, usize)> {
    let mut marked = BTreeSet::new();
    for pair in order.windows(2) {
        let (upper, lower) = (&pair[0], &pair[1]);
        let (mut k0, mut scan) = (0usize, 0usize);
        for (l1, &v) in lower.iter().enumerate() {
            let inner = if v >= n {
                r.up[v].iter().find(|&&u| u >= n).map(|&u| pos[u])
            } else {
                None
            };
            if l1 + 1 != lower.len() && inner.is_none() {
                continue;
            }
            let k1 = inner.unwrap_or(upper.len().saturating_sub(1));
            for &w in &lower[scan..=l1] {
                for &u in &r.up[w] {
                    if (u < n || w < n) && (pos[u] < k0 || pos[u] > k1) {
                        marked.insert((u, w));
                        marked.insert((w, u));
                    }
                }
            }
            scan = l1 + 1;
            k0 = k1;
        }
    }
    marked
}

/// Aligns each node with a median neighbour on the layer before it, as
/// Brandes and Kopf's vertical alignment does, left to right.
///
/// # Arguments
///
/// * `lay` - Each layer's nodes, in the order the alignment walks them.
/// * `prev` - Each node's neighbours on the layer walked before its own.
/// * `pos` - Each node's place in `lay`.
/// * `marked` - The conflicts no alignment may use.
///
/// # Returns
///
/// Each node's block, by the block's first node.
fn align(
    lay: &[Vec<usize>],
    prev: &[Vec<usize>],
    pos: &[usize],
    marked: &BTreeSet<(usize, usize)>,
) -> Vec<usize> {
    let mut root: Vec<usize> = (0..pos.len()).collect();
    let mut align = root.clone();
    let mut nb = Vec::new();
    for layer in lay.iter().skip(1) {
        let mut taken: Option<usize> = None;
        for &v in layer {
            nb.clear();
            nb.extend(prev[v].iter().copied());
            nb.sort_unstable_by_key(|&u| pos[u]);
            nb.dedup();
            let Some(last) = nb.len().checked_sub(1) else {
                continue;
            };
            for m in [last / 2, last.div_ceil(2)] {
                let u = nb[m];
                if align[v] == v && !marked.contains(&(u, v)) && taken.is_none_or(|t| t < pos[u]) {
                    align[u] = v;
                    root[v] = root[u];
                    align[v] = root[v];
                    taken = Some(pos[u]);
                }
            }
        }
    }
    root
}

/// Packs blocks left: each block's center the least that keeps every node
/// clear of its left neighbour, by the longest path over the blocks.
///
/// # Arguments
///
/// * `lay` - Each layer's nodes, left to right as packed.
/// * `root` - Each node's block.
/// * `width` - Each node's width.
///
/// # Returns
///
/// Each node's center in half cells, or `None` when the blocks' order is
/// cyclic, which the alignment rules out.
fn compact(lay: &[Vec<usize>], root: &[usize], width: &[i64]) -> Option<Vec<i64>> {
    let total = root.len();
    let mut next: Vec<Vec<(usize, i64)>> = vec![Vec::new(); total];
    let mut ins = vec![0usize; total];
    for layer in lay {
        for w in layer.windows(2) {
            let (a, b) = (w[0], w[1]);
            if root[a] == root[b] {
                return None;
            }
            next[root[a]].push((root[b], width[a] + width[b] + 2 * GAP_X));
            ins[root[b]] += 1;
        }
    }
    let mut x = vec![0i64; total];
    let mut ready: Vec<usize> = (0..total)
        .filter(|&v| root[v] == v && ins[v] == 0)
        .collect();
    let mut done = 0;
    while let Some(b) = ready.pop() {
        done += 1;
        for &(c, sep) in &next[b] {
            x[c] = x[c].max(x[b] + sep);
            ins[c] -= 1;
            if ins[c] == 0 {
                ready.push(c);
            }
        }
    }
    let blocks = (0..total).filter(|&v| root[v] == v).count();
    (done == blocks).then(|| root.iter().map(|&b| x[b]).collect())
}

/// Returns each node's center in quarter cells: the balance of the four
/// alignments, or the narrowest of them doubled.
///
/// # Arguments
///
/// * `order` - Each layer's nodes, left to right.
/// * `r` - The graph on layers.
/// * `n` - The graph's own node count.
fn coordinates(order: &[Vec<usize>], r: &Ranked, n: usize) -> Vec<i64> {
    let total = r.layer.len();
    let marked = conflicts(order, &positions(order, total), r, n);
    let alone: Vec<usize> = (0..total).collect();
    let mut runs: Vec<Vec<i64>> = Vec::with_capacity(4);
    for (upward, mirror) in [(false, false), (false, true), (true, false), (true, true)] {
        let mut lay = order.to_vec();
        if mirror {
            lay.iter_mut().for_each(|l| l.reverse());
        }
        let pos = positions(&lay, total);
        if upward {
            lay.reverse();
        }
        let prev = if upward { &r.down } else { &r.up };
        let root = align(&lay, prev, &pos, &marked);
        let x = compact(&lay, &root, &r.width)
            .or_else(|| compact(&lay, &alone, &r.width))
            .unwrap_or_else(|| vec![0; total]);
        runs.push(if mirror {
            x.into_iter().map(|v| -v).collect()
        } else {
            x
        });
    }
    balance(order, &runs, &r.width)
}

/// Balances four alignments: each node at the mean of its two median
/// centers once the four are lined up with the narrowest, left-packed ones
/// by their left edge and right-packed ones by their right.
///
/// # Arguments
///
/// * `order` - Each layer's nodes, left to right.
/// * `runs` - Each alignment's centers in half cells, left-packed first.
/// * `width` - Each node's width.
///
/// # Returns
///
/// Each node's center in quarter cells.
fn balance(order: &[Vec<usize>], runs: &[Vec<i64>], width: &[i64]) -> Vec<i64> {
    let extent = |x: &[i64]| {
        x.iter()
            .zip(width)
            .fold((i64::MAX, i64::MIN), |(lo, hi), (&c, &w)| {
                (lo.min(c - w), hi.max(c + w))
            })
    };
    let spans: Vec<(i64, i64)> = runs.iter().map(|x| extent(x)).collect();
    let Some((narrowest, &(lo, hi))) = spans
        .iter()
        .enumerate()
        .min_by_key(|&(k, &(l, h))| (h - l, k))
    else {
        return Vec::new();
    };
    let shifts: Vec<i64> = spans
        .iter()
        .enumerate()
        .map(|(k, &(l, h))| if k % 2 == 0 { lo - l } else { hi - h })
        .collect();
    let c4: Vec<i64> = (0..width.len())
        .map(|v| {
            let mut at = [0i64; 4];
            for (k, (x, s)) in runs.iter().zip(&shifts).enumerate() {
                at[k] = x[v] + s;
            }
            at.sort_unstable();
            at[1] + at[2]
        })
        .collect();
    let clear = order.iter().all(|layer| {
        layer
            .windows(2)
            .all(|p| c4[p[1]] - c4[p[0]] >= 2 * (width[p[0]] + width[p[1]] + 2 * GAP_X))
    });
    if clear {
        c4
    } else {
        runs[narrowest].iter().map(|&x| 2 * x).collect()
    }
}

/// The columns each edge's route turns at and its horizontal runs.
type Columns = (Vec<Vec<i64>>, Vec<Run>, Vec<usize>);

/// Returns each edge's columns, from its source port through its added
/// nodes (or its side column) to its target port, and its horizontal runs
/// in order.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `r` - The graph on layers.
/// * `left` - Each node's left column.
/// * `ports` - Each edge's port columns.
///
/// # Returns
///
/// Each edge's columns (empty for a missing edge), every run, and the
/// index of each edge's first run.
fn columns(g: &Graph, r: &Ranked, left: &[i64], ports: &[(i64, i64)]) -> Columns {
    let n = g.sizes.len();
    let mut lane = left
        .iter()
        .zip(&r.width)
        .map(|(&x, &w)| x + w)
        .max()
        .unwrap_or(0)
        + GAP_X;
    let mut columns: Vec<Vec<i64>> = Vec::with_capacity(g.edges.len());
    let mut runs: Vec<Run> = Vec::new();
    let mut first_run = Vec::with_capacity(g.edges.len());
    for ((e, chain), &(sx, tx)) in g.edges.iter().zip(&r.chains).zip(ports) {
        first_run.push(runs.len());
        let mut xs = Vec::new();
        if e.from < n && e.to < n {
            let (lu, lv) = (r.layer[e.from], r.layer[e.to]);
            match chain {
                Some(path) => {
                    xs.push(sx);
                    xs.extend(
                        path[1..path.len() - 1]
                            .iter()
                            .map(|&w| on_parity(left[w], r.layer[w])),
                    );
                    xs.push(tx);
                    for (k, x) in xs.windows(2).enumerate() {
                        runs.push(Run::between(lu + 1 + k, x[0], x[1]));
                    }
                }
                None => {
                    xs.extend([sx, lane, tx]);
                    runs.push(Run::between(lu + 1, sx, lane));
                    runs.push(Run::between(lv, lane, tx));
                    lane += 1;
                }
            }
        }
        columns.push(xs);
    }
    (columns, runs, first_run)
}

/// One horizontal run of a route, before its line is known.
#[derive(Debug, Clone, Copy)]
struct Run {
    /// The gap it lies in: gap `l` is the one above layer `l`.
    gap: usize,
    /// Its left column.
    lo: i64,
    /// Its right column.
    hi: i64,
    /// Which way the route goes along it.
    way: Way,
}

/// Which way a route goes along a [`Run`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Way {
    /// From its left column to its right.
    Right,
    /// From its right column to its left.
    Left,
    /// Nowhere: the route goes straight down.
    Still,
}

impl Run {
    /// Returns the run of a route coming down at `from` and leaving down
    /// at `to`.
    ///
    /// # Arguments
    ///
    /// * `gap` - The gap it lies in.
    /// * `from` - The column it comes in at.
    /// * `to` - The column it leaves at.
    fn between(gap: usize, from: i64, to: i64) -> Self {
        let way = match from.cmp(&to) {
            std::cmp::Ordering::Less => Way::Right,
            std::cmp::Ordering::Greater => Way::Left,
            std::cmp::Ordering::Equal => Way::Still,
        };
        Self {
            gap,
            lo: from.min(to),
            hi: from.max(to),
            way,
        }
    }
}

/// Places the nodes on the grid and routes the edges.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `r` - The graph on layers.
/// * `rows` - Each layer's nodes, left to right.
/// * `c4` - Each node's center in quarter cells.
fn place(g: &Graph, r: &Ranked, rows: &[Vec<usize>], c4: &[i64]) -> Drawing {
    let n = g.sizes.len();
    let raw: Vec<i64> = c4
        .iter()
        .zip(&r.width)
        .map(|(&c, &w)| (c - 2 * w).div_euclid(4))
        .collect();
    let shift = raw.iter().min().copied().unwrap_or(0);
    let left: Vec<i64> = raw.iter().map(|&x| x - shift).collect();
    let ports = ports(g, r, &positions(rows, r.layer.len()), &left);
    let (columns, runs, first_run) = columns(g, r, &left, &ports);
    let (track, tracks) = tracks(&runs, r.layers + 1);
    let mut height = vec![0i64; r.layers];
    for (v, &(_, h)) in g.sizes.iter().enumerate() {
        height[r.layer[v]] = height[r.layer[v]].max(i64::from(h));
    }
    let mut base = vec![-1i64; r.layers + 1];
    let mut top = vec![0i64; r.layers];
    for l in 0..r.layers {
        top[l] = base[l] + 2 + tracks[l];
        base[l + 1] = top[l] + height[l];
    }
    let row = |k: usize| base[runs[k].gap] + 1 + track[k];
    let mut routes = Vec::with_capacity(g.edges.len());
    let mut routed = Vec::with_capacity(g.edges.len());
    for (i, (e, xs)) in g.edges.iter().zip(&columns).enumerate() {
        let (Some(&sx), Some(&tx)) = (xs.first(), xs.last()) else {
            routes.push(Vec::new());
            routed.push(Routed::Missing);
            continue;
        };
        let mut pts = vec![(sx, top[r.layer[e.from]] + i64::from(g.sizes[e.from].1))];
        if r.chains[i].is_some() {
            for (k, x) in xs.windows(2).enumerate() {
                let y = row(first_run[i] + k);
                pts.extend([(x[0], y), (x[1], y)]);
            }
            routed.push(Routed::Layered);
        } else {
            let (out, back) = (row(first_run[i]), row(first_run[i] + 1));
            pts.extend([(sx, out), (xs[1], out), (xs[1], back), (tx, back)]);
            routed.push(Routed::Side);
        }
        pts.push((tx, top[r.layer[e.to]]));
        pts.dedup();
        routes.push(pts);
    }
    let at: Vec<(i64, i64)> = (0..n).map(|v| (left[v], top[r.layer[v]])).collect();
    let sizes = g
        .sizes
        .iter()
        .zip(&r.width)
        .map(|(&(_, h), &w)| (u32::try_from(w).unwrap_or(u32::MAX), h))
        .collect();
    finish(at, sizes, routes, routed)
}

/// Returns the drawing of placed nodes and routes, sized to hold them.
///
/// # Arguments
///
/// * `at` - Each node's top-left corner.
/// * `sizes` - Each node's box as drawn.
/// * `routes` - Each edge's points.
/// * `routed` - How each edge was routed.
fn finish(
    at: Vec<(i64, i64)>,
    sizes: Vec<(u32, u32)>,
    routes: Vec<Vec<(i64, i64)>>,
    routed: Vec<Routed>,
) -> Drawing {
    let mut size = (0i64, 0i64);
    for (&(x, y), &(w, h)) in at.iter().zip(&sizes) {
        size = (size.0.max(x + i64::from(w)), size.1.max(y + i64::from(h)));
    }
    for &(x, y) in routes.iter().flatten() {
        size = (size.0.max(x), size.1.max(y));
    }
    Drawing {
        at: at
            .into_iter()
            .map(|(x, y)| (narrow(x), narrow(y)))
            .collect(),
        sizes,
        routes: routes
            .into_iter()
            .map(|r| r.into_iter().map(|(x, y)| (narrow(x), narrow(y))).collect())
            .collect(),
        routed,
        size: (
            u32::try_from(size.0).unwrap_or(u32::MAX),
            u32::try_from(size.1).unwrap_or(u32::MAX),
        ),
        crossings_before: 0,
        crossings: 0,
        sided: 0,
    }
}

/// Gives each horizontal run a line of its gap.
///
/// The runs going right on the first lines, each below every run it overlaps that comes in further
/// right, then the runs going left, each below every run it overlaps that
/// comes in further left. Two runs then cross only where their routes
/// swap order across the gap, once: the columns runs come in at and those
/// they leave at differ in parity ([`on_parity`]), so no two meet at an
/// end.
///
/// # Arguments
///
/// * `runs` - The runs.
/// * `gaps` - The gap count.
///
/// # Returns
///
/// Each run's line within its gap, from 0, and each gap's line count.
fn tracks(runs: &[Run], gaps: usize) -> (Vec<i64>, Vec<i64>) {
    let mut by_gap: Vec<Vec<usize>> = vec![Vec::new(); gaps];
    for (k, run) in runs.iter().enumerate() {
        by_gap[run.gap].push(k);
    }
    let mut track = vec![0i64; runs.len()];
    let mut count = vec![0i64; gaps];
    for (ids, used) in by_gap.iter().zip(&mut count) {
        let mut base = 0;
        for way in [Way::Right, Way::Left] {
            let mut items: Vec<(i64, i64, usize)> = ids
                .iter()
                .filter(|&&k| runs[k].way == way)
                .map(|&k| match way {
                    Way::Right => (runs[k].lo, runs[k].hi, k),
                    Way::Left | Way::Still => (-runs[k].hi, -runs[k].lo, k),
                })
                .collect();
            items.sort_unstable_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)));
            let lines = stack(&items);
            for (&(_, _, k), &line) in items.iter().zip(&lines) {
                track[k] = base + line;
            }
            base += lines.iter().max().map_or(0, |&m| m + 1);
        }
        *used = base;
    }
    (track, count)
}

/// Stacks runs that come in at decreasing keys: each on the line under the
/// lowest of the runs before it it overlaps, those whose key is at most
/// its reach.
///
/// # Arguments
///
/// * `items` - Each run's key, where it comes in, and reach, where it
///   leaves, the keys decreasing.
///
/// # Returns
///
/// Each run's line, from 0.
fn stack(items: &[(i64, i64, usize)]) -> Vec<i64> {
    let mut lines = Vec::with_capacity(items.len());
    let mut lowest: Vec<(usize, i64)> = Vec::new();
    for (i, &(_, reach, _)) in items.iter().enumerate() {
        let first = items[..i].partition_point(|&(key, _, _)| key > reach);
        let at = lowest.partition_point(|&(k, _)| k < first);
        let line = lowest.get(at).map_or(0, |&(_, l)| l + 1);
        while lowest.last().is_some_and(|&(_, l)| l <= line) {
            lowest.pop();
        }
        lowest.push((i, line));
        lines.push(line);
    }
    lines
}

/// Returns a column moved right by one where needed to share the parity
/// of its layer, the grid every port and added node's column on that layer
/// lies on.
///
/// # Arguments
///
/// * `x` - The column.
/// * `layer` - The layer it lies on.
fn on_parity(x: i64, layer: usize) -> i64 {
    x + (x - i64::from(layer % 2 == 1)).rem_euclid(2)
}

/// Returns each edge's port columns.
///
/// A node's edges out spread evenly along its bottom edge and its edges in along its top, each ordered by
/// where the edge's other end lies on the next layer, those routed on the
/// side last, then by edge.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `r` - The graph on layers.
/// * `pos` - Each node's place on its layer.
/// * `left` - Each node's left column.
///
/// # Returns
///
/// Each edge's source and target port column; zeros for a missing edge.
fn ports(g: &Graph, r: &Ranked, pos: &[usize], left: &[i64]) -> Vec<(i64, i64)> {
    let n = g.sizes.len();
    let mut outs: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    let mut ins: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    for (k, (e, chain)) in g.edges.iter().zip(&r.chains).enumerate() {
        if e.from < n && e.to < n {
            let (o, i) = chain.as_ref().map_or((usize::MAX, usize::MAX), |c| {
                (pos[c[1]], pos[c[c.len() - 2]])
            });
            outs[e.from].push((o, k));
            ins[e.to].push((i, k));
        }
    }
    let spread = |list: &mut Vec<(usize, usize)>, v: usize| {
        list.sort_unstable();
        let (w, k) = (r.width[v], i64::try_from(list.len()).unwrap_or(i64::MAX));
        (1i64..)
            .zip(list.iter())
            .map(|(j, &(_, e))| (e, on_parity(left[v] + j * w / (k + 1), r.layer[v])))
            .collect::<Vec<_>>()
    };
    let mut at = vec![(0i64, 0i64); g.edges.len()];
    for (v, (o, i)) in outs.iter_mut().zip(&mut ins).enumerate() {
        for (e, x) in spread(o, v) {
            at[e].0 = x;
        }
        for (e, x) in spread(i, v) {
            at[e].1 = x;
        }
    }
    at
}
