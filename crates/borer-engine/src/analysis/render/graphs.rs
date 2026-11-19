//! What every graph the engine lays out shares: its edges, what its caps
//! left out, and the walk and layout that draw it.

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
