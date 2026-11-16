//! The call tree's expansion state: which nodes of a tree of callers or callees are open,
//! laid out as the rows a list shows.
//!
//! The levels are the ones the engine's `call_children` answered. The tree's facts are
//! the engine's; this holds what is open and selected, and a bounded cache of the levels
//! read.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use borer_engine::analysis::render::{CallEdge, Children, Level, Via};

use crate::decompile_item::Form;
use crate::places::Place;

/// Most edges the cache of levels read keeps; past it the least recently read levels go,
/// and a node of one opens again by asking the engine. Levels shown stay while shown.
pub const KEPT_EDGES_MAX: usize = 1 << 16;

/// Which way the tree walks the call graph from its root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// What each node calls.
    Callees,
    /// What calls each node.
    Callers,
}

impl Direction {
    /// Returns the other direction.
    #[must_use]
    pub const fn flipped(self) -> Self {
        match self {
            Self::Callees => Self::Callers,
            Self::Callers => Self::Callees,
        }
    }
}

/// Whether the callees levels list the virtual calls the decompiler resolves, which
/// decompiles each node opened.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Virtuals {
    /// Only the calls the cross-references show.
    Hidden,
    /// Also the virtual calls the decompiler resolves.
    Shown,
}

impl Virtuals {
    /// Returns the other setting.
    #[must_use]
    pub const fn toggled(self) -> Self {
        match self {
            Self::Hidden => Self::Shown,
            Self::Shown => Self::Hidden,
        }
    }
}

/// Returns the level of the engine's call tree a direction and a virtuals setting ask for.
///
/// # Arguments
///
/// * `direction` - Which way the tree walks.
/// * `virtuals` - Whether callees levels list resolved virtual calls; callers levels never do.
#[must_use]
pub const fn level(direction: Direction, virtuals: Virtuals) -> Level {
    match (direction, virtuals) {
        (Direction::Callees, Virtuals::Hidden) => Level::Callees,
        (Direction::Callees, Virtuals::Shown) => Level::CalleesAndVirtuals,
        (Direction::Callers, Virtuals::Hidden | Virtuals::Shown) => Level::Callers,
    }
}

/// Returns the label a row shows for how the engine knows a call.
///
/// # Arguments
///
/// * `via` - How the engine knows the call.
#[must_use]
pub fn via_label(via: Via) -> Cow<'static, str> {
    match via {
        Via::Direct => Cow::Borrowed("direct"),
        Via::Import => Cow::Borrowed("import"),
        Via::Thunk { .. } => Cow::Borrowed("thunk"),
        Via::Bound { .. } => Cow::Borrowed("stub"),
        Via::Virtual { slot } => Cow::Owned(format!("virtual slot {slot}")),
        Via::Data => Cow::Borrowed("data"),
    }
}

/// Whether the engine looked for a node's virtual calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Search {
    /// The level does not list virtual calls.
    NotAsked,
    /// The node decompiled, so its resolvable virtual calls are listed.
    Searched,
    /// The node did not decompile, so its virtual calls were not looked for.
    Failed,
}

/// One node's level as the engine answered it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Answer {
    /// The edges, as `call_children` lists them.
    pub children: Children,
    /// Whether the engine looked for the node's virtual calls.
    pub search: Search,
}

/// What a node with no edge has none of, as its empty row says.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Missing {
    /// No callee, virtual calls looked for.
    Callee,
    /// No callee the cross-references show; virtual calls hidden or not looked for.
    DirectCallee,
    /// No caller.
    Caller,
}

/// What a function row of the tree shows and can do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// Its level is open and listed below it.
    Open,
    /// Its level is open and the engine has not answered yet.
    Reading,
    /// Its level is closed and can open.
    Closed,
    /// The engine says it has no edge of its own to follow.
    Leaf,
    /// It is already on its own path, so it does not open.
    Cycle,
}

/// Names one node of a tree: a place reached by one edge from its parent.
pub type NodeId = usize;

/// One row of the laid-out tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Row {
    /// The root, or the target of an edge.
    Node {
        /// The node.
        id: NodeId,
        /// Its depth, the root at 0.
        depth: usize,
    },
    /// One instruction making the call of the node row above it.
    Site {
        /// Entry of the function the instruction is in.
        function: u64,
        /// Address of the instruction.
        at: u64,
        /// One more than the node's depth.
        depth: usize,
    },
    /// The engine knows the call of the node row above it without an instruction making it.
    NoSites {
        /// One more than the node's depth.
        depth: usize,
    },
    /// The engine cut a level or a list of sites: it lists `shown` of `total`.
    More {
        /// Edges or sites listed.
        shown: usize,
        /// Edges or sites there are.
        total: usize,
        /// Depth of the edges or sites, the root's children at 1.
        depth: usize,
    },
    /// The engine knows no edge of an open node.
    Empty {
        /// Depth the edges would have, the root's children at 1.
        depth: usize,
        /// What the node has none of.
        missing: Missing,
    },
    /// The node did not decompile, so its virtual calls were not looked for.
    Unsearched {
        /// Depth of the node's edges, the root's children at 1.
        depth: usize,
    },
}

impl Row {
    /// Returns the row's depth in the tree, the root at 0.
    #[must_use]
    pub const fn depth(&self) -> usize {
        match *self {
            Self::Node { depth, .. }
            | Self::Site { depth, .. }
            | Self::NoSites { depth }
            | Self::More { depth, .. }
            | Self::Empty { depth, .. }
            | Self::Unsearched { depth } => depth,
        }
    }
}

/// Where following a row leads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Follow {
    /// To the function at this entry.
    Function(u64),
    /// To one instruction of a function.
    Site {
        /// Entry of the function.
        function: u64,
        /// Address of the instruction.
        at: u64,
    },
}

impl Follow {
    /// Returns the place following leads to: a function's decompile, or the listing of the
    /// function making a call with the call's instruction on its top line.
    #[must_use]
    pub const fn place(self) -> Place {
        match self {
            Self::Function(entry) => Place::Code {
                entry,
                form: Form::Decompile,
                at: None,
            },
            Self::Site { function, at } => Place::Code {
                entry: function,
                form: Form::Listing,
                at: Some(at),
            },
        }
    }
}

/// One node of the tree.
#[derive(Debug, Clone)]
struct Node {
    /// The function entry or import slot the node stands for.
    target: u64,
    /// The level holding the edge that leads here and the edge's place in it; `None` for
    /// the root.
    edge: Option<(Arc<Answer>, usize)>,
    /// The node one level up, `None` for the root.
    parent: Option<NodeId>,
    /// Depth, the root at 0.
    depth: usize,
    /// Whether the person opened it.
    open: bool,
    /// Whether its call sites are listed under it.
    sites: bool,
    /// Whether its target is already on its path.
    cycle: bool,
    /// Whether the engine says it has no edge to follow.
    leaf: bool,
    /// Its level and the nodes of its edges, while it is open and answered.
    children: Option<(Arc<Answer>, Vec<NodeId>)>,
}

/// A tree of callers or callees under one root, as far as it is open.
#[derive(Debug, Clone)]
pub struct CallTree {
    /// The function the tree starts from.
    root: u64,
    /// The root's name, once the engine gave it.
    root_name: Option<Box<str>>,
    /// Which way the tree walks.
    direction: Direction,
    /// Whether callees levels list resolved virtual calls.
    virtuals: Virtuals,
    /// The nodes shown, by id; a closed node's subtree is dropped.
    nodes: BTreeMap<NodeId, Node>,
    /// The id the next node takes.
    next_id: NodeId,
    /// The levels read, by node, each with when it was read.
    levels: BTreeMap<u64, (Arc<Answer>, u64)>,
    /// The node of each kept level, by when it was read.
    order: BTreeMap<u64, u64>,
    /// Edges the kept levels hold.
    kept: usize,
    /// Reads answered so far.
    seq: u64,
    /// Nodes whose level is asked for and not yet answered.
    reading: BTreeSet<u64>,
    /// The rows, laid out again only where a node changed.
    rows: Vec<Row>,
    /// Index of the selected row.
    selected: usize,
}

impl CallTree {
    /// Returns a closed tree under `root`.
    ///
    /// # Arguments
    ///
    /// * `root` - Entry of the function the tree starts from.
    /// * `direction` - Which way the tree walks.
    /// * `virtuals` - Whether callees levels list resolved virtual calls.
    #[must_use]
    pub fn new(root: u64, direction: Direction, virtuals: Virtuals) -> Self {
        let node = Node {
            target: root,
            edge: None,
            parent: None,
            depth: 0,
            open: false,
            sites: false,
            cycle: false,
            leaf: false,
            children: None,
        };
        Self {
            root,
            root_name: None,
            direction,
            virtuals,
            nodes: BTreeMap::from([(0, node)]),
            next_id: 1,
            levels: BTreeMap::new(),
            order: BTreeMap::new(),
            kept: 0,
            seq: 0,
            reading: BTreeSet::new(),
            rows: vec![Row::Node { id: 0, depth: 0 }],
            selected: 0,
        }
    }

    /// Returns the function the tree starts from.
    #[must_use]
    pub const fn root(&self) -> u64 {
        self.root
    }

    /// Returns the root's name, once the engine gave it.
    #[must_use]
    pub fn root_name(&self) -> Option<&str> {
        self.root_name.as_deref()
    }

    /// Takes the root's name.
    ///
    /// # Arguments
    ///
    /// * `name` - The root's name, as listings spell it.
    pub fn name_root(&mut self, name: Box<str>) {
        self.root_name = Some(name);
    }

    /// Returns which way the tree walks.
    #[must_use]
    pub const fn direction(&self) -> Direction {
        self.direction
    }

    /// Returns whether callees levels list resolved virtual calls.
    #[must_use]
    pub const fn virtuals(&self) -> Virtuals {
        self.virtuals
    }

    /// Takes a virtuals setting that asks for the same level, which callers levels ignore.
    ///
    /// # Arguments
    ///
    /// * `virtuals` - The new setting.
    ///
    /// # Returns
    ///
    /// Whether the tree took it; `false` when the level would change, which asks for a new
    /// tree.
    pub fn keep_virtuals(&mut self, virtuals: Virtuals) -> bool {
        let same = level(self.direction, virtuals) == self.level();
        if same {
            self.virtuals = virtuals;
        }
        same
    }

    /// Returns the level each node lists.
    #[must_use]
    pub const fn level(&self) -> Level {
        level(self.direction, self.virtuals)
    }

    /// Returns the rows the list shows, in order.
    #[must_use]
    pub fn rows(&self) -> &[Row] {
        &self.rows
    }

    /// Returns the index of the selected row.
    #[must_use]
    pub const fn selected(&self) -> usize {
        self.selected
    }

    /// Returns how many nodes wait for the engine's answer.
    #[must_use]
    pub fn reading(&self) -> usize {
        self.reading.len()
    }

    /// Returns how many edges the root's level lists and how many there are, once read.
    #[must_use]
    pub fn root_level(&self) -> Option<(usize, usize)> {
        let (answer, _) = self.nodes.get(&0)?.children.as_ref()?;
        Some((answer.children.rows.len(), answer.children.total))
    }

    /// Returns the target of a node row.
    ///
    /// # Arguments
    ///
    /// * `row` - A row of [`Self::rows`].
    ///
    /// # Returns
    ///
    /// The function entry or import slot, `None` for rows of no node.
    #[must_use]
    pub fn target(&self, row: &Row) -> Option<u64> {
        Some(self.node(row)?.target)
    }

    /// Returns what a node row shows and can do.
    ///
    /// # Arguments
    ///
    /// * `row` - A row of [`Self::rows`].
    ///
    /// # Returns
    ///
    /// The shape, `None` for rows of no node.
    #[must_use]
    pub fn shape(&self, row: &Row) -> Option<Shape> {
        let node = self.node(row)?;
        Some(match (node.cycle, node.leaf, node.open, &node.children) {
            (true, _, _, _) => Shape::Cycle,
            (false, true, _, _) => Shape::Leaf,
            (false, false, false, _) => Shape::Closed,
            (false, false, true, None) => Shape::Reading,
            (false, false, true, Some(_)) => Shape::Open,
        })
    }

    /// Returns the edge a node row stands for.
    ///
    /// # Arguments
    ///
    /// * `row` - A row of [`Self::rows`].
    ///
    /// # Returns
    ///
    /// The engine's edge, `None` for the root and for rows of no node.
    #[must_use]
    pub fn edge(&self, row: &Row) -> Option<&CallEdge> {
        let (answer, k) = self.node(row)?.edge.as_ref()?;
        answer.children.rows.get(*k)
    }

    /// Selects row `ix`, clamped to the rows shown.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index; past the last selects the last.
    pub fn select(&mut self, ix: usize) {
        self.selected = ix.min(self.rows.len().saturating_sub(1));
    }

    /// Opens the node of row `ix` when it is closed.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// The node whose level the engine must be asked for, `None` when the row did not open,
    /// the level is kept, or it is already asked for.
    pub fn expand(&mut self, ix: usize) -> Option<u64> {
        let row = *self.rows.get(ix)?;
        if self.shape(&row) != Some(Shape::Closed) {
            return None;
        }
        let Row::Node { id, .. } = row else {
            return None;
        };
        let node = self.nodes.get_mut(&id)?;
        node.open = true;
        let target = node.target;
        let ask = match self
            .levels
            .get(&target)
            .map(|(answer, _)| Arc::clone(answer))
        {
            Some(answer) => {
                self.attach(id, answer);
                None
            }
            None => self.reading.insert(target).then_some(target),
        };
        self.relayout(ix);
        ask
    }

    /// Closes the node of row `ix` when it is open, dropping its subtree; its level stays
    /// kept.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// Whether the row closed.
    pub fn collapse(&mut self, ix: usize) -> bool {
        let Some(&Row::Node { id, .. }) = self.rows.get(ix) else {
            return false;
        };
        let Some(node) = self.nodes.get_mut(&id).filter(|node| node.open) else {
            return false;
        };
        node.open = false;
        self.drop_children(id);
        self.relayout(ix);
        true
    }

    /// Opens row `ix` when closed, else closes it.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// The node whose level the engine must be asked for, as [`Self::expand`] says.
    pub fn toggle(&mut self, ix: usize) -> Option<u64> {
        if self.collapse(ix) {
            return None;
        }
        self.expand(ix)
    }

    /// Lists the call sites of row `ix`'s edge, or hides them.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// Whether the row has an edge whose sites it lists or hides; the root has none.
    pub fn toggle_sites(&mut self, ix: usize) -> bool {
        let Some(&Row::Node { id, .. }) = self.rows.get(ix) else {
            return false;
        };
        let Some(node) = self.nodes.get_mut(&id).filter(|node| node.edge.is_some()) else {
            return false;
        };
        node.sites = !node.sites;
        self.relayout(ix);
        true
    }

    /// Returns where following row `ix` leads: a node to its function, a site to its
    /// instruction. An import's node has no function of the binary's to lead to, so
    /// following it lists its call sites instead.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// Where the row leads, `None` for an import and for rows of no node or site.
    pub fn follow(&mut self, ix: usize) -> Option<Follow> {
        let row = *self.rows.get(ix)?;
        match row {
            Row::Node { .. } => {
                let import = self.direction == Direction::Callees
                    && self.edge(&row).is_some_and(|e| e.via == Via::Import);
                if import {
                    self.toggle_sites(ix);
                    return None;
                }
                Some(Follow::Function(self.target(&row)?))
            }
            Row::Site { function, at, .. } => Some(Follow::Site { function, at }),
            Row::NoSites { .. } | Row::More { .. } | Row::Empty { .. } | Row::Unsearched { .. } => {
                None
            }
        }
    }

    /// Returns the index of the node row above row `ix` one level up.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    ///
    /// # Returns
    ///
    /// The parent's index, `None` for the root and past the last row.
    #[must_use]
    pub fn parent(&self, ix: usize) -> Option<usize> {
        let depth = self.rows.get(ix)?.depth().checked_sub(1)?;
        self.rows
            .get(..ix)?
            .iter()
            .rposition(|row| matches!(row, Row::Node { .. }) && row.depth() == depth)
    }

    /// Steps into the selected row: opens it when closed, else selects its first child.
    ///
    /// # Returns
    ///
    /// The node whose level the engine must be asked for, as [`Self::expand`] says.
    pub fn step_in(&mut self) -> Option<u64> {
        let ix = self.selected;
        let row = *self.rows.get(ix)?;
        if self.shape(&row) == Some(Shape::Closed) {
            return self.expand(ix);
        }
        let next = ix.saturating_add(1);
        if self.rows.get(next).is_some_and(|n| n.depth() > row.depth()) {
            self.selected = next;
        }
        None
    }

    /// Steps out of the selected row: closes it when open, else selects its parent.
    pub fn step_out(&mut self) {
        if !self.collapse(self.selected)
            && let Some(parent) = self.parent(self.selected)
        {
            self.selected = parent;
        }
    }

    /// Takes the engine's answer for `node`'s level, keeps it, and lists it under every
    /// open row of `node` waiting for it.
    ///
    /// # Arguments
    ///
    /// * `node` - The node asked for.
    /// * `answer` - Its level.
    pub fn answer(&mut self, node: u64, answer: Answer) {
        self.reading.remove(&node);
        let answer = Arc::new(answer);
        self.keep(node, Arc::clone(&answer));
        let waiting: Vec<(usize, NodeId)> = self
            .rows
            .iter()
            .enumerate()
            .filter_map(|(ix, row)| {
                let &Row::Node { id, .. } = row else {
                    return None;
                };
                let n = self.nodes.get(&id)?;
                (n.target == node && n.open && n.children.is_none()).then_some((ix, id))
            })
            .collect();
        for (ix, id) in waiting.into_iter().rev() {
            self.attach(id, Arc::clone(&answer));
            self.relayout(ix);
        }
    }

    /// Returns the node of a node row.
    ///
    /// # Arguments
    ///
    /// * `row` - A row of [`Self::rows`].
    fn node(&self, row: &Row) -> Option<&Node> {
        let &Row::Node { id, .. } = row else {
            return None;
        };
        self.nodes.get(&id)
    }

    /// Keeps `node`'s level, dropping the least recently read ones past
    /// [`KEPT_EDGES_MAX`]; the newest always stays.
    ///
    /// # Arguments
    ///
    /// * `node` - The node read.
    /// * `answer` - Its level.
    fn keep(&mut self, node: u64, answer: Arc<Answer>) {
        self.seq = self.seq.saturating_add(1);
        let size = answer.children.rows.len();
        if let Some((old, seq)) = self.levels.insert(node, (answer, self.seq)) {
            self.order.remove(&seq);
            self.kept = self.kept.saturating_sub(old.children.rows.len());
        }
        self.order.insert(self.seq, node);
        self.kept = self.kept.saturating_add(size);
        while self.kept > KEPT_EDGES_MAX && self.order.len() > 1 {
            let Some((_, gone)) = self.order.pop_first() else {
                break;
            };
            if let Some((old, _)) = self.levels.remove(&gone) {
                self.kept = self.kept.saturating_sub(old.children.rows.len());
            }
        }
    }

    /// Makes a node for each edge of `answer` under the open node `id`.
    ///
    /// # Arguments
    ///
    /// * `id` - The open node.
    /// * `answer` - Its level.
    fn attach(&mut self, id: NodeId, answer: Arc<Answer>) {
        let Some(depth) = self.nodes.get(&id).map(|n| n.depth.saturating_add(1)) else {
            return;
        };
        let virtuals = self.level() == Level::CalleesAndVirtuals;
        let kids: Vec<Node> = answer
            .children
            .rows
            .iter()
            .enumerate()
            .map(|(k, e)| Node {
                target: e.target,
                edge: Some((Arc::clone(&answer), k)),
                parent: Some(id),
                depth,
                open: false,
                sites: false,
                cycle: self.on_path(id, e.target),
                leaf: e.leaf && (!virtuals || e.via == Via::Import),
                children: None,
            })
            .collect();
        let ids: Vec<NodeId> = kids
            .into_iter()
            .map(|kid| {
                let kid_id = self.next_id;
                self.next_id = self.next_id.saturating_add(1);
                self.nodes.insert(kid_id, kid);
                kid_id
            })
            .collect();
        if let Some(node) = self.nodes.get_mut(&id) {
            node.children = Some((answer, ids));
        }
    }

    /// Returns whether `target` is node `id`'s own target or one of its ancestors'.
    ///
    /// The walk follows parents, each made before its child, so it ends at the root.
    ///
    /// # Arguments
    ///
    /// * `id` - The node to start from.
    /// * `target` - The target to look for.
    fn on_path(&self, id: NodeId, target: u64) -> bool {
        std::iter::successors(self.nodes.get(&id), |n| self.nodes.get(&n.parent?))
            .any(|n| n.target == target)
    }

    /// Drops the nodes under node `id`.
    ///
    /// # Arguments
    ///
    /// * `id` - The node closed.
    fn drop_children(&mut self, id: NodeId) {
        let Some((_, kids)) = self.nodes.get_mut(&id).and_then(|n| n.children.take()) else {
            return;
        };
        for kid in kids {
            self.drop_children(kid);
            self.nodes.remove(&kid);
        }
    }

    /// Lays out again the rows of the node at row `ix` and its subtree, keeping the
    /// selection on the row it was on.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based index of a node row.
    fn relayout(&mut self, ix: usize) {
        let Some(&Row::Node { id, depth }) = self.rows.get(ix) else {
            return;
        };
        let after = ix.saturating_add(1);
        let end = self
            .rows
            .get(after..)
            .and_then(|rest| rest.iter().position(|row| row.depth() <= depth))
            .map_or(self.rows.len(), |k| after.saturating_add(k));
        let mut fresh = Vec::new();
        self.push_subtree(id, &mut fresh);
        let (old, new) = (end.saturating_sub(ix), fresh.len());
        self.rows.splice(ix..end, fresh);
        if self.selected >= end {
            self.selected = self.selected.saturating_sub(old).saturating_add(new);
        } else if self.selected > ix && self.selected.saturating_sub(ix) >= new {
            self.selected = ix;
        }
    }

    /// Pushes the row of node `id` and, when it is open and answered, its subtree's rows.
    ///
    /// The depth of the walk is the depth of an open node, which grows by one per node a
    /// person opens and holds no target twice.
    ///
    /// # Arguments
    ///
    /// * `id` - The node.
    /// * `rows` - The rows laid out so far.
    fn push_subtree(&self, id: NodeId, rows: &mut Vec<Row>) {
        let Some(node) = self.nodes.get(&id) else {
            return;
        };
        rows.push(Row::Node {
            id,
            depth: node.depth,
        });
        if node.sites {
            self.push_sites(node, rows);
        }
        let Some((answer, kids)) = &node.children else {
            return;
        };
        for &kid in kids {
            self.push_subtree(kid, rows);
        }
        let (level, depth) = (&answer.children, node.depth.saturating_add(1));
        if level.total == 0 {
            let missing = self.missing(answer.search);
            rows.push(Row::Empty { depth, missing });
        } else if level.total > level.rows.len() {
            rows.push(Row::More {
                shown: level.rows.len(),
                total: level.total,
                depth,
            });
        }
        if answer.search == Search::Failed {
            rows.push(Row::Unsearched { depth });
        }
    }

    /// Pushes a row for each call site of a node's edge, one saying when the engine cut
    /// them, or one saying it knows none.
    ///
    /// Over callees the sites are in the edge's parent, over callers in its target.
    ///
    /// # Arguments
    ///
    /// * `node` - The node.
    /// * `rows` - The rows laid out so far.
    fn push_sites(&self, node: &Node, rows: &mut Vec<Row>) {
        let Some(edge) = node
            .edge
            .as_ref()
            .and_then(|(answer, k)| answer.children.rows.get(*k))
        else {
            return;
        };
        let parent = node
            .parent
            .and_then(|p| self.nodes.get(&p))
            .map(|p| p.target);
        let function = match self.direction {
            Direction::Callees => parent,
            Direction::Callers => Some(node.target),
        };
        let depth = node.depth.saturating_add(1);
        let Some(function) = function.filter(|_| !edge.sites.is_empty()) else {
            rows.push(Row::NoSites { depth });
            return;
        };
        rows.extend(edge.sites.iter().map(|&at| Row::Site {
            function,
            at,
            depth,
        }));
        if edge.site_count > edge.sites.len() {
            rows.push(Row::More {
                shown: edge.sites.len(),
                total: edge.site_count,
                depth,
            });
        }
    }

    /// Returns what a node with no edge has none of.
    ///
    /// # Arguments
    ///
    /// * `search` - Whether its virtual calls were looked for.
    const fn missing(&self, search: Search) -> Missing {
        match (self.direction, search) {
            (Direction::Callers, Search::NotAsked | Search::Searched | Search::Failed) => {
                Missing::Caller
            }
            (Direction::Callees, Search::Searched) => Missing::Callee,
            (Direction::Callees, Search::NotAsked | Search::Failed) => Missing::DirectCallee,
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use borer_engine::analysis::render::{
        CallEdge, Children, FunctionOrder, Level, Via, function_rows,
    };
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};

    use super::{
        Answer, CallTree, Direction, Follow, KEPT_EDGES_MAX, Missing, Row, Search, Shape, Virtuals,
        via_label,
    };
    use crate::worker::{LoadedBinary, call_level_blocking};

    /// Entry of the tree program's first function, which calls [`ZETA`], [`ALPHA`] and
    /// [`MID`] once each, in that order.
    pub(crate) const MAIN: u64 = 0x1000;

    /// Entry of a function that calls nothing, named `zeta`.
    pub(crate) const ZETA: u64 = 0x1040;

    /// Entry of a function that calls nothing, named `alpha`.
    pub(crate) const ALPHA: u64 = 0x1060;

    /// Entry of a function that calls itself, named `mid`.
    pub(crate) const MID: u64 = 0x1080;

    /// Returns the hand-built tree program as a loaded binary: `main` calls three functions
    /// whose names sort apart from their addresses, and one of them calls itself.
    pub(crate) fn tree_program() -> Arc<LoadedBinary> {
        let mut bytes = vec![0xccu8; 0x100];
        // ASM: sub rsp, 0x28 ; call 0x1040 ; call 0x1060 ; call 0x1080 ; add rsp, 0x28 ; ret
        let main: &[u8] = &[
            0x48, 0x83, 0xec, 0x28, 0xe8, 0x37, 0x00, 0x00, 0x00, 0xe8, 0x52, 0x00, 0x00, 0x00,
            0xe8, 0x6d, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
        ];
        // ASM: mov eax, 1 ; ret
        let zeta: &[u8] = &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3];
        // ASM: xor eax, eax ; ret
        let alpha: &[u8] = &[0x31, 0xc0, 0xc3];
        // ASM: test ecx, ecx ; jz 0x108b ; dec ecx ; call 0x1080 ; ret
        let mid: &[u8] = &[
            0x85, 0xc9, 0x74, 0x07, 0xff, 0xc9, 0xe8, 0xf5, 0xff, 0xff, 0xff, 0xc3,
        ];
        for (at, code) in [(0, main), (0x40, zeta), (0x60, alpha), (0x80, mid)] {
            bytes[at..at + code.len()].copy_from_slice(code);
        }
        let sections = vec![Section::mapped(".text", MAIN, 0, 0x100, false, true)];
        let mut program = Program::raw(bytes, Arch::X86_64, MAIN, Some(MAIN), sections);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            names: [(ZETA, "zeta"), (ALPHA, "alpha"), (MID, "mid")]
                .into_iter()
                .map(|(at, name)| (at, name.to_owned()))
                .collect(),
            ..Overlay::default()
        };
        let initial_rows = Arc::new(function_rows(
            &analysis,
            &overlay,
            None,
            FunctionOrder::Address,
            0,
            usize::MAX,
        ));
        Arc::new(LoadedBinary {
            path: PathBuf::from("tree.bin"),
            program: Arc::new(program),
            analysis: Arc::new(analysis),
            overlay: Arc::new(overlay),
            initial_rows,
            notes: Vec::new(),
        })
    }

    /// Answers the node `asked` names, if any, with the engine's level of it in `loaded`.
    pub(crate) fn answer_asked(tree: &mut CallTree, loaded: &LoadedBinary, asked: Option<u64>) {
        if let Some(node) = asked {
            let (children, search) = call_level_blocking(loaded, node, tree.level());
            tree.answer(node, Answer { children, search });
        }
    }

    /// Returns a made-up edge to `target`, known `via`, made at `sites`.
    pub(crate) fn edge(target: u64, via: Via, sites: &[u64], leaf: bool) -> CallEdge {
        CallEdge {
            target,
            name: format!("f_{target:x}").into_boxed_str(),
            via,
            sites: sites.to_vec(),
            site_count: sites.len(),
            leaf,
        }
    }

    /// Returns a made-up level of `rows` out of `total`, its virtual calls as `search` says.
    pub(crate) fn made(rows: Vec<CallEdge>, total: usize, search: Search) -> Answer {
        Answer {
            children: Children { rows, total },
            search,
        }
    }

    /// Address of `main`'s call to [`ZETA`].
    pub(crate) const MAIN_CALLS_ZETA: u64 = 0x1004;

    /// Returns the target of each node row of `tree`, the root's included.
    pub(crate) fn targets(tree: &CallTree) -> Vec<u64> {
        tree.rows()
            .iter()
            .filter_map(|row| tree.target(row))
            .collect()
    }

    /// Returns the shape of each node row of `tree`.
    fn shapes(tree: &CallTree) -> Vec<Shape> {
        tree.rows()
            .iter()
            .filter_map(|row| tree.shape(row))
            .collect()
    }

    /// Opening the root of `main` shows exactly the engine's level, row for row and in the
    /// engine's order, which is not the order of the names.
    ///
    /// # Panics
    ///
    /// Panics if the rows differ from `call_children`'s.
    #[test]
    fn opening_a_node_shows_the_engine_level_in_its_order() {
        let loaded = tree_program();
        let (want, _) = call_level_blocking(&loaded, MAIN, Level::Callees);
        let names: Vec<&str> = want.rows.iter().map(|e| &*e.name).collect();
        assert_eq!(names, ["zeta", "alpha", "mid"]);
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        assert_eq!(asked, Some(MAIN));
        assert_eq!(shapes(&tree), [Shape::Reading]);
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(targets(&tree), [MAIN, ZETA, ALPHA, MID]);
        let shown: Vec<_> = tree.rows()[1..]
            .iter()
            .map(|row| tree.edge(row).cloned())
            .collect();
        let want: Vec<_> = want.rows.into_iter().map(Some).collect();
        assert_eq!(shown, want);
        assert_eq!(tree.root_level(), Some((3, 3)));
    }

    /// A function that calls itself shows itself once more as a cycle, which does not open,
    /// in either direction.
    ///
    /// # Panics
    ///
    /// Panics if the cycle row is missing, repeated or opens.
    #[test]
    fn a_recursive_function_shows_one_cycle_that_does_not_open() {
        let loaded = tree_program();
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        answer_asked(&mut tree, &loaded, asked);
        let asked = tree.expand(3);
        assert_eq!(asked, Some(MID));
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(targets(&tree), [MAIN, ZETA, ALPHA, MID, MID]);
        let want = [
            Shape::Open,
            Shape::Leaf,
            Shape::Leaf,
            Shape::Open,
            Shape::Cycle,
        ];
        assert_eq!(shapes(&tree), want);
        let before = tree.rows().to_vec();
        assert_eq!(tree.expand(4), None);
        assert_eq!(tree.toggle(4), None);
        assert_eq!(tree.rows(), before);

        let mut callers = CallTree::new(MID, Direction::Callers, Virtuals::Hidden);
        let asked = callers.expand(0);
        answer_asked(&mut callers, &loaded, asked);
        let cycles = shapes(&callers)
            .into_iter()
            .filter(|shape| *shape == Shape::Cycle)
            .count();
        assert_eq!(cycles, 1);
        assert!(targets(&callers).contains(&MAIN));
    }

    /// A closed node's level stays kept, so opening it again asks the engine nothing, and
    /// stepping out of a child selects its parent.
    ///
    /// # Panics
    ///
    /// Panics if a reopen asks again or a step lands on the wrong row.
    #[test]
    fn closing_keeps_the_level_and_steps_follow_the_tree() {
        let loaded = tree_program();
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Hidden);
        let asked = tree.step_in();
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(tree.step_in(), None);
        assert_eq!(tree.selected(), 1);
        tree.step_out();
        assert_eq!(tree.selected(), 0);
        tree.step_out();
        assert_eq!(tree.rows().len(), 1);
        assert_eq!(tree.expand(0), None);
        assert_eq!(tree.rows().len(), 4);
        assert_eq!(tree.reading(), 0);
    }

    /// Two edges to one target are two rows that open apart, the second from the kept
    /// level without asking again.
    ///
    /// # Panics
    ///
    /// Panics if opening one opens the other or the second asks the engine.
    #[test]
    fn two_edges_to_one_target_open_apart() {
        let (root, target, under) = (0x10, 0x20, 0x30);
        let mut tree = CallTree::new(root, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        let both = vec![
            edge(target, Via::Direct, &[0x11], false),
            edge(target, Via::Virtual { slot: 1 }, &[0x15], false),
        ];
        tree.answer(root, made(both, 2, Search::NotAsked));
        assert_eq!(asked, Some(root));
        assert_eq!(tree.expand(1), Some(target));
        let leaf = vec![edge(under, Via::Direct, &[0x21], true)];
        tree.answer(target, made(leaf, 1, Search::NotAsked));
        assert_eq!(targets(&tree), [root, target, under, target]);
        assert_eq!(tree.shape(&tree.rows()[3]), Some(Shape::Closed));
        assert_eq!(tree.expand(3), None);
        assert_eq!(targets(&tree), [root, target, under, target, under]);
    }

    /// A cut level ends with a row saying how many it shows, and an empty one says what it
    /// lacks: no direct callee while virtual calls are hidden.
    ///
    /// # Panics
    ///
    /// Panics if the cut or empty row is missing or wrong.
    #[test]
    fn a_cut_level_says_how_many_it_shows() {
        let mut tree = CallTree::new(0x10, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        let one = vec![edge(0x20, Via::Direct, &[0x11], false)];
        tree.answer(0x10, made(one, 5, Search::NotAsked));
        assert_eq!(asked, Some(0x10));
        let more = Row::More {
            shown: 1,
            total: 5,
            depth: 1,
        };
        assert_eq!(tree.rows().last(), Some(&more));
        assert_eq!(tree.expand(1), Some(0x20));
        tree.answer(0x20, made(Vec::new(), 0, Search::NotAsked));
        let empty = Row::Empty {
            depth: 2,
            missing: Missing::DirectCallee,
        };
        assert_eq!(tree.rows().get(2), Some(&empty));
    }

    /// With virtual calls listed, a function the engine calls a leaf can open.
    ///
    /// That flag never looks for virtual calls; one that does not decompile says its virtual
    /// calls were not looked for, and one that does says it has no callee.
    ///
    /// # Panics
    ///
    /// Panics if the leaf does not open or a row claims more than the search showed.
    #[test]
    fn virtual_calls_listed_open_leaves_and_say_when_not_searched() {
        let loaded = tree_program();
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Shown);
        let asked = tree.expand(0);
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(tree.shape(&tree.rows()[1]), Some(Shape::Closed));
        let asked = tree.expand(1);
        assert_eq!(asked, Some(ZETA));
        answer_asked(&mut tree, &loaded, asked);
        let none = Row::Empty {
            depth: 2,
            missing: Missing::Callee,
        };
        assert_eq!(tree.rows().get(2), Some(&none));

        let mut failed = CallTree::new(0x10, Direction::Callees, Virtuals::Shown);
        let asked = failed.expand(0);
        failed.answer(0x10, made(Vec::new(), 0, Search::Failed));
        assert_eq!(asked, Some(0x10));
        let rows = [
            Row::Node { id: 0, depth: 0 },
            Row::Empty {
                depth: 1,
                missing: Missing::DirectCallee,
            },
            Row::Unsearched { depth: 1 },
        ];
        assert_eq!(failed.rows(), rows);
        assert!(failed.keep_virtuals(Virtuals::Shown));
        assert!(!failed.keep_virtuals(Virtuals::Hidden));
        let mut callers = CallTree::new(0x10, Direction::Callers, Virtuals::Hidden);
        assert!(callers.keep_virtuals(Virtuals::Shown));
        assert_eq!(callers.virtuals(), Virtuals::Shown);
    }

    /// The cache of levels read stays within [`KEPT_EDGES_MAX`] edges: past it the oldest
    /// closed level goes, and opening its node asks the engine again.
    ///
    /// # Panics
    ///
    /// Panics if an evicted level is still used or a kept one asked again.
    #[test]
    fn the_kept_levels_stay_bounded() {
        let (root, a, b) = (0x10, 0x20, 0x30);
        let big = |base: u64| {
            let count = u64::try_from(KEPT_EDGES_MAX / 2 + 1).unwrap();
            let rows: Vec<_> = (0..count)
                .map(|k| edge(base + k, Via::Direct, &[base], true))
                .collect();
            let total = rows.len();
            made(rows, total, Search::NotAsked)
        };
        let mut tree = CallTree::new(root, Direction::Callees, Virtuals::Hidden);
        assert_eq!(tree.expand(0), Some(root));
        let two = vec![
            edge(a, Via::Direct, &[0x11], false),
            edge(b, Via::Direct, &[0x15], false),
        ];
        tree.answer(root, made(two, 2, Search::NotAsked));
        assert_eq!(tree.expand(1), Some(a));
        tree.answer(a, big(0x10_0000));
        assert!(tree.collapse(1));
        assert_eq!(tree.expand(2), Some(b));
        tree.answer(b, big(0x20_0000));
        assert!(tree.collapse(2));
        assert_eq!(tree.expand(2), None);
        assert!(tree.collapse(2));
        assert_eq!(tree.expand(1), Some(a));
    }

    /// A call's sites list under its row, in the function that makes the call: the parent
    /// over callees, the target over callers; following a site leads to its instruction.
    ///
    /// # Panics
    ///
    /// Panics if a site row is missing, misplaced or names the wrong function.
    #[test]
    fn sites_list_under_their_call_in_the_calling_function() {
        let loaded = tree_program();
        let site = Row::Site {
            function: MAIN,
            at: MAIN_CALLS_ZETA,
            depth: 2,
        };
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        answer_asked(&mut tree, &loaded, asked);
        assert!(!tree.toggle_sites(0));
        assert!(tree.toggle_sites(1));
        assert_eq!(tree.rows().get(2), Some(&site));
        assert_eq!(targets(&tree), [MAIN, ZETA, ALPHA, MID]);
        let follow = Follow::Site {
            function: MAIN,
            at: MAIN_CALLS_ZETA,
        };
        assert_eq!(tree.follow(2), Some(follow));
        assert_eq!(tree.follow(1), Some(Follow::Function(ZETA)));
        assert!(tree.toggle_sites(1));
        assert_eq!(tree.rows().len(), 4);

        let mut callers = CallTree::new(ZETA, Direction::Callers, Virtuals::Hidden);
        let asked = callers.expand(0);
        answer_asked(&mut callers, &loaded, asked);
        assert!(callers.toggle_sites(1));
        assert_eq!(callers.rows().get(2), Some(&site));
    }

    /// Following an import lists its call sites instead of opening anything, a call with no
    /// known site says so, and a cut list of sites says how many it shows.
    ///
    /// # Panics
    ///
    /// Panics if an import leads somewhere or a sites row is wrong.
    #[test]
    fn following_an_import_lists_its_sites() {
        let (root, slot, quiet, busy) = (0x10, 0x9000, 0x20, 0x30);
        let mut tree = CallTree::new(root, Direction::Callees, Virtuals::Hidden);
        let asked = tree.expand(0);
        let mut many = edge(busy, Via::Direct, &[0x13, 0x14], false);
        many.site_count = 40;
        let level = vec![
            edge(slot, Via::Import, &[0x11], true),
            edge(quiet, Via::Direct, &[], false),
            many,
        ];
        tree.answer(root, made(level, 3, Search::NotAsked));
        assert_eq!(asked, Some(root));
        assert_eq!(tree.follow(1), None);
        let site = Row::Site {
            function: root,
            at: 0x11,
            depth: 2,
        };
        assert_eq!(tree.rows().get(2), Some(&site));
        assert!(tree.toggle_sites(3));
        assert_eq!(tree.rows().get(4), Some(&Row::NoSites { depth: 2 }));
        assert!(tree.toggle_sites(5));
        let cut = Row::More {
            shown: 2,
            total: 40,
            depth: 2,
        };
        assert_eq!(tree.rows().get(8), Some(&cut));
    }

    /// Every way the engine knows a call has its label.
    ///
    /// # Panics
    ///
    /// Panics if a variant's label differs.
    #[test]
    fn every_via_has_a_label() {
        let cases = [
            (Via::Direct, "direct"),
            (Via::Import, "import"),
            (Via::Thunk { slot: 0x2000 }, "thunk"),
            (Via::Bound { stub: 0x1100 }, "stub"),
            (Via::Virtual { slot: 3 }, "virtual slot 3"),
            (Via::Data, "data"),
        ];
        for (via, label) in cases {
            assert_eq!(via_label(via), label, "{via:?}");
        }
    }
}
