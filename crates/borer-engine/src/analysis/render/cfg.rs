//! A function's control-flow graph as a typed value: its blocks as rows of
//! the function's listing, and each successor edge named by what takes it.

use super::*;
use crate::view::View;
use anyhow::Context as _;
use std::ops::Range;

/// Most blocks a [`Cfg`] holds; a function of more is cut to this many,
/// those the entry reaches first, and says so ([`Cut`]).
///
/// Above [`CFG_BLOCKS_MAX`], the mermaid page, since the graph is drawn
/// rather than read as text: a dispatcher of a few thousand blocks is still
/// one picture, and the layout of this many stays within milliseconds.
pub const CFG_NODES_MAX: usize = 2048;

/// Most edges a [`Cfg`] holds, a jump table's entries to one block counting
/// as one; past it the edges of the last blocks are left out and the graph
/// says so ([`Cut`]).
pub const CFG_EDGES_MAX: usize = 4 * CFG_NODES_MAX;

/// Most instructions a [`Cfg`] lists of one block; a longer block ends in a
/// `// ... N more bytes` row and the graph says so ([`Cut`]).
pub const CFG_ROWS_MAX: usize = 256;

/// Most instructions a [`Cfg`] lists in all, so one graph's listing stays
/// a few megabytes; once they are listed each further block shows its first
/// instruction and a `// ... N more bytes` row ([`Cut`]).
pub const CFG_LISTED_MAX: usize = 8192;

/// A function's control-flow graph.
#[derive(Debug)]
pub struct Cfg {
    /// The listing of the blocks drawn, bytes shown, whose rows the nodes
    /// are.
    pub listing: Arc<View>,
    /// The blocks drawn, in address order.
    pub nodes: Vec<Node>,
    /// The successor edges among the drawn blocks, by source node and then
    /// in the block's successor order.
    pub edges: Vec<Edge>,
    /// What was left out, when the function has more than
    /// [`CFG_NODES_MAX`] blocks, its drawn blocks more than
    /// [`CFG_EDGES_MAX`] edges, or a block more rows than
    /// [`CFG_ROWS_MAX`] and [`CFG_LISTED_MAX`] leave it.
    pub cut: Option<Cut>,
}

/// One block of a [`Cfg`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    /// Address of the block's first instruction.
    pub start: u64,
    /// End of the block's last instruction (exclusive).
    pub end: u64,
    /// How the block ends.
    pub term: BlockTerm,
    /// The rows of [`Cfg::listing`] that show the block's instructions,
    /// from its first instruction's row to its last's, then the
    /// `// ... N more bytes` row of a block cut short.
    pub lines: Range<usize>,
    /// Whether the block is cut short: its last row says how many bytes
    /// it does not list.
    pub shortened: bool,
}

/// One successor edge of a [`Cfg`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    /// The source node's index in [`Cfg::nodes`].
    pub from: usize,
    /// The target node's index in [`Cfg::nodes`].
    pub to: usize,
    /// What takes the edge.
    pub kind: EdgeKind,
    /// Whether the edge closes a cycle: the depth-first walk of
    /// [`mark_back_edges`] found its target still on the walk's stack.
    pub back: bool,
}

/// What takes a successor edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EdgeKind {
    /// The condition the listing shows holds: a conditional branch's
    /// target, or on arm the instructions run under the condition.
    Taken,
    /// The condition the listing shows fails: a conditional branch's
    /// fall-through, the address past instructions run under it, or past a
    /// conditional return or indirect jump.
    NotTaken,
    /// An unconditional jump, an indirect one no resolved table explains,
    /// or an x86 transaction's way to its abort handler.
    Jump,
    /// Straight-line flow into the next block: after a call, after no
    /// branch, or into or out of an x86 transaction.
    Fall,
    /// The entries of the jump table an indirect jump reads that hold this
    /// target, in increasing order: each the index the table is read at,
    /// the switched value less any bias the compiler subtracted first.
    Cases(Vec<u32>),
}

/// What a [`Cfg`] left out of the function: some of its blocks, some of
/// their edges, or the rows of a block past [`CFG_ROWS_MAX`] or past
/// what [`CFG_LISTED_MAX`] leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cut {
    /// Blocks drawn.
    pub shown: usize,
    /// Blocks the function has.
    pub total: usize,
    /// Edges held among the drawn blocks.
    pub edges_shown: usize,
    /// Edges the drawn blocks have among them.
    pub edges_total: usize,
    /// Drawn blocks cut short ([`Node::shortened`]).
    pub shortened: usize,
}

/// Returns whether an arm block ends in no branch, so its two successors
/// are the instructions run under the next block's condition and the
/// address past them.
///
/// # Arguments
///
/// * `p` - The loaded image, decoded from the block's start.
/// * `b` - The block.
fn ends_unbranched(p: &Program, b: &BasicBlock) -> bool {
    if p.arch.isa() != Some(crate::isa::Isa::A32) {
        return false;
    }
    let mut it = crate::isa::a32::ItState::default();
    let (mut va, mut last) = (b.start, None);
    while va < b.end {
        let Some(i) = crate::analysis::a32::decode(p, va, &mut it) else {
            return false;
        };
        if i.next() <= va {
            return false;
        }
        va = i.next();
        last = Some(i.flow());
    }
    last == Some(crate::isa::a32::Flow::Next)
}

/// Returns whether an x86 conditional block ends in a transaction's
/// `xbegin`, `xend` or `xabort`, whose edges test no condition the listing
/// shows.
///
/// A conditional jump always names its target, so a conditional block with
/// one successor is an `xend` or `xabort` and needs no decoding; one with
/// two is decoded to tell an `xbegin` from a `jcc`.
///
/// # Arguments
///
/// * `p` - The loaded image, decoded from the block's start.
/// * `b` - The block.
fn ends_in_transaction(p: &Program, b: &BasicBlock) -> bool {
    let Some(crate::isa::Isa::X86 { bits }) = p.arch.isa() else {
        return false;
    };
    if b.successors.len() < 2 {
        return true;
    }
    let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
    let Some(code) = p.read_va_upto(b.start, len) else {
        return false;
    };
    let mut d = Decoder::with_ip(bits, code, b.start, DecoderOptions::NONE);
    let mut last = None;
    while d.can_decode() {
        last = Some(d.decode().flow_control());
    }
    last == Some(FlowControl::XbeginXabortXend)
}

/// Returns a block's edges: each successor with the kind of its edge, in
/// the block's successor order, the jump table's entries to one target
/// merged into one edge where the target first appears.
///
/// A conditional block's successors are its target and its fall-through:
/// the fall-through, the block's end, is not taken and the other taken.
/// On arm a block that ends in no branch is the test before instructions
/// run under a condition: they, at the block's end, are taken. An x86
/// transaction's `xbegin`, `xend` or `xabort` tests nothing shown: it falls
/// to its end and jumps to its abort handler. An indirect jump's successors
/// are cases only as far as they are its resolved table, entry by entry;
/// the block's end, when it alone follows them, or after a conditional
/// return, is not taken: an indirect jump with other successors beside its
/// end may jump to the end, and claims only jumps.
///
/// # Arguments
///
/// * `p` - The loaded image, for the instruction set and arm blocks.
/// * `a` - The analysis, for jump tables.
/// * `b` - The block.
pub(crate) fn block_edges(p: &Program, a: &Analysis, b: &BasicBlock) -> Vec<(u64, EdgeKind)> {
    let succ = b.successors.as_slice();
    let table = a
        .block_table(b)
        .map(|(_, t)| t)
        .filter(|t| b.term == BlockTerm::Indirect && succ.starts_with(t));
    let (cases, rest) = succ.split_at(table.map_or(0, <[u64]>::len));
    let mut out: Vec<(u64, EdgeKind)> = Vec::new();
    let mut slot: BTreeMap<u64, usize> = BTreeMap::new();
    for (i, &t) in cases.iter().enumerate() {
        let Ok(n) = u32::try_from(i) else { break };
        let k = *slot.entry(t).or_insert_with(|| {
            out.push((t, EdgeKind::Cases(Vec::new())));
            out.len() - 1
        });
        if let Some((_, EdgeKind::Cases(ns))) = out.get_mut(k) {
            ns.push(n);
        }
    }
    let group = b.term == BlockTerm::Cond && ends_unbranched(p, b);
    let transaction = b.term == BlockTerm::Cond && ends_in_transaction(p, b);
    let pair = rest.len() == 2 && rest.get(1) == Some(&b.end);
    out.extend(rest.iter().enumerate().map(|(i, &t)| {
        let (fall, first) = (t == b.end, i == 0);
        let kind = match b.term {
            BlockTerm::Cond if transaction && fall => EdgeKind::Fall,
            BlockTerm::Cond if transaction => EdgeKind::Jump,
            BlockTerm::Cond if group && fall => EdgeKind::Taken,
            BlockTerm::Cond if group => EdgeKind::NotTaken,
            BlockTerm::Cond | BlockTerm::Jmp if pair && first => EdgeKind::Taken,
            BlockTerm::Cond | BlockTerm::Jmp if pair => EdgeKind::NotTaken,
            BlockTerm::Cond if fall => EdgeKind::NotTaken,
            BlockTerm::Cond => EdgeKind::Taken,
            BlockTerm::Ret if fall => EdgeKind::NotTaken,
            BlockTerm::Indirect if fall && rest.len() == 1 => EdgeKind::NotTaken,
            BlockTerm::Fall | BlockTerm::Call => EdgeKind::Fall,
            BlockTerm::Jmp | BlockTerm::Indirect | BlockTerm::Ret | BlockTerm::Invalid => {
                EdgeKind::Jump
            }
        };
        (t, kind)
    }));
    out
}

/// Returns the blocks a [`Cfg`] draws, in address order.
///
/// Every block of a function of at most [`CFG_NODES_MAX`], else that many:
/// those the entry reaches first breadth first, then the rest in address
/// order.
///
/// # Arguments
///
/// * `f` - The function.
fn drawn(f: &Function) -> Vec<&BasicBlock> {
    let at = |va: u64| f.blocks.binary_search_by_key(&va, |b| b.start).ok();
    let mut keep = vec![f.blocks.len() <= CFG_NODES_MAX; f.blocks.len()];
    let mut kept = if keep.first() == Some(&true) {
        keep.len()
    } else {
        0
    };
    let mut queue = std::collections::VecDeque::new();
    if let Some(i) = at(f.entry).filter(|_| kept == 0) {
        keep[i] = true;
        kept = 1;
        queue.push_back(i);
    }
    while let Some(i) = queue.pop_front() {
        for &s in &f.blocks[i].successors {
            if let Some(j) = at(s).filter(|&j| kept < CFG_NODES_MAX && !keep[j]) {
                keep[j] = true;
                kept += 1;
                queue.push_back(j);
            }
        }
    }
    for k in keep.iter_mut().filter(|k| !**k) {
        if kept >= CFG_NODES_MAX {
            break;
        }
        *k = true;
        kept += 1;
    }
    f.blocks
        .iter()
        .zip(&keep)
        .filter_map(|(b, &k)| k.then_some(b))
        .collect()
}

/// Returns a function's control-flow graph: its blocks as rows of their
/// listing and its successor edges by kind, the back edges marked.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the listing.
/// * `a` - The analysis.
/// * `o` - User names and comments the listing shows.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The graph, cut to [`CFG_NODES_MAX`] blocks and [`CFG_EDGES_MAX`] edges.
///
/// # Errors
///
/// When no function starts at `entry`, it has no listing (no disassembler
/// for the architecture), or a block shows no row of the listing, which is
/// a defect of the listing, never guessed around.
pub fn cfg(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> anyhow::Result<Arc<Cfg>> {
    let f = a
        .function(entry)
        .with_context(|| format!("no function starts at {entry:#x}"))?;
    let shown = drawn(f);
    let starts: Vec<u64> = shown.iter().map(|b| b.start).collect();
    let rows = (CFG_ROWS_MAX, CFG_LISTED_MAX);
    let (listing, short) = blocks_view(p, a, o, entry, Bytes::Shown, &starts, rows)
        .with_context(|| format!("no listing of the function at {entry:#x}"))?;
    let firsts: Vec<Option<usize>> = starts.iter().map(|&s| listing.line_of(s)).collect();
    let nodes = shown
        .iter()
        .zip(firsts.iter().copied())
        .enumerate()
        .map(|(k, (b, first))| {
            let first = first.with_context(|| {
                format!(
                    "block {:#x} of the function at {entry:#x} shows no row of its listing",
                    b.start
                )
            })?;
            let limit = firsts.get(k + 1).copied().flatten();
            let shortened = short.binary_search(&b.start).is_ok();
            let lines = block_lines(&listing, b, first, limit, shortened);
            Ok(Node {
                start: b.start,
                end: b.end,
                term: b.term,
                lines,
                shortened,
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let index = |va: u64| starts.binary_search(&va).ok();
    let (mut edges, mut edges_total) = (Vec::new(), 0usize);
    for (from, b) in shown.iter().enumerate() {
        for (s, kind) in block_edges(p, a, b) {
            let Some(to) = index(s) else { continue };
            edges_total += 1;
            if edges.len() < CFG_EDGES_MAX {
                edges.push(Edge {
                    from,
                    to,
                    kind,
                    back: false,
                });
            }
        }
    }
    mark_back_edges(nodes.len(), index(entry).unwrap_or(0), &mut edges);
    let cut = Cut {
        shown: shown.len(),
        total: f.blocks.len(),
        edges_shown: edges.len(),
        edges_total,
        shortened: short.len(),
    };
    let cut = (cut.shown < cut.total || cut.edges_shown < cut.edges_total || cut.shortened > 0)
        .then_some(cut);
    Ok(Arc::new(Cfg {
        listing: Arc::new(listing),
        nodes,
        edges,
        cut,
    }))
}

/// Returns the rows of a listing that show a block's instructions.
///
/// The rows run from the block's first instruction to its last, rows
/// between that show none (a comment) included, and stop before the next
/// listed block's first row, so a block another overlaps keeps only its
/// own rows.
///
/// # Arguments
///
/// * `listing` - The function's listing.
/// * `b` - The block.
/// * `first` - The row of the block's first instruction.
/// * `limit` - The next listed block's first row, if any.
/// * `cut` - Whether the block was cut short, so its last row is the
///   `// ... N more bytes` one after its last instruction.
fn block_lines(
    listing: &View,
    b: &BasicBlock,
    first: usize,
    limit: Option<usize>,
    cut: bool,
) -> Range<usize> {
    let mut last = first;
    for i in first..limit.unwrap_or(listing.lines()) {
        match listing.address(i) {
            Some(va) if (b.start..b.end).contains(&va) => last = i,
            Some(_) => break,
            None => {}
        }
    }
    first..last.saturating_add(1).saturating_add(usize::from(cut))
}

/// Where a node stands in the walk of [`mark_back_edges`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Walk {
    /// Not reached yet.
    New,
    /// On the walk's stack.
    Open,
    /// Left, every successor walked.
    Done,
}

/// Marks the edges that close a cycle.
///
/// A depth-first walk from the root takes each node's successors in their
/// stored order, then walks again from each node it did not reach, in
/// address order; an edge to a node on the walk's stack is a back edge.
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
/// * `edges` - The edges, grouped by source in increasing order; each
///   `back` is set.
fn mark_back_edges(n: usize, root: usize, edges: &mut [Edge]) {
    let mut starts = vec![0usize; n.saturating_add(1)];
    for e in edges.iter() {
        if let Some(s) = starts.get_mut(e.from.saturating_add(1)) {
            *s += 1;
        }
    }
    for i in 1..starts.len() {
        starts[i] += starts[i - 1];
    }
    let mut state = vec![Walk::New; n];
    let mut stack: Vec<(usize, usize)> = Vec::new();
    for r in std::iter::once(root).chain(0..n) {
        if state.get(r) != Some(&Walk::New) {
            continue;
        }
        state[r] = Walk::Open;
        stack.push((r, starts[r]));
        while let Some(top) = stack.last_mut() {
            let (v, k) = *top;
            if k >= starts[v + 1] {
                state[v] = Walk::Done;
                stack.pop();
                continue;
            }
            top.1 += 1;
            let Some(e) = edges.get_mut(k) else { continue };
            match state.get(e.to) {
                Some(Walk::Open) => e.back = true,
                Some(Walk::New) => {
                    state[e.to] = Walk::Open;
                    stack.push((e.to, starts[e.to]));
                }
                Some(Walk::Done) | None => {}
            }
        }
    }
}
