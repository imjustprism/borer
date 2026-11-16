//! A function's control-flow graph as a typed value ([`cfg`]): each block a
//! node over rows of its listing, each successor edge named by what takes
//! it, the back edges marked.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use crate::common::fixture;
use crate::drawn::{cfg_digest, check, digest, graph_of, rows};
use crate::raw::image;

use borer_engine::analysis::render::{
    CFG_EDGES_MAX, CFG_LISTED_MAX, CFG_NODES_MAX, CFG_ROWS_MAX, Drawing, EdgeKind, Graph,
    GraphEdge, LAYOUT_DUMMIES_PER_NODE, Route, Routed, cfg, layout,
};
use borer_engine::analysis::{Analysis, BasicBlock, BlockTerm, Overlay};
use borer_engine::program::{Arch, Program, Section};

/// Where the hand-built functions' code starts.
const TEXT: u64 = 0x401000;

/// Builds a function of one-byte blocks over `nop`s from [`TEXT`], ending
/// in a `ret`.
///
/// # Arguments
///
/// * `blocks` - Each block's terminator and successor block numbers.
fn one_byte_blocks(blocks: &[(BlockTerm, Vec<u64>)]) -> (Program, Analysis) {
    blocks_from(TEXT, blocks)
}

/// Builds a function of one-byte blocks over `nop`s from `base`, ending in
/// a `ret`, entered at [`TEXT`].
///
/// Discovery finds one function at [`TEXT`]; its blocks are then replaced
/// by `blocks`, each `(term, successors)` a one-byte block in address
/// order from `base`, its successors given as block numbers.
///
/// # Arguments
///
/// * `base` - The first block's address, at most [`TEXT`].
/// * `blocks` - Each block's terminator and successor block numbers.
fn blocks_from(base: u64, blocks: &[(BlockTerm, Vec<u64>)]) -> (Program, Analysis) {
    let len = u64::try_from(blocks.len()).expect("fits") + 1;
    let mut bytes = vec![0x90u8; usize::try_from(len).expect("fits")];
    if let Some(last) = bytes.last_mut() {
        *last = 0xc3;
    }
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400000,
        Some(TEXT),
        vec![Section::mapped(".text", base, 0, len, false, true)],
    );
    let mut a = Analysis::compute(&p);
    let f = a
        .functions
        .iter_mut()
        .find(|f| f.entry == TEXT)
        .expect("a function at the entry");
    f.blocks = blocks
        .iter()
        .zip(base..)
        .map(|((term, succ), start)| BasicBlock {
            start,
            end: start + 1,
            term: *term,
            successors: succ.iter().map(|&s| base + s).collect(),
        })
        .collect();
    (p, a)
}

/// Each edge is named by what takes it, and the loop's is the back edge.
///
/// A conditional block's two edges are taken then not taken, an indirect
/// jump through its resolved table has one edge per target listing its
/// entries, straight-line flow falls, a jump jumps, and the loop's one edge back to the entry is
/// the only back edge.
///
/// Blocks 0 and 3 are conditional (3 loops back to 0), 1 jumps through a
/// three-entry table to 2, 4 and 2 again, 2 falls into 3, 4 jumps to 5,
/// which returns.
#[test]
fn each_edge_is_named_by_what_takes_it_and_the_loop_edge_is_back() {
    let (p, mut a) = one_byte_blocks(&[
        (BlockTerm::Cond, vec![3, 1]),
        (BlockTerm::Indirect, vec![2, 4, 2]),
        (BlockTerm::Fall, vec![3]),
        (BlockTerm::Cond, vec![0, 4]),
        (BlockTerm::Jmp, vec![5]),
        (BlockTerm::Ret, vec![]),
    ]);
    a.jump_tables
        .insert(TEXT + 1, vec![TEXT + 2, TEXT + 4, TEXT + 2]);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let got: Vec<(usize, usize, EdgeKind, bool)> = g
        .edges
        .iter()
        .map(|e| (e.from, e.to, e.kind.clone(), e.back))
        .collect();
    assert_eq!(
        got,
        [
            (0, 3, EdgeKind::Taken, false),
            (0, 1, EdgeKind::NotTaken, false),
            (1, 2, EdgeKind::Cases(vec![0, 2]), false),
            (1, 4, EdgeKind::Cases(vec![1]), false),
            (2, 3, EdgeKind::Fall, false),
            (3, 0, EdgeKind::Taken, true),
            (3, 4, EdgeKind::NotTaken, false),
            (4, 5, EdgeKind::Jump, false),
        ]
    );
    assert_eq!(g.cut, None);
    check(&graph_of(&g, TEXT), &g.layout()).expect("a clear drawing");
}

/// An indirect jump whose successors are not its table's entries claims no
/// case: its edges are plain jumps.
#[test]
fn an_indirect_jump_no_table_explains_claims_no_case() {
    let (p, a) = one_byte_blocks(&[
        (BlockTerm::Indirect, vec![1, 2]),
        (BlockTerm::Ret, vec![]),
        (BlockTerm::Ret, vec![]),
    ]);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    assert!(
        g.edges.iter().all(|e| e.kind == EdgeKind::Jump),
        "{:?}",
        g.edges
    );
}

/// Each node of every fixture graph covers its block's rows, and the graph
/// draws clear.
///
/// Each node of every fixture function covers exactly the listing rows
/// whose instruction lies in its block, from its first row to its last,
/// and every graph draws clear: boxes apart, edges down, routes from
/// bottoms to tops through no box and along no other route, the crossings
/// it shows those it reports.
#[test]
fn each_node_covers_the_rows_of_its_block_and_draws_clear() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for f in &a.functions {
        let g = cfg(&p, &a, &o, f.entry).expect("graph");
        if let Err(e) = rows(&g).and_then(|()| check(&graph_of(&g, f.entry), &g.layout())) {
            panic!("{:#x}: {e}", f.entry);
        }
    }
}

/// A function of a hundred thousand blocks is cut to the cap in address
/// order, and the graph says so.
#[test]
fn a_function_past_the_cap_is_cut_and_says_so() {
    let blocks: Vec<(BlockTerm, Vec<u64>)> = (1..=100_000)
        .map(|next| (BlockTerm::Fall, vec![next]))
        .collect();
    let (p, a) = one_byte_blocks(&blocks);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let cut = g.cut.expect("a cut");
    assert_eq!((cut.shown, cut.total), (CFG_NODES_MAX, 100_000));
    assert_eq!(g.nodes.len(), CFG_NODES_MAX);
    assert_eq!(g.edges.len(), CFG_NODES_MAX - 1);
    assert!(g.nodes.windows(2).all(|w| w[0].end == w[1].start));
    let v = &g.listing;
    let listed = (0..v.lines()).filter(|&i| v.address(i).is_some()).count();
    assert_eq!(
        listed, CFG_NODES_MAX,
        "the listing shows only the drawn blocks"
    );
    assert_eq!(g.layout().at.len(), CFG_NODES_MAX);
    check(&graph_of(&g, TEXT), &g.layout()).expect("a clear drawing");
}

/// A function cut to the cap draws the blocks its entry reaches first,
/// whatever lies before them by address: the entry, a cap's worth of
/// blocks below it nothing reaches, and the block the entry jumps to.
#[test]
fn a_cut_keeps_the_blocks_the_entry_reaches() {
    let below = u64::try_from(CFG_NODES_MAX).expect("fits") + 10;
    let mut blocks: Vec<(BlockTerm, Vec<u64>)> = (1..=below)
        .map(|next| (BlockTerm::Fall, vec![next]))
        .collect();
    blocks.push((BlockTerm::Jmp, vec![below + 1]));
    blocks.push((BlockTerm::Ret, vec![]));
    let (p, a) = blocks_from(TEXT - below, &blocks);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let at = |va: u64| g.nodes.iter().position(|n| n.start == va);
    let (entry, next) = (
        at(TEXT).expect("the entry"),
        at(TEXT + 1).expect("its jump"),
    );
    assert!(
        g.edges.iter().any(|e| (e.from, e.to) == (entry, next)),
        "{:?}",
        g.cut
    );
    assert_eq!(g.nodes.len(), CFG_NODES_MAX);
}

/// A jump table's entries to one block are one edge listing them, and a
/// graph whose drawn blocks have more edges than the cap keeps the cap and
/// says how many it left out.
#[test]
fn table_entries_merge_and_edges_past_the_cap_are_counted() {
    let (p, mut a) = one_byte_blocks(&[
        (BlockTerm::Indirect, (0..4096).map(|i| 1 + i % 2).collect()),
        (BlockTerm::Ret, vec![]),
        (BlockTerm::Ret, vec![]),
    ]);
    a.jump_tables
        .insert(TEXT, (0..4096).map(|i| TEXT + 1 + i % 2).collect());
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let even: Vec<u32> = (0..4096).step_by(2).collect();
    let odd: Vec<u32> = (1..4096).step_by(2).collect();
    let kinds: Vec<(usize, EdgeKind)> = g.edges.iter().map(|e| (e.to, e.kind.clone())).collect();
    assert_eq!(
        kinds,
        [(1, EdgeKind::Cases(even)), (2, EdgeKind::Cases(odd))]
    );
    assert_eq!(g.cut, None);

    let n = u64::try_from(CFG_NODES_MAX).expect("fits");
    let wide: Vec<(BlockTerm, Vec<u64>)> = (0..n)
        .map(|i| (BlockTerm::Indirect, (1..=8).map(|k| (i + k) % n).collect()))
        .collect();
    let (p, mut a) = one_byte_blocks(&wide);
    for (i, (_, targets)) in (0..n).zip(&wide) {
        a.jump_tables
            .insert(TEXT + i, targets.iter().map(|&t| TEXT + t).collect());
    }
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    assert_eq!(g.edges.len(), CFG_EDGES_MAX);
    let cut = g.cut.expect("a cut");
    assert_eq!(
        (cut.shown, cut.total, cut.edges_shown, cut.edges_total),
        (
            CFG_NODES_MAX,
            CFG_NODES_MAX,
            CFG_EDGES_MAX,
            CFG_NODES_MAX * 8
        )
    );
}

/// Returns `cmp r0, #0; popeq {r4, pc}; mov r0, #1; bx lr` as an arm
/// image at 0x401000, analyzed: a test, then a return run under its
/// condition.
fn arm_run() -> (Program, Analysis) {
    let code = [
        0x00, 0x00, 0x50, 0xe3, // ASM: cmp r0, #0
        0x10, 0x80, 0xbd, 0x08, // ASM: popeq {r4, pc}
        0x01, 0x00, 0xa0, 0xe3, // ASM: mov r0, #1
        0x1e, 0xff, 0x2f, 0xe1, // ASM: bx lr
    ];
    let p = image(Arch::Arm, &code, &[]);
    let a = Analysis::compute(&p);
    (p, a)
}

/// On arm a conditional run's test is taken into the run.
///
/// The test before an instruction run under a condition is taken
/// into that instruction, the one the listing shows the condition on, and
/// not taken past it: `cmp r0, #0; popeq {r4, pc}; mov r0, #1; bx lr`.
#[test]
fn an_arm_conditional_run_is_taken_when_its_condition_holds() {
    let (p, a) = arm_run();
    let g = cfg(&p, &a, &Overlay::default(), 0x401000).expect("graph");
    let at = |va: u64| g.nodes.iter().position(|n| n.start == va).expect("a node");
    let kinds: Vec<(usize, usize, EdgeKind)> = g
        .edges
        .iter()
        .filter(|e| e.from == at(0x401000))
        .map(|e| (e.from, e.to, e.kind.clone()))
        .collect();
    assert_eq!(
        kinds,
        [
            (at(0x401000), at(0x401008), EdgeKind::NotTaken),
            (at(0x401000), at(0x401004), EdgeKind::Taken),
        ]
    );
}

/// A block's end is not taken only after a test, and a transaction falls.
///
/// A conditional return falls to its end not taken, an indirect jump's
/// end after its table's entries is not taken, and an x86 conditional
/// block with no successor but its end, a transaction's `xend` or
/// `xabort`, falls.
#[test]
fn a_guarded_return_or_jump_and_a_transaction_end_are_named() {
    let (p, mut a) = one_byte_blocks(&[
        (BlockTerm::Ret, vec![1]),
        (BlockTerm::Indirect, vec![3, 2]),
        (BlockTerm::Cond, vec![3]),
        (BlockTerm::Ret, vec![]),
    ]);
    a.jump_tables.insert(TEXT + 1, vec![TEXT + 3]);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let got: Vec<(usize, usize, EdgeKind)> = g
        .edges
        .iter()
        .map(|e| (e.from, e.to, e.kind.clone()))
        .collect();
    assert_eq!(
        got,
        [
            (0, 1, EdgeKind::NotTaken),
            (1, 3, EdgeKind::Cases(vec![0])),
            (1, 2, EdgeKind::NotTaken),
            (2, 3, EdgeKind::Fall),
        ]
    );
}

/// Returns an edge laid out down.
///
/// # Arguments
///
/// * `from` - The source node.
/// * `to` - The target node.
fn down(from: usize, to: usize) -> GraphEdge {
    GraphEdge {
        from,
        to,
        route: Route::Down,
    }
}

/// A seeded generator of graphs: a linear congruential sequence, so the
/// graphs are the same on every host.
#[derive(Debug)]
struct Lcg(u64);

impl Lcg {
    /// Returns the next number below `n`.
    ///
    /// # Arguments
    ///
    /// * `n` - The bound, above zero.
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }

    /// Returns a graph: up to `nodes` boxes, each with up to three edges to
    /// later nodes, some edges back to earlier ones or itself, routed up,
    /// and nodes no edge reaches.
    ///
    /// # Arguments
    ///
    /// * `nodes` - Most nodes.
    fn graph(&mut self, nodes: u64) -> Graph {
        let n = usize::try_from(1 + self.below(nodes)).expect("fits");
        let mut sizes = Vec::with_capacity(n);
        let mut edges = Vec::new();
        for u in 0..n {
            let w = u32::try_from(3 + self.below(40)).expect("fits");
            let h = u32::try_from(3 + self.below(10)).expect("fits");
            sizes.push((w, h));
            for _ in 0..self.below(4) {
                let span = usize::try_from(1 + self.below(6)).expect("fits");
                if u + span < n {
                    edges.push(down(u, u + span));
                }
            }
            if self.below(8) == 0 {
                let to =
                    usize::try_from(self.below(u64::try_from(u + 1).expect("fits"))).expect("fits");
                edges.push(GraphEdge {
                    from: u,
                    to,
                    route: Route::Up,
                });
            }
        }
        Graph {
            sizes,
            edges,
            root: 0,
        }
    }
}

/// Seeded random graphs, a self loop, parallel edges and unreachable nodes
/// among them, draw clear and the same twice, and reduction never adds a
/// crossing.
#[test]
fn random_graphs_draw_clear_and_never_cross_more() {
    let mut rng = Lcg(7);
    for i in 0..300 {
        let g = rng.graph(if i % 10 == 0 { 400 } else { 60 });
        let l = layout(&g);
        if let Err(e) = check(&g, &l) {
            panic!("graph {i} ({} nodes): {e}", g.sizes.len());
        }
        assert_eq!(digest(&g, &layout(&g)), digest(&g, &l), "graph {i}");
    }
}

/// Two edges that cross in the input order, `r -> a, r -> b, a -> d,
/// b -> c`, are uncrossed, and the drawing shows the crossings it
/// reports, their runs on lines of their own.
#[test]
fn crossed_edges_are_uncrossed_on_lines_of_their_own() {
    let g = Graph {
        sizes: vec![(6, 3); 5],
        edges: vec![down(0, 1), down(0, 2), down(1, 4), down(2, 3)],
        root: 0,
    };
    let l = layout(&g);
    check(&g, &l).expect("a clear drawing");
    assert_eq!((l.crossings_before, l.crossings), (1, 0));
}

/// Two edges from one wide node to the two small nodes under it run on
/// lines stacked so neither crosses the other, and the drawing's own
/// segments show the crossings it reports: none.
#[test]
fn runs_from_one_node_are_stacked_not_to_cross() {
    let g = Graph {
        sizes: vec![(40, 1), (4, 1), (4, 1), (60, 1)],
        edges: vec![down(0, 1), down(0, 2), down(0, 3)],
        root: 0,
    };
    let l = layout(&g);
    check(&g, &l).expect("a clear drawing");
    assert_eq!(l.crossings, 0);
}

/// Runs that would meet at a column cross there, and the drawing reports
/// them.
///
/// Two nodes each to the same two nodes below them, `r -> u1, r -> u2`,
/// `u1 -> l1, u1 -> l2, u2 -> l1, u2 -> l2`: the runs that would meet at a
/// column cross there instead, and the drawing shows the crossings it
/// reports.
#[test]
fn runs_meeting_at_a_column_cross_once() {
    let g = Graph {
        sizes: vec![(6, 3); 5],
        edges: vec![
            down(0, 1),
            down(0, 2),
            down(1, 3),
            down(1, 4),
            down(2, 3),
            down(2, 4),
        ],
        root: 0,
    };
    let l = layout(&g);
    check(&g, &l).expect("a clear drawing");
}

/// A node with more edges than columns is drawn wide enough to give each
/// its own port on its layer's parity.
#[test]
fn a_node_too_narrow_for_its_edges_is_widened() {
    let g = Graph {
        sizes: vec![(2, 3), (2, 3), (2, 3), (2, 3), (2, 3)],
        edges: (1..5).map(|v| down(0, v)).collect(),
        root: 0,
    };
    let l = layout(&g);
    check(&g, &l).expect("a clear drawing");
    assert_eq!(l.sizes[0], (10, 3));
    let ports: std::collections::BTreeSet<i32> = l.routes.iter().map(|r| r[0].0).collect();
    assert_eq!(ports.len(), 4);
}

/// Runs going left and right keep their verticals apart.
///
/// A run going left that leaves down the column a run going right comes
/// in at would share a vertical with it: two upper nodes, each to both of
/// two lower ones of other widths, with a long edge past them, keep every
/// route's verticals apart and show the crossings they report.
#[test]
fn runs_leaving_and_entering_one_column_never_meet() {
    for widths in [[6, 6, 6, 6, 6], [4, 9, 5, 12, 3], [11, 3, 7, 3, 11]] {
        let g = Graph {
            sizes: widths.iter().map(|&w| (w, 3)).chain([(6, 3)]).collect(),
            edges: vec![
                down(0, 1),
                down(0, 2),
                down(1, 3),
                down(1, 4),
                down(2, 4),
                down(2, 3),
                down(0, 5),
                down(3, 5),
            ],
            root: 0,
        };
        let l = layout(&g);
        if let Err(e) = check(&g, &l) {
            panic!("{widths:?}: {e}");
        }
    }
}

/// Edges naming nodes the graph does not have get no route, and a root it
/// does not have counts as the first node; nothing panics.
#[test]
fn a_graph_naming_nodes_it_lacks_still_draws() {
    let g = Graph {
        sizes: vec![(4, 3), (4, 3)],
        edges: vec![
            down(0, 1),
            down(0, 9),
            GraphEdge {
                from: 9,
                to: 0,
                route: Route::Up,
            },
        ],
        root: 5,
    };
    let l = layout(&g);
    assert_eq!(
        l.routed,
        [Routed::Layered, Routed::Missing, Routed::Missing]
    );
    assert!(l.routes[1].is_empty() && l.routes[2].is_empty());
    assert!(!l.routes[0].is_empty());
    assert_eq!(layout(&Graph::default()), Drawing::default());
}

/// Long and dense graphs lay out in seconds, and a fan spends its budget.
///
/// A chain of ten thousand blocks and ten thousand blocks each jumping to
/// the next eight lay out in seconds, even unoptimized, and a fan from one
/// node to every node of a long chain spends its budget of added nodes and
/// says how many edges it routed on the side instead.
#[test]
#[expect(clippy::disallowed_methods, reason = "the bound is a time")]
fn long_and_dense_graphs_lay_out_in_seconds() {
    let n = 10_000;
    let chain = Graph {
        sizes: vec![(20, 5); n],
        edges: (1..n).map(|v| down(v - 1, v)).collect(),
        root: 0,
    };
    let dense = Graph {
        sizes: vec![(20, 5); n],
        edges: (0..n)
            .flat_map(|u| (u + 1..n.min(u + 9)).map(move |v| down(u, v)))
            .collect(),
        root: 0,
    };
    let m = 2000;
    let fan = Graph {
        sizes: vec![(20, 5); m],
        edges: (1..m)
            .map(|v| down(v - 1, v))
            .chain((2..m).map(|v| down(0, v)))
            .collect(),
        root: 0,
    };
    for (name, g) in [("chain", &chain), ("dense", &dense), ("fan", &fan)] {
        let started = std::time::Instant::now();
        let l = layout(g);
        let took = started.elapsed();
        assert!(took.as_secs() < 20, "{name} took {took:?}");
        if let Err(e) = check(g, &l) {
            panic!("{name}: {e}");
        }
    }
    let l = layout(&fan);
    assert!(
        l.sided > 0,
        "{LAYOUT_DUMMIES_PER_NODE} added nodes per node never ran out"
    );
    assert_eq!(
        l.routed.iter().filter(|&&r| r == Routed::Side).count(),
        l.sided
    );
}

/// A function whose long edges would take more added nodes than the budget
/// draws them on the side and its drawing says how many: one block jumping
/// through a table to each of six hundred chained blocks.
#[test]
fn a_graph_past_the_budget_of_added_nodes_says_so() {
    let n = 600;
    let mut blocks: Vec<(BlockTerm, Vec<u64>)> = vec![(BlockTerm::Indirect, (1..n).collect())];
    blocks.extend((1..n).map(|i| (BlockTerm::Fall, vec![i + 1])));
    let (p, mut a) = one_byte_blocks(&blocks);
    a.jump_tables
        .insert(TEXT, (1..n).map(|i| TEXT + i).collect());
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    assert!(g.layout().sided > 0);
    assert_eq!(g.cut, None, "routing on the side leaves nothing out");
    check(&graph_of(&g, TEXT), &g.layout()).expect("a clear drawing");
}

/// Two graphs drawn alike but for one edge's kind digest apart.
#[test]
fn an_edge_kind_changes_the_digest() {
    let (p, a) = one_byte_blocks(&[(BlockTerm::Jmp, vec![1]), (BlockTerm::Ret, vec![])]);
    let (q, b) = one_byte_blocks(&[(BlockTerm::Fall, vec![1]), (BlockTerm::Ret, vec![])]);
    let o = Overlay::default();
    let (g, h) = (
        cfg(&p, &a, &o, TEXT).expect("graph"),
        cfg(&q, &b, &o, TEXT).expect("graph"),
    );
    assert_eq!(g.layout(), h.layout());
    assert_ne!(cfg_digest(&g, TEXT), cfg_digest(&h, TEXT));
}

/// A block another overlaps keeps only its own rows: `jmp -1` at 0x401000
/// jumps into its own second byte, where `inc eax; ret` decodes.
#[test]
fn an_overlapped_block_keeps_only_its_own_rows() {
    let p = image(Arch::X86_64, &[0xeb, 0xff, 0xc0, 0xc3], &[]);
    let a = Analysis::compute(&p);
    let g = cfg(&p, &a, &Overlay::default(), 0x401000).expect("graph");
    let jmp = g
        .nodes
        .iter()
        .find(|n| n.start == 0x401000)
        .expect("the jmp");
    assert_eq!(jmp.lines.len(), 1, "{:?}", g.nodes);
}

/// A block of a hundred thousand instructions lists the first
/// [`CFG_ROWS_MAX`] and one row saying how many bytes it left out, and the
/// graph says it shortened a block.
#[test]
fn a_long_block_is_listed_to_the_row_cap() {
    let mut code = vec![0x90u8; 100_001];
    if let Some(last) = code.last_mut() {
        *last = 0xc3;
    }
    let len = u64::try_from(code.len()).expect("fits");
    let p = Program::raw(
        code,
        Arch::X86_64,
        0x400000,
        Some(TEXT),
        vec![Section::mapped(".text", TEXT, 0, len, false, true)],
    );
    let a = Analysis::compute(&p);
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let n = &g.nodes[0];
    assert_eq!(n.lines.len(), CFG_ROWS_MAX + 1);
    let marker = g.listing.line(n.lines.end - 1).expect("a row");
    assert!(marker.contains("more bytes"), "{marker}");
    assert_eq!(g.cut.map(|c| c.shortened), Some(1));
}

/// An x86 transaction's `xbegin` tests no condition the listing shows: it
/// falls into the transaction and jumps to its abort handler, unlabelled.
#[test]
fn a_transaction_begin_is_neither_taken_nor_not_taken() {
    let code = [
        0xc7, 0xf8, 0x01, 0x00, 0x00, 0x00, // ASM: xbegin 0x401007
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let g = cfg(&p, &a, &Overlay::default(), 0x401000).expect("graph");
    let at = |va: u64| g.nodes.iter().position(|n| n.start == va).expect("a node");
    let got: Vec<(usize, EdgeKind)> = g
        .edges
        .iter()
        .filter(|e| e.from == at(0x401000))
        .map(|e| (e.to, e.kind.clone()))
        .collect();
    assert_eq!(
        got,
        [
            (at(0x401007), EdgeKind::Jump),
            (at(0x401006), EdgeKind::Fall)
        ]
    );
}

/// A graph lists at most [`CFG_LISTED_MAX`] instructions in all: of 2048
/// blocks of 256 `nop`s the first take the whole budget, and every later
/// one shows its first instruction and the bytes it leaves out.
#[test]
fn a_graph_lists_at_most_its_total_of_rows() {
    let (n, each) = (2048u64, 256u64);
    let len = n * each + 1;
    let mut code = vec![0x90u8; usize::try_from(len).expect("fits")];
    if let Some(last) = code.last_mut() {
        *last = 0xc3;
    }
    let p = Program::raw(
        code,
        Arch::X86_64,
        0x400000,
        Some(TEXT),
        vec![Section::mapped(".text", TEXT, 0, len, false, true)],
    );
    let mut a = Analysis::compute(&p);
    let f = a
        .functions
        .iter_mut()
        .find(|f| f.entry == TEXT)
        .expect("a function at the entry");
    f.blocks = (0..n)
        .map(|i| BasicBlock {
            start: TEXT + i * each,
            end: TEXT + (i + 1) * each,
            term: BlockTerm::Fall,
            successors: [TEXT + (i + 1) * each].into_iter().collect(),
        })
        .collect();
    let g = cfg(&p, &a, &Overlay::default(), TEXT).expect("graph");
    let v = &g.listing;
    let listed = (0..v.lines()).filter(|&i| v.address(i).is_some()).count();
    let full = CFG_LISTED_MAX / CFG_ROWS_MAX;
    assert_eq!(listed, CFG_LISTED_MAX + (CFG_NODES_MAX - full));
    assert_eq!(g.cut.map(|c| c.shortened), Some(CFG_NODES_MAX - full));
    assert!(
        g.nodes
            .iter()
            .skip(full)
            .all(|n| n.shortened && n.lines.len() == 2)
    );
    rows(&g).expect("rows of the shortened blocks");
    check(&graph_of(&g, TEXT), &g.layout()).expect("a clear drawing");
}

/// A graph is built once per function and names in force: asked for again,
/// it is the one kept, and nothing more is built; a failure is kept too and
/// names the address.
#[test]
fn a_graph_is_built_once_and_kept() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entry = a.functions[0].entry;
    let first = cfg(&p, &a, &o, entry).expect("graph");
    let built = a.derived.builds();
    let again = cfg(&p, &a, &o, entry).expect("graph");
    assert_eq!(a.derived.builds(), built);
    assert_eq!(first.edges, again.edges);
    assert_eq!(first.layout(), again.layout());
    let nowhere = cfg(&p, &a, &o, 0x7).expect_err("no function at 0x7");
    let built = a.derived.builds();
    assert_eq!(
        cfg(&p, &a, &o, 0x7).expect_err("still none").to_string(),
        nowhere.to_string()
    );
    assert_eq!(a.derived.builds(), built);
    assert!(nowhere.to_string().contains("0x7"), "{nowhere}");
}
