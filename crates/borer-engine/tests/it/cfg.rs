//! A function's control-flow graph as a typed value ([`cfg`]): each block a
//! node over rows of its listing, each successor edge named by what takes
//! it, the back edges marked.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use crate::common::fixture;
use crate::raw::image;

use borer_engine::analysis::render::{
    CFG_EDGES_MAX, CFG_LISTED_MAX, CFG_NODES_MAX, CFG_ROWS_MAX, EdgeKind, cfg,
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

/// Each node of every fixture function covers exactly the listing rows
/// whose instruction lies in its block, from its first row to its last.
#[test]
fn each_node_covers_exactly_the_rows_of_its_block() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for f in &a.functions {
        let g = cfg(&p, &a, &o, f.entry).expect("graph");
        let v = &g.listing;
        for n in &g.nodes {
            let inside = |i: usize| {
                v.address(i)
                    .is_some_and(|va| (n.start..n.end).contains(&va))
            };
            let rows: Vec<usize> = (0..v.lines()).filter(|&i| inside(i)).collect();
            let shown: Vec<usize> = n
                .lines
                .clone()
                .filter(|&i| v.address(i).is_some())
                .collect();
            assert_eq!(rows, shown, "{:#x} block {:#x}", f.entry, n.start);
            assert!(inside(n.lines.start), "{:#x} block {:#x}", f.entry, n.start);
            assert!(
                inside(n.lines.end - 1),
                "{:#x} block {:#x}",
                f.entry,
                n.start
            );
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
}
