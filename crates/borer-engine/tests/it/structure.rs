//! Structural tests over generated control flow: small graphs are written as
//! machine code, decompiled, and checked against what the graph says must be
//! in the text.
//!
//! Each block marks itself twice, by storing its own number and by passing it
//! to one callee, so a block that never reaches the text is plain to see. The
//! three questions asked of every graph are whether each goto lands on a
//! label, whether every block a run can reach says its number, and whether
//! every one of those blocks writes its store.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::{cleanup, decompile, decompile_raw};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::{from_usize, lo32, saturating_usize};
use borer_engine::program::{Arch, Program, Section};
use std::collections::BTreeSet;

/// Where the generated function starts.
const CODE: u64 = 0x1000;

/// Where the jump tables sit, one per switch, in read-only data.
const TABLES: u64 = 0x8000;

/// Where the data slots sit, one per block, in writable data.
const SLOTS: u64 = 0xa000;

/// Bytes before a block's terminator: the store, the mark and the call.
const HEAD: usize = 20;

/// How a generated block ends.
#[derive(Clone, Debug)]
enum Term {
    /// `ret`.
    Ret,
    /// `jmp` to another block.
    Jmp(usize),
    /// `jb` to another block, falling through to the next one.
    Cond(usize),
    /// A second call to the callee, falling through to the next block.
    Call,
    /// A call to a function that never returns: the block has no successor,
    /// and its text ends on the call rather than a `return` or a `goto`. A
    /// loop that absorbs such a block as an exit must not pretend it breaks to
    /// the join, a shape that once left a trailing `goto` to an absorbed dup.
    Noreturn,
    /// A bounded jump through a table, defaulting to the next block.
    Switch(Vec<usize>),
}

/// The bytes of one block before its jumps are resolved.
///
/// # Arguments
///
/// * `t` - How the block ends.
///
/// # Returns
///
/// The block's machine code with zero displacements.
fn block_bytes(t: &Term) -> Vec<u8> {
    let mut b = vec![
        0xc7, 0x05, 0, 0, 0, 0, 0, 0, 0, 0, 0xb9, 0, 0, 0, 0, 0xe8, 0, 0, 0, 0,
    ];
    match t {
        Term::Ret => b.push(0xc3),
        Term::Jmp(_) => b.extend_from_slice(&[0xe9, 0, 0, 0, 0]),
        Term::Cond(_) => b.extend_from_slice(&[0x3b, 0xca, 0x0f, 0x82, 0, 0, 0, 0]),
        Term::Call | Term::Noreturn => b.extend_from_slice(&[0xe8, 0, 0, 0, 0]),
        Term::Switch(arms) => {
            let n = u8::try_from(arms.len().max(1) - 1).unwrap_or(0);
            b.extend_from_slice(&[0x83, 0xf8, n, 0x0f, 0x87, 0, 0, 0, 0]);
            b.extend_from_slice(&[0xff, 0x24, 0xc5, 0, 0, 0, 0]);
        }
    }
    b
}

/// The displacement bytes a jump or call encodes to reach its target.
///
/// A `rel32` is the distance from the end of the instruction, kept to its
/// low 32 bits: the fixture's addresses are small, so nothing is lost.
///
/// # Arguments
///
/// * `target` - Where the instruction lands.
/// * `next` - The address of the instruction that follows it.
///
/// # Returns
///
/// The four little-endian bytes of the displacement.
fn rel32(target: u64, next: u64) -> [u8; 4] {
    lo32(target.wrapping_sub(next)).to_le_bytes()
}

/// Assembles the blocks and the callee they all share.
///
/// # Arguments
///
/// * `blocks` - The graph.
///
/// # Returns
///
/// `(the blocks' bytes, their addresses, the marking callee's address, the
/// noreturn callee's address)`.
fn assemble(blocks: &[Term]) -> (Vec<Vec<u8>>, Vec<u64>, u64, u64) {
    let mut code: Vec<Vec<u8>> = blocks.iter().map(block_bytes).collect();
    let mut at = Vec::with_capacity(blocks.len());
    let mut off = CODE;
    for b in &code {
        at.push(off);
        off += b.len() as u64;
    }
    let callee = off + 0x10;
    let noreturn = callee + 0x10;
    for (i, t) in blocks.iter().enumerate() {
        let mark = u32::try_from(i + 1).unwrap_or(1);
        let slot = SLOTS + (i as u64) * 8;
        code[i][2..6].copy_from_slice(&rel32(slot, at[i] + 10));
        code[i][6..10].copy_from_slice(&mark.to_le_bytes());
        code[i][11..15].copy_from_slice(&mark.to_le_bytes());
        code[i][16..20].copy_from_slice(&rel32(callee, at[i] + HEAD as u64));
        let n = code[i].len();
        if matches!(t, Term::Switch(_)) {
            code[i][25..29].copy_from_slice(&rel32(at[(i + 1) % blocks.len()], at[i] + 29));
            let table = TABLES + (i as u64) * 0x100;
            code[i][n - 4..].copy_from_slice(&u32::try_from(table).unwrap_or(0).to_le_bytes());
            continue;
        }
        let target = match t {
            Term::Call => callee,
            Term::Noreturn => noreturn,
            Term::Jmp(d) | Term::Cond(d) => at[*d % blocks.len()],
            Term::Ret | Term::Switch(_) => continue,
        };
        code[i][n - 4..].copy_from_slice(&rel32(target, at[i] + n as u64));
    }
    (code, at, callee, noreturn)
}

/// Builds the program a graph describes: the blocks, the callee they mark
/// themselves with, the jump tables, and the slots they store into.
///
/// # Arguments
///
/// * `blocks` - The graph.
///
/// # Returns
///
/// A raw x86-64 program whose entry is the first block.
fn program(blocks: &[Term]) -> Program {
    let (code, at, callee, noreturn) = assemble(blocks);
    let mut bytes = vec![0xccu8; saturating_usize(CODE)];
    for b in &code {
        bytes.extend_from_slice(b);
    }
    bytes.resize(saturating_usize(callee), 0xcc);
    bytes.extend_from_slice(&[0x8b, 0xc1, 0xc3]);
    // The noreturn callee is `jmp $`: a self-loop the analysis reads as a
    // function that never returns, so a `Term::Noreturn` block ends there.
    bytes.resize(saturating_usize(noreturn), 0xcc);
    bytes.extend_from_slice(&[0xeb, 0xfe]);
    bytes.resize(saturating_usize(TABLES), 0xcc);
    for (i, t) in blocks.iter().enumerate() {
        let Term::Switch(arms) = t else {
            continue;
        };
        let table = saturating_usize(TABLES + (i as u64) * 0x100);
        for (k, d) in arms.iter().enumerate() {
            let off = table + k * 8;
            bytes.resize(bytes.len().max(off + 8), 0);
            bytes[off..off + 8].copy_from_slice(&at[*d % blocks.len()].to_le_bytes());
        }
    }
    bytes.resize(saturating_usize(SLOTS) + 8 * blocks.len().max(1), 0);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(CODE),
        vec![
            Section::mapped(".text", CODE, CODE, TABLES - CODE, false, true),
            Section::mapped(".rdata", TABLES, TABLES, SLOTS - TABLES, false, false),
            Section::mapped(".data", SLOTS, SLOTS, 0x1000, true, false),
        ],
    )
}

/// The blocks a run of the function can reach.
///
/// # Arguments
///
/// * `blocks` - The graph.
///
/// # Returns
///
/// Their indices, the entry included.
fn reachable(blocks: &[Term]) -> BTreeSet<usize> {
    let mut seen: BTreeSet<usize> = [0].into_iter().collect();
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        let mut go = |d: usize, work: &mut Vec<usize>| {
            if seen.insert(d) {
                work.push(d);
            }
        };
        match &blocks[b] {
            Term::Ret | Term::Noreturn => {}
            Term::Call if b + 1 < blocks.len() => go(b + 1, &mut work),
            Term::Call => {}
            Term::Jmp(d) => go(d % blocks.len(), &mut work),
            Term::Cond(d) => {
                go(d % blocks.len(), &mut work);
                if b + 1 < blocks.len() {
                    go(b + 1, &mut work);
                }
            }
            Term::Switch(arms) => {
                for d in arms {
                    go(d % blocks.len(), &mut work);
                }
                go((b + 1) % blocks.len(), &mut work);
            }
        }
    }
    seen
}

/// What the text fails to say about a graph.
///
/// # Arguments
///
/// * `blocks` - The graph.
/// * `text` - The decompilation of its entry.
///
/// # Returns
///
/// One line per broken promise: a goto without a label, a reachable block
/// whose call is missing, or one whose store is.
fn faults(blocks: &[Term], text: &str) -> Vec<String> {
    let labels: BTreeSet<&str> = text
        .lines()
        .filter_map(|l| l.trim().strip_suffix(':'))
        .filter(|l| l.starts_with("L_"))
        .collect();
    let mut out = Vec::new();
    for l in text.lines() {
        let t = l.trim();
        let target = t
            .strip_prefix("goto ")
            .or_else(|| t.rsplit_once(") goto ").map(|(_, g)| g))
            .and_then(|g| g.strip_suffix(';'))
            .filter(|g| g.starts_with("L_"));
        if let Some(g) = target
            && !labels.contains(g)
        {
            out.push(format!("{g} has no label"));
        }
    }
    for b in reachable(blocks) {
        if !text.contains(&format!("({})", b + 1)) {
            out.push(format!("block {} never calls", b + 1));
        }
        if !text.contains(&format!("g32_{:x}", SLOTS + (b as u64) * 8)) {
            out.push(format!("block {} never stores", b + 1));
        }
    }
    out
}

/// Renders a graph the way a failure message can name it.
///
/// # Arguments
///
/// * `blocks` - The graph.
///
/// # Returns
///
/// A comma-separated list such as `J3,R,R,S1-2-3`.
fn spec(blocks: &[Term]) -> String {
    blocks
        .iter()
        .map(|t| match t {
            Term::Ret => "R".to_owned(),
            Term::Call => "K".to_owned(),
            Term::Noreturn => "N".to_owned(),
            Term::Jmp(d) => format!("J{d}"),
            Term::Cond(d) => format!("C{d}"),
            Term::Switch(arms) => format!(
                "S{}",
                arms.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("-")
            ),
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// A random draw reduced to a block index below `n`.
///
/// # Arguments
///
/// * `draw` - The generator's next value.
/// * `n` - How many blocks there are.
///
/// # Returns
///
/// A value in `0..n`.
fn below(draw: u64, n: usize) -> usize {
    saturating_usize(draw % from_usize(n))
}

/// Builds one graph from a seed.
///
/// Targets favour the last blocks, which makes shared tails, and blocks
/// already passed, which makes loops.
///
/// # Arguments
///
/// * `seed` - Which graph to build.
///
/// # Returns
///
/// Between six and sixteen blocks.
fn graph(seed: u64) -> Vec<Term> {
    let mut s = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let n = 6 + (next() % 11) as usize;
    (0..n)
        .map(|i| {
            let d = match next() % 10 {
                0..=3 => n - 1 - (next() % 3) as usize,
                4 | 5 if i > 0 => below(next(), i),
                _ => below(next(), n),
            };
            if i + 1 >= n {
                return Term::Ret;
            }
            match next() % 10 {
                0 => Term::Ret,
                1 => Term::Call,
                2 => Term::Jmp(d),
                3 => {
                    let k = 2 + (next() % 3) as usize;
                    Term::Switch((0..k).map(|_| below(next(), n)).collect())
                }
                4 => Term::Noreturn,
                _ => Term::Cond(d),
            }
        })
        .collect()
}

/// A richer graph: larger and switch-heavy, with the same target bias toward
/// shared tails and back-edges, so nested switches and switch arms interleaved
/// with loop blocks by address arise often.
fn graph_rich(seed: u64) -> Vec<Term> {
    let mut s = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let n = 10 + (next() % 14) as usize;
    (0..n)
        .map(|i| {
            let d = match next() % 10 {
                0..=3 => n - 1 - (next() % 4) as usize,
                4 | 5 if i > 0 => below(next(), i),
                _ => below(next(), n),
            };
            if i + 1 >= n {
                return Term::Ret;
            }
            match next() % 9 {
                0 => Term::Ret,
                1 => Term::Call,
                2 => Term::Jmp(d),
                3 | 4 => {
                    let k = 2 + (next() % 4) as usize;
                    Term::Switch((0..k).map(|_| below(next(), n)).collect())
                }
                5 => Term::Noreturn,
                _ => Term::Cond(d),
            }
        })
        .collect()
}

/// The same invariants over larger, switch-heavy graphs.
///
/// Nested switches and switch arms interleaved with a loop's blocks by address
/// are common here; a switch arm folded into a loop that happened to span it
/// (seed 85488) hid until the corpus grew this dense. `BORER_SEARCH_SEEDS`
/// raises the count.
#[test]
fn rich_control_flow_keeps_every_block() {
    let seeds: u64 = std::env::var("BORER_SEARCH_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let o = Overlay::default();
    for seed in 0..seeds {
        let blocks = graph_rich(seed);
        let p = program(&blocks);
        let a = Analysis::compute(&p);
        let Some(text) = decompile(&p, &a, &o, CODE) else {
            continue;
        };
        let faults = faults(&blocks, &text);
        assert!(
            faults.is_empty(),
            "seed {seed} ({}): {faults:?}\n{text}",
            spec(&blocks)
        );
    }
}

/// Every goto lands, every reachable block calls, and every one stores.
///
/// The sweep is short by default so it costs a second; `BORER_SEARCH_SEEDS`
/// raises it for a hunt. A failure names the graph, which
/// `graph_from_spec` in this file reads back.
#[test]
fn generated_control_flow_keeps_every_block() {
    let seeds: u64 = std::env::var("BORER_SEARCH_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let o = Overlay::default();
    for seed in 0..seeds {
        let blocks = graph(seed);
        let p = program(&blocks);
        let a = Analysis::compute(&p);
        let Some(text) = decompile(&p, &a, &o, CODE) else {
            continue;
        };
        let faults = faults(&blocks, &text);
        assert!(
            faults.is_empty(),
            "seed {seed} ({}): {faults:?}\n{text}",
            spec(&blocks)
        );
    }
}

/// Every generated graph's text follows its control flow.
///
/// Each path the text claims is one the graph has, and each path of the
/// graph one the text claims, as far as the blocks' calls and the labels
/// tell them apart.
///
/// `BORER_SEARCH_SEEDS` raises the count of each kind of graph.
#[test]
fn the_structure_agrees_with_the_cfg_over_generated_graphs() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let seeds: u64 = std::env::var("BORER_SEARCH_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let o = Overlay::default();
    let mut wrong = Vec::new();
    for seed in 0..seeds {
        for blocks in [graph(seed), graph_rich(seed)] {
            let p = program(&blocks);
            let a = Analysis::compute(&p);
            let Some(text) = decompile(&p, &a, &o, CODE) else {
                continue;
            };
            let verdict = check_structure(&p, &a, &o, CODE, &text);
            if verdict != Structure::Agrees {
                wrong.push(format!("{} {verdict:?}", spec(&blocks)));
            }
        }
    }
    assert!(wrong.is_empty(), "{} graphs: {wrong:#?}", wrong.len());
}

/// Reads a graph written the way [`spec`] writes one.
///
/// # Arguments
///
/// * `text` - A list such as `J3,R,R,S1-2-3`.
///
/// # Returns
///
/// The graph it names.
fn graph_from_spec(text: &str) -> Vec<Term> {
    text.split(',')
        .map(|t| {
            let (kind, rest) = t.split_at(1);
            let d: usize = rest.parse().unwrap_or(0);
            match kind {
                "R" => Term::Ret,
                "K" => Term::Call,
                "N" => Term::Noreturn,
                "J" => Term::Jmp(d),
                "S" => Term::Switch(rest.split('-').filter_map(|x| x.parse().ok()).collect()),
                _ => Term::Cond(d),
            }
        })
        .collect()
}

/// The graphs that stood behind defects, kept so they stay fixed.
///
/// In order: a loop entered below its lowest block; a loop left only by a
/// break under a condition; a break carried into another loop; a switch
/// whose arms the text reaches before the dispatch is printed; and a switch
/// at a loop header whose one arm's blocks sit, by address, inside a nested
/// loop's span — the loop folded them into its body and stamped them emitted,
/// so the arm that owns them came out empty and their store and call were
/// lost (seed 85488, found once the fuzzer modelled noreturn control flow);
/// and a loop with two exits, the latch's a return placed right after the
/// loop and the body's a break to the code beyond it — the do-while form
/// put the return where the break lands, and the code beyond, three calls
/// in an fmod64 function, was pruned as unreachable.
#[test]
fn the_graphs_that_found_defects_stay_whole() {
    let o = Overlay::default();
    for text in [
        "J3,C4,J8,J6,C7,C1,C4,C2,J8",
        "J2,C0,C1,R",
        "J4,J3,J1,C1,J6,C2,C5,R",
        "J3,R,R,S1-2-3",
        "C12,R,S14-5-13,S3-6-9-1,C14,C13,C7,C11,J14,C13,J13,C6,S12-5-9,J14,R",
        "J1,C4,C1,R,K,R",
    ] {
        let blocks = graph_from_spec(text);
        let p = program(&blocks);
        let a = Analysis::compute(&p);
        let Some(out) = decompile(&p, &a, &o, CODE) else {
            panic!("{text} did not decompile");
        };
        assert!(faults(&blocks, &out).is_empty(), "{text}: {out}");
    }
}

/// The body of a raw decompilation, its header lines dropped.
///
/// # Arguments
///
/// * `raw` - What [`decompile_raw`] returned.
fn raw_body(raw: &str) -> &str {
    raw.split_once("\n\n").map_or("", |(_, body)| body)
}

/// Cleaning a cleaned text changes nothing.
///
/// The cleanup runs its rules to a fixpoint, so a second run that still
/// rewrites means a rule ran outside the loop (chained spills used to be
/// merged once, before it) or two rules undo each other. Every generated
/// graph's raw text is cleaned twice.
#[test]
fn cleanup_is_idempotent_over_generated_graphs() {
    let o = Overlay::default();
    for seed in 0..200 {
        for blocks in [graph(seed), graph_rich(seed)] {
            let p = program(&blocks);
            let a = Analysis::compute(&p);
            let Some(raw) = decompile_raw(&p, &a, &o, CODE) else {
                continue;
            };
            let once = cleanup(raw_body(&raw));
            assert_eq!(cleanup(&once), once, "seed {seed} ({})", spec(&blocks));
        }
    }
}

/// Cleaning a cleaned text changes nothing, over every function of the
/// `BORER_DOGFOOD` binary (kernel32, say).
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn cleanup_is_idempotent_over_a_binary() {
    let Ok(path) = std::env::var("BORER_DOGFOOD") else {
        panic!("BORER_DOGFOOD env var");
    };
    let Ok(p) = Program::load(std::path::Path::new(&path)) else {
        panic!("cannot load {path}");
    };
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let mut differ: Vec<u64> = Vec::new();
    for f in &a.functions {
        let Some(raw) = decompile_raw(&p, &a, &o, f.entry) else {
            continue;
        };
        let once = cleanup(raw_body(&raw));
        if cleanup(&once) != once {
            differ.push(f.entry);
        }
    }
    assert!(differ.is_empty(), "{} functions: {differ:x?}", differ.len());
}

/// Cleaning a decompiled byte search's cleaned text changes nothing.
///
/// The function has the shape of kernel32's 0x18007a450, one of the
/// functions whose cleanup a second run still rewrote: `xor r10d,r10d;
/// test edx,edx; je D; cmp r9d,edx; ja D; mov r11d,r10d; H: lea
/// eax,[r11+r9]; cmp eax,edx; ja D; mov eax,r11d; cmp byte [rax+rcx],0; je
/// F; inc r11d; jmp H; F: mov r10d,r11d; add r10,rcx; D: mov rax,r10; ret`.
/// Its raw text zeroes `r11` and, after the loop header's label, `r10`: two
/// spills of one value that sit side by side only once the cleanup has
/// dropped the label, so the chain they form is the first cleanup's work,
/// not the second's.
#[test]
fn cleanup_is_idempotent_over_a_decompiled_search_loop() {
    use borer_engine::program::BinaryFormat;
    let code = [
        0x45, 0x33, 0xd2, 0x85, 0xd2, 0x74, 0x24, 0x44, 0x3b, 0xca, 0x77, 0x1f, 0x45, 0x8b, 0xda,
        0x43, 0x8d, 0x04, 0x0b, 0x3b, 0xc2, 0x77, 0x14, 0x41, 0x8b, 0xc3, 0x80, 0x3c, 0x08, 0x00,
        0x74, 0x05, 0x41, 0xff, 0xc3, 0xeb, 0xea, 0x45, 0x8b, 0xd3, 0x4c, 0x03, 0xd1, 0x49, 0x8b,
        0xc2, 0xc3,
    ];
    let mut bytes = vec![0xccu8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_1000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let Some(raw) = decompile_raw(&p, &a, &Overlay::default(), 0x1_4000_1000) else {
        panic!("the search loop did not decompile");
    };
    let once = cleanup(raw_body(&raw));
    assert!(once.contains("r11 = r10 = 0;"), "{once}");
    assert_eq!(cleanup(&once), once);
}

/// An `else` taken over by the code after an `if`/`else if` chain must
/// leave the earlier arms' paths alone.
///
/// The second arm jumps over the tail, and the first falls into it: an
/// `else` around the tail would skip it after the first arm too. Where the
/// first arm returns, nothing falls into the tail but the chain's own
/// fall-through, and the tail becomes the chain's `else`.
#[test]
fn an_else_if_arm_does_not_take_the_tail_another_arm_falls_into() {
    let falls = concat!(
        "if (a1 == 1) {\n",
        "  sub_1(a1);\n",
        "} else if (a1 == 2) {\n",
        "  sub_2(a1);\n",
        "  goto L_1;\n",
        "}\n",
        "sub_3(a1);\n",
        "L_1:\n",
        "return 0;\n",
    );
    let out = cleanup(falls);
    assert!(!out.contains("} else {\n  sub_3(a1);"), "{out}");
    assert!(out.contains("sub_3(a1);"), "{out}");
    let leaves = falls.replace("  sub_1(a1);\n", "  sub_1(a1);\n  return 1;\n");
    let out = cleanup(&leaves);
    assert!(out.contains("} else {\n  sub_3(a1);\n}"), "{out}");
}

/// A call to a function whose name begins with `return` is a call: the
/// code after it is not dead.
#[test]
fn a_call_named_like_return_is_not_a_return() {
    let out = cleanup("returnBuffer(a1);\nsub_3(a1);\nreturn 0;\n");
    assert!(out.contains("sub_3(a1);"), "{out}");
    let early = concat!(
        "if (a1 == 0) {\n",
        "  sub_1(a1);\n",
        "  sub_2(a1);\n",
        "  sub_4(a1);\n",
        "  returnBuffer(a1);\n",
        "}\n",
        "sub_3(a1);\n",
        "return 0;\n",
    );
    let out = cleanup(early);
    assert!(out.starts_with("if (a1 == 0) {\n  sub_1(a1);"), "{out}");
}

/// A comparison of floats negates as a whole, never by flipping it.
///
/// `a < b` and `a >= b` are both false on a NaN, so the arm a `goto`
/// skipped runs under `!(a < b)`. An integer comparison still flips, and a
/// negation loses its `!`.
#[test]
fn a_float_comparison_negates_as_a_whole() {
    let float = cleanup("if (xmm0 < 1.0f) goto L_1;\nsub_1(a1);\nL_1:\nreturn 0;\n");
    assert!(
        float.contains("if (!(xmm0 < 1.0f)) {\n  sub_1(a1);\n}"),
        "{float}"
    );
    let int = cleanup("if (a1 < 5) goto L_1;\nsub_1(a1);\nL_1:\nreturn 0;\n");
    assert!(int.contains("if (a1 >= 5) {\n  sub_1(a1);\n}"), "{int}");
    let negated = cleanup("if (!(xmm0 >= 1.0f)) goto L_1;\nsub_1(a1);\nL_1:\nreturn 0;\n");
    assert!(
        negated.contains("if (xmm0 >= 1.0f) {\n  sub_1(a1);\n}"),
        "{negated}"
    );
    let call = cleanup("if (isgreater(a1, a2)) goto L_1;\nsub_1(a1);\nL_1:\nreturn 0;\n");
    assert!(call.contains("if (!(isgreater(a1, a2))) {"), "{call}");
}

/// A block that breaks out of a loop does not move into a switch arm.
///
/// Inside a switch that the loop holds, the block's `break` would leave the
/// switch instead of the loop; the arms' braces stand at the switch's own
/// indentation, and nesting is read from the braces.
#[test]
fn a_loop_break_does_not_move_into_a_switch_arm() {
    let text = concat!(
        "while (1) {\n",
        "  switch (a1) {\n",
        "  case 0: {\n",
        "    sub_1(a1);\n",
        "    break;\n",
        "  }\n",
        "  case 1: goto L_1;\n",
        "  }\n",
        "  sub_2(a1);\n",
        "  if (a2 == 0) continue;\n",
        "  break;\n",
        "  L_1:\n",
        "  sub_3(a1);\n",
        "  break;\n",
        "}\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(out.contains("case 1: goto L_1;"), "{out}");
    assert!(!out.contains("case 1: {"), "{out}");
}

/// Two calls with the same text are two calls: a run of assignments
/// chained by value stops at a call.
#[test]
fn equal_calls_are_not_chained_into_one() {
    let out =
        cleanup("rax = sub_1(a1);\nrbx = sub_2(a1);\nrcx = sub_1(a1);\nreturn rax + rbx + rcx;\n");
    assert_eq!(out.matches("sub_1(a1)").count(), 2, "{out}");
    let spills = cleanup(
        "local_8 = a1;\nlocal_10 = a2;\nlocal_18 = a1;\nreturn local_8 + local_10 + local_18;\n",
    );
    assert!(spills.contains("local_8 = local_18 = a1;"), "{spills}");
}

/// A switch arm whose body an earlier arm runs into jumps to that body.
///
/// Case 0 counts `edx` up past its test and falls into case 1's body, ten
/// instructions and a call, too long to copy: case 0's text writes it, and
/// case 1's arm, coming up after, found it written and broke out of the
/// switch, so case 1 returned without the call. d3dx9's 0x101adb0c, a
/// state machine whose case 3 runs on into cases 5 and 6, broke out of
/// both. The structure check holds the text to every path.
#[test]
fn a_switch_arm_another_arm_runs_into_jumps_to_its_body() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let base = 0x1000u64;
    let table = 0x2000u64;
    // ASM: xor edx,edx; xor ecx,ecx; test eax,eax; cmp eax,1; ja J; jmp [rax*8+T]
    let mut code: Vec<u8> = vec![
        0x31, 0xd2, 0x31, 0xc9, 0x85, 0xc0, 0x83, 0xf8, 0x01, 0x0f, 0x87, 0, 0, 0, 0, 0xff, 0x24,
        0xc5,
    ];
    code.extend_from_slice(&lo32(table).to_le_bytes());
    let case0 = code.len();
    for _ in 0..9 {
        code.extend_from_slice(&[0xff, 0xc2]); // ASM: inc edx
    }
    code.extend_from_slice(&[0x83, 0xfa, 0x05, 0x0f, 0x82, 0, 0, 0, 0]); // ASM: cmp edx,5; jb J
    let jb = code.len() - 4;
    let case1 = code.len();
    for _ in 0..9 {
        code.extend_from_slice(&[0xff, 0xc1]); // ASM: inc ecx
    }
    let call_x = code.len() + 1;
    code.extend_from_slice(&[0xe8, 0, 0, 0, 0, 0xc3]); // ASM: call X; ret
    let join = code.len();
    let call_z = join + 1;
    code.extend_from_slice(&[0xe8, 0, 0, 0, 0, 0xc3]); // ASM: call Z; ret
    let (x, z) = (0x80, 0x90);
    let mut patch = |at: usize, to: usize| {
        let rel = lo32(from_usize(to).wrapping_sub(from_usize(at + 4)));
        code[at..at + 4].copy_from_slice(&rel.to_le_bytes());
    };
    patch(11, join);
    patch(jb, join);
    patch(call_x, x);
    patch(call_z, z);
    let mut image = vec![0xccu8; 0x3000];
    image[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    image[0x1000 + x..0x1000 + x + 6].copy_from_slice(&[0xb8, 1, 0, 0, 0, 0xc3]); // ASM: mov eax,1; ret
    image[0x1000 + z..0x1000 + z + 6].copy_from_slice(&[0xb8, 2, 0, 0, 0, 0xc3]); // ASM: mov eax,2; ret
    for (k, case) in [case0, case1].into_iter().enumerate() {
        let at = 0x2000 + 8 * k;
        image[at..at + 8].copy_from_slice(&(base + from_usize(case)).to_le_bytes());
    }
    let p = Program::raw(
        image,
        Arch::X86_64,
        0,
        Some(base),
        vec![
            Section::mapped(".text", base, base, 0x1000, false, true),
            Section::mapped(".rdata", table, table, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let Some(out) = decompile(&p, &a, &o, base) else {
        panic!("the switch did not decompile");
    };
    let case1 = out.split("case 1:").nth(1).unwrap_or("");
    assert!(case1.contains("sub_1080()"), "{out}");
    assert_eq!(
        check_structure(&p, &a, &o, base, &out),
        Structure::Agrees,
        "{out}"
    );
}

/// A block that runs on into another function jumps there.
///
/// `A` calls `B`, then, when `ecx` is zero, increments it and falls into
/// `B`'s first byte, which the unwind table says is `B`'s and not `A`'s.
/// Nothing of `A` starts there, so the text has no label to go to; ending
/// the block with nothing let it fall into the text after it, a `return`,
/// where the binary goes on into `B`.
#[test]
fn a_block_that_falls_out_of_its_function_jumps_out() {
    let base = 0x1000u64;
    let code: [u8; 17] = [
        0xe8, 0x07, 0, 0, 0, // ASM: call B (0x100c)
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x01, // ASM: je 0x100a
        0xc3, // ASM: ret
        0xff, 0xc1, // ASM: inc ecx (falls into B)
        0xb8, 0x07, 0, 0, 0, // ASM: B: mov eax,7
    ];
    let mut image = vec![0xccu8; 0x2000];
    image[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    image[0x1000 + code.len()] = 0xc3; // ASM: ret
    let mut p = Program::raw(
        image,
        Arch::X86_64,
        0,
        Some(base),
        vec![Section::mapped(".text", base, base, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1000, 0x100c), (0x100c, 0x1012)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let Some(out) = decompile(&p, &a, &o, base) else {
        panic!("A did not decompile");
    };
    assert!(out.contains("goto *0x100c;"), "{out}");
}

/// The structure check rejects a text whose control flow is not the
/// graph's, on the side that holds the path the other lacks.
///
/// `C4,K,C1,R,R` is a loop whose blocks call `2`, `2` and `3` and that
/// leaves on a test to a return; its own text agrees. With the call of `3`
/// taken out or written twice, or with the loop's test leaving where it
/// continues, the text claims a path the binary lacks (`2` right after
/// `2`, `3` after `3`, a return after `3`); with the return turned into a
/// `continue`, the binary has a path the text lacks: it leaves the loop.
#[test]
fn the_structure_check_rejects_a_text_that_is_not_the_graph() {
    use borer_engine::analysis::decompile::traces::{Side, Structure, check_structure};
    let blocks = graph_from_spec("C4,K,C1,R,R");
    let p = program(&blocks);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let Some(text) = decompile(&p, &a, &o, CODE) else {
        panic!("the graph did not decompile");
    };
    assert_eq!(
        check_structure(&p, &a, &o, CODE, &text),
        Structure::Agrees,
        "{text}"
    );
    let side = |t: &str| match check_structure(&p, &a, &o, CODE, t) {
        Structure::Disagrees(d) => Some(d.side),
        Structure::Agrees | Structure::Unchecked(_) => None,
    };
    let call = text
        .lines()
        .find(|l| l.ends_with("(3);"))
        .unwrap_or_default()
        .to_owned();
    let exit = text
        .lines()
        .find(|l| l.ends_with("(4);"))
        .unwrap_or_default()
        .to_owned();
    assert!(!call.is_empty() && exit.contains("return"), "{text}");
    let mutants = [
        (
            text.replacen(
                &format!(
                    "{call}
"
                ),
                "",
                1,
            ),
            Side::Text,
        ),
        (
            text.replacen(
                &call,
                &format!(
                    "{call}
{call}"
                ),
                1,
            ),
            Side::Text,
        ),
        (text.replacen("continue;", "break;", 1), Side::Text),
        (text.replacen(&exit, "  continue;", 1), Side::Binary),
    ];
    for (mutant, by) in mutants {
        assert_ne!(mutant, text);
        assert_eq!(side(&mutant), Some(by), "{mutant}");
    }
}

/// A function entered above its lowest block decompiles from its entry.
///
/// The entry at 0x1010 tests `ecx` and returns -1, or jumps back to a tail
/// at 0x1000 that calls `sub_1100` and returns: code below the entry, as a
/// compiler places a shared tail or chunk. Read from the lowest block, the
/// text was the tail alone, `return sub_1100();`, with the test and the -1
/// dropped as unreachable.
#[test]
fn a_function_entered_above_its_lowest_block_starts_at_its_entry() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let mut image = vec![0xccu8; 0x2000];
    let mut put = |at: usize, bytes: &[u8]| image[at..at + bytes.len()].copy_from_slice(bytes);
    put(0x1000, &[0xe8, 0xfb, 0x00, 0x00, 0x00, 0xc3]); // ASM: call 0x1100; ret
    put(0x1010, &[0x83, 0xf9, 0x01, 0x74, 0x06]); // ASM: cmp ecx,1; je 0x101b
    put(0x1015, &[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]); // ASM: mov eax,-1; ret
    put(0x101b, &[0xe9, 0xe0, 0xff, 0xff, 0xff]); // ASM: jmp 0x1000
    put(0x1100, &[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,5; ret
    let p = Program::raw(
        image,
        Arch::X86_64,
        0,
        Some(0x1010),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x1010)
            .and_then(|f| f.blocks.first())
            .map(|b| b.start),
        Some(0x1000)
    );
    let o = Overlay::default();
    let Some(out) = decompile(&p, &a, &o, 0x1010) else {
        panic!("the function did not decompile");
    };
    assert!(out.contains("== 1") || out.contains("!= 1"), "{out}");
    assert!(out.contains("sub_1100()"), "{out}");
    assert!(out.contains("-1;") || out.contains("0xffffffff;"), "{out}");
    assert!(!out.contains("unreachable"), "{out}");
    assert_eq!(
        check_structure(&p, &a, &o, 0x1010, &out),
        Structure::Agrees,
        "{out}"
    );
}

/// A register or stack slot assigned its own value is no statement.
///
/// A function entered above a shared tail pops a saved register and jumps
/// to the tail, which pushes it back into the same slot: `local_4 =
/// local_4;`, true and empty. A global assigned itself is a store, and
/// stays.
#[test]
fn a_variable_assigned_its_own_value_is_dropped() {
    let out = cleanup(
        "local_4 = local_4;
rsi = rsi;
rax = sub_1(a1);
g32_a000 = g32_a000;
return rax;
",
    );
    assert!(!out.contains("local_4 = local_4;"), "{out}");
    assert!(!out.contains("rsi = rsi;"), "{out}");
    assert!(out.contains("g32_a000 = g32_a000;"), "{out}");
    assert!(out.contains("rax = sub_1(a1);"), "{out}");
}

/// A shared `return` that every arm of a switch copied is not written again
/// after the switch.
///
/// Three compares on `ecx` pick `mov eax,K; jmp R` arms, and anything else
/// zeroes `eax` and jumps to the same `R: ret`. Each arm copies the return,
/// so no path of the text leaves the switch; the original, written after
/// it as the next block by address, was a `return` nothing runs (a 32-bit
/// game client's 0x9a896d printed `return st0;` there).
#[test]
fn a_return_every_switch_arm_copied_is_not_written_after_it() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let base = 0x1000u64;
    let code: [u8; 39] = [
        0x83, 0xf9, 0x01, 0x74, 0x0e, // ASM: cmp ecx,1; je A
        0x83, 0xf9, 0x02, 0x74, 0x10, // ASM: cmp ecx,2; je B
        0x83, 0xf9, 0x03, 0x74, 0x12, // ASM: cmp ecx,3; je C
        0x31, 0xc0, 0xeb, 0x13, // ASM: xor eax,eax; jmp R
        0xb8, 0x0a, 0, 0, 0, 0xeb, 0x0c, // ASM: A: mov eax,10; jmp R
        0xb8, 0x14, 0, 0, 0, 0xeb, 0x05, // ASM: B: mov eax,20; jmp R
        0xb8, 0x1e, 0, 0, 0,    // ASM: C: mov eax,30
        0xc3, // ASM: R: ret
    ];
    let mut image = vec![0xccu8; 0x2000];
    image[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = Program::raw(
        image,
        Arch::X86_64,
        0,
        Some(base),
        vec![Section::mapped(".text", base, base, 0x1000, false, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let Some(out) = decompile(&p, &a, &o, base) else {
        panic!("the ladder did not decompile");
    };
    assert!(out.contains("switch ("), "{out}");
    assert_eq!(out.matches("return").count(), 4, "{out}");
    assert_eq!(out.trim_end().lines().last(), Some("}"), "{out}");
    assert_eq!(
        check_structure(&p, &a, &o, base, &out),
        Structure::Agrees,
        "{out}"
    );
}

/// A copied block whose branch the lifter proved one-way goes on to the
/// side it takes.
///
/// `ecx == 1` leads to a test of `edx`, whose one side runs `mov eax,5`
/// into the join `J: call G2`, shared with the other arm. After `J`,
/// `xor ebx,ebx; test ebx,ebx; jle Z` always jumps, so `C` has one live
/// successor, `Z: mov eax,7; ret`, and the arm copies `J`, `C` and `Z`.
/// The copy of `C` holds no statement and no branch, and ended the copied
/// chain there: the arm fell out of its `if` into the other arm's call
/// (a 32-bit game client's 0x673c94 ran from the copy of its join into
/// the else side's `operator []`).
#[test]
fn a_copied_one_way_branch_goes_on_to_its_side() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let base = 0x1000u64;
    let code: [u8; 39] = [
        0x83, 0xf9, 0x01, 0x74, 0x07, // ASM: cmp ecx,1; je T
        0xe8, 0x76, 0, 0, 0, // ASM: call G1 (0x1080)
        0xeb, 0x0a, // ASM: jmp J
        0x83, 0xfa, 0x01, 0x74, 0x0a, // ASM: T: cmp edx,1; je C
        0xb8, 0x05, 0, 0, 0, // ASM: mov eax,5
        0xe8, 0x75, 0, 0, 0, // ASM: J: call G2 (0x1090)
        0x31, 0xdb, 0x85, 0xdb, 0x7e, 0x06, // ASM: C: xor ebx,ebx; test ebx,ebx; jle Z
        0xe8, 0x7a, 0, 0, 0,    // ASM: call G3 (0x10a0)
        0xc3, // ASM: ret
    ];
    let mut image = vec![0xccu8; 0x2000];
    image[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    image[0x1027..0x102d].copy_from_slice(&[0xb8, 7, 0, 0, 0, 0xc3]); // ASM: Z: mov eax,7; ret
    for (at, k) in [(0x1080, 1u8), (0x1090, 2), (0x10a0, 3)] {
        image[at..at + 6].copy_from_slice(&[0xb8, k, 0, 0, 0, 0xc3]); // ASM: mov eax,k; ret
    }
    let p = Program::raw(
        image,
        Arch::X86_64,
        0,
        Some(base),
        vec![Section::mapped(".text", base, base, 0x1000, false, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let Some(out) = decompile(&p, &a, &o, base) else {
        panic!("the function did not decompile");
    };
    assert_eq!(
        check_structure(&p, &a, &o, base, &out),
        Structure::Agrees,
        "{out}"
    );
}
