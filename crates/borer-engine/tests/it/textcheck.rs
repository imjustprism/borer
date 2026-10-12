//! What the final text of a function claims, checked: every value it reads
//! comes from a line of it or is an input, and run as C it does what the
//! binary does ([`check_generated`]).

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::{decompile_named, mark_unset, unset_reads};
use borer_engine::analysis::render::{Verdict, check_generated};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};

/// Where the hand-assembled code sits; the data page follows it.
const TEXT: u64 = 0x1000;

/// Loads x86-64 code at [`TEXT`] and data at the page after it.
///
/// # Arguments
///
/// * `code` - The code, `int3` padding after it.
/// * `data` - The data page's bytes.
fn program(code: &[u8], data: &[u8]) -> Program {
    let mut bytes = vec![0xccu8; 0x2000];
    bytes[..code.len()].copy_from_slice(code);
    bytes[0x1000..0x1000 + data.len()].copy_from_slice(data);
    bytes[0x1000 + data.len()..].fill(0);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(TEXT),
        vec![
            Section::mapped(".text", TEXT, 0, 0x1000, false, true),
            Section::mapped(".rdata", TEXT + 0x1000, 0x1000, 0x1000, false, false),
        ],
    )
}

/// Decompiles a function as the tools show it, its text and the lines of it
/// that read a value no line sets.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
fn text_of(p: &Program, entry: u64) -> (String, Vec<(usize, Vec<String>)>) {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let text = decompile_named(p, &a, &o, entry).unwrap_or_default();
    let unset = unset_reads(p, &a, &o, entry, &text).unwrap_or_default();
    (text, unset)
}

/// Runs a function's final text and the binary on generated inputs and
/// requires that no input differs and some agree.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
fn runs_alike(p: &Program, entry: u64) {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let rows = check_generated(p, &a, &o, entry, 8, 1, 20_000).expect("the text reads");
    let text = decompile_named(p, &a, &o, entry).unwrap_or_default();
    assert!(
        rows.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{text}\n{rows:?}"
    );
    assert!(
        !rows.iter().any(|(_, v)| matches!(v, Verdict::Differs(..))),
        "{text}\n{rows:?}"
    );
}

/// A text that reads a register no line sets is flagged at that line.
///
/// One set on some path, or whose address a call takes, is not; one the
/// text names without declaring it is. The flagged lines are marked.
#[test]
fn a_value_no_line_sets_is_flagged_and_marked() {
    let p = program(&[0xc3], &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = concat!(
        "// sub_1000 @ 0x1000: 1 instructions, 1 blocks\n",
        "// signature: uint64_t sub_1000(uint64_t a1)\n",
        "uint64_t rax, rcx, r10;\n",
        "\n",
        "rax = r10 + a1;\n",
        "if (a1 != 0) {\n",
        "  rax = 1;\n",
        "}\n",
        "sub_1000(&rcx);\n",
        "return rax + rcx + r11;\n",
    );
    let reads = unset_reads(&p, &a, &o, TEXT, text).expect("the text reads");
    assert_eq!(
        reads,
        vec![(5, vec!["r10".to_owned()]), (10, vec!["r11".to_owned()])]
    );
    let marked = mark_unset(text, &reads);
    assert!(
        marked.contains("rax = r10 + a1;  // !unset: r10\n"),
        "{marked}"
    );
    assert_eq!(marked.matches("// !unset").count(), 2, "{marked}");
    assert_eq!(mark_unset(text, &[]), text);
}

/// A decompiled function that returns a register it never sets is flagged
/// at its `return`; one that computes from its parameter is closed and
/// runs as the binary does.
#[test]
fn a_decompiled_read_of_a_register_no_line_sets_is_flagged() {
    let mut code = vec![
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
        0x4c, 0x89, 0xd0, // ASM: mov rax,r10
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend([0x48, 0x8d, 0x41, 0x01, 0xc3]); // ASM: lea rax,[rcx+1]; ret
    let p = program(&code, &[]);
    let (text, unset) = text_of(&p, TEXT);
    assert_eq!(unset.len(), 1, "{text}\n{unset:?}");
    assert_eq!(unset[0].1, vec!["r10".to_owned()], "{text}");
    let (closed, unset) = text_of(&p, TEXT + 0x10);
    assert!(unset.is_empty(), "{closed}\n{unset:?}");
    runs_alike(&p, TEXT + 0x10);
}
