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

/// A register a callee and every function it calls leave alone keeps its
/// value across the call.
///
/// The compiler that saw them all (link-time code generation) relies on
/// it: the text reads the copy it made before the call, never a register
/// no line sets.
///
/// `mov r10d,ecx; call f; mov eax,r10d; ret`, `f` is `sub rsp,0x28; call
/// g; add rsp,0x28; ret` and `g` is `mov eax,1; ret`: neither writes `r10`.
#[test]
fn a_register_a_callees_callees_leave_alone_survives_the_call() {
    let mut code = vec![
        0x41, 0x89, 0xca, // ASM: mov r10d,ecx
        0xe8, 0x18, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0x44, 0x89, 0xd0, // ASM: mov eax,r10d
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend([0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    let p = program(&code, &[]);
    let (text, unset) = text_of(&p, TEXT);
    assert!(unset.is_empty(), "{text}\n{unset:?}");
    assert!(text.contains("a1"), "{text}");
    runs_alike(&p, TEXT);
}

/// A position a function's signature lists below a parameter it reads is a
/// parameter too, when the function only hands it on: the call passes it
/// by its name, not as a register no line sets.
///
/// `sub rsp,0x28; mov r9,[r9]; call f; add rsp,0x28; ret` with `f` reading
/// all four argument registers (`lea rax,[rcx+rdx]; add rax,r8; add
/// rax,r9; ret`).
#[test]
fn a_parameter_a_function_only_hands_on_is_named() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x4d, 0x8b, 0x09, // ASM: mov r9,[r9]
        0xe8, 0x34, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([
        0x48, 0x8d, 0x04, 0x11, // ASM: lea rax,[rcx+rdx]
        0x4c, 0x01, 0xc0, // ASM: add rax,r8
        0x4c, 0x01, 0xc8, // ASM: add rax,r9
        0xc3, // ASM: ret
    ]);
    let p = program(&code, &[]);
    let (text, unset) = text_of(&p, TEXT);
    assert!(unset.is_empty(), "{text}\n{unset:?}");
    assert!(text.contains("(a1, a2, a3, "), "{text}");
}

/// A function one of whose exits hands back a void callee's leftover in
/// `rax` returns nothing itself, whatever its other exits write.
///
/// Rust's drop glue sets `eax` testing a discriminant and calls a drop on
/// the other path, and the text claimed the drop's leftover as a value it
/// then compared with the binary's.
///
/// `f` is `mov eax,1; xor edx,edx; cmp qword [rcx],2; cmove eax,edx; test
/// eax,eax; jne .call; ret; .call: sub rsp,0x28; call g; add rsp,0x28;
/// ret`; `g` is `test rcx,rcx; je .out; call h; .out: ret`, which reaches
/// its `ret` without writing `rax`; `h` is `mov [rcx],rdx; ret`.
#[test]
fn an_exit_handing_back_a_void_callees_leftover_returns_nothing() {
    let mut code = vec![
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0x31, 0xd2, // ASM: xor edx,edx
        0x48, 0x83, 0x39, 0x02, // ASM: cmp qword [rcx],2
        0x0f, 0x44, 0xc2, // ASM: cmove eax,edx
        0x85, 0xc0, // ASM: test eax,eax
        0x75, 0x01, // ASM: jne 0x1013
        0xc3, // ASM: ret
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x24, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([
        0x48, 0x85, 0xc9, // ASM: test rcx,rcx
        0x74, 0x05, // ASM: je 0x104a
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1060
        0xc3, // ASM: ret
    ]);
    code.resize(0x60, 0xcc);
    code.extend([0x48, 0x89, 0x11, 0xc3]); // ASM: mov [rcx],rdx; ret
    let p = program(&code, &[]);
    let (text, _) = text_of(&p, TEXT);
    assert!(text.contains("// signature: void sub_1000("), "{text}");
}

/// A function that returns what it calls returns what its callee does.
///
/// `call g; ret` with `g` handing back a byte (`mov al,[rcx+4]; ret`)
/// returns a byte, and the bits above it are the caller's leftovers, which
/// the text compared as part of a 64-bit value.
#[test]
fn a_call_returned_as_it_stands_has_its_callees_width() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x8a, 0x41, 0x04, 0xc3]); // ASM: mov al,[rcx+4]; ret
    let p = program(&code, &[]);
    let (text, _) = text_of(&p, TEXT);
    assert!(text.contains("// signature: uint8_t sub_1000("), "{text}");
}

/// A second result a callee hands back in `rdx` is passed on in `rdx` to
/// the next call that takes it: a Rust slice returned in `rax:rdx` and
/// handed on whole, where the text passed only `rax`.
///
/// `f` is `sub rsp,0x28; call g; mov rcx,rax; call h; add rsp,0x28; ret`;
/// `g` is `mov rax,rcx; mov edx,5; ret`; `h` is `lea rax,[rcx+rdx]; ret`.
#[test]
fn a_second_result_is_passed_on_in_rdx() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x89, 0xc1, // ASM: mov rcx,rax
        0xe8, 0x4f, 0x00, 0x00, 0x00, // ASM: call 0x1060
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0xba, 0x05, 0x00, 0x00, 0x00, // ASM: mov edx,5
        0xc3, // ASM: ret
    ]);
    code.resize(0x60, 0xcc);
    code.extend([0x48, 0x8d, 0x04, 0x11, 0xc3]); // ASM: lea rax,[rcx+rdx]; ret
    let p = program(&code, &[]);
    let (text, unset) = text_of(&p, TEXT);
    assert!(unset.is_empty(), "{text}\n{unset:?}");
    assert!(text.contains(", rdx)"), "{text}");
    runs_alike(&p, TEXT);
}

/// A narrow operand C would compute narrower than the machine keeps its
/// width.
///
/// A sum of two 32-bit values carries past 32 bits, a byte shifted past
/// `int`'s width keeps its bit, while a narrow operand beside a 64-bit one
/// needs no cast.
#[test]
fn narrow_operands_keep_the_machines_width() {
    use borer_engine::analysis::decompile::polish;
    let packs = borer_engine::pack::Packs::default();
    let sum = polish(
        concat!(
            "// signature: uint64_t f(uint64_t a1, uint64_t a2)\n",
            "uint64_t rax;\n",
            "rax = (a1 & 0xffffffff) + (a2 & 0xffffffff);\n",
            "return rax;\n",
        ),
        64,
        &packs,
    );
    assert!(sum.contains("uint32_t a1, uint32_t a2)"), "{sum}");
    assert!(sum.contains("rax = (uint64_t)a1 + a2;"), "{sum}");
    let shifted = polish(
        concat!(
            "// signature: uint64_t f(uint64_t a1)\n",
            "return (a1 & 0xff) >> 7 << 0x3f;\n",
        ),
        64,
        &packs,
    );
    assert!(shifted.contains("(uint64_t)a1 >> 7 << 0x3f"), "{shifted}");
}

/// A byte-swapped 32-bit value shifted into the upper half is shifted as a
/// 64-bit value: `mov eax,ecx; bswap eax; shl rax,0x20; ret`, where C's
/// 32-bit `bswap(..) << 32` lost every bit.
#[test]
fn a_narrow_value_shifted_into_the_upper_half_is_widened() {
    let code = [
        0x89, 0xc8, // ASM: mov eax,ecx
        0x0f, 0xc8, // ASM: bswap eax
        0x48, 0xc1, 0xe0, 0x20, // ASM: shl rax,0x20
        0xc3, // ASM: ret
    ];
    let p = program(&code, &[]);
    runs_alike(&p, TEXT);
}

/// A register a 32-bit write left is passed with its upper half clear to a
/// callee that reads it whole: `mov eax,ecx; mov ecx,eax; call g` hands `g`
/// the low half of `a1`, where the text passed all of it.
#[test]
fn a_32_bit_register_is_passed_with_its_upper_half_clear() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x89, 0xc8, // ASM: mov eax,ecx
        0x89, 0xc1, // ASM: mov ecx,eax
        0xe8, 0x33, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x48, 0x89, 0xc8, 0xc3]); // ASM: mov rax,rcx; ret
    let p = program(&code, &[]);
    runs_alike(&p, TEXT);
}

/// A 32-bit sum is passed with its upper half clear.
///
/// `lea ecx,[rcx-1]; call g` hands a callee that reads the whole register
/// the low half of `a1 - 1`, which wraps at 32 bits where the 64-bit sum
/// does not.
#[test]
fn a_32_bit_sum_is_passed_with_its_upper_half_clear() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x8d, 0x49, 0xff, // ASM: lea ecx,[rcx-1]
        0xe8, 0x34, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x48, 0x89, 0xc8, 0xc3]); // ASM: mov rax,rcx; ret
    let p = program(&code, &[]);
    let (text, _) = text_of(&p, TEXT);
    assert!(text.contains("sub_1040((a1 - 1) & 0xffffffff)"), "{text}");
    runs_alike(&p, TEXT);
}
