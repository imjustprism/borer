//! What the final text of a function claims, checked: every value it reads
//! comes from a line of it or is an input, and run as C it does what the
//! binary does ([`check_generated`]).

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::{Site, checked_header, decompile_named, unset_reads};
use borer_engine::analysis::render::{
    Budget, Evidence, Repair, Verdict, answered, check_generated, check_generated_iso, repair_iso,
};
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
/// text names without declaring it is.
#[test]
fn a_value_no_line_sets_is_flagged() {
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
    assert!(text.contains("var2 = sub_1040__rdx(a1);"), "{text}");
    assert!(text.contains("sub_1060(var1, var2)"), "{text}");
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

/// A field read both as a `double` and as an integer keeps its casts: named
/// as one integer field, the `double` copied out of it converted the value
/// where the machine moves the bits.
///
/// `f(dst, src)` copies `src`'s two words to `dst` through `xmm0` when the
/// first is not 3, through `rax` when it is.
#[test]
fn a_field_read_as_float_and_integer_keeps_its_casts() {
    let code = [
        0x48, 0x8b, 0x02, // ASM: mov rax,[rdx]
        0x48, 0x83, 0xf8, 0x03, // ASM: cmp rax,3
        0x74, 0x0f, // ASM: je 0x1018
        0xf2, 0x0f, 0x10, 0x42, 0x08, // ASM: movsd xmm0,[rdx+8]
        0x48, 0x89, 0x01, // ASM: mov [rcx],rax
        0xf2, 0x0f, 0x11, 0x41, 0x08, // ASM: movsd [rcx+8],xmm0
        0xeb, 0x0f, // ASM: jmp 0x1027
        0x48, 0x8b, 0x42, 0x08, // ASM: mov rax,[rdx+8]
        0x48, 0x89, 0x41, 0x08, // ASM: mov [rcx+8],rax
        0x48, 0xc7, 0x01, 0x03, 0x00, 0x00, 0x00, // ASM: mov qword [rcx],3
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0xc3, // ASM: ret
    ];
    let p = program(&code, &[]);
    let (text, _) = text_of(&p, TEXT);
    assert!(text.contains("*(double*)(a2 + 8)"), "{text}");
    runs_alike(&p, TEXT);
}

/// A caller's widest read of a result is the result's width, not its first.
///
/// `movzx edx,ax; shr eax,0x10` reads the low half first and then the upper
/// one: taken as a 16-bit result, the text cut what `g` (`mov eax,ecx; ret`)
/// hands back to its low half before the shift read the rest.
#[test]
fn a_result_is_as_wide_as_its_widest_read() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x0f, 0xb7, 0xd0, // ASM: movzx edx,ax
        0xc1, 0xe8, 0x10, // ASM: shr eax,0x10
        0x01, 0xd0, // ASM: add eax,edx
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x89, 0xc8, 0xc3]); // ASM: mov eax,ecx; ret
    let p = program(&code, &[]);
    runs_alike(&p, TEXT);
}

/// A wide literal holding a newline reads whole, where it read as the
/// one-character narrow `"%"`; a table of 16-bit values whose first entry
/// is a space is no string at all.
#[test]
fn wide_literals_read_whole_and_tables_of_words_are_none() {
    let mut code = vec![
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax,[rip+0xff9]
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend([
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax,[rip+0xff9]
        0xc3, // ASM: ret
    ]);
    let mut data = vec![0u8; 0x20];
    for (k, c) in "%ws:\n".bytes().enumerate() {
        data[2 * k] = c;
    }
    data[0x10..0x1c].copy_from_slice(&[
        0x20, 0x00, 0x22, 0x00, 0x24, 0x00, 0x26, 0x00, 0x74, 0x61, 0x69, 0x6c,
    ]);
    let p = program(&code, &data);
    let (wide, _) = text_of(&p, TEXT);
    assert!(wide.contains(r#"return L"%ws:\n";"#), "{wide}");
    let (table, _) = text_of(&p, TEXT + 0x10);
    assert!(!table.contains('"'), "{table}");
}

/// An integer read at a constant address in the image's data is the global
/// there.
///
/// It is named as the lifter names one (`g64_2008`), where the text read
/// `*(uint64_t*)0x2008`; the text's run resolves the name to the address.
#[test]
fn a_read_at_a_constant_data_address_is_a_global() {
    let code = [
        0xb8, 0x08, 0x20, 0x00, 0x00, // ASM: mov eax,0x2008
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0xc3, // ASM: ret
    ];
    let p = program(&code, &[0, 0, 0, 0, 0, 0, 0, 0, 7, 6, 5, 4, 3, 2, 1, 0]);
    let (text, _) = text_of(&p, TEXT);
    assert!(text.contains("return g64_2008;"), "{text}");
    runs_alike(&p, TEXT);
}

/// A sized `STT_OBJECT` symbol of an ELF's `.symtab` names the data it
/// marks, so the global reads by name and a byte table indexes by it,
/// converting the entry a signed read takes.
#[test]
fn an_elf_object_symbol_names_the_data_it_marks() {
    use crate::elfgen::{self, AX, EM_X86_64, ET_EXEC, PROGBITS, STRTAB, SYMTAB, Sec, WA};
    use borer_engine::program::SymbolKind;
    let mut code = vec![
        0xb8, 0x00, 0x20, 0x00, 0x00, // ASM: mov eax,0x2000
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend([0x0f, 0xb6, 0x87, 0x00, 0x20, 0x00, 0x00, 0xc3]); // ASM: movzx eax,byte [rdi+0x2000]; ret
    code.extend([0x48, 0x0f, 0xbe, 0x87, 0x00, 0x20, 0x00, 0x00, 0xc3]); // ASM: movsx rax,byte [rdi+0x2000]; ret
    let mut symtab = vec![0u8; 24];
    symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0x1000, 9));
    symtab.extend(elfgen::sym_sized(3, 0x11, 2, 0x2000, 8));
    symtab.extend(elfgen::sym_sized(9, 0x12, 1, 0x1010, 8));
    symtab.extend(elfgen::sym_sized(11, 0x12, 1, 0x1018, 9));
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, 0x1000, code),
        Sec::new(".data", PROGBITS, WA, 0x2000, vec![7, 0, 0, 0, 0, 0, 0, 0]),
        Sec::new(".symtab", SYMTAB, 0, 0x3000, symtab),
        Sec::new(".strtab", STRTAB, 0, 0x3100, b"\0f\0table\0g\0h\0".to_vec()),
    ];
    secs[2].link = 4;
    secs[2].info = 1;
    secs[2].entsize = 24;
    let bytes = elfgen::build(ET_EXEC, EM_X86_64, 0x1000, &secs);
    let p = Program::from_bytes(std::path::PathBuf::from("data.elf"), bytes).expect("parses");
    assert!(
        p.symbols
            .iter()
            .any(|s| s.name == "table" && s.kind == SymbolKind::Data && s.addr == 0x2000),
        "{:?}",
        p.symbols
    );
    let (text, _) = text_of(&p, 0x1000);
    assert!(text.contains("return table;"), "{text}");
    let (indexed, _) = text_of(&p, 0x1010);
    assert!(indexed.contains("return table[a1];"), "{indexed}");
    let (signed, _) = text_of(&p, 0x1018);
    assert!(signed.contains("return (int8_t)table[a1];"), "{signed}");
    runs_alike(&p, 0x1010);
    runs_alike(&p, 0x1018);
}

/// A call that never returns ends its path where it stands.
///
/// The text no longer jumps to the padding after it (`goto *0x1009;`),
/// whether the callee is a thunk to an import that never returns by name
/// or a function with no way back followed by `ud2`.
#[test]
fn a_call_that_never_returns_ends_the_path() {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1020
    ];
    code.resize(0x20, 0xcc);
    code.extend([0xff, 0x25, 0xda, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfda]
    code.resize(0x40, 0xcc);
    code.extend([0xeb, 0xfe]); // ASM: jmp 0x1040
    code.resize(0x60, 0xcc);
    code.extend([
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1040
        0x0f, 0x0b, // ASM: ud2
    ]);
    let mut p = program(&code, &[]);
    p.symbols = vec![Symbol {
        name: "msvcrt.dll!_CxxThrowException".to_owned(),
        addr: 0x2000,
        kind: SymbolKind::Import,
    }];
    let (thrown, _) = text_of(&p, TEXT);
    assert!(thrown.contains("_CxxThrowException("), "{thrown}");
    assert!(!thrown.contains("goto *"), "{thrown}");
    let (looped, _) = text_of(&p, TEXT + 0x60);
    assert!(!looped.contains("goto *"), "{looped}");
}

/// The ISO check agrees where the text is the C it claims to be: a
/// computed value returned, and a value handed to a callee and returned
/// from it, each run on the machine by its prototype alone.
#[test]
fn the_iso_check_agrees_where_the_text_is_c() {
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
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for entry in [TEXT, TEXT + 0x40] {
        let rows = check_generated_iso(&p, &a, &o, entry, 8, 1, 20_000).expect("the text reads");
        let text = decompile_named(&p, &a, &o, entry).unwrap_or_default();
        assert!(
            rows.iter().all(|(_, v)| *v == Verdict::Agrees),
            "{text}
{rows:?}"
        );
    }
}

/// A block that reads through a computed address what it just stored,
/// round after round, is checked in bounded time.
///
/// Each read sees the bytes written so far, and copying their values
/// into every read grew the replay's terms eightfold a round.
#[test]
fn reads_of_stores_of_reads_are_checked_in_bounded_time() {
    const ROUNDS: usize = 24;
    let mut code = vec![0x48, 0x83, 0xec, 0x18]; // ASM: sub rsp,0x18
    for _ in 0..ROUNDS {
        code.extend([0x48, 0x8b, 0x07]); // ASM: mov rax,[rdi]
        code.extend([0x48, 0x89, 0x44, 0x24, 0x08]); // ASM: mov [rsp+8],rax
        code.extend([0x48, 0x8b, 0x3c, 0x24]); // ASM: mov rdi,[rsp]
    }
    code.extend([0x48, 0x83, 0xc4, 0x18, 0xc3]); // ASM: add rsp,0x18; ret
    let p = program(&code, &[]);
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        tx.send(checked_header(&p, &a, &o, TEXT).unwrap_or_default())
    });
    let header = rx
        .recv_timeout(std::time::Duration::from_secs(60))
        .expect("the check finishes");
    assert!(header.contains("checked vs binary"), "{header}");
}

/// A block that squares the value it holds round after round is checked
/// in bounded time.
///
/// A product past the polynomials' degree stays an opaque multiply of
/// two copies of its operand, so its terms double a round, and the
/// function's proof budget leaves the block to the samples once they
/// outgrow it.
#[test]
fn values_that_double_each_round_are_checked_in_bounded_time() {
    const ROUNDS: usize = 48;
    let mut code = vec![0x48, 0x89, 0xf8]; // ASM: mov rax,rdi
    for _ in 0..ROUNDS {
        code.extend([0x48, 0x0f, 0xaf, 0xc0]); // ASM: imul rax,rax
        code.extend([0x48, 0x01, 0xf8]); // ASM: add rax,rdi
    }
    code.push(0xc3); // ASM: ret
    let p = program(&code, &[]);
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        tx.send(checked_header(&p, &a, &o, TEXT).unwrap_or_default())
    });
    let header = rx
        .recv_timeout(std::time::Duration::from_secs(60))
        .expect("the check finishes");
    assert!(header.contains("checked vs binary"), "{header}");
}

/// The repair search masks a signed quotient returned in `rax` to its lane.
///
/// The text spells the value as C converts it, which widens it by its sign where the machine's `idiv`
/// cleared the upper half; the ISO check finds the difference and the
/// repair search keeps the rendering that masks the value to its lane.
/// A function the check agrees with is answered as it was.
#[test]
fn the_repair_search_masks_a_signed_quotient_to_its_lane() {
    let mut code = vec![
        0x89, 0xc8, // ASM: mov eax,ecx
        0xb9, 0xfb, 0xff, 0xff, 0xff, // ASM: mov ecx,0xfffffffb
        0x99, // ASM: cdq
        0xf7, 0xf9, // ASM: idiv ecx
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x48, 0x89, 0xc8, 0xc3]); // ASM: mov rax,rcx; ret
    let p = program(&code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let plain = decompile_named(&p, &a, &o, TEXT).unwrap_or_default();
    let rows = check_generated_iso(&p, &a, &o, TEXT, 8, 1, 20_000).expect("the text reads");
    assert!(
        rows.iter().any(|(_, v)| matches!(v, Verdict::Differs(..))),
        "{plain}\n{rows:?}"
    );
    let r = repair_iso(&p, &a, &o, TEXT, Budget::ANSWER);
    let Repair::Repaired { moved, tried, .. } = &r else {
        panic!("{plain}\n{r:?}");
    };
    assert_eq!(moved, &[Site::Return]);
    assert!(matches!(tried.last().map(|t| &t.evidence), Some(Evidence::Tested(n)) if *n > 0));
    let (u, note) = answered(&p, &a, &o, TEXT);
    assert!(note.is_none());
    let text = decompile_named(&p, &a, &u, TEXT).unwrap_or_default();
    assert!(text.contains("& 0xffffffff;"), "{text}");
    let rows = check_generated_iso(&p, &a, &u, TEXT, 8, 1, 20_000).expect("the text reads");
    assert!(
        rows.iter().all(|(_, v)| *v == Verdict::Agrees),
        "{text}\n{rows:?}"
    );
    let (same, note) = answered(&p, &a, &o, TEXT + 0x40);
    assert!(note.is_none());
    assert_eq!(same.fingerprint(), o.fingerprint());
}

/// A 32-bit hash the function keeps in a 64-bit register is a `uint32_t`.
///
/// `lanes3` folds bytes into `h = (h << 5) - h + *p` and stores `h` as a
/// dword: no read needs more than its low half, so the text declares it
/// at 32 bits and writes no mask, and run as ISO C it agrees with the
/// binary.
#[test]
fn a_hash_stored_at_32_bits_needs_no_mask() {
    let code = [
        0x45, 0x85, 0xc0, // ASM: test r8d,r8d
        0x74, 0x24, // ASM: je 0x1029
        0x45, 0x89, 0xc0, // ASM: mov r8d,r8d
        0x31, 0xc0, // ASM: xor eax,eax
        0x45, 0x31, 0xc9, // ASM: xor r9d,r9d
        0x41, 0x89, 0xc2, // ASM: mov r10d,eax
        0x41, 0xc1, 0xe2, 0x05, // ASM: shl r10d,5
        0x41, 0x29, 0xc2, // ASM: sub r10d,eax
        0x42, 0x0f, 0xb6, 0x04, 0x0a, // ASM: movzx eax,byte [rdx+r9]
        0x44, 0x01, 0xd0, // ASM: add eax,r10d
        0x49, 0xff, 0xc1, // ASM: inc r9
        0x45, 0x39, 0xc8, // ASM: cmp r8d,r9d
        0x75, 0xe6, // ASM: jne 0x100d
        0xeb, 0x02, // ASM: jmp 0x102b
        0x31, 0xc0, // ASM: xor eax,eax
        0x89, 0x01, // ASM: mov [rcx],eax
        0xc3, // ASM: ret
    ];
    let p = program(&code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, TEXT).unwrap_or_default();
    assert!(!text.contains("0xffffffff"), "{text}");
    assert!(text.contains("uint32_t"), "{text}");
    let rows = check_generated_iso(&p, &a, &o, TEXT, 8, 1, 20_000).expect("the text reads");
    assert!(
        rows.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{text}
{rows:?}"
    );
    assert!(
        !rows.iter().any(|(_, v)| matches!(v, Verdict::Differs(..))),
        "{text}
{rows:?}"
    );
}

/// A stack pointer lowered by a size computed at run time is an `alloca`.
///
/// `dyn_sum` asks `__chkstk` to probe `n * 4` bytes rounded to sixteen,
/// lowers `rsp` by them, and fills and sums the block through `rdx`, the
/// new stack pointer. The text asks `alloca` for the size the source did
/// and indexes the block through the variable holding it; the probe is
/// no statement. Run as ISO C on its own block it agrees with the binary.
#[test]
fn a_run_time_stack_drop_is_an_alloca() {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0x4c, 0x63, 0xc9, // ASM: movsxd r9,ecx
        0x4a, 0x8d, 0x04, 0x8d, 0x0f, 0x00, 0x00, 0x00, // ASM: lea rax,[r9*4+0xf]
        0x48, 0x83, 0xe0, 0xf0, // ASM: and rax,-0x10
        0xe8, 0x58, 0x00, 0x00, 0x00, // ASM: call 0x1070
        0x48, 0x29, 0xc4, // ASM: sub rsp,rax
        0x48, 0x89, 0xe2, // ASM: mov rdx,rsp
        0x41, 0x89, 0xc8, // ASM: mov r8d,ecx
        0x45, 0x85, 0xc9, // ASM: test r9d,r9d
        0x7e, 0x1d, // ASM: jle 0x1043
        0x31, 0xc0, // ASM: xor eax,eax
        0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: nop dword [rax+rax]
        0x41, 0x89, 0xc1, // ASM: mov r9d,eax
        0x44, 0x0f, 0xaf, 0xc8, // ASM: imul r9d,eax
        0x44, 0x89, 0x0c, 0x82, // ASM: mov [rdx+rax*4],r9d
        0x48, 0xff, 0xc0, // ASM: inc rax
        0x49, 0x39, 0xc0, // ASM: cmp r8,rax
        0x75, 0xed, // ASM: jne 0x1030
        0x31, 0xc0, // ASM: xor eax,eax
        0x85, 0xc9, // ASM: test ecx,ecx
        0x7e, 0x19, // ASM: jle 0x1062
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x0f, 0x1f, 0x44, 0x00, 0x00, // ASM: nop dword [rax+rax]
        0x44, 0x8b, 0x0c, 0x8a, // ASM: mov r9d,[rdx+rcx*4]
        0x41, 0x31, 0xc9, // ASM: xor r9d,ecx
        0x44, 0x01, 0xc8, // ASM: add eax,r9d
        0x48, 0xff, 0xc1, // ASM: inc rcx
        0x49, 0x39, 0xc8, // ASM: cmp r8,rcx
        0x75, 0xee, // ASM: jne 0x1050
        0x48, 0x89, 0xec, // ASM: mov rsp,rbp
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    code.resize(0x70, 0xcc);
    code.push(0xc3); // ASM: ret
    let mut p = program(&code, &[]);
    p.symbols = vec![Symbol {
        name: "__chkstk".to_owned(),
        addr: TEXT + 0x70,
        kind: SymbolKind::Local,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, TEXT).unwrap_or_default();
    assert!(
        text.contains("var1 = alloca((int64_t)(int32_t)a1 * 4);"),
        "{text}"
    );
    assert!(text.contains("((uint32_t*)var1)["), "{text}");
    assert!(!text.contains("__chkstk"), "{text}");
    assert!(!text.contains("rsp"), "{text}");
    let rows = check_generated_iso(&p, &a, &o, TEXT, 8, 1, 200_000).expect("the text reads");
    assert!(
        rows.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{text}
{rows:?}"
    );
    assert!(
        !rows.iter().any(|(_, v)| matches!(v, Verdict::Differs(..))),
        "{text}
{rows:?}"
    );
}

/// Constant stores that spell a string are a `strcpy` of it.
///
/// `sh2` writes `"abcde"` to its frame as a dword and a word and hashes
/// it through a callee: the two slots are one `char` array the text
/// copies the literal into and hands on. `fill` writes `"hello, world"`
/// through its argument as two overlapping qwords. Run as ISO C, each
/// text agrees with the binary: the callee hashes the same bytes, and the
/// buffer holds the same bytes after the copy.
#[test]
fn constant_stores_that_spell_a_string_are_a_strcpy() {
    let mut code = vec![
        0x56, // ASM: push rsi
        0x48, 0x83, 0xec, 0x30, // ASM: sub rsp,0x30
        0x89, 0xce, // ASM: mov esi,ecx
        0xc7, 0x44, 0x24, 0x28, 0x61, 0x62, 0x63,
        0x64, // ASM: mov dword [rsp+0x28],0x64636261
        0x66, 0xc7, 0x44, 0x24, 0x2c, 0x65, 0x00, // ASM: mov word [rsp+0x2c],0x65
        0x48, 0x8d, 0x4c, 0x24, 0x28, // ASM: lea rcx,[rsp+0x28]
        0xe8, 0x10, 0x00, 0x00, 0x00, // ASM: call 0x1030
        0x01, 0xf0, // ASM: add eax,esi
        0x48, 0x83, 0xc4, 0x30, // ASM: add rsp,0x30
        0x5e, // ASM: pop rsi
        0xc3, // ASM: ret
    ];
    code.resize(0x30, 0xcc);
    code.extend([
        0x0f, 0xb6, 0x11, // ASM: movzx edx,byte [rcx]
        0x84, 0xd2, // ASM: test dl,dl
        0x74, 0x24, // ASM: je 0x105b
        0x48, 0xff, 0xc1, // ASM: inc rcx
        0x31, 0xc0, // ASM: xor eax,eax
        0x0f, 0x1f, 0x40, 0x00, // ASM: nop dword [rax]
        0x41, 0x89, 0xc0, // ASM: mov r8d,eax
        0x41, 0xc1, 0xe0, 0x05, // ASM: shl r8d,5
        0x41, 0x29, 0xc0, // ASM: sub r8d,eax
        0x0f, 0xbe, 0xc2, // ASM: movsx eax,dl
        0x44, 0x01, 0xc0, // ASM: add eax,r8d
        0x0f, 0xb6, 0x11, // ASM: movzx edx,byte [rcx]
        0x48, 0xff, 0xc1, // ASM: inc rcx
        0x84, 0xd2, // ASM: test dl,dl
        0x75, 0xe6, // ASM: jne 0x1040
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ]);
    code.resize(0x70, 0xcc);
    code.extend([
        0x48, 0xb8, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64,
        0x00, // ASM: mov rax,0x646c726f77202c
        0x48, 0x89, 0x41, 0x05, // ASM: mov [rcx+5],rax
        0x48, 0xb8, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20,
        0x77, // ASM: mov rax,0x77202c6f6c6c6568
        0x48, 0x89, 0x01, // ASM: mov [rcx],rax
        0xc3, // ASM: ret
    ]);
    let p = program(&code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for (entry, copy) in [
        (TEXT, "strcpy(local_10, \"abcde\");"),
        (TEXT + 0x70, "strcpy((char*)a1, \"hello, world\");"),
    ] {
        let text = decompile_named(&p, &a, &o, entry).unwrap_or_default();
        assert!(text.contains(copy), "{text}");
        let rows = check_generated_iso(&p, &a, &o, entry, 8, 1, 20_000).expect("the text reads");
        assert!(
            rows.iter().any(|(_, v)| *v == Verdict::Agrees),
            "{text}
{rows:?}"
        );
        assert!(
            !rows.iter().any(|(_, v)| matches!(v, Verdict::Differs(..))),
            "{text}
{rows:?}"
        );
    }
}
