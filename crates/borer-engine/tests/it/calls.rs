//! `borer://calls/{callee}` over hand-built images.
//!
//! Every call site of a function or import, with the arguments the
//! decompiler resolves and the predicate filters that narrow them.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::calls_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// A raw x64 image whose one function calls an import four times.
///
/// The import `VirtualProtect` is called with a constant protection flag
/// `0x40`, with `0x04`, with the address of a data global, and with the
/// address of a string.
///
/// The slot sits in `.data` at `0x2100`, the global at `0x2000` (zeroed, so
/// it reads as a global and not a literal), and the string at `0x2010`.
fn four_calls() -> Program {
    let mut bytes = vec![0xccu8; 0x3000];
    let code: &[u8] = &[
        // ASM: mov ecx, 0x40
        0xb9, 0x40, 0x00, 0x00, 0x00, // ASM: call qword [rip+0x10f5]  (slot 0x2100)
        0xff, 0x15, 0xf5, 0x10, 0x00, 0x00, // ASM: mov ecx, 4
        0xb9, 0x04, 0x00, 0x00, 0x00, // ASM: call qword [rip+0x10ea]
        0xff, 0x15, 0xea, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip+0xfe3]  (global 0x2000)
        0x48, 0x8d, 0x0d, 0xe3, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0x10dd]
        0xff, 0x15, 0xdd, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip+0xfe6]  (string 0x2010)
        0x48, 0x8d, 0x0d, 0xe6, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0x10d0]
        0xff, 0x15, 0xd0, 0x10, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    bytes[0x2010..0x2018].copy_from_slice(b"cmd.exe\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x2000, 0x1000, true, false),
        ],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!VirtualProtect".to_owned(),
        addr: 0x2100,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(0x1000, 0x1031)];
    p
}

/// Every call to an import through its slot is a row.
///
/// Each argument is in the position its callee reads it: a constant in hex,
/// a global by name, a string quoted, and `?` for the declared parameters
/// the site leaves unset.
#[test]
fn every_call_site_lists_its_arguments() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    assert!(
        out.starts_with("# calls to VirtualProtect (slot 0x2100): 4 sites in 1 function"),
        "{out}"
    );
    assert!(out.contains("VirtualProtect(0x40, "), "{out}");
    assert!(out.contains("&g64_2000"), "{out}");
    assert!(out.contains("\"cmd.exe\""), "{out}");
    assert!(out.contains("VirtualProtect(4, ?, ?, ?)"), "{out}");
    assert!(out.contains("# showing 4 of 4 from 0"), "{out}");
}

/// A predicate keeps only the calls whose argument matches: `a1=0x40` one
/// of the four, `a1=?` none, a text the string argument, and `a1>0x30` the
/// two above `0x30`.
#[test]
fn a_predicate_filters_the_sites() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let one = calls_tsv(&p, &a, &o, "VirtualProtect,a1=0x40").expect("calls");
    assert!(one.contains("# where a1=0x40: 1 site"), "{one}");
    assert!(one.contains("VirtualProtect(0x40, "), "{one}");
    assert!(!one.contains("VirtualProtect(4, "), "{one}");
    let text = calls_tsv(&p, &a, &o, "VirtualProtect,a1=cmd").expect("calls");
    assert!(text.contains("# where a1=cmd: 1 site"), "{text}");
    assert!(text.contains("\"cmd.exe\""), "{text}");
    let lt = calls_tsv(&p, &a, &o, "VirtualProtect,a1<0x10").expect("calls");
    assert!(lt.contains("# where a1<0x10: 1 site"), "{lt}");
    assert!(lt.contains("VirtualProtect(4, "), "{lt}");
}

/// A direct call to a discovered function is a site too, with the argument
/// the caller sets.
#[test]
fn a_direct_call_is_a_site() {
    let mut bytes = vec![0xccu8; 0x2000];
    let code: &[u8] = &[
        // ASM: mov ecx, 7
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: call 0x1060  (rel = 0x1060 - 0x100a = 0x56)
        0xe8, 0x56, 0x00, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    // ASM: mov rax, rcx; ret  (reads the first argument)
    bytes[0x1060..0x1064].copy_from_slice(&[0x48, 0x89, 0xc8, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.function_ranges = vec![(0x1000, 0x100b), (0x1060, 0x1064)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = calls_tsv(&p, &a, &o, "0x1060").expect("calls");
    assert!(out.contains(": 1 site in 1 function"), "{out}");
    assert!(out.contains("(7)"), "{out}");
}

/// The same request, run twice, gives byte-identical text.
#[test]
fn the_listing_is_deterministic() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let first = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    let second = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    assert_eq!(first, second);
}

/// An address inside a function but not its entry is refused, and a bad
/// predicate position too.
#[test]
fn a_mid_function_address_and_a_bad_predicate_are_refused() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let inside = calls_tsv(&p, &a, &o, "0x1008").expect_err("not an entry");
    assert!(inside.contains("not a function's entry"), "{inside}");
    let bad = calls_tsv(&p, &a, &o, "VirtualProtect,a0=4").expect_err("a0");
    assert!(bad.contains("count from one"), "{bad}");
}

/// A 32-bit image's call through a pointer passes its words.
///
/// `f(a, 3)` through a pointer in the first parameter's object pushes two
/// 32-bit words, so the callee is cast to a function of two `uint32_t`s;
/// `uint64_t`s would take two stack slots each and call it with four.
#[test]
fn a_32_bit_call_through_a_pointer_passes_32_bit_words() {
    let code = [
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0x6a, 0x03, // ASM: push 3
        0xff, 0x74, 0x24, 0x0c, // ASM: push dword [esp+0xc]
        0xff, 0x50, 0x04, // ASM: call [eax+4]
        0x83, 0xc4, 0x08, // ASM: add esp,8
        0xc3, // ASM: ret
    ];
    let p = crate::raw::image(Arch::X86, &code, &[]);
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::decompile::decompile(&p, &a, &Overlay::default(), 0x401000)
        .unwrap_or_default();
    assert!(
        text.contains("((uint32_t (*)(uint32_t, uint32_t))"),
        "{text}"
    );
    assert!(!text.contains("uint64_t"), "{text}");
}

/// Decompiles an arm64 function at `0x401000` that jumps through a table
/// of functions at `0x402000`, its entries `op0`, `op1`, ... after the
/// head, from `0x401020` for a head of eight words or fewer.
///
/// # Arguments
///
/// * `head` - The function's words up to its `br x3`, padded to eight.
/// * `ops` - The table functions' words, two each.
fn table_jump(head: &[u32], ops: &[u32]) -> String {
    let mut words = head.to_vec();
    words.resize(head.len().max(8), 0xd503_201f);
    let first = 0x40_1000 + 4 * from_usize(words.len());
    words.extend_from_slice(ops);
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let entries: Vec<u64> = (0..ops.len() / 2)
        .map(|k| first + 8 * from_usize(k))
        .collect();
    let table: Vec<u8> = entries.iter().flat_map(|w| w.to_le_bytes()).collect();
    let mut p = crate::raw::image(Arch::Arm64, &code, &table);
    p.symbols = entries
        .iter()
        .enumerate()
        .map(|(k, &addr)| Symbol {
            name: format!("op{k}"),
            addr,
            kind: SymbolKind::Local,
        })
        .collect();
    let a = Analysis::compute(&p);
    borer_engine::analysis::decompile::decompile(&p, &a, &Overlay::default(), 0x401000)
        .unwrap_or_default()
}

/// `adrp x9, 0x402000; add x9, x9, #0; ldr x3, [x9, x0, lsl #3]`.
const LOAD_ENTRY: [u32; 3] = [0xb000_0009, 0x9100_0129, 0xf860_7923];

/// `br x3`.
const BR_X3: u32 = 0xd61f_0060;

/// A jump through a register read from a table of functions is a tail
/// call through the table, not a computed `goto`.
///
/// `return ops[k](a, b);` on arm64 loads the entry and branches to it with
/// `br`; the callee takes the arguments the table's functions take, the
/// most any of them reads, and its result is the function's.
#[test]
fn a_jump_through_a_function_table_is_a_tail_call() {
    let mut head = LOAD_ENTRY.to_vec();
    head.extend_from_slice(&[
        0xaa01_03e0, // ASM: mov x0, x1
        0xaa02_03e1, // ASM: mov x1, x2
        BR_X3,
    ]);
    let ops = [
        0x9100_0400, // ASM: add x0, x0, #1
        0xd65f_03c0, // ASM: ret
        0xcb01_0000, // ASM: sub x0, x0, x1
        0xd65f_03c0, // ASM: ret
    ];
    let text = table_jump(&head, &ops);
    assert!(!text.contains("goto"), "{text}");
    assert!(
        text.contains("return ((uint64_t (*)(uint64_t, uint64_t))"),
        "{text}"
    );
    assert!(text.contains("(a2, a3);"), "{text}");
}

/// A jump through a table entry the lifter wrote out early, as an index
/// too long to read inline makes it, is still a tail call through the table.
///
/// Windows on Arm's `return ops[k % 3](a, b);` computes `k % 3` with a
/// multiply-high before the load, so the entry is written out as a variable
/// and the jump reads only its name. An instruction with no model that
/// writes the register after the load leaves that name standing for
/// something else, and the jump a computed `goto`.
#[test]
fn a_jump_through_a_table_entry_written_out_early_is_a_tail_call() {
    let mut head = vec![
        0x5295_5568, // ASM: mov w8, #0xaaab
        0xb000_0009, // ASM: adrp x9, 0x402000
        0x9100_0129, // ASM: add x9, x9, #0
        0x72b5_5548, // ASM: movk w8, #0xaaaa, lsl #16
        0x9ba8_7c08, // ASM: umull x8, w0, w8
        0xd361_fd08, // ASM: lsr x8, x8, #33
        0x0b08_0508, // ASM: add w8, w8, w8, lsl #1
        0x4b08_0008, // ASM: sub w8, w0, w8
        0x2a01_03e0, // ASM: mov w0, w1
        0x2a02_03e1, // ASM: mov w1, w2
        0xf868_5923, // ASM: ldr x3, [x9, w8, uxtw #3]
        BR_X3,
    ];
    let ops = [
        0x9100_0400, // ASM: add x0, x0, #1
        0xd65f_03c0, // ASM: ret
        0xcb01_0000, // ASM: sub x0, x0, x1
        0xd65f_03c0, // ASM: ret
        0x9b01_7c00, // ASM: mul x0, x0, x1
        0xd65f_03c0, // ASM: ret
    ];
    let text = table_jump(&head, &ops);
    assert!(!text.contains("goto"), "{text}");
    assert!(
        text.contains("return ((uint64_t (*)(uint64_t, uint64_t))"),
        "{text}"
    );
    head.insert(11, 0xd538_0003); // ASM: mrs x3, midr_el1
    let text = table_jump(&head, &ops);
    assert!(text.contains("goto *"), "{text}");
}

/// A table jump whose functions read a register the function never sets
/// stays a computed `goto`: the call would pass a value nothing gave it.
#[test]
fn a_table_jump_with_an_unknown_argument_stays_a_goto() {
    let mut head = LOAD_ENTRY.to_vec();
    head.push(BR_X3);
    let ops = [
        0x8b01_0000, // ASM: add x0, x0, x1
        0xd65f_03c0, // ASM: ret
        0xcb01_0000, // ASM: sub x0, x0, x1
        0xd65f_03c0, // ASM: ret
    ];
    let text = table_jump(&head, &ops);
    assert!(text.contains("goto *"), "{text}");
}

/// A table whose functions take their arguments in different registers
/// stays a computed `goto`: no one call passes what each of them reads.
#[test]
fn a_table_of_unlike_functions_stays_a_goto() {
    let mut head = LOAD_ENTRY.to_vec();
    head.push(BR_X3);
    let ops = [
        0x9100_0400, // ASM: add x0, x0, #1
        0xd65f_03c0, // ASM: ret
        0x1e60_2800, // ASM: fadd d0, d0, d0
        0xd65f_03c0, // ASM: ret
    ];
    let text = table_jump(&head, &ops);
    assert!(text.contains("goto *"), "{text}");
}

/// A table of float functions stays a computed `goto`: the call through it
/// would print an integer function pointer and pass the wrong registers.
#[test]
fn a_table_of_float_functions_stays_a_goto() {
    let mut head = LOAD_ENTRY.to_vec();
    head.push(BR_X3);
    let ops = [
        0x1e60_2800, // ASM: fadd d0, d0, d0
        0xd65f_03c0, // ASM: ret
        0x1e60_0800, // ASM: fmul d0, d0, d0
        0xd65f_03c0, // ASM: ret
    ];
    let text = table_jump(&head, &ops);
    assert!(text.contains("goto *"), "{text}");
}
