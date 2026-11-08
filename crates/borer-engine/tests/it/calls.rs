//! `borer://calls/{callee}` over hand-built images.
//!
//! Every call site of a function or import, with the arguments the
//! decompiler resolves and the predicate filters that narrow them, and the
//! `// callers pass:` header that lists a parameter's constants only when
//! every site sets it to one.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{calls_tsv, function_summary};
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

/// The callee of the `// callers pass:` images: `mov eax, ecx; ret`, which
/// reads its first argument.
const PASSED_TO: u64 = 0x40_1080;

/// The second caller of [`PASSED_TO`] in every such image, at 0x401040.
const PASSES_SEVEN: [u8; 19] = [
    0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
    0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
    0xe8, 0x32, 0x00, 0x00, 0x00, // ASM: call 0x401080
    0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
    0xc3, // ASM: ret
];

/// A raw x64 image of `first` from 0x401000, a function from `entry` to its
/// end, and [`PASSES_SEVEN`] at 0x401040, both calling [`PASSED_TO`], with
/// `data` in `.rdata` at 0x402000 and no entry point.
///
/// # Arguments
///
/// * `first` - The bytes from 0x401000, at most 0x80 of them.
/// * `entry` - Where the first function starts.
/// * `data` - The bytes of `.rdata`.
fn two_callers(first: &[u8], entry: u64, data: &[u8]) -> Program {
    let mut code = vec![0xccu8; 0x83];
    code[..first.len()].copy_from_slice(first);
    code[0x40..0x53].copy_from_slice(&PASSES_SEVEN);
    code[0x80..].copy_from_slice(&[0x89, 0xc8, 0xc3]); // ASM: mov eax, ecx; ret
    let mut p = crate::raw::image(Arch::X86_64, &code, data);
    p.entry = None;
    p.function_ranges = vec![
        (entry, 0x40_1000 + from_usize(first.len())),
        (0x40_1040, 0x40_1053),
        (PASSED_TO, 0x40_1083),
    ];
    p
}

/// Decompiles [`PASSED_TO`] in `p`.
///
/// # Arguments
///
/// * `p` - An image [`two_callers`] built.
fn callee_text(p: &Program) -> String {
    let a = Analysis::compute(p);
    borer_engine::analysis::decompile::decompile(p, &a, &Overlay::default(), PASSED_TO)
        .unwrap_or_default()
}

/// Two callers that both set the argument to 7 put `a1 = 7` in the header
/// and in the summary's `passed:` line.
///
/// The first caller's `je` lands on its `mov ecx, 7`, which runs on both
/// ways in, so nothing lands between the setup and the call.
#[test]
fn callers_that_agree_are_listed() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x02, // ASM: je 0x40100a
        0x31, 0xc0, // ASM: xor eax, eax
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x6c, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let p = two_callers(&first, 0x40_1000, &[]);
    let text = callee_text(&p);
    assert!(text.contains("// callers pass: a1 = 7\n"), "{text}");
    let a = Analysis::compute(&p);
    let summary = function_summary(&p, &a, &Overlay::default(), PASSED_TO).unwrap_or_default();
    assert!(summary.contains("passed:   a1 = 7\n"), "{summary}");
}

/// A branch that lands between the setup and the call is a way in the setup
/// does not run on, so the callers no longer agree.
///
/// `mov ecx, 5; test edx, edx; je C; mov ecx, 7; C: call` passes 5 when its
/// second argument is zero; reading the `mov ecx, 7` that falls into the
/// call as its setup made the header say both callers pass 7.
#[test]
fn a_branch_onto_the_call_passes_no_agreed_constant() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x05, // ASM: je 0x401012
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x69, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let p = two_callers(&first, 0x40_1000, &[]);
    let text = callee_text(&p);
    assert!(!text.contains("callers pass"), "{text}");
    let a = Analysis::compute(&p);
    let summary = function_summary(&p, &a, &Overlay::default(), PASSED_TO).unwrap_or_default();
    assert!(!summary.contains("passed:"), "{summary}");
}

/// A jump back to the call that the walk decodes after the call is a way in
/// too: the call's setup is read once the walk has every branch.
///
/// `jne X` is followed after the fall-through path, so `X: mov ecx, 5; jmp
/// C` comes after the call at `C` it lands on.
#[test]
fn a_jump_to_the_call_found_after_it_counts_too() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x85, 0xd2, // ASM: test edx, edx
        0x75, 0x0f, // ASM: jne 0x401017
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x6e, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0xeb, 0xef, // ASM: jmp 0x40100d
    ];
    let text = callee_text(&two_callers(&first, 0x40_1000, &[]));
    assert!(!text.contains("callers pass"), "{text}");
}

/// A jump table's case that lands on the call is a way in no branch names.
///
/// Case 0 enters the call with whatever `ecx` holds and case 1 sets it to
/// 7 first; the table lists case 0 first, so the walk reaches the call by
/// falling from case 1 before it takes case 0's way in.
#[test]
fn a_jump_table_case_on_the_call_counts_too() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x83, 0xfa, 0x01, // ASM: cmp edx, 1
        0x77, 0x1e, // ASM: ja 0x401027
        0x4c, 0x8d, 0x05, 0xf0, 0xff, 0xff, 0xff, // ASM: lea r8, [rip - 0x10]
        0x41, 0x8b, 0x84, 0x90, 0x00, 0x10, 0x00,
        0x00, // ASM: mov eax, dword ptr [r8 + rdx*4 + 0x1000]
        0x4c, 0x01, 0xc0, // ASM: add rax, r8
        0xff, 0xe0, // ASM: jmp rax
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x59, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let table: Vec<u8> = [0x22u32, 0x1d]
        .iter()
        .flat_map(|o| o.to_le_bytes())
        .collect();
    let p = two_callers(&first, 0x40_1000, &table);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&0x40_101b),
        Some(&vec![0x40_1022, 0x40_101d]),
        "the table was not resolved"
    );
    let text = callee_text(&p);
    assert!(!text.contains("callers pass"), "{text}");
}

/// A call at a function's entry takes nothing from a block below it that
/// falls into the entry: the function's own callers come in there too.
///
/// `B: mov ecx, 5; E: call; test eax, eax; jne B; ret` starts at `E`, and
/// only its back edge runs `B`.
#[test]
fn a_call_at_the_entry_takes_nothing_from_the_block_below() {
    let first = [
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0xe8, 0x76, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x85, 0xc0, // ASM: test eax, eax
        0x75, 0xf2, // ASM: jne 0x401000
        0xc3, // ASM: ret
    ];
    let text = callee_text(&two_callers(&first, 0x40_1005, &[]));
    assert!(!text.contains("callers pass"), "{text}");
}

/// A site that passes a variable leaves the parameter unknown, so the
/// other caller's 7 is no agreement.
#[test]
fn a_site_passing_a_variable_leaves_no_agreed_constant() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x89, 0xd1, // ASM: mov ecx, edx
        0xe8, 0x75, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let text = callee_text(&two_callers(&first, 0x40_1000, &[]));
    assert!(!text.contains("callers pass"), "{text}");
}

/// A function the program reaches through its address has callers no call
/// site shows, so its calls' agreement says nothing about them.
///
/// Both callers pass 7, but `.rdata` holds the function's address, or the
/// first caller loads it with `lea`, or the image exports it.
#[test]
fn a_function_reached_through_its_address_lists_no_callers() {
    let first = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x72, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let plain = callee_text(&two_callers(&first, 0x40_1000, &[]));
    assert!(plain.contains("// callers pass: a1 = 7\n"), "{plain}");
    let pointer = callee_text(&two_callers(&first, 0x40_1000, &PASSED_TO.to_le_bytes()));
    assert!(!pointer.contains("callers pass"), "{pointer}");
    let loads = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x8d, 0x05, 0x75, 0x00, 0x00, 0x00, // ASM: lea rax, [rip + 0x75]
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x6b, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let loaded = callee_text(&two_callers(&loads, 0x40_1000, &[]));
    assert!(!loaded.contains("callers pass"), "{loaded}");
    let mut p = two_callers(&first, 0x40_1000, &[]);
    p.symbols.push(Symbol {
        name: "passed_to".to_owned(),
        addr: PASSED_TO,
        kind: SymbolKind::Export,
    });
    let exported = callee_text(&p);
    assert!(!exported.contains("callers pass"), "{exported}");
}

/// A function with more references than its list keeps may have lost one
/// that takes its address, so its calls' agreement says nothing either.
///
/// One caller sets the argument to 7 before each of 65,536 calls, as many
/// sites as a list keeps, and `.rdata` holds the function's address, a
/// reference read only once the calls filled the list.
#[test]
fn a_function_with_more_references_than_listed_lists_no_callers() {
    /// The references one function's list keeps.
    const LISTED: usize = 65_536;
    let callee = 0x40_1000 + from_usize(LISTED * 10 + 0x20);
    let mut code = vec![0x48, 0x83, 0xec, 0x28]; // ASM: sub rsp, 0x28
    for _ in 0..LISTED {
        let next = 0x40_1000 + from_usize(code.len() + 10);
        let rel = i32::try_from(callee - next).expect("near");
        code.extend_from_slice(&[0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8]); // ASM: mov ecx, 7; call
        code.extend_from_slice(&rel.to_le_bytes());
    }
    code.extend_from_slice(&[0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
    code.resize(LISTED * 10 + 0x10, 0xcc);
    let next = 0x40_1000 + from_usize(code.len() + 10);
    let rel = i32::try_from(callee - next).expect("near");
    code.extend_from_slice(&[0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8]); // ASM: mov ecx, 7; call
    code.extend_from_slice(&rel.to_le_bytes());
    code.extend_from_slice(&[0xc3, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc]); // ASM: ret; int3 x5
    code.extend_from_slice(&[0x89, 0xc8, 0xc3]); // ASM: mov eax, ecx; ret
    let size = code.len().next_multiple_of(0x1000);
    let mut bytes = code;
    bytes.resize(size + 0x1000, 0);
    bytes[size..size + 8].copy_from_slice(&callee.to_le_bytes());
    let text_size = from_usize(size);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x40_0000,
        None,
        vec![
            Section::mapped(".text", 0x40_1000, 0, text_size, false, true),
            Section::mapped(
                ".rdata",
                0x40_1000 + text_size,
                text_size,
                0x1000,
                false,
                false,
            ),
        ],
    );
    p.function_ranges = vec![
        (0x40_1000, callee - 0x10),
        (callee - 0x10, callee - 0x5),
        (callee, callee + 3),
    ];
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::decompile::decompile(&p, &a, &Overlay::default(), callee)
        .unwrap_or_default();
    assert!(!text.contains("callers pass"), "{text}");
}

/// A site only a function's earlier walk read counts for nothing.
///
/// The first caller's first walk follows `call N` and reads `mov ecx, edx;
/// call F`; once `N: ud2` proves never to return, it is walked again and
/// ends at `call N`. The two callers left both pass 7.
#[test]
fn a_site_only_an_earlier_walk_read_counts_for_nothing() {
    let mut first = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x57, 0x00, 0x00, 0x00, // ASM: call 0x401060
        0x89, 0xd1, // ASM: mov ecx, edx
        0xe8, 0x70, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    first.resize(0x20, 0xcc);
    first.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0x52, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ]);
    first.resize(0x60, 0xcc);
    first.extend_from_slice(&[0x0f, 0x0b]); // ASM: ud2
    let mut p = two_callers(&first, 0x40_1000, &[]);
    p.function_ranges = vec![
        (0x40_1000, 0x40_1015),
        (0x40_1020, 0x40_1033),
        (0x40_1040, 0x40_1053),
        (0x40_1060, 0x40_1062),
        (PASSED_TO, 0x40_1083),
    ];
    let a = Analysis::compute(&p);
    let rewalked = a.function(0x40_1000).expect("the first caller");
    assert!(
        !rewalked.callees.contains(&PASSED_TO),
        "{:x?}",
        rewalked.callees
    );
    let text = callee_text(&p);
    assert!(text.contains("// callers pass: a1 = 7\n"), "{text}");
}

/// A tail jump passes the function what it set, as a call does.
///
/// `mov ecx, 9; jmp F` and `mov ecx, 9; test edx, edx; jne F; ret` each
/// pass 9 where the other caller passes 7.
#[test]
fn a_tail_jump_passes_its_constants_too() {
    let jumps = [
        0xb9, 0x09, 0x00, 0x00, 0x00, // ASM: mov ecx, 9
        0xeb, 0x79, // ASM: jmp 0x401080
    ];
    let text = callee_text(&two_callers(&jumps, 0x40_1000, &[]));
    assert!(text.contains("// callers pass: a1 = 7, 9\n"), "{text}");
    let branches = [
        0xb9, 0x09, 0x00, 0x00, 0x00, // ASM: mov ecx, 9
        0x85, 0xd2, // ASM: test edx, edx
        0x75, 0x77, // ASM: jne 0x401080
        0xc3, // ASM: ret
    ];
    let text = callee_text(&two_callers(&branches, 0x40_1000, &[]));
    assert!(text.contains("// callers pass: a1 = 7, 9\n"), "{text}");
}

/// A two-byte jump right before the function is a thunk to it, which passes
/// on whatever its own callers gave it.
#[test]
fn a_thunk_into_the_function_passes_no_agreed_constant() {
    let mut thunk = vec![0xccu8; 0x7e];
    thunk.extend_from_slice(&[0xeb, 0x00]); // ASM: jmp 0x401080
    let text = callee_text(&two_callers(&thunk, 0x40_107e, &[]));
    assert!(!text.contains("callers pass"), "{text}");
}
