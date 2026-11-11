//! Unpacking, devirtualizing and the emulator's answers.

use super::*;

/// A dispatch loop is found and its handlers described.
///
/// An interpreter fetches an operation, jumps through a table to the code
/// for it, and comes back; a virtualizing protector leaves exactly that
/// where the original function used to be. The machine here has sixteen
/// handlers, each adding its own number and jumping back, which is the
/// smallest thing that has the shape.
#[test]
fn a_dispatch_loop_is_found_with_its_handlers() {
    const TABLE: u64 = 0x8000;
    const FIRST: u64 = 0x1020;
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.extend_from_slice(&[
        0x48, 0x8d, 0x35, 0xf9, 0x70, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x48, 0xff, 0xc6, 0x83, 0xf8,
        0x0f, 0x77, 0x07, 0xff, 0x24, 0xc5, 0x00, 0x80, 0x00, 0x00, 0xc3,
    ]);
    bytes.resize(usize::try_from(FIRST).unwrap_or(0), 0xcc);
    for i in 0..16u64 {
        let at = FIRST + i * 16;
        bytes.resize(usize::try_from(at).unwrap_or(0), 0xcc);
        let back = i32::try_from(0x1007i64 - i64::try_from(at + 9).unwrap_or(0)).unwrap_or(0);
        bytes.extend_from_slice(&[0x48, 0x83, 0xc3, u8::try_from(i).unwrap_or(0), 0xe9]);
        bytes.extend_from_slice(&back.to_le_bytes());
    }
    bytes.resize(usize::try_from(TABLE).unwrap_or(0), 0xcc);
    for i in 0..16u64 {
        bytes.extend_from_slice(&(FIRST + i * 16).to_le_bytes());
    }
    bytes.resize(0x9000, 0);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x7000, false, true),
            Section::mapped(".rdata", TABLE, TABLE, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    assert!(list.contains("      16 "), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(one.contains("16 handlers"), "{one}");
    let next = borer_engine::analysis::render::next_steps(&p, &a, &o, 0x1000);
    assert!(
        next.first()
            .is_some_and(|s| s.starts_with("borer://vm/0x1000 (a dispatch loop of 16 handlers")),
        "{next:?}"
    );
    assert!(
        one.contains("add"),
        "the handlers say nothing about what they do: {one}"
    );
    assert!(one.contains("0x1020"), "{one}");
    assert!(
        one.contains("read through rsi, pointed at 0x8100"),
        "the bytecode pointer and its address are not named: {one}"
    );
}

/// A rel32 jump table whose targets sit below its lea'd base resolves.
///
/// The entries are negative offsets, and reading them unsigned lands the
/// targets far outside every section, which is exactly the table a
/// hand-built interpreter over read-only data carries.
#[test]
fn a_rel32_table_with_targets_below_it_resolves() {
    let p = small_vm(true);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&VM_JMP),
        Some(&vec![0x1030, 0x1035, 0x103a, 0x103f, 0x1044]),
        "the negative rel32 entries did not read as their handlers"
    );
}

/// A dispatch of five handlers is found when it fetches its index from
/// memory, and the same loop with a computed index is not.
///
/// The first is an interpreter's shape: read the next opcode out of the
/// program, jump through the table for it, come back. The second is the
/// ordinary small `switch` the handler floor has always refused, and the
/// fetch is the only difference between them.
#[test]
fn a_small_dispatch_that_fetches_from_memory_is_found() {
    let p = small_vm(true);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    assert!(list.contains("     5 "), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x102e").unwrap();
    assert!(one.contains("5 handlers"), "{one}");
    assert!(one.contains("add"), "the handlers say nothing: {one}");
    let plain = small_vm(false);
    let pa = Analysis::compute(&plain);
    let refused = borer_engine::analysis::render::vm_dispatch_tsv(&plain, &pa, &o, "").unwrap();
    assert!(refused.starts_with("# 0 dispatch loops found"), "{refused}");
}

/// A dispatch whose fetch is xored with a running key is named as one.
///
/// The machine here is `VoidVault v7.1`'s shape in miniature: the fetch reads
/// three operands through one base, the immediate is xored with `rbx` before
/// the jump, and every handler returns through a tail that calls a mixer,
/// xors its result with a register-file slot and writes it back into `rbx`.
/// The bytecode on disk is then noise for every run but the one that
/// produced it, and the view must say so rather than leave the reader to
/// discover it opcode by opcode.
///
/// # Panics
///
/// Never in practice: every displacement constant fits by construction.
#[test]
fn a_running_key_fetch_is_named_in_the_dispatch_view() {
    const TABLE: u64 = 0x8000;
    const PROG: u64 = 0x9000;
    const HANDLER: u64 = 0x1040;
    const TAIL: u64 = 0x10a0;
    const MIXER: u64 = 0x10b8;
    let mut bytes = vec![0xccu8; 0x1000];
    let mut code: Vec<u8> = Vec::new();
    code.extend_from_slice(&[0x4c, 0x8d, 0x0d]);
    code.extend_from_slice(&i32::try_from(PROG - 0x1007).unwrap().to_le_bytes());
    code.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
    code.extend_from_slice(&i32::try_from(TABLE - 0x100e).unwrap().to_le_bytes());
    code.extend_from_slice(&[0x41, 0x0f, 0xb6, 0x11]);
    code.extend_from_slice(&[0x45, 0x0f, 0xb6, 0x51, 0x01]);
    code.extend_from_slice(&[0x49, 0x8b, 0x49, 0x04]);
    code.extend_from_slice(&[0x48, 0x31, 0xd9]);
    code.extend_from_slice(&[0x49, 0x83, 0xc1, 0x02]);
    code.extend_from_slice(&[0x80, 0xfa, 0x0b]);
    code.extend_from_slice(&[0x0f, 0x87]);
    code.extend_from_slice(&(i32::try_from(MIXER - 0x102b).unwrap()).to_le_bytes());
    code.extend_from_slice(&[0x49, 0x63, 0x14, 0x93]);
    code.extend_from_slice(&[0x4c, 0x01, 0xda]);
    code.extend_from_slice(&[0xff, 0xe2]);
    bytes.extend_from_slice(&code);
    for i in 0..12u8 {
        let at = HANDLER + u64::from(i) * 8;
        bytes.resize(usize::try_from(at).unwrap(), 0xcc);
        bytes.extend_from_slice(&[0x83, 0xc3, i]);
        let back = i32::try_from(TAIL - (at + 8)).unwrap();
        bytes.extend_from_slice(&[0xe9]);
        bytes.extend_from_slice(&back.to_le_bytes());
    }
    bytes.resize(usize::try_from(TAIL).unwrap(), 0xcc);
    bytes.extend_from_slice(&[0xe8]);
    bytes.extend_from_slice(&i32::try_from(MIXER - (TAIL + 5)).unwrap().to_le_bytes());
    bytes.extend_from_slice(&[0x4b, 0x33, 0x04, 0xa8]);
    bytes.extend_from_slice(&[0x48, 0x89, 0xc3]);
    bytes.extend_from_slice(&[0xe9]);
    bytes.extend_from_slice(
        &i32::try_from(0x100ei64 - i64::try_from(TAIL).unwrap() - 0x11)
            .unwrap()
            .to_le_bytes(),
    );
    bytes.resize(usize::try_from(MIXER).unwrap(), 0xcc);
    bytes.extend_from_slice(&[0xc3]);
    bytes.resize(usize::try_from(TABLE).unwrap(), 0xcc);
    for i in 0..12u64 {
        let entry = i32::try_from(HANDLER + i * 8).unwrap() - i32::try_from(TABLE).unwrap();
        bytes.extend_from_slice(&entry.to_le_bytes());
    }
    bytes.resize(usize::try_from(PROG).unwrap(), 0xcc);
    bytes.extend_from_slice(&[3, 0, 0, 0x5a, 2, 3, 3, 0, 1, 0x33, 2, 7]);
    bytes.resize(0xA000, 0);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x7000, false, true),
            Section::mapped(".rdata", TABLE, TABLE, 0x2000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(one.contains("12 handlers"), "{one}");
    assert!(
        one.contains("running-key fetch"),
        "the running key is not named: {one}"
    );
    assert!(
        one.contains("xored with rbx"),
        "the key register is not named: {one}"
    );
    assert!(
        one.contains(&format!("mixer at {MIXER:#x}")),
        "the mixer is not named: {one}"
    );
    assert!(
        one.contains("solve per input step with derailment as the oracle"),
        "the reading is not told how to proceed: {one}"
    );
}

/// A string built on the stack a byte at a time is recovered.
///
/// Malware keeps a string out of the data sections by writing it onto the
/// stack piece by piece; here a function spells a URL with thirteen
/// byte stores, and the recovery reads it back while a plain function offers
/// nothing.
#[test]
fn a_stack_string_is_recovered_from_its_stores() {
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.extend_from_slice(&[
        0xc6, 0x44, 0x24, 0x10, 0x68, 0xc6, 0x44, 0x24, 0x11, 0x74, 0xc6, 0x44, 0x24, 0x12, 0x74,
        0xc6, 0x44, 0x24, 0x13, 0x70, 0xc6, 0x44, 0x24, 0x14, 0x3a, 0xc6, 0x44, 0x24, 0x15, 0x2f,
        0xc6, 0x44, 0x24, 0x16, 0x2f, 0xc6, 0x44, 0x24, 0x17, 0x78, 0xc6, 0x44, 0x24, 0x18, 0x2e,
        0xc6, 0x44, 0x24, 0x19, 0x69, 0xc6, 0x44, 0x24, 0x1a, 0x6f, 0xc6, 0x44, 0x24, 0x1b, 0x2f,
        0xc6, 0x44, 0x24, 0x1c, 0x61, 0xc3,
    ]);
    bytes.resize(0x2000, 0xcc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "");
    assert!(
        text.contains("http://x.io/a"),
        "the stack string is not recovered: {text}"
    );
    let filtered = borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "x.io");
    assert!(filtered.contains("http://x.io/a"), "{filtered}");
    assert!(
        !borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "notthere").contains("http"),
        "the filter let everything through"
    );
    let plain = borer_engine::analysis::render::stack_strings_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
        "",
    );
    assert!(
        plain.starts_with("# 0 ") || !plain.contains("http"),
        "{plain}"
    );
}

/// The emulator runs a self-contained decoder and reads its plaintext.
///
/// A crypter puts a decoder in front of its strings: the routine carries its
/// own source pointer, length and key, reads the embedded ciphertext, and
/// writes the plaintext. Running it is the exact way to read that text with
/// no key to guess. Here a decoder at 0x1000 turns the ciphertext at 0x2000
/// into a URL at 0x2800.
#[test]
fn the_emulator_decodes_a_self_contained_string() {
    let code = [
        0x48u8, 0xb9, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xba, 0x00, 0x20, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x34, 0x5a,
        0x42, 0x88, 0x04, 0x11, 0x49, 0xff, 0xc2, 0x49, 0x83, 0xfa, 0x10, 0x72, 0xec, 0xc3,
    ];
    let enc = [
        0x32u8, 0x2e, 0x2e, 0x2a, 0x60, 0x75, 0x75, 0x39, 0x68, 0x74, 0x32, 0x35, 0x29, 0x2e, 0x75,
        0x22,
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".flat", 0, 0, 0x3000, true, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::emulate_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(
        text.contains("returned"),
        "the decoder did not return: {text}"
    );
    assert!(
        text.contains("http://c2.host/x"),
        "the plaintext was not decoded: {text}"
    );
}

/// The emulator resource takes arguments read from a decoder's call site.
///
/// A decoder that takes `(dst, src, len, key)` is run by naming those in the
/// target, `0x1000,rcx=0x2800,rdx=0x2000,r8=16,r9=0x5a`, the values an
/// analyst reads at the call. It XORs the ciphertext at 0x2000 into plaintext
/// at 0x2800.
#[test]
fn the_emulator_takes_call_site_arguments() {
    let code = [
        0x4du8, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04, 0x11,
        0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
    ];
    let enc = [
        0x29u8, 0x3f, 0x39, 0x28, 0x3f, 0x2e, 0x7a, 0x2a, 0x3b, 0x23, 0x36, 0x35, 0x3b, 0x3e, 0x7b,
        0x7b,
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".flat", 0, 0, 0x3000, true, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::emulate_tsv(
        &p,
        &a,
        &o,
        "0x1000,rcx=0x2800,rdx=0x2000,r8=0x10,r9=0x5a",
    )
    .unwrap();
    assert!(
        text.contains("secret payload!!"),
        "arguments not applied: {text}"
    );
}

/// The devirtualizer runs a bytecode interpreter and recovers its program.
///
/// `VM` is a real interpreter: `rsi` is the virtual instruction pointer over
/// the bytecode `[0, 1, 2, 3]`, the dispatch jumps through a table to a
/// handler per opcode, and each handler runs an operation and loops back.
/// Running it recovers the four steps as one straight-line run, `v0` to
/// `v3`, with each handler's effect, which is the virtualized function's
/// real logic.
#[test]
fn the_devirtualizer_recovers_a_virtual_program() {
    let code = [
        0x48u8, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x31, 0xdb, 0x0f, 0xb6, 0x06, 0x48, 0xff, 0xc6,
        0x83, 0xf8, 0x03, 0x77, 0x07, 0xff, 0x24, 0xc5, 0x00, 0x21, 0x00, 0x00, 0xc3, 0x83, 0xc3,
        0x01, 0xe9, 0xe5, 0xff, 0xff, 0xff, 0x83, 0xc3, 0x02, 0xe9, 0xdd, 0xff, 0xff, 0xff, 0x83,
        0xf3, 0x7f, 0xe9, 0xd5, 0xff, 0xff, 0xff, 0xc3,
    ];
    let mut bytes = vec![0xccu8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2004].copy_from_slice(&[0, 1, 2, 3]);
    for (i, h) in [0x101cu64, 0x1024, 0x102c, 0x1034].iter().enumerate() {
        bytes[0x2100 + i * 8..0x2100 + i * 8 + 8].copy_from_slice(&h.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x1035)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::devirtualize_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(
        text.contains("4 virtual instructions"),
        "the program length is wrong: {text}"
    );
    assert!(
        text.contains("# virtual program: 4 of 4 instructions in 1 run"),
        "the program is not rendered as one run: {text}"
    );
    assert!(
        text.contains("  v0 = add;\n  v1 = add;\n  v2 = xor;"),
        "the steps are wrong: {text}"
    );
    assert!(
        text.contains("xor"),
        "the handler effects are missing: {text}"
    );
}

/// The emulator unpacks self-modifying code and recovers the hidden routine.
///
/// The stub at `0x1000` is a packer: it XOR-decrypts six bytes from `0x2000`
/// into the executable region at `0x3000`, then jumps there. On disk `0x3000`
/// holds only `int3` padding, so the hidden routine exists solely as the bytes
/// the run writes. Recovering `mov eax, 0x2a; ret` proves the emulator fetched
/// its own writes as code and that the trace found the original entry point.
#[test]
fn the_unpacker_materializes_self_modifying_code() {
    let code: [u8; 45] = [
        0x48, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0xb9,
        0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a, 0x88, 0x07, 0x48, 0xff, 0xc6, 0x48,
        0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05, 0xd5, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0xccu8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x3000, 0x3000, 0x1000, true, true),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x102d)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "").unwrap();
    assert!(
        text.contains("original entry point"),
        "no entry point recovered: {text}"
    );
    assert!(text.contains("0x3000"), "wrong materialized region: {text}");
    assert!(
        text.contains("mov eax,2Ah") || text.contains("mov eax,0x2a"),
        "the decrypted routine was not disassembled: {text}"
    );
    assert!(
        text.contains("entropy"),
        "the materialized region's entropy was not reported: {text}"
    );
}

/// An unpacked PE materializes into a section the file backs with no bytes.
///
/// The same packer stub, but as a PE whose destination section has a megabytes-
/// wide virtual size and zero raw bytes, the shape a protector's `.themida`
/// takes. Writing the payload back at the original file offsets would drop it,
/// since the file has no room there; rebuilding the image in memory layout
/// gives the write a home, so re-analysis discovers the routine the run
/// decrypted into `0x3000`. Before, the report carried no re-analysis at all.
#[test]
fn an_unpacked_pe_materializes_a_virtual_only_section() {
    let code: [u8; 45] = [
        0x48, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0xb9,
        0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a, 0x88, 0x07, 0x48, 0xff, 0xc6, 0x48,
        0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05, 0xd5, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0xccu8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
            Section {
                file_size: 0,
                ..Section::mapped(".themida", 0x3000, 0, 0x1000, true, true)
            },
        ],
    );
    p.format = BinaryFormat::Pe;
    p.function_ranges = vec![(0x1000, 0x102d)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "").unwrap();
    assert!(
        text.contains("re-analyzed the materialized image"),
        "the virtual-only write was not rebuilt: {text}"
    );
    assert!(
        text.contains("only the materialized image has") && text.contains("0x3000"),
        "the decrypted routine was not discovered in the rebuilt image: {text}"
    );
}

/// The emulator maps the PE header page the way the OS loader would.
///
/// A packer's bootstrap walks its own headers to find its imports: it reads
/// `e_lfanew` at `image_base + 0x3c`, which lies below the first section and
/// so is backed by no section's file bytes. The emulator serves it from the
/// header page at the image base, as the loader does. The stub reads that byte
/// and stores it, so a clean return with a materialized byte proves the header
/// read resolved instead of faulting.
#[test]
fn the_unpacker_maps_the_header_page() {
    let code: [u8; 17] = [
        0x0f, 0xb6, 0x05, 0x35, 0xf0, 0xff, 0xff, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0x88,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x3c] = 0x40;
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![Section::mapped(
            ".data",
            0x1_4000_3000,
            0x3000,
            0x1000,
            true,
            false,
        )],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(text.contains("returned"), "the header read faulted: {text}");
    assert!(
        text.contains("1 region"),
        "the header byte was not stored: {text}"
    );
}

/// A run that writes only data is not analyzed again; one that writes into
/// an executable section is.
///
/// The second analysis of the rebuilt image cost as much as the first, a
/// plain program's startup writes only its globals, and the code it would
/// analyze is byte for byte the original's; on borer's own build under load
/// the unpack request spent minutes there. The same store into a section
/// that is executable may be code, so that image is analyzed again.
#[test]
fn an_unpack_that_writes_only_data_is_not_analyzed_again() {
    let code: [u8; 17] = [
        0x0f, 0xb6, 0x05, 0x35, 0xf0, 0xff, 0xff, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0x88,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x3c] = 0x40;
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    for (executable, again) in [(false, false), (true, true)] {
        let p = packed_pe(
            bytes.clone(),
            code.len(),
            vec![Section::mapped(
                ".data",
                0x1_4000_3000,
                0x3000,
                0x1000,
                true,
                executable,
            )],
        );
        let a = Analysis::compute(&p);
        let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &Overlay::default(), "")
            .expect("the stub runs");
        assert!(text.contains("1 region"), "{text}");
        assert_eq!(
            text.contains("re-analyzed the materialized image"),
            again,
            "{text}"
        );
        assert_eq!(
            text.contains(
                "# not re-analyzed: every byte the run wrote is data, outside the image's executable sections, and none of it ran"
            ),
            !again,
            "{text}"
        );
    }
}

/// The emulator services an imported call the OS loader would have resolved.
///
/// The stub calls `GetModuleHandleA` through its import-address-table slot. On
/// a static image that slot is zero, so the call would fault; the emulator
/// prefills it with a stub, recognizes the call, and models the API (a module
/// handle is the image base). The stub stores the result and returns, so a
/// clean return proves the imported call was serviced rather than followed
/// into nothing.
#[test]
fn the_unpacker_services_an_imported_call() {
    let code: [u8; 17] = [
        0xff, 0x15, 0xfa, 0x1f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x03, 0x20, 0x00, 0x00, 0x48, 0x89,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let mut p = packed_pe(
        bytes,
        code.len(),
        vec![Section::mapped(
            ".data",
            0x1_4000_3000,
            0x3000,
            0x1000,
            true,
            false,
        )],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetModuleHandleA".to_owned(),
        addr: 0x1_4000_3000,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(
        text.contains("GetModuleHandleA"),
        "the imported call was not reported: {text}"
    );
    assert!(
        text.contains("returned"),
        "the imported call faulted: {text}"
    );
}

/// The emulator runs `rep movs`, the instruction a packer copies payload with.
///
/// `cld; rep movsb` copies six bytes from a read-only source into a writable
/// region, driven by the count in `rcx`. Recovering all six bytes as a
/// materialized region proves the repeated string move ran to completion
/// rather than stopping after one step.
#[test]
fn the_unpacker_runs_a_rep_movs() {
    let code: [u8; 4] = [0xfc, 0xf3, 0xa4, 0xc3];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2006].copy_from_slice(b"ABCDEF");
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".rodata", 0x1_4000_2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, true),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(
        &p,
        &a,
        &o,
        "0x140001000,rcx=6,rsi=0x140002000,rdi=0x140003000",
    )
    .unwrap();
    assert!(text.contains("returned"), "the copy faulted: {text}");
    assert!(
        text.contains("0x140003000..0x140003006"),
        "the six bytes were not all copied: {text}"
    );
}

/// The emulator maps a section's page-rounded tail, as the loader does.
///
/// A section's virtual size is rarely a whole page; the loader rounds it up to
/// the page boundary and zero-fills the remainder, so a packer's decrypt loop
/// that runs to the end of a section reads mapped zeroes there rather than
/// faulting. Section `.bss` sizes `0x800` but the read at offset `0x900` lies
/// in its rounded-up page. A clean return proves the tail was mapped.
#[test]
fn the_unpacker_maps_a_page_rounded_tail() {
    let code: [u8; 5] = [0x8a, 0x06, 0x88, 0x07, 0xc3];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".bss", 0x1_4000_2000, 0x2000, 0x800, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(
        &p,
        &a,
        &o,
        "0x140001000,rsi=0x140002900,rdi=0x140003000",
    )
    .unwrap();
    assert!(
        text.contains("returned"),
        "the page-rounded tail faulted: {text}"
    );
}

/// Best-effort mode skips an unresolved import call and reaches the payload.
///
/// The stub calls through an import slot the loader would fill but a static
/// run leaves zero, then decrypts a routine and jumps to it. Best-effort is the
/// default: the call is skipped as a stub returning zero, so the decrypt runs
/// and the hidden `mov eax, 0x2a; ret` is recovered at its entry point. A
/// `strict` token faults at that call instead, pinning what the bootstrap
/// still needs.
#[test]
fn best_effort_skips_an_unresolved_call_to_reach_the_payload() {
    let code: [u8; 51] = [
        0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x35, 0xf3, 0x10, 0x00, 0x00, 0x48, 0x8d,
        0x3d, 0xec, 0x1f, 0x00, 0x00, 0xb9, 0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a,
        0x88, 0x07, 0x48, 0xff, 0xc6, 0x48, 0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05,
        0xcf, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2100..0x2106].copy_from_slice(&enc);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".rdata", 0x1_4000_2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, true),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let best = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(
        best.contains("skipped"),
        "the skip was not reported: {best}"
    );
    assert!(
        best.contains("original entry point"),
        "best-effort did not reach the payload: {best}"
    );
    assert!(
        best.contains("mov eax,2Ah") || best.contains("mov eax,0x2a"),
        "the decrypted routine was not recovered: {best}"
    );
    let strict =
        borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000,strict").unwrap();
    assert!(
        !strict.contains("original entry point"),
        "strict mode should stop at the unresolved call: {strict}"
    );
}

/// The oracle runs a function and reports what it returned.
///
/// A constant table says which algorithm a function resembles; running it on
/// the published probe says which algorithm it is. On a real binary this
/// turns "a table matching CRC-32C is present" into "this function returns
/// the CRC-32C check value".
#[test]
fn the_oracle_runs_a_function_and_reports_its_result() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0x1810").unwrap();
    assert!(out.contains("# ran "), "{out}");
    assert!(out.contains("rax "), "{out}");
    let missing = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0xdeadbeef").unwrap_err();
    assert!(missing.contains("no discovered function"), "{missing}");
}

/// A function that returns in no argument shape is reported once per shape.
///
/// The table listed the first four of the eight tries, a strict and a
/// lenient run per shape, so two shapes appeared twice and two not at all;
/// its header promises one outcome per shape. `NR` spins at `jmp $`, so
/// every try runs out of budget.
#[test]
fn the_oracle_lists_each_failed_shape_once() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0x12b0").unwrap();
    assert!(out.contains("did not run to a return"), "{out}");
    let shapes: Vec<&str> = out
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| l.get(..22).map_or(l, str::trim_end))
        .collect();
    assert_eq!(
        shapes,
        [
            "buffer, length",
            "length, buffer",
            "buffer",
            "this, buffer, length"
        ],
        "{out}"
    );
}
