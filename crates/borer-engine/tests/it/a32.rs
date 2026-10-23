//! ARM32 images: the loaders' instruction sets, and the decoder.
//!
//! An ELF for `EM_ARM` and a Windows on ARM (`IMAGE_FILE_MACHINE_ARMNT`)
//! PE load as ARM32 with each stretch of code in the instruction set the
//! file says: an ELF's mapping symbols, the interworking bit on a function
//! symbol or an entry point, a Windows image's T32 throughout. Every form
//! the decoder models, in A32 and in T32, assembled by LLVM (`clang
//! --target=armv7a-linux-gnueabihf -mcpu=cortex-a15 -mfpu=vfpv4`, linked
//! by `ld.lld`), reads as `llvm-objdump` reads it, an `IT` block's
//! conditions carried along; random bytes decode and print without a
//! panic.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::analysis::{Analysis, BlockTerm};
use borer_engine::disasm;
use borer_engine::isa::Isa;
use borer_engine::isa::a32::{ItState, Mode, decode, text};
use borer_engine::program::{Arch, BinaryFormat, Program};

/// Where the ELF's code is mapped.
const ELF_TEXT: u64 = 0x1_0080;

/// `STT_FUNC` with `STB_GLOBAL`.
const GLOBAL_FUNC: u8 = 0x12;

/// `STT_NOTYPE` with `STB_LOCAL`: a mapping symbol.
const LOCAL_NOTYPE: u8 = 0;

/// An A32 function, then a T32 one, then a word of data, as one `.text`.
const MIXED: [u8; 20] = [
    0x01, 0x00, 0x80, 0xe0, // ASM: add r0, r0, r1
    0x1e, 0xff, 0x2f, 0xe1, // ASM: bx lr
    0x40, 0x18, // ASM: adds r0, r0, r1
    0x70, 0x47, // ASM: bx lr
    0x00, 0xbf, // ASM: nop
    0x00, 0xbf, // ASM: nop
    0x78, 0x56, 0x34, 0x12, // ASM: .word 0x12345678
];

/// Writes a little-endian value of `n` bytes at `off`.
///
/// # Arguments
///
/// * `out` - The image.
/// * `off` - The file offset.
/// * `v` - The value.
/// * `n` - Its width in bytes.
fn put(out: &mut [u8], off: usize, v: u64, n: usize) {
    out[off..off + n].copy_from_slice(&v.to_le_bytes()[..n]);
}

/// A 32-bit little-endian `EM_ARM` executable: one loaded segment holding
/// `.text` at [`ELF_TEXT`], and a symbol table of `syms`.
///
/// # Arguments
///
/// * `text` - The code.
/// * `syms` - Each symbol's name, value and `st_info`, all in `.text`.
/// * `entry` - `e_entry`.
fn elf32(text: &[u8], syms: &[(&str, u64, u8)], entry: u64) -> Vec<u8> {
    /// The file offset of `.text`.
    const TEXT_OFF: usize = 0x80;
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 16];
    for &(name, value, info) in syms {
        let at = symtab.len();
        symtab.resize(at + 16, 0);
        put(
            &mut symtab,
            at,
            u64::try_from(strtab.len()).expect("fits"),
            4,
        );
        put(&mut symtab, at + 4, value, 4);
        symtab[at + 12] = info;
        put(&mut symtab, at + 14, 1, 2);
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
    }
    let shstrtab = b"\0.text\0.symtab\0.strtab\0.shstrtab\0".to_vec();
    let sym_off = TEXT_OFF + text.len().next_multiple_of(4);
    let str_off = sym_off + symtab.len();
    let shstr_off = str_off + strtab.len();
    let sh_off = (shstr_off + shstrtab.len()).next_multiple_of(4);
    let mut out = vec![0u8; sh_off + 5 * 40];
    out[..4].copy_from_slice(b"\x7fELF");
    out[4] = 1;
    out[5] = 1;
    out[6] = 1;
    put(&mut out, 16, 2, 2);
    put(&mut out, 18, 40, 2);
    put(&mut out, 20, 1, 4);
    put(&mut out, 24, entry, 4);
    put(&mut out, 28, 52, 4);
    put(&mut out, 32, u64::try_from(sh_off).expect("fits"), 4);
    put(&mut out, 36, 0x0500_0400, 4);
    put(&mut out, 40, 52, 2);
    put(&mut out, 42, 32, 2);
    put(&mut out, 44, 1, 2);
    put(&mut out, 46, 40, 2);
    put(&mut out, 48, 5, 2);
    put(&mut out, 50, 4, 2);
    let offset = |v: usize| u64::try_from(v).expect("fits");
    let text_len = offset(text.len());
    let segment = [
        1,
        0,
        ELF_TEXT - offset(TEXT_OFF),
        ELF_TEXT - offset(TEXT_OFF),
        offset(TEXT_OFF) + text_len,
        offset(TEXT_OFF) + text_len,
        5,
        0x1000,
    ];
    for (k, v) in segment.iter().enumerate() {
        put(&mut out, 52 + 4 * k, *v, 4);
    }
    out[TEXT_OFF..TEXT_OFF + text.len()].copy_from_slice(text);
    out[sym_off..sym_off + symtab.len()].copy_from_slice(&symtab);
    out[str_off..str_off + strtab.len()].copy_from_slice(&strtab);
    out[shstr_off..shstr_off + shstrtab.len()].copy_from_slice(&shstrtab);
    let sections = [
        [1, 1, 6, ELF_TEXT, offset(TEXT_OFF), text_len, 0, 0, 4, 0],
        [
            7,
            2,
            0,
            0,
            offset(sym_off),
            offset(symtab.len()),
            3,
            1,
            4,
            16,
        ],
        [
            15,
            3,
            0,
            0,
            offset(str_off),
            offset(strtab.len()),
            0,
            0,
            1,
            0,
        ],
        [
            23,
            3,
            0,
            0,
            offset(shstr_off),
            offset(shstrtab.len()),
            0,
            0,
            1,
            0,
        ],
    ];
    for (k, s) in sections.iter().enumerate() {
        for (j, v) in s.iter().enumerate() {
            put(&mut out, sh_off + 40 * (k + 1) + 4 * j, *v, 4);
        }
    }
    out
}

/// The text of the instructions in `len` bytes from `va` as the listing
/// reads them, in the instruction set the program marks there.
///
/// # Arguments
///
/// * `p` - The image.
/// * `va` - The first instruction.
/// * `len` - The bytes they take.
fn listed(p: &Program, va: u64, len: usize) -> Vec<String> {
    let n = len / 2;
    let code = p.read_va(va, len).expect("mapped");
    disasm::disassemble_program(p, code, va, Isa::A32, n)
        .into_iter()
        .map(|l| l.text)
        .collect()
}

/// An `EM_ARM` ELF marks its A32 and T32 code as the file says.
///
/// The marks come from its mapping symbols and the interworking bit on its
/// function symbols and entry, which is cleared from every address, and
/// both functions are found.
#[test]
fn an_arm_elf_marks_its_a32_and_t32_code() {
    let t32 = ELF_TEXT + 8;
    let bytes = elf32(
        &MIXED,
        &[
            ("$a", ELF_TEXT, LOCAL_NOTYPE),
            ("$t", t32, LOCAL_NOTYPE),
            ("$d", ELF_TEXT + 16, LOCAL_NOTYPE),
            ("add_arm", ELF_TEXT, GLOBAL_FUNC),
            ("add_thumb", t32 | 1, GLOBAL_FUNC),
        ],
        t32 | 1,
    );
    let p = Program::from_bytes(PathBuf::from("mixed.elf"), bytes).expect("parses");
    assert_eq!(
        (p.format, p.arch, p.is_64),
        (BinaryFormat::Elf, Arch::Arm, false)
    );
    assert_eq!(p.entry, Some(t32));
    assert_eq!(p.modes.at(ELF_TEXT), Mode::Arm);
    assert_eq!(p.modes.at(t32), Mode::Thumb);
    assert!(
        p.symbols
            .iter()
            .any(|s| s.name == "add_thumb" && s.addr == t32)
    );
    assert_eq!(listed(&p, ELF_TEXT, 8), ["add r0, r0, r1", "bx lr"]);
    assert_eq!(listed(&p, t32, 4), ["adds r0, r0, r1", "bx lr"]);
    let a = Analysis::compute(&p);
    assert!(a.function(ELF_TEXT).is_some_and(|f| f.entry == ELF_TEXT));
    assert!(a.function(t32).is_some_and(|f| f.entry == t32));
}

/// An ELF without mapping symbols takes T32 from an odd function symbol
/// alone, and A32 from an even one.
#[test]
fn an_arm_elf_without_mapping_symbols_reads_the_interworking_bit() {
    let t32 = ELF_TEXT + 8;
    let bytes = elf32(
        &MIXED,
        &[
            ("add_arm", ELF_TEXT, GLOBAL_FUNC),
            ("add_thumb", t32 | 1, GLOBAL_FUNC),
        ],
        ELF_TEXT,
    );
    let p = Program::from_bytes(PathBuf::from("bare.elf"), bytes).expect("parses");
    assert_eq!(p.entry, Some(ELF_TEXT));
    assert_eq!(p.modes.at(ELF_TEXT), Mode::Arm);
    assert_eq!(p.modes.at(t32), Mode::Thumb);
}

/// A Windows on ARM PE is T32 throughout, its entry point's interworking
/// bit cleared.
#[test]
fn an_armnt_pe_is_t32_from_its_entry() {
    let code = [
        0x40, 0x18, // ASM: adds r0, r0, r1
        0x70, 0x47, // ASM: bx lr
        0x00, 0xbf, // ASM: nop
        0x00, 0xbf, // ASM: nop
    ];
    let mut bytes = crate::protection::pe(
        &[crate::protection::sec(".text", 0x1000, code.to_vec())],
        0x1001,
    );
    let machine = crate::protection::PE_AT + 4;
    bytes[machine..machine + 2].copy_from_slice(&0x01c4u16.to_le_bytes());
    let p = Program::from_bytes(PathBuf::from("armnt.exe"), bytes).expect("parses");
    let entry = crate::protection::IMAGE_BASE + 0x1000;
    assert_eq!((p.format, p.arch), (BinaryFormat::Pe, Arch::Arm));
    assert_eq!(p.entry, Some(entry));
    assert_eq!(p.modes.at(entry), Mode::Thumb);
    assert_eq!(listed(&p, entry, 4), ["adds r0, r0, r1", "bx lr"]);
}

/// A Cortex-M image: a vector table, the reset handler calling through a
/// literal pool's pointer, the callback it names, a function nothing
/// names, the NMI handler only the table names, and a string.
fn cortex_m() -> Vec<u8> {
    let mut text = vec![0u8; 0x68];
    put(&mut text, 0, 0x2000_1000, 4);
    put(&mut text, 4, (ELF_TEXT + 0x40) | 1, 4);
    put(&mut text, 8, (ELF_TEXT + 0x5a) | 1, 4);
    let code: [(usize, u64); 12] = [
        (0x40, 0xb510), // ASM: push {r4, lr}
        (0x42, 0x4802), // ASM: ldr r0, [pc, #8]
        (0x44, 0x4780), // ASM: blx r0
        (0x46, 0xbd10), // ASM: pop {r4, pc}
        (0x48, 0xbf00), // ASM: nop
        (0x4a, 0xbf00), // ASM: nop
        (0x50, 0x3001), // ASM: adds r0, #1
        (0x52, 0x4770), // ASM: bx lr
        (0x54, 0xb580), // ASM: push {r7, lr}
        (0x56, 0x2000), // ASM: movs r0, #0
        (0x58, 0xbd80), // ASM: pop {r7, pc}
        (0x5a, 0xe7fe), // ASM: b 0x5a
    ];
    for (at, h) in code {
        put(&mut text, at, h, 2);
    }
    put(&mut text, 0x4c, (ELF_TEXT + 0x50) | 1, 4);
    text[0x5c..0x68].copy_from_slice(b"hello world\0");
    elf32(&text, &[], ELF_TEXT + 0x40)
}

/// A stripped image that opens with an M-profile vector table is T32.
///
/// So is its even entry point, and discovery finds the functions only a
/// pointer names (the callback in a literal pool, the
/// handler in the table) and the one in the gap between them, but not the
/// string after them.
#[test]
fn a_cortex_m_image_finds_its_unnamed_t32_functions() {
    let p = Program::from_bytes(PathBuf::from("m.elf"), cortex_m()).expect("parses");
    assert_eq!(p.modes.at(ELF_TEXT + 0x40), Mode::Thumb);
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0x40, 0x50, 0x54, 0x5a]);
}

/// A function another falls into after its own return is a start: the
/// called stub jumping to it, and the unnamed one beside it, each
/// tail-call it.
#[test]
fn a_shared_tail_after_a_return_is_a_function() {
    let text: [u16; 16] = [
        0xb510, // ASM: push {r4, lr}
        0xf000, // ASM: bl 0xe
        0xf804, // ASM: (bl, second half)
        0xbd10, // ASM: pop {r4, pc}
        0xbf00, // ASM: nop
        0x0943, // ASM: lsrs r3, r0, #5
        0x4770, // ASM: bx lr
        0x2107, // ASM: movs r1, #7
        0x201c, // ASM: movs r0, #0x1c
        0xe7fa, // ASM: b 0xa
        0x210c, // ASM: movs r1, #0xc
        0x2026, // ASM: movs r0, #0x26
        0xe7f7, // ASM: b 0xa
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("tail.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 0xa, 0xe, 0x14]);
}

/// A handler that only spins, and that nothing points at, is still a function.
///
/// The bytes after it that neither return nor branch stay data.
#[test]
fn a_closed_loop_in_a_gap_is_a_function() {
    let text: [u16; 8] = [
        0x2001, // ASM: movs r0, #1
        0x4770, // ASM: bx lr
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0x3001, // ASM: adds r0, #1
        0xe7fe, // ASM: b .
        0x2002, // ASM: movs r0, #2
        0x2003, // ASM: movs r1, #3
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("loop.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 8]);
}

/// An unconditional jump over another function, into a straight run that
/// returns, is a tail call. The run is its own function.
#[test]
fn a_jump_past_another_function_is_a_tail_call() {
    let text: [u16; 8] = [
        0xe004, // ASM: b .+12
        0x2002, // ASM: movs r0, #2
        0x4770, // ASM: bx lr
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0x2003, // ASM: movs r0, #3
        0x4770, // ASM: bx lr
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("out.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 2, 0xc]);
    let jumper = a.function_at(ELF_TEXT).expect("the jump");
    assert!(jumper.blocks.iter().all(|b| b.start != ELF_TEXT + 0xc));
}

/// A `pop` of the registers the caller pushed stays in that caller when
/// the `pop` is laid out past another function.
#[test]
fn a_pop_past_another_function_stays_with_its_caller() {
    let text: [u16; 7] = [
        0xb510, // ASM: push {r4, lr}
        0xe003, // ASM: b 0xc
        0x2002, // ASM: movs r0, #2
        0x4770, // ASM: bx lr
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0xbd10, // ASM: pop {r4, pc}
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("epi.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 4]);
    let caller = a
        .functions
        .iter()
        .find(|f| f.entry == ELF_TEXT)
        .expect("the caller");
    let pop = caller
        .blocks
        .iter()
        .find(|b| b.start == ELF_TEXT + 0xc)
        .expect("the pop stays in the caller");
    assert_eq!(pop.term, BlockTerm::Ret);
}

/// A conditional return that falls into a block, and a jump to that same
/// block, keep the block in the caller.
#[test]
fn a_conditional_return_into_a_block_keeps_it() {
    let text: [u32; 8] = [
        0xe350_0000, // ASM: cmp r0, #0
        0x0a00_0002, // ASM: beq 0x14
        0xea00_0002, // ASM: b 0x18
        0xe3a0_0002, // ASM: mov r0, #2
        0xe12f_ff1e, // ASM: bx lr
        0x012f_ff1e, // ASM: bxeq lr
        0xe3a0_0003, // ASM: mov r0, #3
        0xe12f_ff1e, // ASM: bx lr
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|w| w.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("ceq.elf"), elf32(&bytes, &[], ELF_TEXT))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 0xc]);
    let caller = a
        .functions
        .iter()
        .find(|f| f.entry == ELF_TEXT)
        .expect("the caller");
    assert!(caller.blocks.iter().any(|b| b.start == ELF_TEXT + 0x18));
}

/// A conditional return that falls through into a branch back stays with
/// the caller. The return is not the end of that block.
#[test]
fn a_conditional_return_that_falls_back_stays_with_its_caller() {
    let text: [u32; 5] = [
        0xea00_0001, // ASM: b 0xc
        0xe3a0_0002, // ASM: mov r0, #2
        0xe12f_ff1e, // ASM: bx lr
        0x012f_ff1e, // ASM: bxeq lr
        0xeaff_fffa, // ASM: b 0
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|w| w.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("bxeq.elf"), elf32(&bytes, &[], ELF_TEXT))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 4]);
    let caller = a
        .functions
        .iter()
        .find(|f| f.entry == ELF_TEXT)
        .expect("the caller");
    assert!(caller.blocks.iter().any(|b| b.start == ELF_TEXT + 0xc));
}

/// A switch case that a jump also targets stays in the switch's function.
#[test]
fn a_jump_table_case_stays_in_its_caller() {
    let text: [u16; 14] = [
        0x2800, // ASM: cmp r0, #0
        0xd003, // ASM: beq 0xc
        0xe008, // ASM: b 0x18
        0x2002, // ASM: movs r0, #2
        0x4770, // ASM: bx lr
        0xbf00, // ASM: nop
        0x2800, // ASM: cmp r0, #0
        0xd802, // ASM: bhi 0x16
        0xe8df, 0xf000, // ASM: tbb [pc, r0]
        0x0002, // ASM: .byte 2, 0
        0x4770, // ASM: bx lr
        0x2003, // ASM: movs r0, #3
        0x4770, // ASM: bx lr
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("tbb.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry - ELF_TEXT).collect();
    assert_eq!(entries, [0, 6]);
    let caller = a
        .functions
        .iter()
        .find(|f| f.entry == ELF_TEXT)
        .expect("the caller");
    assert!(caller.blocks.iter().any(|b| b.start == ELF_TEXT + 0x18));
}

/// A body a later thunk enters by jumping backward is recovered as its own
/// function when `start_gap_function` is asked for its address, and an
/// address inside a function's own entry block is refused.
///
/// Recovering a gap that reads a callee's result clears the derived cache so
/// decompiling that callee again reflects the new caller.
#[test]
fn a_thunk_body_and_a_span_hole_are_recovered_as_functions() {
    use borer_engine::analysis::Overlay;
    use borer_engine::analysis::decompile::decompile_named;
    let text: [u16; 20] = [
        0xb510, // ASM: push {r4, lr}
        0xf000, // ASM: bl 0xe
        0xf804, // ASM: (bl, second half)
        0x2000, // ASM: movs r0, #0
        0xbd10, // ASM: pop {r4, pc}
        0xbf00, // ASM: nop
        0xbf00, // ASM: nop
        0x4770, // ASM: bx lr
        0xde00, // ASM: udf #0
        0x4903, // ASM: ldr r1, [pc, #12]
        0xf7ff, // ASM: bl 0xe
        0xfffb, // ASM: (bl, second half)
        0x3001, // ASM: adds r0, #1
        0xf000, // ASM: bl 0x24
        0xf803, // ASM: (bl, second half)
        0x4770, // ASM: bx lr
        0x0000, // ASM: .word 0
        0x0000, // ASM: (.word, high half)
        0x2102, // ASM: movs r1, #2
        0x4770, // ASM: bx lr
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("thunk.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let mut a = Analysis::compute(&p);
    let before = decompile_named(&p, &a, &Overlay::default(), ELF_TEXT + 0xe).expect("decompiles");
    assert!(before.contains("// signature: void sub_"), "{before}");
    assert_eq!(a.start_gap_function(&p, ELF_TEXT), None);
    let entry = a
        .start_gap_function(&p, ELF_TEXT + 0x12)
        .expect("recovered");
    assert_eq!(entry, ELF_TEXT + 0x12);
    assert_eq!(a.xrefs_to(ELF_TEXT + 0x20).len(), 1);
    assert!(a.function(ELF_TEXT + 0x24).is_some());
    let after = decompile_named(&p, &a, &Overlay::default(), ELF_TEXT + 0xe).expect("decompiles");
    assert!(after.contains("// signature: uint32_t sub_"), "{after}");
}

/// One instruction's encoding in its instruction set.
#[derive(Debug, Clone, Copy)]
enum Enc {
    /// An A32 word.
    A32(u32),
    /// T32 halfwords, the first first.
    T32(&'static [u16]),
}

/// Every form the decoder models, at the address it was linked at, with
/// the text it reads as.
const FORMS: &[(u64, Enc, &str)] = &[
    (0x200b4, Enc::A32(0xe081_0002), "add r0, r1, r2"),
    (0x200b8, Enc::A32(0xe291_0001), "adds r0, r1, #0x1"),
    (0x200bc, Enc::A32(0xe041_0182), "sub r0, r1, r2, lsl #3"),
    (0x200c0, Enc::A32(0xe054_3fa5), "subs r3, r4, r5, lsr #31"),
    (0x200c4, Enc::A32(0xe261_0000), "rsb r0, r1, #0x0"),
    (0x200c8, Enc::A32(0xe0a1_0002), "adc r0, r1, r2"),
    (0x200cc, Enc::A32(0xe0d1_0002), "sbcs r0, r1, r2"),
    (0x200d0, Enc::A32(0xe201_00ff), "and r0, r1, #0xff"),
    (0x200d4, Enc::A32(0xe181_0142), "orr r0, r1, r2, asr #2"),
    (0x200d8, Enc::A32(0xe021_03e2), "eor r0, r1, r2, ror #7"),
    (0x200dc, Enc::A32(0xe3c1_0102), "bic r0, r1, #0x80000000"),
    (0x200e0, Enc::A32(0xe1e0_0001), "mvn r0, r1"),
    (0x200e4, Enc::A32(0xe1a0_0211), "lsl r0, r1, r2"),
    (0x200e8, Enc::A32(0xe1b0_0231), "lsrs r0, r1, r2"),
    (0x200ec, Enc::A32(0xe1a0_0251), "asr r0, r1, r2"),
    (0x200f0, Enc::A32(0xe1a0_0271), "ror r0, r1, r2"),
    (0x200f4, Enc::A32(0xe1a0_0061), "rrx r0, r1"),
    (0x200f8, Enc::A32(0xe350_000a), "cmp r0, #0xa"),
    (0x200fc, Enc::A32(0xe170_0001), "cmn r0, r1"),
    (0x20100, Enc::A32(0xe310_0004), "tst r0, #0x4"),
    (0x20104, Enc::A32(0xe130_0001), "teq r0, r1"),
    (0x20108, Enc::A32(0xe000_0291), "mul r0, r1, r2"),
    (0x2010c, Enc::A32(0xe020_3291), "mla r0, r1, r2, r3"),
    (0x20110, Enc::A32(0xe060_3291), "mls r0, r1, r2, r3"),
    (0x20114, Enc::A32(0xe081_0392), "umull r0, r1, r2, r3"),
    (0x20118, Enc::A32(0xe0c1_0392), "smull r0, r1, r2, r3"),
    (0x2011c, Enc::A32(0xe0a1_0392), "umlal r0, r1, r2, r3"),
    (0x20120, Enc::A32(0xe0e1_0392), "smlal r0, r1, r2, r3"),
    (0x20124, Enc::A32(0xe750_f211), "smmul r0, r1, r2"),
    (0x20128, Enc::A32(0xe160_0281), "smulbb r0, r1, r2"),
    (0x2012c, Enc::A32(0xe100_3281), "smlabb r0, r1, r2, r3"),
    (0x20130, Enc::A32(0xe710_f211), "sdiv r0, r1, r2"),
    (0x20134, Enc::A32(0xe730_f211), "udiv r0, r1, r2"),
    (0x20138, Enc::A32(0xe591_0000), "ldr r0, [r1]"),
    (0x2013c, Enc::A32(0xe591_0004), "ldr r0, [r1, #0x4]"),
    (0x20140, Enc::A32(0xe511_0004), "ldr r0, [r1, #-0x4]"),
    (0x20144, Enc::A32(0xe5b1_0004), "ldr r0, [r1, #0x4]!"),
    (0x20148, Enc::A32(0xe491_0004), "ldr r0, [r1], #0x4"),
    (0x2014c, Enc::A32(0xe791_0002), "ldr r0, [r1, r2]"),
    (0x20150, Enc::A32(0xe791_0102), "ldr r0, [r1, r2, lsl #2]"),
    (0x20154, Enc::A32(0xe5d1_0001), "ldrb r0, [r1, #0x1]"),
    (0x20158, Enc::A32(0xe1d1_00d1), "ldrsb r0, [r1, #0x1]"),
    (0x2015c, Enc::A32(0xe1d1_00b2), "ldrh r0, [r1, #0x2]"),
    (0x20160, Enc::A32(0xe1d1_00f2), "ldrsh r0, [r1, #0x2]"),
    (0x20164, Enc::A32(0xe1c2_00d8), "ldrd r0, r1, [r2, #0x8]"),
    (0x20168, Enc::A32(0xe1c2_00f8), "strd r0, r1, [r2, #0x8]"),
    (0x2016c, Enc::A32(0xe521_0008), "str r0, [r1, #-0x8]!"),
    (0x20170, Enc::A32(0xe4c1_0001), "strb r0, [r1], #0x1"),
    (0x20174, Enc::A32(0xe181_00b2), "strh r0, [r1, r2]"),
    (0x20178, Enc::A32(0xe191_0f9f), "ldrex r0, [r1]"),
    (0x2017c, Enc::A32(0xe181_2f90), "strex r2, r0, [r1]"),
    (0x20180, Enc::A32(0xe890_000e), "ldmia r0, {r1, r2, r3}"),
    (0x20184, Enc::A32(0xe8b0_0006), "ldmia r0!, {r1, r2}"),
    (0x20188, Enc::A32(0xe920_0006), "stmdb r0!, {r1, r2}"),
    (0x2018c, Enc::A32(0xe92d_4030), "push {r4, r5, lr}"),
    (0x20190, Enc::A32(0xe8bd_8030), "pop {r4, r5, pc}"),
    (0x20194, Enc::A32(0xe301_0234), "movw r0, #0x1234"),
    (0x20198, Enc::A32(0xe345_0678), "movt r0, #0x5678"),
    (0x2019c, Enc::A32(0xe16f_0f11), "clz r0, r1"),
    (0x201a0, Enc::A32(0xe6ff_0f31), "rbit r0, r1"),
    (0x201a4, Enc::A32(0xe6bf_0f31), "rev r0, r1"),
    (0x201a8, Enc::A32(0xe6bf_0fb1), "rev16 r0, r1"),
    (0x201ac, Enc::A32(0xe6ff_0fb1), "revsh r0, r1"),
    (0x201b0, Enc::A32(0xe7e4_01d1), "ubfx r0, r1, #3, #5"),
    (0x201b4, Enc::A32(0xe7a7_0251), "sbfx r0, r1, #4, #8"),
    (0x201b8, Enc::A32(0xe7cb_0411), "bfi r0, r1, #8, #4"),
    (0x201bc, Enc::A32(0xe7cb_001f), "bfc r0, #0, #12"),
    (0x201c0, Enc::A32(0xe6ef_0071), "uxtb r0, r1"),
    (0x201c4, Enc::A32(0xe6af_0071), "sxtb r0, r1"),
    (0x201c8, Enc::A32(0xe6ff_0071), "uxth r0, r1"),
    (0x201cc, Enc::A32(0xe6bf_0471), "sxth r0, r1, ror #8"),
    (0x201d0, Enc::A32(0xe6e1_0072), "uxtab r0, r1, r2"),
    (0x201d4, Enc::A32(0xe6b1_0072), "sxtah r0, r1, r2"),
    (0x201d8, Enc::A32(0xe6e8_0011), "usat r0, #8, r1"),
    (0x201dc, Enc::A32(0xe6af_0111), "ssat r0, #16, r1, lsl #2"),
    (0x201e0, Enc::A32(0xee30_0a81), "vadd.f32 s0, s1, s2"),
    (0x201e4, Enc::A32(0xee31_0b42), "vsub.f64 d0, d1, d2"),
    (0x201e8, Enc::A32(0xee20_0a81), "vmul.f32 s0, s1, s2"),
    (0x201ec, Enc::A32(0xee81_0b02), "vdiv.f64 d0, d1, d2"),
    (0x201f0, Enc::A32(0xee00_0a81), "vmla.f32 s0, s1, s2"),
    (0x201f4, Enc::A32(0xee21_0b42), "vnmul.f64 d0, d1, d2"),
    (0x201f8, Enc::A32(0xeea0_0a81), "vfma.f32 s0, s1, s2"),
    (0x201fc, Enc::A32(0xeeb1_0a60), "vneg.f32 s0, s1"),
    (0x20200, Enc::A32(0xeeb0_0bc1), "vabs.f64 d0, d1"),
    (0x20204, Enc::A32(0xeeb1_0bc1), "vsqrt.f64 d0, d1"),
    (0x20208, Enc::A32(0xeeb0_0a60), "vmov.f32 s0, s1"),
    (0x2020c, Enc::A32(0xeeb7_0b00), "vmov.f64 d0, #1.0"),
    (0x20210, Enc::A32(0xeeb4_0a60), "vcmp.f32 s0, s1"),
    (0x20214, Enc::A32(0xeeb5_0bc0), "vcmp.f64 d0, #0"),
    (0x20218, Enc::A32(0xeef1_fa10), "vmrs apsr_nzcv, fpscr"),
    (0x2021c, Enc::A32(0xeeb7_0ae0), "vcvt.f64.f32 d0, s1"),
    (0x20220, Enc::A32(0xeeb7_0bc1), "vcvt.f32.f64 s0, d1"),
    (0x20224, Enc::A32(0xeebd_0bc1), "vcvt.s32.f64 s0, d1"),
    (0x20228, Enc::A32(0xeeb8_0a60), "vcvt.f32.u32 s0, s1"),
    (0x2022c, Enc::A32(0xee10_0a90), "vmov r0, s1"),
    (0x20230, Enc::A32(0xee00_1a10), "vmov s0, r1"),
    (0x20234, Enc::A32(0xec51_0b12), "vmov r0, r1, d2"),
    (0x20238, Enc::A32(0xec41_0b12), "vmov d2, r0, r1"),
    (0x2023c, Enc::A32(0xed90_0a01), "vldr s0, [r0, #0x4]"),
    (0x20240, Enc::A32(0xed01_0b02), "vstr d0, [r1, #-0x8]"),
    (0x20244, Enc::A32(0xed2d_8b04), "vpush {d8, d9}"),
    (0x20248, Enc::A32(0xecbd_8b04), "vpop {d8, d9}"),
    (
        0x2024c,
        Enc::A32(0xecb0_0a04),
        "vldmia r0!, {s0, s1, s2, s3}",
    ),
    (0x20250, Enc::A32(0xe320_f000), "nop"),
    (0x20254, Enc::A32(0xef00_0000), "svc #0x0"),
    (0x20258, Enc::A32(0xe7f0_00f0), "udf"),
    (0x2025c, Enc::A32(0xebff_ff94), "bl 0x200b4"),
    (0x20260, Enc::A32(0xe12f_ff33), "blx r3"),
    (0x20264, Enc::A32(0xe12f_ff1e), "bx lr"),
    (0x20268, Enc::A32(0x03a0_0001), "moveq r0, #0x1"),
    (0x2026c, Enc::A32(0x1080_0001), "addne r0, r0, r1"),
    (0x20270, Enc::A32(0xc591_0000), "ldrgt r0, [r1]"),
    (0x20274, Enc::A32(0xd12f_ff1e), "bxle lr"),
    (0x20278, Enc::A32(0x0aff_fffe), "beq 0x20278"),
    (0x2027c, Enc::A32(0xeaff_ff8c), "b 0x200b4"),
    (0x200b4, Enc::T32(&[0xeb01, 0x0002]), "add r0, r1, r2"),
    (0x200b8, Enc::T32(&[0x1c48]), "adds r0, r1, #0x1"),
    (
        0x200ba,
        Enc::T32(&[0xeba1, 0x00c2]),
        "sub r0, r1, r2, lsl #3",
    ),
    (
        0x200be,
        Enc::T32(&[0xebb4, 0x73d5]),
        "subs r3, r4, r5, lsr #31",
    ),
    (0x200c2, Enc::T32(&[0xf1c1, 0x0000]), "rsb r0, r1, #0x0"),
    (0x200c6, Enc::T32(&[0xeb41, 0x0002]), "adc r0, r1, r2"),
    (0x200ca, Enc::T32(&[0xeb71, 0x0002]), "sbcs r0, r1, r2"),
    (0x200ce, Enc::T32(&[0xf001, 0x00ff]), "and r0, r1, #0xff"),
    (
        0x200d2,
        Enc::T32(&[0xea41, 0x00a2]),
        "orr r0, r1, r2, asr #2",
    ),
    (
        0x200d6,
        Enc::T32(&[0xea81, 0x10f2]),
        "eor r0, r1, r2, ror #7",
    ),
    (
        0x200da,
        Enc::T32(&[0xf021, 0x4000]),
        "bic r0, r1, #0x80000000",
    ),
    (0x200de, Enc::T32(&[0xea6f, 0x0001]), "mvn r0, r1"),
    (0x200e2, Enc::T32(&[0xfa01, 0xf002]), "lsl r0, r1, r2"),
    (0x200e6, Enc::T32(&[0xfa31, 0xf002]), "lsrs r0, r1, r2"),
    (0x200ea, Enc::T32(&[0xfa41, 0xf002]), "asr r0, r1, r2"),
    (0x200ee, Enc::T32(&[0xfa61, 0xf002]), "ror r0, r1, r2"),
    (0x200f2, Enc::T32(&[0xea4f, 0x0031]), "rrx r0, r1"),
    (0x200f6, Enc::T32(&[0x280a]), "cmp r0, #0xa"),
    (0x200f8, Enc::T32(&[0x42c8]), "cmn r0, r1"),
    (0x200fa, Enc::T32(&[0xf010, 0x0f04]), "tst r0, #0x4"),
    (0x200fe, Enc::T32(&[0xea90, 0x0f01]), "teq r0, r1"),
    (0x20102, Enc::T32(&[0xfb01, 0xf002]), "mul r0, r1, r2"),
    (0x20106, Enc::T32(&[0xfb01, 0x3002]), "mla r0, r1, r2, r3"),
    (0x2010a, Enc::T32(&[0xfb01, 0x3012]), "mls r0, r1, r2, r3"),
    (0x2010e, Enc::T32(&[0xfba2, 0x0103]), "umull r0, r1, r2, r3"),
    (0x20112, Enc::T32(&[0xfb82, 0x0103]), "smull r0, r1, r2, r3"),
    (0x20116, Enc::T32(&[0xfbe2, 0x0103]), "umlal r0, r1, r2, r3"),
    (0x2011a, Enc::T32(&[0xfbc2, 0x0103]), "smlal r0, r1, r2, r3"),
    (0x2011e, Enc::T32(&[0xfb51, 0xf002]), "smmul r0, r1, r2"),
    (0x20122, Enc::T32(&[0xfb11, 0xf002]), "smulbb r0, r1, r2"),
    (
        0x20126,
        Enc::T32(&[0xfb11, 0x3002]),
        "smlabb r0, r1, r2, r3",
    ),
    (0x2012a, Enc::T32(&[0xfb91, 0xf0f2]), "sdiv r0, r1, r2"),
    (0x2012e, Enc::T32(&[0xfbb1, 0xf0f2]), "udiv r0, r1, r2"),
    (0x20132, Enc::T32(&[0x6808]), "ldr r0, [r1]"),
    (0x20134, Enc::T32(&[0x6848]), "ldr r0, [r1, #0x4]"),
    (0x20136, Enc::T32(&[0xf851, 0x0c04]), "ldr r0, [r1, #-0x4]"),
    (0x2013a, Enc::T32(&[0xf851, 0x0f04]), "ldr r0, [r1, #0x4]!"),
    (0x2013e, Enc::T32(&[0xf851, 0x0b04]), "ldr r0, [r1], #0x4"),
    (0x20142, Enc::T32(&[0x5888]), "ldr r0, [r1, r2]"),
    (
        0x20144,
        Enc::T32(&[0xf851, 0x0022]),
        "ldr r0, [r1, r2, lsl #2]",
    ),
    (0x20148, Enc::T32(&[0x7848]), "ldrb r0, [r1, #0x1]"),
    (0x2014a, Enc::T32(&[0xf991, 0x0001]), "ldrsb r0, [r1, #0x1]"),
    (0x2014e, Enc::T32(&[0x8848]), "ldrh r0, [r1, #0x2]"),
    (0x20150, Enc::T32(&[0xf9b1, 0x0002]), "ldrsh r0, [r1, #0x2]"),
    (
        0x20154,
        Enc::T32(&[0xe9d2, 0x0102]),
        "ldrd r0, r1, [r2, #0x8]",
    ),
    (
        0x20158,
        Enc::T32(&[0xe9c2, 0x0102]),
        "strd r0, r1, [r2, #0x8]",
    ),
    (0x2015c, Enc::T32(&[0xf841, 0x0d08]), "str r0, [r1, #-0x8]!"),
    (0x20160, Enc::T32(&[0xf801, 0x0b01]), "strb r0, [r1], #0x1"),
    (0x20164, Enc::T32(&[0x5288]), "strh r0, [r1, r2]"),
    (0x20166, Enc::T32(&[0xe851, 0x0f00]), "ldrex r0, [r1]"),
    (0x2016a, Enc::T32(&[0xe841, 0x0200]), "strex r2, r0, [r1]"),
    (
        0x2016e,
        Enc::T32(&[0xe890, 0x000e]),
        "ldmia r0, {r1, r2, r3}",
    ),
    (0x20172, Enc::T32(&[0xc806]), "ldmia r0!, {r1, r2}"),
    (0x20174, Enc::T32(&[0xe920, 0x0006]), "stmdb r0!, {r1, r2}"),
    (0x20178, Enc::T32(&[0xb530]), "push {r4, r5, lr}"),
    (0x2017a, Enc::T32(&[0xbd30]), "pop {r4, r5, pc}"),
    (0x2017c, Enc::T32(&[0xf241, 0x2034]), "movw r0, #0x1234"),
    (0x20180, Enc::T32(&[0xf2c5, 0x6078]), "movt r0, #0x5678"),
    (0x20184, Enc::T32(&[0xfab1, 0xf081]), "clz r0, r1"),
    (0x20188, Enc::T32(&[0xfa91, 0xf0a1]), "rbit r0, r1"),
    (0x2018c, Enc::T32(&[0xba08]), "rev r0, r1"),
    (0x2018e, Enc::T32(&[0xba48]), "rev16 r0, r1"),
    (0x20190, Enc::T32(&[0xbac8]), "revsh r0, r1"),
    (0x20192, Enc::T32(&[0xf3c1, 0x00c4]), "ubfx r0, r1, #3, #5"),
    (0x20196, Enc::T32(&[0xf341, 0x1007]), "sbfx r0, r1, #4, #8"),
    (0x2019a, Enc::T32(&[0xf361, 0x200b]), "bfi r0, r1, #8, #4"),
    (0x2019e, Enc::T32(&[0xf36f, 0x000b]), "bfc r0, #0, #12"),
    (0x201a2, Enc::T32(&[0xb2c8]), "uxtb r0, r1"),
    (0x201a4, Enc::T32(&[0xb248]), "sxtb r0, r1"),
    (0x201a6, Enc::T32(&[0xb288]), "uxth r0, r1"),
    (0x201a8, Enc::T32(&[0xfa0f, 0xf091]), "sxth r0, r1, ror #8"),
    (0x201ac, Enc::T32(&[0xfa51, 0xf082]), "uxtab r0, r1, r2"),
    (0x201b0, Enc::T32(&[0xfa01, 0xf082]), "sxtah r0, r1, r2"),
    (0x201b4, Enc::T32(&[0xf381, 0x0008]), "usat r0, #8, r1"),
    (
        0x201b8,
        Enc::T32(&[0xf301, 0x008f]),
        "ssat r0, #16, r1, lsl #2",
    ),
    (0x201bc, Enc::T32(&[0xee30, 0x0a81]), "vadd.f32 s0, s1, s2"),
    (0x201c0, Enc::T32(&[0xee31, 0x0b42]), "vsub.f64 d0, d1, d2"),
    (0x201c4, Enc::T32(&[0xee20, 0x0a81]), "vmul.f32 s0, s1, s2"),
    (0x201c8, Enc::T32(&[0xee81, 0x0b02]), "vdiv.f64 d0, d1, d2"),
    (0x201cc, Enc::T32(&[0xee00, 0x0a81]), "vmla.f32 s0, s1, s2"),
    (0x201d0, Enc::T32(&[0xee21, 0x0b42]), "vnmul.f64 d0, d1, d2"),
    (0x201d4, Enc::T32(&[0xeea0, 0x0a81]), "vfma.f32 s0, s1, s2"),
    (0x201d8, Enc::T32(&[0xeeb1, 0x0a60]), "vneg.f32 s0, s1"),
    (0x201dc, Enc::T32(&[0xeeb0, 0x0bc1]), "vabs.f64 d0, d1"),
    (0x201e0, Enc::T32(&[0xeeb1, 0x0bc1]), "vsqrt.f64 d0, d1"),
    (0x201e4, Enc::T32(&[0xeeb0, 0x0a60]), "vmov.f32 s0, s1"),
    (0x201e8, Enc::T32(&[0xeeb7, 0x0b00]), "vmov.f64 d0, #1.0"),
    (0x201ec, Enc::T32(&[0xeeb4, 0x0a60]), "vcmp.f32 s0, s1"),
    (0x201f0, Enc::T32(&[0xeeb5, 0x0bc0]), "vcmp.f64 d0, #0"),
    (
        0x201f4,
        Enc::T32(&[0xeef1, 0xfa10]),
        "vmrs apsr_nzcv, fpscr",
    ),
    (0x201f8, Enc::T32(&[0xeeb7, 0x0ae0]), "vcvt.f64.f32 d0, s1"),
    (0x201fc, Enc::T32(&[0xeeb7, 0x0bc1]), "vcvt.f32.f64 s0, d1"),
    (0x20200, Enc::T32(&[0xeebd, 0x0bc1]), "vcvt.s32.f64 s0, d1"),
    (0x20204, Enc::T32(&[0xeeb8, 0x0a60]), "vcvt.f32.u32 s0, s1"),
    (0x20208, Enc::T32(&[0xee10, 0x0a90]), "vmov r0, s1"),
    (0x2020c, Enc::T32(&[0xee00, 0x1a10]), "vmov s0, r1"),
    (0x20210, Enc::T32(&[0xec51, 0x0b12]), "vmov r0, r1, d2"),
    (0x20214, Enc::T32(&[0xec41, 0x0b12]), "vmov d2, r0, r1"),
    (0x20218, Enc::T32(&[0xed90, 0x0a01]), "vldr s0, [r0, #0x4]"),
    (0x2021c, Enc::T32(&[0xed01, 0x0b02]), "vstr d0, [r1, #-0x8]"),
    (0x20220, Enc::T32(&[0xed2d, 0x8b04]), "vpush {d8, d9}"),
    (0x20224, Enc::T32(&[0xecbd, 0x8b04]), "vpop {d8, d9}"),
    (
        0x20228,
        Enc::T32(&[0xecb0, 0x0a04]),
        "vldmia r0!, {s0, s1, s2, s3}",
    ),
    (0x2022c, Enc::T32(&[0xbf00]), "nop"),
    (0x2022e, Enc::T32(&[0xdf00]), "svc #0x0"),
    (0x20230, Enc::T32(&[0xde00]), "udf"),
    (0x20232, Enc::T32(&[0xf7ff, 0xff3f]), "bl 0x200b4"),
    (0x20236, Enc::T32(&[0x4798]), "blx r3"),
    (0x20238, Enc::T32(&[0x4770]), "bx lr"),
    (0x2023a, Enc::T32(&[0xb158]), "cbz r0, 0x20254"),
    (0x2023c, Enc::T32(&[0xb951]), "cbnz r1, 0x20254"),
    (0x2023e, Enc::T32(&[0xbf06]), "itte eq"),
    (0x20246, Enc::T32(&[0xe8df, 0xf000]), "tbb [pc, r0]"),
    (0x2024c, Enc::T32(&[0xe8df, 0xf011]), "tbh [pc, r1, lsl #1]"),
    (0x20254, Enc::T32(&[0xd0fe]), "beq 0x20254"),
    (0x20256, Enc::T32(&[0xf7ff, 0xbf2d]), "b 0x200b4"),
];

/// Every modeled form decodes to its instruction and prints as LLVM reads
/// it, its length the encoding's.
#[test]
fn every_modeled_form_decodes_and_prints() {
    for &(va, enc, want) in FORMS {
        let (bytes, mode): (Vec<u8>, Mode) = match enc {
            Enc::A32(w) => (w.to_le_bytes().to_vec(), Mode::Arm),
            Enc::T32(h) => (
                h.iter().flat_map(|x| x.to_le_bytes()).collect(),
                Mode::Thumb,
            ),
        };
        let i = decode(&bytes, va, mode, &mut ItState::default()).expect("decodes");
        assert_eq!(text(&i), want, "{va:#x} {enc:x?}");
        assert_eq!(usize::from(i.len), bytes.len(), "{va:#x} {want}");
    }
}

/// An `IT` block's instructions decode under its conditions, the `else`
/// one under the inverse, and those after it under none.
#[test]
fn an_it_block_conditions_the_instructions_it_covers() {
    let halves: [u16; 5] = [
        // ASM: itte eq
        0xbf06, // ASM: moveq r0, #0x1
        0x2001, // ASM: addeq r0, r0, r1
        0x1840, // ASM: movne r0, #0x2
        0x2002, // ASM: movs r0, #0x3
        0x2003,
    ];
    let p = crate::a32_emulate::image(0x1_0000, crate::a32_emulate::Code::Thumb(&halves));
    assert_eq!(
        listed(&p, 0x1_0000, 10),
        [
            "itte eq",
            "moveq r0, #0x1",
            "addeq r0, r0, r1",
            "movne r0, #0x2",
            "movs r0, #0x3"
        ]
    );
}

/// Random words and halfwords decode and print in both instruction sets
/// without a panic.
#[test]
fn random_bytes_decode_without_a_panic() {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    for _ in 0..20_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let bytes = x.to_le_bytes();
        for mode in [Mode::Arm, Mode::Thumb] {
            if let Some(i) = decode(&bytes, 0x1_0000, mode, &mut ItState::default()) {
                assert!(!text(&i).is_empty());
                assert!(i.registers().writes.len() <= 32);
            }
        }
    }
}
