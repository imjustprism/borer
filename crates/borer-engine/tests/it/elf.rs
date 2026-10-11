//! ELF tests on a hand-built dynamically linked x86-64 executable.
//!
//! GOT slots on imports, PLT stub naming, `.symtab` locals with sizes, `.eh_frame`
//! extents on a stripped copy, tail-call splitting, header facts, a
//! decompile that names `puts`, and `.debug_info` frame locals.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay, decompile::decompile};
use borer_engine::num::lo32;
use borer_engine::program::{Program, SymbolKind};

/// Image base of the fixture.
const BASE: u64 = 0x40_0000;
/// File offset of the section header table.
const SHOFF: usize = 0x700;
/// Size of the fixture file.
const FILE_SIZE: usize = 0xb00;
/// PLT stub for `puts`: `jmp [rip+X]` through the GOT slot.
const PLT_PUTS: u64 = BASE + 0x160;
/// `main`: `lea rdi, [msg]; call puts@plt; xor eax, eax; ret`.
const MAIN: u64 = BASE + 0x180;
/// `helper`: `lea eax, [rdi+1]; ret`.
const HELPER: u64 = BASE + 0x190;
/// `wrapper`: `mov edi, 7; jmp helper`.
const WRAPPER: u64 = BASE + 0x1a0;
/// `frames`: the slot `.debug_info` names, written out at a join.
const FRAMES: u64 = BASE + 0x1b0;
/// GOT slot the PLT relocation for `puts` fills.
const GOT_PUTS: u64 = BASE + 0x218;

/// Appends little-endian integers to a byte vector at fixed offsets.
struct Image(Vec<u8>);

impl Image {
    /// Writes bytes at a file offset.
    fn put(&mut self, off: usize, bytes: &[u8]) {
        self.0[off..off + bytes.len()].copy_from_slice(bytes);
    }

    /// Writes a little-endian `u16`.
    fn u16(&mut self, off: usize, v: u16) {
        self.put(off, &v.to_le_bytes());
    }

    /// Writes a little-endian `u32`.
    fn u32(&mut self, off: usize, v: u32) {
        self.put(off, &v.to_le_bytes());
    }

    /// Writes a little-endian `u64`.
    fn u64(&mut self, off: usize, v: u64) {
        self.put(off, &v.to_le_bytes());
    }

    /// Writes an `Elf64_Phdr`.
    fn phdr(&mut self, off: usize, p_type: u32, flags: u32, offset: u64, vaddr: u64, size: u64) {
        self.u32(off, p_type);
        self.u32(off + 4, flags);
        self.u64(off + 8, offset);
        self.u64(off + 16, vaddr);
        self.u64(off + 24, vaddr);
        self.u64(off + 32, size);
        self.u64(off + 40, size);
        self.u64(off + 48, 0x1000);
    }

    /// Writes an `Elf64_Shdr`.
    #[expect(
        clippy::too_many_arguments,
        reason = "one call per header field, mirroring the on-disk layout"
    )]
    fn shdr(
        &mut self,
        index: usize,
        name: u32,
        sh_type: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
        entsize: u64,
    ) {
        let off = SHOFF + index * 64;
        self.u32(off, name);
        self.u32(off + 4, sh_type);
        self.u64(off + 8, flags);
        self.u64(off + 16, addr);
        self.u64(off + 24, offset);
        self.u64(off + 32, size);
        self.u32(off + 40, link);
        self.u32(off + 44, info);
        self.u64(off + 48, 8);
        self.u64(off + 56, entsize);
    }

    /// Writes an `Elf64_Sym`.
    fn sym(&mut self, off: usize, name: u32, info: u8, shndx: u16, value: u64, size: u64) {
        self.u32(off, name);
        self.0[off + 4] = info;
        self.0[off + 5] = 0;
        self.u16(off + 6, shndx);
        self.u64(off + 8, value);
        self.u64(off + 16, size);
    }

    /// Writes an `Elf64_Dyn`.
    fn dynamic(&mut self, off: usize, tag: u64, val: u64) {
        self.u64(off, tag);
        self.u64(off + 8, val);
    }
}

/// Builds the fixture as a real dynamically linked executable.
///
/// `ET_EXEC`, one RWX `PT_LOAD` covering the file, `PT_DYNAMIC`, a
/// non-executable `PT_GNU_STACK`, `.dynsym`/`.dynstr` with the import `puts`
/// from `libc.so.6`, `.rela.plt` with its `JUMP_SLOT`, a one-entry `.plt`,
/// `.text` with `main`, `helper`, `wrapper` and `frames`, `.rodata` holding
/// `"hello, elf"`, `.got.plt` (its slot aims at the stub's padding, as lazy
/// binding does), `.dynamic` (`DT_FLAGS` bind-now), `.eh_frame_hdr` and an
/// `.eh_frame` with one `zR` CIE (`pcrel|sdata4`) and one FDE per function
/// whose extents match the symbol sizes, `.symtab`/`.strtab` naming the
/// four functions with their sizes, and `.debug_abbrev`/`.debug_info`
/// stating `frames`'s frame base and locals, a struct's layout and an
/// enum's constants.
fn elf_fixture() -> Program {
    build_elf(false)
}

/// The same image with `.symtab`/`.strtab` turned into `SHT_NULL` sections,
/// as `strip` leaves a binary: only `.dynsym` and `.eh_frame` describe code.
fn elf_fixture_stripped() -> Program {
    build_elf(true)
}

/// The same image laid out as a `-g` build leaves it: `.debug_info` and
/// `.debug_abbrev` at address zero, file-only, mapped by no segment.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
fn elf_fixture_unmapped_debug() -> Program {
    let mut bytes = elf_bytes(false);
    for index in [14, 15] {
        let addr = SHOFF + index * 64 + 16;
        bytes[addr..addr + 8].fill(0);
    }
    Program::from_bytes(std::path::PathBuf::from("fixture.elf"), bytes).expect("fixture parses")
}

/// Builds the fixture image and parses it.
///
/// # Arguments
///
/// * `stripped` - Whether to drop the symbol table.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
fn build_elf(stripped: bool) -> Program {
    Program::from_bytes(std::path::PathBuf::from("fixture.elf"), elf_bytes(stripped))
        .expect("fixture parses")
}

/// Builds the fixture image's bytes.
///
/// # Arguments
///
/// * `stripped` - Whether to drop the symbol table.
#[expect(
    clippy::expect_used,
    reason = "a fixture whose fields do not fit has no useful recovery"
)]
fn elf_bytes(stripped: bool) -> Vec<u8> {
    let mut im = Image(vec![0u8; FILE_SIZE]);
    im.put(0, &[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
    im.u16(0x10, 2);
    im.u16(0x12, 62);
    im.u32(0x14, 1);
    im.u64(0x18, MAIN);
    im.u64(0x20, 0x40);
    im.u64(0x28, SHOFF as u64);
    im.u16(0x34, 64);
    im.u16(0x36, 56);
    im.u16(0x38, 3);
    im.u16(0x3a, 64);
    im.u16(0x3c, 16);
    im.u16(0x3e, 13);

    im.phdr(0x40, 1, 7, 0, BASE, FILE_SIZE as u64);
    im.phdr(0x78, 2, 6, 0x240, BASE + 0x240, 176);
    im.phdr(0xb0, 0x6474_e551, 6, 0, 0, 0);

    im.sym(0x100 + 24, 1, 0x12, 0, 0, 0);
    im.put(0x130, b"\0puts\0libc.so.6\0");

    im.u64(0x140, GOT_PUTS);
    im.u64(0x148, (1 << 32) | 7);
    im.u64(0x150, 0);

    im.put(0x160, &[0xff, 0x25, 0xb2, 0x00, 0x00, 0x00]); // ASM: jmp qword [rip+0xb2] -> GOT slot
    im.put(0x166, &[0xcc; 10]);

    im.put(0x180, &[0x48, 0x8d, 0x3d, 0x49, 0x00, 0x00, 0x00]); // ASM: lea rdi,[rip+0x49] -> "hello, elf"
    im.put(0x187, &[0xe8, 0xd4, 0xff, 0xff, 0xff]); // ASM: call 0x400160 (puts@plt)
    im.put(0x18c, &[0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    im.put(0x190, &[0x8d, 0x47, 0x01, 0xc3]); // ASM: lea eax,[rdi+1]; ret
    im.put(0x1a0, &[0xbf, 0x07, 0x00, 0x00, 0x00]); // ASM: mov edi,7
    im.put(0x1a5, &[0xeb, 0xe9]); // ASM: jmp 0x400190 (helper)
    im.put(0x1b0, &[0xc6, 0x44, 0x24, 0xf0, 0x09]); // ASM: mov byte [rsp-0x10],9
    im.put(0x1b5, &[0x4d, 0x85, 0xc0]); // ASM: test r8,r8
    im.put(0x1b8, &[0x74, 0x06]); // ASM: je 0x4001c0
    im.put(0x1ba, &[0x8a, 0x01]); // ASM: mov al,[rcx]
    im.put(0x1bc, &[0x88, 0x44, 0x24, 0xf0]); // ASM: mov [rsp-0x10],al
    im.put(0x1c0, &[0x0f, 0xb6, 0x44, 0x24, 0xf0]); // ASM: movzx eax,byte [rsp-0x10]
    im.put(0x1c5, &[0xc3]); // ASM: ret
    im.put(0x1d0, b"hello, elf\0");

    im.u64(0x200, BASE + 0x240);
    im.u64(0x218, PLT_PUTS + 6);

    let dyns: [(u64, u64); 11] = [
        (1, 6),
        (2, 24),
        (3, BASE + 0x200),
        (5, BASE + 0x130),
        (6, BASE + 0x100),
        (10, 16),
        (11, 24),
        (30, 8),
        (20, 7),
        (23, BASE + 0x140),
        (0, 0),
    ];
    for (i, (tag, val)) in dyns.iter().enumerate() {
        im.dynamic(0x240 + i * 16, *tag, *val);
    }

    im.sym(0x300 + 24, 6, 0x02, 5, HELPER, 4);
    im.sym(0x300 + 48, 1, 0x12, 5, MAIN, 15);
    im.sym(0x300 + 72, 13, 0x12, 5, WRAPPER, 7);
    im.sym(0x300 + 96, 21, 0x12, 5, FRAMES, 22);
    im.put(0x380, b"\0main\0helper\0wrapper\0frames\0");

    im.put(0x400, &[0x01, 0x1b, 0x03, 0x3b]);
    im.u32(0x404, 0x3c);
    im.u32(0x408, 4);
    for (i, (func, fde)) in [
        (MAIN, 0x54u32),
        (HELPER, 0x68),
        (WRAPPER, 0x7c),
        (FRAMES, 0x90),
    ]
    .iter()
    .enumerate()
    {
        let rel = lo32(func.wrapping_sub(BASE + 0x400));
        im.u32(0x40c + i * 8, rel);
        im.u32(0x410 + i * 8, *fde);
    }
    im.u32(0x440, 16);
    im.u32(0x444, 0);
    im.put(
        0x448,
        &[0x01, b'z', b'R', 0x00, 0x01, 0x78, 0x10, 0x01, 0x1b],
    );
    for (i, (func, size)) in [(MAIN, 15u32), (HELPER, 4), (WRAPPER, 7), (FRAMES, 22)]
        .iter()
        .enumerate()
    {
        let at = 0x454 + i * 20;
        im.u32(at, 16);
        im.u32(at + 4, u32::try_from(at + 4 - 0x440).expect("fits"));
        im.u32(at + 8, lo32(func.wrapping_sub(BASE + at as u64 + 8)));
        im.u32(at + 12, *size);
        im.0[at + 16] = 0;
    }
    im.u32(0x4a4, 0);

    let abbrev: &[u8] = &[
        // code 1: DW_TAG_subprogram, has children, name (string),
        // low_pc (addr), frame_base (exprloc)
        0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x70, 0x09, 0x00, 0x00,
        // code 2: DW_TAG_variable, no children, name (string),
        // location (exprloc)
        0x02, 0x34, 0x00, 0x03, 0x08, 0x02, 0x09, 0x00, 0x00,
        // code 3: DW_TAG_structure_type, has children, name (string),
        // byte_size (data1)
        0x03, 0x13, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00,
        // code 4: DW_TAG_member, no children, name (string),
        // data_member_location (data1), type (ref4)
        0x04, 0x0d, 0x00, 0x03, 0x08, 0x38, 0x0b, 0x49, 0x13, 0x00, 0x00,
        // code 5: DW_TAG_base_type, no children, name (string),
        // byte_size (data1), encoding (data1)
        0x05, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00, 0x00,
        // code 6: DW_TAG_pointer_type, no children, type (ref4)
        0x06, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00,
        // code 7: DW_TAG_enumeration_type, has children, name (string),
        // byte_size (data1)
        0x07, 0x04, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00,
        // code 8: DW_TAG_enumerator, no children, name (string),
        // const_value (data1)
        0x08, 0x28, 0x00, 0x03, 0x08, 0x1c, 0x0b, 0x00, 0x00, // end of table
        0x00,
    ];
    im.put(0x580, abbrev);
    let mut dies: Vec<u8> = vec![0x01];
    dies.extend_from_slice(b"frames\0");
    dies.extend_from_slice(&FRAMES.to_le_bytes());
    dies.extend_from_slice(&[0x01, 0x9c]); // frame_base: DW_OP_call_frame_cfa
    for (name, expr) in [
        ("count", [0x91u8, 0x68].as_slice()), // fbreg -0x18, slot -0x10
        ("limit", [0x91, 0x70].as_slice()),   // fbreg -0x10, slot -0x8
        ("1bad", [0x91, 0x60].as_slice()),    // a name the text refuses
        ("missing", [].as_slice()),           // no location stated
    ] {
        dies.push(0x02);
        dies.extend_from_slice(name.as_bytes());
        dies.push(0);
        dies.push(u8::try_from(expr.len()).expect("fits"));
        dies.extend_from_slice(expr);
    }
    dies.push(0x00); // end of the subprogram's children
    // The types the unit states, at offsets a ref4 counts from: the unit
    // body starts 12 bytes into the section.
    let die_at = |dies: &[u8]| u32::try_from(12 + dies.len()).expect("fits");
    let u32_at = die_at(&dies);
    dies.push(0x05);
    dies.extend_from_slice(b"unsigned int");
    dies.push(0);
    dies.push(4); // byte size
    dies.push(0x07); // DW_ATE_unsigned
    let char_at = die_at(&dies);
    dies.push(0x05);
    dies.extend_from_slice(b"char");
    dies.push(0);
    dies.push(1);
    dies.push(0x06); // DW_ATE_signed_char
    let ptr_at = die_at(&dies);
    dies.push(0x06);
    dies.extend_from_slice(&char_at.to_le_bytes());
    let mode_at = die_at(&dies);
    dies.push(0x07);
    dies.extend_from_slice(b"Mode");
    dies.push(0);
    dies.push(4); // byte size
    for (name, value) in [("Off", 0u8), ("On", 1u8)] {
        dies.push(0x08);
        dies.extend_from_slice(name.as_bytes());
        dies.push(0);
        dies.push(value);
    }
    dies.push(0x00); // end of the enumeration's children
    dies.push(0x03);
    dies.extend_from_slice(b"Point");
    dies.push(0);
    dies.push(16); // byte size
    for (name, off, ty) in [
        ("x", 0u8, u32_at),
        ("text", 8, ptr_at),
        ("mode", 12, mode_at),
    ] {
        dies.push(0x04);
        dies.extend_from_slice(name.as_bytes());
        dies.push(0);
        dies.push(off);
        dies.extend_from_slice(&ty.to_le_bytes());
    }
    dies.push(0x00); // end of the structure's children
    let mut body: Vec<u8> = Vec::new();
    body.extend_from_slice(&5u16.to_le_bytes()); // version
    body.push(0x01); // DW_UT_compile
    body.push(8); // address size
    body.extend_from_slice(&0u32.to_le_bytes()); // abbreviation offset
    body.extend_from_slice(&dies);
    let mut info = u32::try_from(body.len())
        .expect("fits")
        .to_le_bytes()
        .to_vec();
    info.extend_from_slice(&body);
    im.put(0x600, &info);

    let names = [
        ".dynsym",
        ".dynstr",
        ".rela.plt",
        ".plt",
        ".text",
        ".rodata",
        ".got.plt",
        ".dynamic",
        ".symtab",
        ".strtab",
        ".eh_frame_hdr",
        ".eh_frame",
        ".shstrtab",
        ".debug_info",
        ".debug_abbrev",
    ];
    let mut shstr: Vec<u8> = vec![0];
    let mut name_off: Vec<u32> = Vec::new();
    for n in names {
        name_off.push(u32::try_from(shstr.len()).expect("fits"));
        shstr.extend_from_slice(n.as_bytes());
        shstr.push(0);
    }
    im.put(0x4e0, &shstr);

    im.shdr(1, name_off[0], 11, 2, BASE + 0x100, 0x100, 48, 2, 1, 24);
    im.shdr(2, name_off[1], 3, 2, BASE + 0x130, 0x130, 16, 0, 0, 0);
    im.shdr(3, name_off[2], 4, 0x42, BASE + 0x140, 0x140, 24, 1, 7, 24);
    im.shdr(4, name_off[3], 1, 6, BASE + 0x160, 0x160, 16, 0, 0, 0);
    im.shdr(5, name_off[4], 1, 6, BASE + 0x180, 0x180, 0x50, 0, 0, 0);
    im.shdr(6, name_off[5], 1, 2, BASE + 0x1d0, 0x1d0, 11, 0, 0, 0);
    im.shdr(7, name_off[6], 1, 3, BASE + 0x200, 0x200, 32, 0, 0, 8);
    im.shdr(8, name_off[7], 6, 3, BASE + 0x240, 0x240, 176, 2, 0, 16);
    let (symtab_type, strtab_type) = if stripped { (0, 0) } else { (2, 3) };
    im.shdr(9, name_off[8], symtab_type, 0, 0, 0x300, 120, 10, 2, 24);
    im.shdr(10, name_off[9], strtab_type, 0, 0, 0x380, 28, 0, 0, 0);
    im.shdr(11, name_off[10], 1, 2, BASE + 0x400, 0x400, 0x2c, 0, 0, 0);
    im.shdr(12, name_off[11], 1, 2, BASE + 0x440, 0x440, 0x68, 0, 0, 0);
    im.shdr(
        13,
        name_off[12],
        3,
        0,
        0,
        0x4e0,
        shstr.len() as u64,
        0,
        0,
        0,
    );
    im.shdr(
        14,
        name_off[13],
        1,
        0,
        BASE + 0x600,
        0x600,
        info.len() as u64,
        0,
        0,
        0,
    );
    im.shdr(
        15,
        name_off[14],
        1,
        0,
        BASE + 0x580,
        0x580,
        abbrev.len() as u64,
        0,
        0,
        0,
    );

    im.0
}

/// Without `.symtab`, the `.eh_frame` FDEs still give every function's
/// extent: `helper` and `wrapper` are found although nothing calls them, and
/// the header counts the three unwind entries.
#[test]
fn eh_frame_seeds_the_functions_of_a_stripped_binary() {
    let p = elf_fixture_stripped();
    // The symtab contributes nothing; the one local name left is the
    // DWARF's, which a stripped image keeps.
    assert!(
        p.symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Local)
            .all(|s| s.name == "frames"),
        "symtab still read"
    );
    assert_eq!(
        p.function_ranges,
        vec![
            (MAIN, MAIN + 15),
            (HELPER, HELPER + 4),
            (WRAPPER, WRAPPER + 7),
            (FRAMES, FRAMES + 22)
        ]
    );
    assert_eq!(p.headers.unwind_functions, 4);
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(
        entries.contains(&HELPER) && entries.contains(&WRAPPER),
        "{entries:x?}"
    );
}

/// An ELF for an architecture the disassembler does not decode names its
/// machine and says no code analysis applies, while still loading sections.
///
/// The fixture's `e_machine` is rewritten to `EM_ARM` (40). The summary
/// then carries a `machine:` line, `no_code` fires, and the sections the
/// loader read are still there for triage.
#[test]
fn a_non_x86_machine_is_named_and_code_analysis_declines() {
    let mut bytes = elf_bytes(false);
    bytes[0x12] = 40;
    bytes[0x13] = 0;
    let p = Program::from_bytes(std::path::PathBuf::from("arm.elf"), bytes).expect("parses");
    assert_eq!(
        p.headers.machine.as_deref(),
        Some("ARM (e_machine 40)"),
        "the machine is named"
    );
    let summary = p.summary();
    assert!(summary.contains("machine: ARM (e_machine 40)"), "{summary}");
    assert!(p.no_code().is_some(), "no code analysis on a foreign arch");
    assert!(
        p.sections.iter().any(|s| s.name == ".text"),
        "the sections still loaded"
    );
}

/// The loader records the import's GOT slot, the `.symtab` functions with
/// their ranges, the needed library and the header facts.
#[test]
fn loader_reads_dynamic_linking_facts() {
    let p = elf_fixture();
    let puts = p
        .symbols
        .iter()
        .find(|s| s.name == "puts")
        .expect("import present");
    assert_eq!((puts.kind, puts.addr), (SymbolKind::Import, GOT_PUTS));
    let locals: Vec<(&str, u64)> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| (s.name.as_str(), s.addr))
        .collect();
    assert_eq!(
        locals,
        vec![
            ("helper", HELPER),
            ("main", MAIN),
            ("wrapper", WRAPPER),
            ("frames", FRAMES)
        ]
    );
    assert_eq!(
        p.function_ranges,
        vec![
            (MAIN, MAIN + 15),
            (HELPER, HELPER + 4),
            (WRAPPER, WRAPPER + 7),
            (FRAMES, FRAMES + 22)
        ]
    );
    assert_eq!(p.headers.kind, Some("ET_EXEC"));
    assert_eq!(p.headers.libraries, vec!["libc.so.6".to_owned()]);
    assert_eq!(p.headers.mitigations, vec!["nx"]);
    assert_eq!(p.headers.missing, vec!["no-relro", "no-pie", "no-canary"]);
    assert_eq!(p.headers.stripped, Some(false));
    let summary = p.summary();
    assert!(summary.contains("kind ET_EXEC"), "{summary}");
    assert!(summary.contains("mitigations: nx"), "{summary}");
    assert!(summary.contains("libraries (1): libc.so.6"), "{summary}");
    assert!(summary.contains("locals:  4 named functions"), "{summary}");
}

/// Discovery finds the four functions, names the PLT stub after its import,
/// and splits `wrapper` at its tail jump instead of absorbing `helper`.
#[test]
fn plt_stub_is_named_and_tail_calls_split() {
    let p = elf_fixture();
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert_eq!(entries, vec![PLT_PUTS, MAIN, HELPER, WRAPPER, FRAMES]);
    assert_eq!(a.function(PLT_PUTS).unwrap().name.as_deref(), Some("puts"));
    assert_eq!(a.function(MAIN).unwrap().name.as_deref(), Some("main"));
    let wrapper = a.function(WRAPPER).unwrap();
    assert_eq!(wrapper.end, WRAPPER + 7, "tail jump absorbed helper");
    assert_eq!(wrapper.callees, vec![HELPER]);
    assert_eq!(a.function(HELPER).unwrap().callers, vec![WRAPPER]);
    assert_eq!(a.function(MAIN).unwrap().callees, vec![PLT_PUTS]);
}

/// The debug information a `-g` build leaves names a function's frame
/// locals: the map the decompiler's own naming reads, in the shape the
/// PDB's locals arrive in, with the names the text refuses left out.
#[test]
fn dwarf_names_the_frames_locals() {
    let p = elf_fixture();
    let frames = p
        .debug_functions
        .iter()
        .find(|d| d.low_pc == FRAMES)
        .expect("the debug information states frames");
    assert_eq!(frames.name, "frames");
    assert_eq!(
        frames.locals,
        [(-0x10i64, "count".to_owned()), (-0x08, "limit".to_owned())]
            .into_iter()
            .collect()
    );
}

/// Debug sections no segment maps, as a `-g` build leaves them at address
/// zero, are read all the same: the frame's locals and the stated types
/// come back exactly as they do from the mapped copy.
#[test]
fn dwarf_reads_debug_sections_no_segment_maps() {
    let mapped = elf_fixture();
    let p = elf_fixture_unmapped_debug();
    assert!(
        p.sections.iter().all(|s| !s.name.starts_with(".debug_")),
        "an unmapped debug section joined the mapped table"
    );
    let frames = p
        .debug_functions
        .iter()
        .find(|d| d.low_pc == FRAMES)
        .expect("the debug information states frames");
    assert_eq!(frames.name, "frames");
    assert_eq!(p.debug_functions, mapped.debug_functions);
    assert_eq!(p.debug_types, mapped.debug_types);
}

/// A frame local the debug information names renders by its name, where
/// `local_10` otherwise would, through the same seam the PDB's locals do.
#[test]
fn dwarf_local_names_reach_the_decompiled_text() {
    let p = elf_fixture();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), FRAMES).expect("frames decompiles");
    assert!(text.contains("count"), "the local does not render:\n{text}");
    assert!(
        !text.contains("local_10"),
        "the slot renders synthesized:\n{text}"
    );
}

/// The struct layouts and enum constants the debug information states
/// land in the shape a user type takes, offered as proposals.
///
/// They are facts of the file, not annotations, so they ride the program
/// and never the overlay: nothing is applied until an agent states the
/// same entry as a user type, which is the proposal `borer://layout`
/// makes of a pointer's accesses too.
#[test]
fn dwarf_states_type_layouts_as_proposals() {
    use borer_engine::analysis::utypes::{TypeExpr, UserField};
    use std::collections::BTreeMap;
    let p = elf_fixture();
    let point = p.debug_types.get("Point").expect("Point is stated");
    let borer_engine::analysis::utypes::UserType::Struct(s) = point else {
        panic!("Point is not a struct: {point:?}");
    };
    assert_eq!(s.size, 16);
    assert_eq!(
        s.fields,
        BTreeMap::from([
            (
                0u64,
                UserField {
                    name: "x".to_owned(),
                    ty: TypeExpr::U32,
                }
            ),
            (
                8,
                UserField {
                    name: "text".to_owned(),
                    ty: TypeExpr::Ptr(Box::new(TypeExpr::Char)),
                }
            ),
            (
                12,
                UserField {
                    name: "mode".to_owned(),
                    ty: TypeExpr::Named("Mode".to_owned()),
                }
            ),
        ])
    );
    let mode = p.debug_types.get("Mode").expect("Mode is stated");
    let borer_engine::analysis::utypes::UserType::Enum(e) = mode else {
        panic!("Mode is not an enum: {mode:?}");
    };
    assert_eq!(e.size, 4);
    assert_eq!(e.values, vec![(0, "Off".to_owned()), (1, "On".to_owned())]);
}

/// `main` decompiles to `puts("hello, elf"); return 0;` and `wrapper` to a tail call.
#[test]
fn decompile_names_the_import_and_the_tail_call() {
    let p = elf_fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let main = decompile(&p, &a, &o, MAIN).expect("main decompiles");
    assert!(main.contains("puts(\"hello, elf\");"), "{main}");
    assert!(main.contains("return 0;"), "{main}");
    let wrapper = decompile(&p, &a, &o, WRAPPER).expect("wrapper decompiles");
    assert!(wrapper.contains("return helper("), "{wrapper}");
    assert!(wrapper.contains('7'), "{wrapper}");
}

/// The fixture with `.rodata`'s `sh_size` rewritten.
///
/// # Arguments
///
/// * `size` - The size the header states.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
fn with_rodata_size(size: u64) -> Program {
    let mut bytes = elf_bytes(false);
    let at = SHOFF + 6 * 64 + 32;
    bytes[at..at + 8].copy_from_slice(&size.to_le_bytes());
    Program::from_bytes(std::path::PathBuf::from("sized.elf"), bytes).expect("parses")
}

/// A section whose header states a size no file could hold is dropped and said
/// to be.
///
/// The analysis of what is left finishes: a `.rodata` of 2^55 bytes kept
/// the walk over its file bytes reading nothing for hours.
#[test]
fn a_section_no_file_could_hold_is_dropped_and_analysis_finishes() {
    let p = with_rodata_size(1 << 55);
    assert!(
        !p.sections.iter().any(|s| s.name == ".rodata"),
        "{:?}",
        p.sections
    );
    assert_eq!(p.headers.dropped_sections, 1);
    let summary = p.summary();
    assert!(
        summary.contains("# warning: 1 section(s) dropped"),
        "{summary}"
    );
    let a = Analysis::compute(&p);
    assert!(a.function(MAIN).is_some(), "main is still found");
}

/// A section the end of the file cuts keeps the bytes the file holds, no more.
///
/// The summary says the file is truncated, and every walk over its file bytes
/// is then bounded by the file.
#[test]
fn a_section_the_file_ends_inside_keeps_only_what_the_file_holds() {
    let size = 0x1000_0000u64;
    let p = with_rodata_size(size);
    let rodata = p
        .sections
        .iter()
        .find(|s| s.name == ".rodata")
        .expect("the section is kept");
    let file_len = u64::try_from(FILE_SIZE).expect("fits");
    assert_eq!(rodata.file_size, file_len - 0x1d0);
    assert_eq!(rodata.vsize, size, "the memory size is what the row states");
    assert_eq!(p.headers.truncated, Some(0x1d0 + size));
    let summary = p.summary();
    assert!(
        summary.contains("# warning: truncated: the sections state bytes up to file offset 0x100001d0 and the file ends at 0xb00"),
        "{summary}"
    );
    assert!(p.read_va(BASE + 0x1d0, 11) == Some(&b"hello, elf\0"[..]));
    let a = Analysis::compute(&p);
    assert!(a.function(MAIN).is_some(), "main is still found");
}
