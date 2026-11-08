//! A constant that lands in loader metadata is a number, not the string the
//! loader keeps there.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::function_strings_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Program, Section};

use crate::decompiled::decompiled;
use crate::elfgen::{self, A, AX, EM_X86_64, ET_EXEC, PROGBITS, STRTAB, Sec};

/// The function at `0x3000`: it stores two constants that land in
/// `.dynstr`, reads at an offset that lands there too, and stores the
/// address of the `.rodata` string.
///
/// `0x100b` starts `GLIBC_2.28` and `0x100a` is the terminator before it,
/// which reads as `""`: the shapes of shred's `and r8d, 0x1002` (C-53).
const CODE: [u8; 34] = [
    0x48, 0xc7, 0x07, 0x0b, 0x10, 0x00, 0x00, // ASM: mov qword [rdi],0x100b
    0x48, 0xc7, 0x47, 0x08, 0x0a, 0x10, 0x00, 0x00, // ASM: mov qword [rdi+8],0x100a
    0x48, 0x8d, 0x05, 0xea, 0xef, 0xff, 0xff, // ASM: lea rax,[rip-0x1016]
    0x48, 0x89, 0x47, 0x10, // ASM: mov [rdi+0x10],rax
    0x48, 0x8b, 0x87, 0x0b, 0x10, 0x00, 0x00, // ASM: mov rax,[rdi+0x100b]
    0xc3, // ASM: ret
];

/// The `.dynstr` bytes at `0x1000`.
const DYNSTR: &[u8] = b"\0libc.so.6\0GLIBC_2.28\0";

/// `PT_LOAD`.
const PT_LOAD: u32 = 1;
/// `PT_DYNAMIC`.
const PT_DYNAMIC: u32 = 2;
/// `PF_X`: executable.
const PF_X: u32 = 1;
/// `PF_R`: readable.
const PF_R: u32 = 4;
/// `DT_STRTAB`: the dynamic string table's address.
const DT_STRTAB: u64 = 5;
/// `DT_STRSZ`: its size in bytes.
const DT_STRSZ: u64 = 10;

/// An ELF of [`CODE`] at `0x3000`, `.dynstr` at `0x1000` and `"hello"` in
/// `.rodata` at `0x2000`, with its section table.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
fn dynstr_constants_elf() -> Program {
    let bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x3000,
        &[
            Sec::new(".dynstr", STRTAB, A, 0x1000, DYNSTR.to_vec()),
            Sec::new(".rodata", PROGBITS, A, 0x2000, b"hello\0".to_vec()),
            Sec::new(".text", PROGBITS, AX, 0x3000, CODE.to_vec()),
        ],
    );
    Program::from_bytes(std::path::PathBuf::from("dynstr.elf"), bytes).expect("the image loads")
}

/// An `Elf64_Phdr` of a segment at the file offset equal to its address.
///
/// # Arguments
///
/// * `ty` - `p_type`.
/// * `flags` - `p_flags`.
/// * `at` - Its address and file offset.
/// * `size` - Its size, in the file and in memory.
fn phdr(ty: u32, flags: u32, at: u64, size: u64) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&ty.to_le_bytes());
    out.extend_from_slice(&flags.to_le_bytes());
    for v in [at, at, at, size, size, 0x1000] {
        out.extend_from_slice(&v.to_le_bytes());
    }
    out
}

/// [`dynstr_constants_elf`] with no section table.
///
/// A read-only `PT_LOAD` holds the headers, `.dynstr`, `"hello"` and the
/// dynamic table, whose `DT_STRTAB` is all that says where `.dynstr` is; a
/// second maps the code. The ELF header's `e_shoff` (at 0x28), `e_shnum` and `e_shstrndx` (at
/// 0x3c) are zeroed and `e_phnum` (at 0x38) is 3, the headers at 0x40.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
fn headerless_elf() -> Program {
    let len = |b: &[u8]| u64::try_from(b.len()).expect("fits");
    let table = elfgen::dynamic(&[(DT_STRTAB, 0x1000), (DT_STRSZ, len(DYNSTR))]);
    let mut bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x3000,
        &[
            Sec::new(".dynstr", STRTAB, A, 0x1000, DYNSTR.to_vec()),
            Sec::new(".rodata", PROGBITS, A, 0x2000, b"hello\0".to_vec()),
            Sec::new(".table", PROGBITS, A, 0x2800, table.clone()),
            Sec::new(".text", PROGBITS, AX, 0x3000, CODE.to_vec()),
        ],
    );
    let headers = [
        phdr(PT_LOAD, PF_R, 0, 0x3000),
        phdr(PT_LOAD, PF_R | PF_X, 0x3000, len(&CODE)),
        phdr(PT_DYNAMIC, PF_R, 0x2800, len(&table)),
    ]
    .concat();
    bytes[0x40..0x40 + headers.len()].copy_from_slice(&headers);
    bytes[0x28..0x30].fill(0);
    bytes[0x38..0x3a].copy_from_slice(&3u16.to_le_bytes());
    bytes[0x3c..0x40].fill(0);
    Program::from_bytes(std::path::PathBuf::from("headerless.elf"), bytes).expect("the image loads")
}

/// Asserts the constants of [`CODE`] print as numbers and the `.rodata`
/// string beside them as its literal, in the pseudo-C and in
/// `function_strings`.
///
/// # Arguments
///
/// * `program` - An image of [`CODE`].
fn constants_are_numbers(program: &Program) {
    let text = decompiled(program, 0x3000);
    assert!(text.contains("\"hello\""), "{text}");
    assert!(!text.contains("GLIBC") && !text.contains("\"\""), "{text}");
    assert!(text.contains("0x100b") && text.contains("0x100a"), "{text}");
    let analysis = Analysis::compute(program);
    let rows =
        function_strings_tsv(program, &analysis, &Overlay::default(), 0x3000).unwrap_or_default();
    assert!(rows.contains("\"hello\""), "{rows}");
    assert!(!rows.contains("GLIBC") && !rows.contains("\"\""), "{rows}");
}

/// Constants in `.dynstr` print as numbers; the `.rodata` string beside them
/// still prints as its literal.
#[test]
fn a_constant_in_loader_metadata_is_a_number() {
    constants_are_numbers(&dynstr_constants_elf());
}

/// With no section table the loader maps the segments, which no metadata
/// name matches, and the dynamic table still says where `.dynstr` is.
#[test]
fn a_constant_in_headerless_metadata_is_a_number() {
    let program = headerless_elf();
    assert!(program.sections.iter().all(|s| s.name.starts_with("LOAD")));
    constants_are_numbers(&program);
}

/// The sections a loader or an unwinder reads are metadata by name; the
/// program's own data, read-only or relocated, is not.
#[test]
fn loader_sections_are_metadata() {
    let named = |name: &str| Section::mapped(name, 0x1000, 0, 0x10, false, false).holds_metadata();
    for name in [
        ".dynstr",
        ".interp",
        ".rela.plt",
        ".note.gnu.build-id",
        ".gnu.version_r",
        ".eh_frame",
        ".pdata",
        "__TEXT,__unwind_info",
    ] {
        assert!(named(name), "{name}");
    }
    for name in [".rodata", ".data.rel.ro", ".rdata", "__TEXT,__cstring"] {
        assert!(!named(name), "{name}");
    }
}
