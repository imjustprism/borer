//! Library signatures from ELF objects, `ar` archives and IDA `.pat`
//! signature files.
//!
//! `borer sigmake` reads a static ELF library (`.a`) or a Rust `.rlib` the
//! way it reads a COFF `.lib`: each function's bytes with the relocated
//! ones masked from the object's own `.rela` entries, named after its
//! symbol, so a statically linked ELF names the copy it carries. A long
//! member name comes from the GNU long-name table, a `lib.rmeta` is passed
//! over, a damaged member is named and skipped, and two functions whose
//! signatures agree are told apart by the bytes after them.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::sync::Arc;

use crate::elfgen::{self, AX, EM_X86_64, ET_EXEC, ET_REL, PROGBITS, RELA, STRTAB, SYMTAB, Sec};
use borer_engine::analysis::libnames::library_names_tsv;
use borer_engine::analysis::{Analysis, NameSource};
use borer_engine::libsig::{LibFunction, Tail, pack_text, read, tail_hash};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Arch, Program, Section};

/// `lib_mix`: an arithmetic body around a call to `helper`, whose
/// displacement at offset 0xe the object leaves zero for an
/// `R_X86_64_PLT32`.
const LIB_MIX: [u8; 24] = [
    0x69, 0xc1, 0x67, 0x45, 0x23, 0x01, // ASM: imul eax,ecx,0x1234567
    0x35, 0xef, 0xbe, 0xad, 0xde, // ASM: xor eax,0xdeadbeef
    0x89, 0xc1, // ASM: mov ecx,eax
    0xe8, 0x00, 0x00, 0x00, 0x00, // ASM: call helper
    0x05, 0x11, 0x22, 0x33, 0x44, // ASM: add eax,0x44332211
    0xc3, // ASM: ret
];

/// An x86-64 relocatable object defining `lib_mix` (sized) in `.text`,
/// its call to the undefined `helper` relocated by `R_X86_64_PLT32`.
fn elf_object() -> Vec<u8> {
    let mut symtab = vec![0u8; 24];
    symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0, 24));
    symtab.extend(elfgen::sym(9, 0x10, 0, 0));
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, 0x1000, LIB_MIX.to_vec()),
        Sec::new(
            ".rela.text",
            RELA,
            0x40,
            0x1100,
            elfgen::rela(0xe, 2, 4, -4),
        ),
        Sec::new(".symtab", SYMTAB, 0, 0x1200, symtab),
        Sec::new(
            ".strtab",
            STRTAB,
            0,
            0x1300,
            b"\0lib_mix\0helper\0".to_vec(),
        ),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    secs[2].link = 4;
    secs[2].info = 1;
    secs[2].entsize = 24;
    elfgen::build(ET_REL, EM_X86_64, 0, &secs)
}

/// A GNU `ar` archive of `members`, a name over 15 bytes kept in the
/// long-name table (`//`) and named `/<offset>`.
///
/// # Arguments
///
/// * `members` - Each member's name and bytes.
fn ar(members: &[(&str, &[u8])]) -> Vec<u8> {
    let header = |name: &str, len: usize| {
        let mut h = format!("{name:<16}{:<12}{:<6}{:<6}{:<8}", 0, 0, 0, 644).into_bytes();
        h.extend_from_slice(format!("{len:<10}`\n").as_bytes());
        h
    };
    let mut table = Vec::new();
    let mut names = Vec::new();
    for (name, _) in members {
        if name.len() > 15 {
            names.push(format!("/{}", table.len()));
            table.extend_from_slice(name.as_bytes());
            table.extend_from_slice(b"/\n");
        } else {
            names.push(format!("{name}/"));
        }
    }
    let mut out = b"!<arch>\n".to_vec();
    let push = |out: &mut Vec<u8>, name: &str, data: &[u8]| {
        out.extend(header(name, data.len()));
        out.extend_from_slice(data);
        if data.len() % 2 == 1 {
            out.push(b'\n');
        }
    };
    if !table.is_empty() {
        push(&mut out, "//", &table);
    }
    for ((_, data), name) in members.iter().zip(&names) {
        push(&mut out, name, data);
    }
    out
}

/// A static ELF executable carrying `lib_mix` at 0x1010 with its call
/// reaching 0x1040, a displacement no object holds, called from the entry.
fn static_elf() -> Program {
    let mut text = vec![0xccu8; 0x41];
    text[..6].copy_from_slice(&[0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3]); // ASM: call 0x1010; ret
    text[0x10..0x28].copy_from_slice(&LIB_MIX);
    text[0x1e..0x22].copy_from_slice(&0x1eu32.to_le_bytes());
    text[0x40] = 0xc3; // ASM: ret
    let bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x1000,
        &[Sec::new(".text", PROGBITS, AX, 0x1000, text)],
    );
    Program::from_bytes(std::path::PathBuf::from("static.elf"), bytes).expect("the image loads")
}

/// Analyzes a program with one pack's text.
///
/// # Arguments
///
/// * `p` - The program.
/// * `text` - The pack.
fn with_pack(p: &Program, text: &str) -> Analysis {
    let (pack, warnings) = Pack::parse(text, "lib.borer").expect("the pack reads");
    assert!(warnings.is_empty(), "{warnings:?}");
    Analysis::compute_with(p, Arc::new(Packs { packs: vec![pack] }))
}

/// The library name a function took, if any.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `va` - The function's entry.
fn library_name(a: &Analysis, va: u64) -> Option<String> {
    a.function(va)
        .filter(|f| f.name_source == NameSource::Library)
        .and_then(|f| f.name.clone())
}

/// An ELF object inside an `ar` archive names the copy a static ELF carries.
///
/// The object sits under a long member name beside a Rust `lib.rmeta`; its
/// `lib` line has the call masked, and names the function the static ELF
/// carries with another displacement.
#[test]
fn an_elf_object_in_an_archive_names_a_static_function() {
    let obj = elf_object();
    let rlib = ar(&[
        ("lib.rmeta", b"rust\0\0\0\x08not an object"),
        ("mix-0123456789abcdef.mix.cgu.0.rcgu.o", &obj),
    ]);
    let (found, damaged) = read(&rlib).expect("the archive reads");
    assert!(damaged.is_empty(), "{damaged:?}");
    assert_eq!(found.len(), 1, "{found:?}");
    let f = &found[0];
    assert_eq!(f.name, "lib_mix");
    assert_eq!(f.sig.len(), 24);
    assert!(f.sig[0xe..0x12].iter().all(Option::is_none), "{f:?}");
    assert_eq!(f.fixed(), 20);
    assert_eq!(f.refs, vec![(0xe, "helper".to_owned())]);
    let text = pack_text("mix", "a test", &found);
    assert!(
        text.contains("lib 69C16745230135EFBEADDE89C1E8????????0511223344C3 lib_mix e=helper\n"),
        "{text}"
    );
    let p = static_elf();
    let a = with_pack(&p, &text);
    assert_eq!(library_name(&a, 0x1010).as_deref(), Some("lib_mix"));
}

/// A damaged archive is refused member by member, never with a panic.
///
/// A member opening with the ELF magic whose headers do not read is named
/// by its long name, a member running past the end ends the walk, and an
/// ELF that is no relocatable object, or a cut one, is refused whole.
#[test]
fn a_corrupt_archive_is_refused_cleanly() {
    let obj = elf_object();
    let broken = ar(&[
        (
            "broken_member_with_a_long_name.o",
            b"\x7fELF\x02\x01\x01 and nothing",
        ),
        ("good.o", &obj),
    ]);
    let (found, damaged) = read(&broken).expect("the archive reads");
    assert_eq!(found.len(), 1, "the sound member is read");
    assert_eq!(damaged.len(), 1, "{damaged:?}");
    assert!(
        damaged[0].starts_with("member broken_member_with_a_long_name.o at ")
            && damaged[0].ends_with(": an ELF file whose headers do not parse"),
        "{damaged:?}"
    );
    let mut cut = ar(&[("good.o", &obj)]);
    cut.truncate(cut.len() - 100);
    let (found, damaged) = read(&cut).expect("the archive reads");
    assert!(found.is_empty());
    assert!(
        damaged.len() == 1 && damaged[0].contains("runs past the end of the file"),
        "{damaged:?}"
    );
    let exec = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x1000,
        &[Sec::new(".text", PROGBITS, AX, 0x1000, vec![0xc3])],
    );
    assert_eq!(
        read(&exec)
            .expect_err("an executable is no object")
            .to_string(),
        "an ELF file that is not a relocatable object (.o)"
    );
    assert!(read(&obj[..80]).is_err());
}

/// Two library functions whose 128-byte signatures agree are told apart by
/// their tails, and two names over one body name it neither and are
/// listed.
///
/// Without the tail both signatures matched both functions, and neither
/// was named.
#[test]
fn a_tail_tells_apart_functions_whose_signatures_agree() {
    /// A 149-byte body: 37 four-byte instructions of `op`, the 33rd's
    /// immediate `odd`, then `ret`.
    fn body(op: [u8; 3], odd: u8) -> Vec<u8> {
        let mut out = Vec::new();
        for k in 0..37 {
            out.extend_from_slice(&op);
            out.push(if k == 32 { odd } else { 1 }); // ASM: add r64,imm8
        }
        out.push(0xc3); // ASM: ret
        out
    }
    let add_rax = [0x48, 0x83, 0xc0];
    let bodies = [
        body(add_rax, 1),
        body(add_rax, 2),
        body([0x48, 0x83, 0xc1], 1),
    ];
    let mut bytes = vec![0xccu8; 0x400];
    for (k, b) in bodies.iter().enumerate() {
        bytes[0x100 * k..0x100 * k + b.len()].copy_from_slice(b);
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x400, false, true)],
    );
    p.function_ranges = (0..3u64)
        .map(|k| (0x1000 + 0x100 * k, 0x1000 + 0x100 * k + 149))
        .collect();
    let line = |name: &str, b: &[u8]| LibFunction {
        name: name.to_owned(),
        sig: b[..128].iter().copied().map(Some).collect(),
        tail: Some(Tail {
            len: 21,
            hash: tail_hash(&b[128..]),
        }),
        refs: Vec::new(),
    };
    let text = pack_text(
        "tails",
        "a test",
        &[
            line("fa", &bodies[0]),
            line("fb", &bodies[1]),
            line("fc", &bodies[2]),
            line("fd", &bodies[2]),
        ],
    );
    assert!(text.contains(" fa tail=15:"), "{text}");
    let a = with_pack(&p, &text);
    assert_eq!(library_name(&a, 0x1000).as_deref(), Some("fa"));
    assert_eq!(library_name(&a, 0x1100).as_deref(), Some("fb"));
    assert_eq!(library_name(&a, 0x1200), None);
    assert_eq!(
        a.library_names.ambiguous,
        vec![(0x1200, vec!["fc".to_owned(), "fd".to_owned()])]
    );
    let tsv = library_names_tsv(&a.library_names);
    assert!(
        tsv.contains("# library names ambiguous, so named neither: 0x1200 fc|fd\n"),
        "{tsv}"
    );
}

/// An IDA `.pat` signature file names a program's copy of a function.
///
/// The 16 leading bytes match with the call's displacement wildcarded,
/// and the references and tail bytes that trail the name on the line are
/// passed over.
///
/// # Panics
///
/// When the record is misread or names nothing.
#[test]
fn a_pat_file_names_a_static_function() {
    let body = [
        0x55, 0x8b, 0xec, // ASM: push ebp; mov ebp,esp
        0x6a, 0x0a, // ASM: push 0xa
        0xe8, 0x08, 0x00, 0x00, 0x00, // ASM: call deeper
        0x83, 0xc4, 0x04, // ASM: add esp,4
        0x5d, 0xc3, // ASM: pop ebp; ret
        0x90, 0x90, 0x90, 0x90, // ASM: nops the signature does not reach
    ];
    let pat = "558BEC6A0AE8????????83C4045DC390 pat_func #0#90909090\r\n";
    let (found, damaged) = read(pat.as_bytes()).expect("the pattern file reads");
    assert!(damaged.is_empty(), "{damaged:?}");
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].name, "pat_func");
    assert_eq!(found[0].fixed(), 12);
    assert!(found[0].sig[6..10].iter().all(Option::is_none), "{found:?}");
    let text = pack_text("ida", "a test", &found);
    assert!(
        text.contains("lib 558BEC6A0AE8????????83C4045DC390 pat_func\n"),
        "{text}"
    );
    let mut bytes = vec![0xccu8; 0x20];
    bytes[..body.len()].copy_from_slice(&body);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x20, false, true)],
    );
    p.function_ranges = vec![(0x1000, 0x1000 + 19)];
    let a = with_pack(&p, &text);
    assert_eq!(library_name(&a, 0x1000).as_deref(), Some("pat_func"));
}

/// Oversized ELF `STT_FUNC` symbol names are refused without copying or
/// truncating them, while sound functions stay and `damaged` counts the skips.
#[test]
fn oversized_elf_symbol_names_are_refused_with_a_damaged_note() {
    const COUNT: usize = 21_845;
    let mut text = LIB_MIX.to_vec();
    text.extend(std::iter::repeat_n(0xc3u8, COUNT));
    let mut strtab = b"\0lib_mix\0".to_vec();
    let huge_at = u32::try_from(strtab.len()).expect("strtab offset fits u32");
    strtab.extend(std::iter::repeat_n(b'a', 512 << 10));
    strtab.push(0);
    let mut symtab = vec![0u8; 24];
    symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0, 24));
    for k in 0..COUNT {
        let off = u64::try_from(24 + k).expect("offset fits u64");
        symtab.extend(elfgen::sym_sized(huge_at, 0x12, 1, off, 1));
    }
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, 0x1000, text),
        Sec::new(".symtab", SYMTAB, 0, 0x10_000, symtab),
        Sec::new(".strtab", STRTAB, 0, 0xa0_000, strtab),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    let evil = elfgen::build(ET_REL, EM_X86_64, 0, &secs);

    #[expect(
        clippy::disallowed_methods,
        reason = "the test asserts a wall-time bound on sigmake reading"
    )]
    let started = std::time::Instant::now();
    let (found, damaged) = read(&evil).expect("the object reads");
    assert!(
        started.elapsed() < std::time::Duration::from_secs(2),
        "took {:?}",
        started.elapsed()
    );
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].name, "lib_mix");
    assert_eq!(
        damaged,
        vec!["skipped 21845 symbol(s) with names past 4096 bytes"]
    );

    let archive = ar(&[("evil_member_name.o", &evil)]);
    let (found, damaged) = read(&archive).expect("the archive reads");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, "lib_mix");
    assert!(
        damaged.len() == 1
            && damaged[0].starts_with("member evil_member_name.o at ")
            && damaged[0].ends_with(": skipped 21845 symbol(s) with names past 4096 bytes"),
        "{damaged:?}"
    );
}

/// Indirect `/` section headers in COFF objects stay fast and bounded without
/// copying the COFF string table per section row.
#[test]
fn coff_indirect_sections_do_not_copy_string_table() {
    /// Indirect `/4` COFF section headers pointing into one `256 KiB` string.
    const SLASH_SECS: usize = 4000;
    /// Shared COFF string length (`256 KiB`).
    const BIG_SEC_NAME: usize = 256 << 10;
    let code = [0x48, 0x89, 0xc8, 0xc3]; // ASM: mov rax,rcx; ret
    let text_at = 20 + SLASH_SECS * 40;
    let sym_at = text_at + code.len();
    let mut coff = Vec::with_capacity(sym_at + 18 + 4 + BIG_SEC_NAME + 1);
    coff.extend_from_slice(&0x8664u16.to_le_bytes());
    coff.extend_from_slice(&u16::try_from(SLASH_SECS).expect("fits").to_le_bytes());
    coff.extend_from_slice(&0u32.to_le_bytes());
    coff.extend_from_slice(&u32::try_from(sym_at).expect("fits").to_le_bytes());
    coff.extend_from_slice(&1u32.to_le_bytes());
    coff.extend_from_slice(&0u16.to_le_bytes());
    coff.extend_from_slice(&0u16.to_le_bytes());
    for i in 0..SLASH_SECS {
        coff.extend_from_slice(b"/4\0\0\0\0\0\0");
        coff.extend_from_slice(&0u32.to_le_bytes());
        coff.extend_from_slice(&0u32.to_le_bytes());
        let (sz, ptr, ch) = if i == 0 {
            (
                u32::try_from(code.len()).expect("fits"),
                u32::try_from(text_at).expect("fits"),
                0x6000_0020u32,
            )
        } else {
            (0, 0, 0x4000_0040u32)
        };
        coff.extend_from_slice(&sz.to_le_bytes());
        coff.extend_from_slice(&ptr.to_le_bytes());
        coff.extend_from_slice(&[0u8; 12]);
        coff.extend_from_slice(&ch.to_le_bytes());
    }
    coff.extend_from_slice(&code);
    coff.extend_from_slice(b"keep\0\0\0\0");
    coff.extend_from_slice(&0u32.to_le_bytes());
    coff.extend_from_slice(&1i16.to_le_bytes());
    coff.extend_from_slice(&0x20u16.to_le_bytes());
    coff.extend_from_slice(&[2, 0]);
    coff.extend_from_slice(
        &u32::try_from(4 + BIG_SEC_NAME + 1)
            .expect("fits")
            .to_le_bytes(),
    );
    coff.resize(coff.len() + BIG_SEC_NAME, b'S');
    coff.push(0);
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time indirect COFF section rows take"
    )]
    let started = std::time::Instant::now();
    let (found, damaged) = read(&coff).expect("the COFF object reads");
    assert!(started.elapsed() < std::time::Duration::from_secs(2));
    assert!(damaged.is_empty(), "{damaged:?}");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, "keep");
}

/// Multi-member archives share a single symbol-name budget across all members,
/// and oversized `.pat` symbol names are skipped with a `damaged` note.
#[test]
fn archive_symbol_budget_and_pat_cap_stay_bounded() {
    let long_sym = "f".repeat(3500);
    let mut member_strtab = vec![0u8];
    let sym_off = u32::try_from(member_strtab.len()).expect("fits");
    member_strtab.extend_from_slice(long_sym.as_bytes());
    member_strtab.push(0);
    let mut member_symtab = vec![0u8; 24];
    let mut member_text = Vec::new();
    for k in 0..64u64 {
        member_text.extend_from_slice(&[0x48, 0x83, 0xc0, 0x01, 0xc3]); // ASM: add rax,1; ret
        member_symtab.extend(elfgen::sym_sized(sym_off, 0x12, 1, k * 5, 5));
    }
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, 0x1000, member_text),
        Sec::new(".symtab", SYMTAB, 0, 0x2000, member_symtab),
        Sec::new(".strtab", STRTAB, 0, 0x3000, member_strtab),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    let member_obj = elfgen::build(ET_REL, EM_X86_64, 0, &secs);
    let entries: Vec<(String, &[u8])> = (0..60)
        .map(|i| (format!("m{i}.o"), member_obj.as_slice()))
        .collect();
    let refs: Vec<(&str, &[u8])> = entries.iter().map(|(n, d)| (n.as_str(), *d)).collect();
    let archive = ar(&refs);
    let (found, damaged) = read(&archive).expect("archive reads");
    let copied: usize = found.iter().map(|f| f.name.len()).sum();
    let cap = (archive.len() * 8).max(1 << 20);
    assert!(copied <= cap, "copied {copied} > cap {cap}");
    assert!(found.len() < 60 * 64, "budget capped later members");
    assert!(
        damaged
            .iter()
            .any(|d| d.contains("past the symbol-name budget")),
        "{damaged:?}"
    );

    let pat = format!(
        "558BEC83EC0C535657E8000000005DC3 {}\n558BEC83EC0C535657E8000000005DC3 ok_pat\n",
        "p".repeat(4097)
    );
    let (found, damaged) = read(pat.as_bytes()).expect("pat reads");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, "ok_pat");
    assert_eq!(
        damaged,
        vec!["skipped 1 symbol(s) with names past 4096 bytes"]
    );
}
