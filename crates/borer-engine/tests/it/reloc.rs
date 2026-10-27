//! ELF dynamic relocations applied to the image.
//!
//! A position-independent ELF lld links keeps its pointer tables as zeros
//! on disk and states each pointer as a dynamic relocation. The loader
//! writes them, so borer does: a `RELATIVE` slot reads as its target, the
//! target is discovered and the slot is its cross-reference, an import's
//! GOT slots are named after it, a `DT_RELR` bitmap decodes into the words
//! it relocates, and a hostile table is refused without a panic.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use crate::elfgen::{
    self, A, AX, DYNAMIC, DYNSYM, EM_X86_64, ET_DYN, PROGBITS, RELA, RELR, STRTAB, Sec, WA,
};
use borer_engine::analysis::render::xrefs_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Program, SymbolKind};

/// The entry: `xor eax,eax; ret`.
const ENTRY: u64 = 0x1000;
/// Reached only through the `RELATIVE` slot: `mov eax,42; ret`.
const TABLED: u64 = 0x1010;
/// The defined symbol `helper` an absolute word names: `mov eax,7; ret`.
const HELPER: u64 = 0x1020;
/// The `.data.rel.ro` slot the `RELATIVE` entry writes.
const SLOT: u64 = 0x2000;
/// The slot the absolute word against `helper` writes.
const ABS_SLOT: u64 = 0x2008;
/// The GOT slot `GLOB_DAT` binds to `puts`.
const GOT_PUTS: u64 = 0x2100;
/// The GOT slot `JUMP_SLOT` binds to `puts`.
const PLT_PUTS: u64 = 0x2108;

/// `R_X86_64_64`.
const R_64: u32 = 1;
/// `R_X86_64_GLOB_DAT`.
const R_GLOB_DAT: u32 = 6;
/// `R_X86_64_JUMP_SLOT`.
const R_JUMP_SLOT: u32 = 7;
/// `R_X86_64_RELATIVE`.
const R_RELATIVE: u32 = 8;

/// Builds an x86-64 PIE with the given `.rela.dyn` entries and `DT_RELR`
/// table, its size stated as `relr_size`.
///
/// `.text` holds the three functions, `.data.rel.ro` and `.got` are zeros
/// on disk, `.dynsym` holds the import `puts` (1) and the defined `helper`
/// (2).
///
/// # Arguments
///
/// * `relas` - The `Elf64_Rela` entries.
/// * `rela_size` - The size `DT_RELASZ` states, `None` for theirs.
/// * `relr` - The `DT_RELR` words.
/// * `relr_size` - The size `DT_RELRSZ` states.
fn pie(relas: &[Vec<u8>], rela_size: Option<u64>, relr: &[u64], relr_size: u64) -> Program {
    let mut text = vec![0xccu8; 0x30];
    text[0..3].copy_from_slice(&[0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    text[0x10..0x16].copy_from_slice(&[0xb8, 0x2a, 0, 0, 0, 0xc3]); // ASM: mov eax,42; ret
    text[0x20..0x26].copy_from_slice(&[0xb8, 0x07, 0, 0, 0, 0xc3]); // ASM: mov eax,7; ret
    let rela: Vec<u8> = relas.concat();
    let relr_bytes: Vec<u8> = relr.iter().flat_map(|w| w.to_le_bytes()).collect();
    let dynstr = b"\0puts\0helper\0".to_vec();
    let mut dynsym = vec![0u8; 24];
    dynsym.extend(elfgen::sym(1, 0x12, 0, 0));
    dynsym.extend(elfgen::sym(6, 0x12, 1, HELPER));
    let dynamic = elfgen::dynamic(&[
        (7, 0x3000),
        (
            8,
            rela_size.unwrap_or_else(|| u64::try_from(rela.len()).expect("fits")),
        ),
        (9, 24),
        (6, 0x3200),
        (5, 0x3300),
        (10, u64::try_from(dynstr.len()).expect("fits")),
        (11, 24),
        (36, 0x3100),
        (35, relr_size),
        (37, 8),
    ]);
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, 0x1000, text),
        Sec::new(".data.rel.ro", PROGBITS, WA, 0x2000, vec![0; 0x40]),
        Sec::new(".got", PROGBITS, WA, 0x2100, vec![0; 0x10]),
        Sec::new(".rela.dyn", RELA, A, 0x3000, rela),
        Sec::new(".relr.dyn", RELR, A, 0x3100, relr_bytes),
        Sec::new(".dynsym", DYNSYM, A, 0x3200, dynsym),
        Sec::new(".dynstr", STRTAB, A, 0x3300, dynstr),
        Sec::new(".dynamic", DYNAMIC, WA, 0x3400, dynamic),
    ];
    secs[3].link = 6;
    secs[3].entsize = 24;
    secs[4].entsize = 8;
    secs[5].link = 7;
    secs[5].entsize = 24;
    secs[7].link = 7;
    secs[7].entsize = 16;
    let bytes = elfgen::build(ET_DYN, EM_X86_64, ENTRY, &secs);
    Program::from_bytes(std::path::PathBuf::from("pie.so"), bytes).expect("the PIE loads")
}

/// The well-formed image: a `RELATIVE` slot, an absolute word against
/// `helper`, `puts` bound through a GOT and a PLT slot, and a `DT_RELR`
/// table of an address and a bitmap.
fn applied() -> Program {
    pie(
        &[
            elfgen::rela(SLOT, 0, R_RELATIVE, i64::try_from(TABLED).expect("fits")),
            elfgen::rela(ABS_SLOT, 2, R_64, 0),
            elfgen::rela(GOT_PUTS, 1, R_GLOB_DAT, 0),
            elfgen::rela(PLT_PUTS, 1, R_JUMP_SLOT, 0),
        ],
        None,
        &[0x2010, 0b1011],
        16,
    )
}

/// Reads the word at `va` as the image holds it.
///
/// # Arguments
///
/// * `p` - The program.
/// * `va` - The word's address.
fn word(p: &Program, va: u64) -> u64 {
    let b = p.read_va(va, 8).expect("the word is mapped");
    u64::from_le_bytes(b.try_into().expect("eight bytes"))
}

/// A `RELATIVE` entry into a slot zero on disk reads as its target, the
/// target is discovered as a function, and `xrefs` lists the slot.
///
/// The slot read as the zero the file holds, so nothing pointed at the
/// function and nothing found it.
#[test]
fn a_relative_slot_reads_as_its_target_and_names_it() {
    let p = applied();
    assert_eq!(word(&p, SLOT), TABLED);
    assert_eq!(word(&p, ABS_SLOT), HELPER, "S + A against a defined symbol");
    assert!(
        p.bytes[0x2000..0x2010].iter().all(|b| *b == 0),
        "the file's own bytes stay as they were read"
    );
    let a = Analysis::compute(&p);
    assert!(
        a.function(TABLED).is_some(),
        "{:#x?}",
        a.functions.iter().map(|f| f.entry).collect::<Vec<_>>()
    );
    let xrefs = xrefs_tsv(&p, &a, &Overlay::default(), TABLED, 0, 50, false);
    assert!(xrefs.contains(&format!("-: {SLOT:#x} ")), "{xrefs}");
    let summary = p.summary();
    assert!(
        summary.contains("relocs:  7 dynamic relocation(s) applied to the image\n"),
        "{summary}"
    );
}

/// Every slot `GLOB_DAT` or `JUMP_SLOT` binds to an import is named after
/// it, so a call through either reads as the import.
///
/// Only the first slot any relocation named was the import's.
#[test]
fn every_slot_bound_to_an_import_is_named() {
    let p = applied();
    let mut puts: Vec<u64> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.name == "puts")
        .map(|s| s.addr)
        .collect();
    puts.sort_unstable();
    assert_eq!(puts, vec![GOT_PUTS, PLT_PUTS]);
}

/// A `DT_RELR` address and bitmap decode into the words they relocate,
/// which with the `RELATIVE` and absolute words are the image's pointers.
#[test]
fn a_relr_bitmap_decodes() {
    let p = applied();
    assert_eq!(
        p.relocated_words(),
        vec![SLOT, ABS_SLOT, 0x2010, 0x2018, 0x2028],
        "the address 0x2010, then bits 1 and 3 of the bitmap: the first and third words after it"
    );
}

/// A hostile table is refused entry by entry, and the load goes on.
///
/// A slot past every section, one at the top of the address space, a word
/// over one already written and a `DT_RELRSZ` no section holds each count
/// as refused, and the one sound entry still applies. A `DT_RELR` bitmap
/// claims only the words a section holds, and a `DT_RELASZ` past the end
/// of the file loads with no entry applied.
#[test]
fn a_hostile_table_is_refused_cleanly() {
    let p = pie(
        &[
            elfgen::rela(0xdead_0000, 0, R_RELATIVE, 0x1010),
            elfgen::rela(SLOT, 0, R_RELATIVE, i64::try_from(TABLED).expect("fits")),
            elfgen::rela(SLOT + 4, 0, R_RELATIVE, 0x1020),
            elfgen::rela(u64::MAX - 3, 0, R_RELATIVE, 0x1020),
        ],
        None,
        &[0x2030, u64::MAX],
        u64::MAX - 7,
    );
    assert_eq!(
        word(&p, SLOT),
        TABLED,
        "the sound entry applied and the one overlapping it did not"
    );
    assert_eq!(p.relocated_words(), vec![SLOT]);
    let summary = p.summary();
    assert!(
        summary.contains("relocs:  1 dynamic relocation(s) applied to the image; 4 refused"),
        "{summary}"
    );
    Analysis::compute(&p);

    let bitmap = pie(&[], None, &[0x2030, u64::MAX], 16);
    assert_eq!(
        bitmap.relocated_words(),
        vec![0x2030, 0x2038, GOT_PUTS, PLT_PUTS],
        "of the 63 words the bitmap claims, the three a section holds"
    );
    assert!(
        bitmap
            .summary()
            .contains("relocs:  4 dynamic relocation(s) applied to the image; 60 refused"),
        "{}",
        bitmap.summary()
    );

    let absurd = pie(
        &[elfgen::rela(SLOT, 0, R_RELATIVE, 0x1010)],
        Some(1 << 40),
        &[],
        0,
    );
    assert_eq!(word(&absurd, SLOT), 0);
    Analysis::compute(&absurd);
}
