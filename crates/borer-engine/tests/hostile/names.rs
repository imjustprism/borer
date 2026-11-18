//! Shared long table names stay within the file-size bar.
//!
//! The loader copies only a row's head and replaces names past the per-load
//! budget so total heap stays within the bar. A find over the names and
//! strings a file holds keeps to the same bar, in time linear in the text.

use std::path::PathBuf;

use borer_engine::analysis::find::{HitKind, KIND_MAX, NEEDLE_MAX, Query, everywhere};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program, SymbolKind};
use borer_engine::text::OUTSIDE_MAX;

use super::{
    CODE, DATA, FILE_ALIGN, IMPORT_DIR, LOAD_HEAP_PER_BYTE, OPTIONAL, PE_AT, Sec, descriptor,
    elfgen, machogen, measured, pe, put16, put32, put64, serial, text,
};

/// Function or local symbols that all name one string.
const SYMBOLS: usize = 2000;
/// Import entries that all name one string.
const IMPORTS: usize = 1000;
/// Bytes of the long ASCII string they name.
const NAME_LEN: usize = 64 << 10;

/// Checks that `names` starts with budgeted `shown` copies followed by
/// sequential `<name n>` placeholders and a matching `lenient` count.
///
/// # Arguments
///
/// * `p` - Loaded program whose `lenient` notes are checked.
/// * `names` - Extracted symbol names in load order.
/// * `total` - Expected total entry count.
/// * `shown` - Expected rendered string for budgeted entries.
/// * `extra_cut` - Additional names replaced later in the same load (such as header library rows).
fn assert_budgeted(p: &Program, names: &[&str], total: usize, shown: &str, extra_cut: usize) {
    assert_eq!(names.len(), total);
    let kept = names.iter().take_while(|n| **n == shown).count();
    assert!(kept > 0 && kept < total, "kept {kept} of {total}");
    for (k, actual) in names[kept..].iter().enumerate() {
        assert_eq!(*actual, format!("<name {}>", k + 1));
    }
    let cut = total - kept + extra_cut;
    let expected = format!("{cut} names past the load name budget replaced");
    assert!(
        p.headers.lenient.iter().any(|w| w == &expected),
        "{:?}",
        p.headers.lenient
    );
}

/// Builds an ELF64 image with `count` `.symtab` function entries all naming
/// `name`, placing `.strtab` at `strtab_addr`.
///
/// # Arguments
///
/// * `count` - Number of function symbol entries.
/// * `name` - Shared symbol name bytes (without NUL).
/// * `strtab_addr` - File offset and section address for `.strtab`, or `0`
///   to place `.strtab` immediately after `.symtab`.
///
/// # Returns
///
/// Raw ELF64 image bytes.
fn symtab_elf(count: usize, name: &[u8], strtab_addr: u64) -> Vec<u8> {
    let mut symtab = vec![0u8; 24];
    for k in 0..count {
        symtab.extend(elfgen::sym(1, 0x12, 1, 0x1000 + from_usize(k)));
    }
    let mut strtab = vec![0u8];
    strtab.extend_from_slice(name);
    strtab.push(0);
    let strtab_at = if strtab_addr == 0 {
        0x2000 + from_usize(symtab.len())
    } else {
        strtab_addr
    };
    let code = vec![0xc3; 0x800];
    let mut secs = vec![
        elfgen::Sec::new(".text", elfgen::PROGBITS, elfgen::AX, 0x1000, code),
        elfgen::Sec::new(".symtab", elfgen::SYMTAB, 0, 0x2000, symtab),
        elfgen::Sec::new(".strtab", elfgen::STRTAB, 0, strtab_at, strtab),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    elfgen::build(elfgen::ET_EXEC, elfgen::EM_X86_64, 0x1000, &secs)
}

/// Loads `bytes` under `label`, verifies peak heap against
/// [`LOAD_HEAP_PER_BYTE`], and checks that `total` local symbols follow the
/// name budget for `glyph`.
///
/// # Arguments
///
/// * `label` - Synthetic filename passed to [`Program::from_bytes`].
/// * `bytes` - Raw image bytes.
/// * `total` - Expected `SymbolKind::Local` count.
/// * `glyph` - Repeated character or scalar forming the budgeted prefix.
fn check_local_names(label: &str, bytes: Vec<u8>, total: usize, glyph: &str) {
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from(label), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let shown = format!("{}...", glyph.repeat(OUTSIDE_MAX));
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, total, &shown, 0);
}

/// An ELF of [`SYMBOLS`] function symbols that all name one string of
/// [`NAME_LEN`] bytes loads within the heap bar, keeping budgeted heads and
/// replacing the excess deterministically.
#[test]
fn symbols_naming_one_long_string_load_within_the_heap_bar() {
    let _one = serial();
    let bytes = symtab_elf(SYMBOLS, &vec![b'A'; NAME_LEN], 0x1_0000);
    check_local_names("names.elf", bytes, SYMBOLS, "A");

    let escaped = symtab_elf(SYMBOLS, &[b'\n'; 64], 0);
    let esc_size = escaped.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("nl.elf"), escaped));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * esc_size,
        "a {esc_size} byte file took {extra} bytes of heap to load"
    );
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, SYMBOLS, &"\\x0a".repeat(64), 0);
}

/// An ELF of [`SYMBOLS`] function symbols sharing one 258-character 4-byte
/// UTF-8 string packed right after `.symtab` stays within the heap bar.
///
/// Each uncut head holds `1,027` UTF-8 bytes while each `.symtab` row adds
/// only `24` file bytes, so per-entry truncation alone would exceed the
/// `8x` heap bar without the per-load name budget.
#[test]
fn four_byte_symbol_names_packed_tight_stay_within_the_heap_bar() {
    let _one = serial();
    let shared = "🦀".repeat(OUTSIDE_MAX + 2);
    let bytes = symtab_elf(SYMBOLS, shared.as_bytes(), 0);
    check_local_names("crab.elf", bytes, SYMBOLS, "🦀");
}

/// A PE whose [`IMPORTS`] lookup entries all name one [`NAME_LEN`]-byte
/// `HintNameTableEntry` loads within the heap bar.
#[test]
fn pe_imports_naming_one_long_string_load_within_the_heap_bar() {
    let _one = serial();
    /// RVA of `.rdata`.
    const RDATA: u32 = 0x2000;
    /// Offset of the shared `HintNameTableEntry` within `.rdata`.
    const HINT_AT: usize = 0x4200;
    let mut rdata = vec![0u8; HINT_AT + 2 + NAME_LEN + 1];
    rdata[0xa0..0xa6].copy_from_slice(b"K.dll\0");
    descriptor(&mut rdata, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x2100);
    let hint_rva = u64::from(RDATA) + from_usize(HINT_AT);
    for k in 0..IMPORTS {
        put64(&mut rdata, 0x100 + k * 8, hint_rva);
        put64(&mut rdata, 0x2100 + k * 8, hint_rva);
    }
    rdata[HINT_AT + 2..HINT_AT + 2 + NAME_LEN].fill(b'A');
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(IMPORT_DIR, RDATA, 40)],
    );
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("imp.exe"), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let shown = format!("K.dll!{}...", "A".repeat(OUTSIDE_MAX - 6));
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, IMPORTS, &shown, 1);
    assert!(p.headers.libraries[0].starts_with("<name "));
}

/// PE delay imports keep 200 four-byte characters whole, mark 300 with
/// `...`, and stay within the heap bar across [`IMPORTS`] thunks.
#[test]
fn pe_delay_imports_bound_four_byte_names_and_heap() {
    let _one = serial();
    /// Delay-load directory index.
    const DELAY_DIR: usize = 13;
    /// RVA of `.rdata`.
    const RDATA: u32 = 0x2000;
    let short_crab = "🦀".repeat(200);
    let long_crab = "🦀".repeat(300);
    let mut rdata = vec![0u8; 0x4200];
    rdata[0x80..0x86].copy_from_slice(b"D.dll\0");
    put32(&mut rdata, 0, 1);
    put32(&mut rdata, 4, RDATA + 0x80);
    put32(&mut rdata, 12, RDATA + 0x2100);
    put32(&mut rdata, 16, RDATA + 0x100);
    let push_hint = |buf: &mut Vec<u8>, s: &[u8]| -> u64 {
        let off = buf.len();
        buf.extend_from_slice(&[0, 0]);
        buf.extend_from_slice(s);
        buf.push(0);
        u64::from(RDATA) + from_usize(off)
    };
    let h0 = push_hint(&mut rdata, short_crab.as_bytes());
    let h1 = push_hint(&mut rdata, long_crab.as_bytes());
    let h2 = push_hint(&mut rdata, &vec![b'A'; NAME_LEN]);
    put64(&mut rdata, 0x100, h0);
    put64(&mut rdata, 0x108, h1);
    for k in 2..IMPORTS {
        put64(&mut rdata, 0x100 + k * 8, h2);
    }
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(DELAY_DIR, RDATA, 64)],
    );
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("delay.exe"), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(names[0], format!("D.dll!{short_crab}"));
    assert_eq!(
        names[1],
        format!("D.dll!{}...", "🦀".repeat(OUTSIDE_MAX - 6))
    );
    let shown = format!("D.dll!{}...", "A".repeat(OUTSIDE_MAX - 6));
    assert_budgeted(&p, &names[2..], IMPORTS - 2, &shown, 0);
}

/// A 64-bit Mach-O of [`SYMBOLS`] `nlist_64` entries sharing one
/// [`NAME_LEN`]-byte string loads within the heap bar without duplicating
/// names in `seen`.
#[test]
fn macho_nlists_naming_one_long_string_load_within_the_heap_bar() {
    let _one = serial();
    /// Preferred base of `__TEXT`.
    const TEXT: u64 = 0x1_0000_0000;
    let mut seg_bytes = vec![0u8; 0x1000];
    seg_bytes[0x400..0xc00].fill(0xc3);
    let seg = machogen::Seg {
        name: "__TEXT",
        vmaddr: TEXT,
        fileoff: 0,
        bytes: seg_bytes,
        prot: machogen::RX,
        sections: vec![machogen::Sect {
            name: "__text",
            addr: TEXT + 0x400,
            size: 0x800,
            flags: machogen::CODE,
        }],
    };
    let symoff = 0x1000u32;
    let nsyms = u32::try_from(SYMBOLS).expect("fits");
    let stroff = symoff + nsyms * 16;
    let strsize = u32::try_from(NAME_LEN + 3).expect("fits");
    let mut symtab = vec![0u8; 24];
    put32(&mut symtab, 0, 0x2);
    put32(&mut symtab, 4, 24);
    put32(&mut symtab, 8, symoff);
    put32(&mut symtab, 12, nsyms);
    put32(&mut symtab, 16, stroff);
    put32(&mut symtab, 20, strsize);
    let mut bytes = machogen::build(machogen::X86_64, machogen::PIE, &[seg], &[symtab]);
    for k in 0..SYMBOLS {
        bytes.extend_from_slice(&1u32.to_le_bytes());
        bytes.push(0x0e);
        bytes.push(1);
        bytes.extend_from_slice(&0u16.to_le_bytes());
        bytes.extend_from_slice(&(TEXT + 0x400 + from_usize(k)).to_le_bytes());
    }
    bytes.extend_from_slice(b"\0_");
    bytes.resize(bytes.len() + NAME_LEN, b'A');
    bytes.push(0);
    check_local_names("names.macho", bytes, SYMBOLS, "A");
}

/// A PE with [`SYMBOLS`] `/0` and `//` indirect section headers naming one
/// [`NAME_LEN`]-byte COFF string loads within the heap bar and restores its
/// header bytes intact.
#[test]
fn pe_indirect_section_names_stay_within_the_heap_bar() {
    let _one = serial();
    let mut b = pe(&[Sec::sound(".text", 0x1000, text(), CODE)], &[]);
    let table = PE_AT + 24 + OPTIONAL;
    let headers_end = (table + SYMBOLS * 40).div_ceil(FILE_ALIGN) * FILE_ALIGN;
    b.truncate(table);
    b.resize(headers_end, 0);
    put16(
        &mut b,
        PE_AT + 6,
        u16::try_from(SYMBOLS).expect("fits in u16"),
    );
    let opt = PE_AT + 24;
    let image_end = u32::try_from((SYMBOLS + 1) * 0x1000).expect("fits in u32");
    put32(&mut b, opt + 56, image_end);
    put32(
        &mut b,
        opt + 60,
        u32::try_from(headers_end).expect("fits in u32"),
    );
    let table_size = 4 + NAME_LEN + 1;
    let out_of_table = format!("/{table_size}");
    for k in 0..SYMBOLS {
        let row = table + k * 40;
        let label: &[u8] = match k {
            1 => b"//AAAAAE",
            2 => out_of_table.as_bytes(),
            _ => b"/4",
        };
        b[row..row + label.len()].copy_from_slice(label);
        put32(&mut b, row + 8, 0x200);
        put32(
            &mut b,
            row + 12,
            u32::try_from((k + 1) * 0x1000).expect("fits in u32"),
        );
        if k == 0 {
            put32(&mut b, row + 16, 0x200);
            put32(
                &mut b,
                row + 20,
                u32::try_from(headers_end).expect("fits in u32"),
            );
            put32(&mut b, row + 36, CODE);
        } else {
            put32(&mut b, row + 36, DATA);
        }
    }
    b.extend_from_slice(&text());
    let strtab_at = u32::try_from(b.len()).expect("fits in u32");
    put32(&mut b, PE_AT + 12, strtab_at);
    put32(&mut b, PE_AT + 16, 0);
    b.extend_from_slice(
        &u32::try_from(table_size)
            .expect("fits in u32")
            .to_le_bytes(),
    );
    b.resize(b.len() + NAME_LEN, b'A');
    b.push(0);
    b.extend_from_slice(b"TAIL\0");
    let chk_field = PE_AT + 88;
    let mut sum = 0u32;
    for (i, pair) in b.chunks(2).enumerate() {
        let at = i * 2;
        if (chk_field..chk_field + 4).contains(&at) {
            continue;
        }
        let lo = u32::from(pair.first().copied().unwrap_or(0));
        let hi = u32::from(pair.get(1).copied().unwrap_or(0));
        sum += lo | (hi << 8);
        sum = (sum & 0xffff) + (sum >> 16);
    }
    sum = (sum & 0xffff) + (sum >> 16);
    let declared = (sum & 0xffff).wrapping_add(u32::try_from(b.len()).expect("fits"));
    put32(&mut b, chk_field, declared);
    let expected_bytes = b.clone();
    let size = b.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("secs.exe"), b));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    assert_eq!(p.bytes, expected_bytes);
    assert_eq!(p.headers.checksum, Some((declared, declared)));
    let shown = format!("{}...", "A".repeat(OUTSIDE_MAX));
    let sec_names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(sec_names[2], out_of_table);
    let indirect: Vec<&str> = sec_names[..2]
        .iter()
        .chain(&sec_names[3..])
        .copied()
        .collect();
    assert_budgeted(&p, &indirect, SYMBOLS - 1, &shown, 0);
}

/// Builds an ELF64 whose `e_shstrndx` names `.bad`, a string table of
/// `bad`, beside a one-instruction `.text`.
///
/// # Arguments
///
/// * `bad` - The section-name string table's bytes.
///
/// # Returns
///
/// Raw ELF64 image bytes.
fn shstrtab_elf(bad: Vec<u8>) -> Vec<u8> {
    let mut bytes = elfgen::build(
        elfgen::ET_EXEC,
        elfgen::EM_X86_64,
        0x1000,
        &[
            elfgen::Sec::new(
                ".text",
                elfgen::PROGBITS,
                elfgen::AX,
                0x1000,
                vec![0xc3; 16],
            ),
            elfgen::Sec::new(".bad", elfgen::STRTAB, 0, 0x2000, bad),
        ],
    );
    put16(&mut bytes, 62, 2);
    bytes
}

/// An ELF64 whose `e_shstrndx` names a `256 KiB` non-UTF-8 string table
/// (either all `0xff` or ASCII ending in `0xff`) is refused without running
/// goblin's quadratic permissive `Strtab` rescan.
#[test]
fn elf_non_utf8_shstrtab_is_refused_without_quadratic_rescan() {
    /// Bytes in the malformed `.shstrtab` replacement.
    const BAD_LEN: usize = 256 << 10;
    let _one = serial();
    let mut tail_bad = vec![b'a'; BAD_LEN - 2];
    tail_bad.extend_from_slice(&[0xff, 0]);
    for bad in [vec![0xff; BAD_LEN], tail_bad] {
        let bytes = shstrtab_elf(bad);
        let refused = Program::from_bytes(PathBuf::from("bad_shstr.elf"), bytes)
            .expect_err("the strict parse fails and the retry is not run");
        let why = format!("{refused:#}");
        assert!(!why.contains("lenient:"), "the permissive retry ran: {why}");
    }
}

/// A dense non-UTF-8 section-name table loads or is refused within the heap bar.
///
/// `e_shstrndx` names `256 KiB` of alternating `0xff 0x00`: one permissive
/// string-table entry per byte, a cheap linear scan. The permissive retry's
/// entries are capped by the file's length, not a fixed count.
#[test]
fn elf_dense_non_utf8_shstrtab_stays_within_the_heap_bar() {
    /// Bytes in the malformed `.shstrtab` replacement.
    const BAD_LEN: usize = 256 << 10;
    let _one = serial();
    let bad: Vec<u8> = [0xff, 0].repeat(BAD_LEN / 2);
    let bytes = shstrtab_elf(bad);
    let size = bytes.len();
    let (_, extra) = measured(|| Program::from_bytes(PathBuf::from("dense_shstr.elf"), bytes));
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
}

/// A 32-bit Mach-O with `43,690` `nlist` records naming one string stays bounded.
///
/// The string is `512 KiB`; the file loads within the heap bar, each
/// record's name read from a window
/// of the string rather than the `22.9 GB` all of them span (the window is
/// `macho::tests::an_nlist_name_scan_stops_at_its_window`).
#[test]
fn macho32_many_nlists_naming_half_megabyte_string_stay_within_the_heap_bar() {
    let _one = serial();
    /// 32-bit `nlist` entry count (`524,280` bytes of `nlist` table).
    const NLISTS: usize = 43_690;
    /// Shared string length (`512 KiB`).
    const STR_LEN: usize = 512 << 10;
    let code_at = 0x100usize;
    let code_len = 0x1_0000usize;
    let symoff = code_at + code_len;
    let stroff = symoff + NLISTS * 12;
    let strsize = STR_LEN + 3;
    let mut b = vec![0u8; code_at];
    put32(&mut b, 0, 0xfeed_face);
    put32(&mut b, 4, 7);
    put32(&mut b, 8, 3);
    put32(&mut b, 12, 2);
    put32(&mut b, 16, 2);
    put32(&mut b, 20, 124 + 24);
    put32(&mut b, 28, 1);
    put32(&mut b, 32, 124);
    b[36..42].copy_from_slice(b"__TEXT");
    put32(&mut b, 52, 0x1000);
    put32(
        &mut b,
        56,
        u32::try_from(symoff).expect("fits in 32-bit vmsize"),
    );
    put32(&mut b, 60, 0);
    put32(
        &mut b,
        64,
        u32::try_from(symoff).expect("fits in 32-bit filesize"),
    );
    put32(&mut b, 68, 7);
    put32(&mut b, 72, 5);
    put32(&mut b, 76, 1);
    b[84..90].copy_from_slice(b"__text");
    b[100..106].copy_from_slice(b"__TEXT");
    put32(
        &mut b,
        116,
        0x1000 + u32::try_from(code_at).expect("fits in u32"),
    );
    put32(&mut b, 120, u32::try_from(code_len).expect("fits in u32"));
    put32(&mut b, 124, u32::try_from(code_at).expect("fits in u32"));
    put32(&mut b, 140, 0x8000_0400);
    let sym_cmd = 28 + 124;
    put32(&mut b, sym_cmd, 2);
    put32(&mut b, sym_cmd + 4, 24);
    put32(&mut b, sym_cmd + 8, u32::try_from(symoff).expect("fits"));
    put32(&mut b, sym_cmd + 12, u32::try_from(NLISTS).expect("fits"));
    put32(&mut b, sym_cmd + 16, u32::try_from(stroff).expect("fits"));
    put32(&mut b, sym_cmd + 20, u32::try_from(strsize).expect("fits"));
    b.resize(symoff, 0xc3);
    for k in 0..NLISTS {
        b.extend_from_slice(&1u32.to_le_bytes());
        b.push(0x0e);
        b.push(1);
        b.extend_from_slice(&0u16.to_le_bytes());
        let va = 0x1100 + u32::try_from(k).expect("fits");
        b.extend_from_slice(&va.to_le_bytes());
    }
    b.extend_from_slice(b"\0_");
    b.resize(b.len() + STR_LEN, b'A');
    b.push(0);
    check_local_names("nlist32.macho", b, NLISTS, "A");
}

/// DWARF struct and member names resolved through `.debug_str` share the
/// per-load `Names` budget and stay within `LOAD_HEAP_PER_BYTE`.
#[test]
fn dwarf_struct_member_names_stay_within_the_heap_bar() {
    let _one = serial();
    /// Number of `DW_TAG_structure_type` DIEs in the unit.
    const STRUCTS: usize = 400;
    /// `DW_TAG_member` children per structure DIE.
    const MEMBERS: usize = 128;
    let abbrev = vec![
        0x01, 0x13, 0x01, 0x03, 0x0e, 0x0b, 0x05, 0x00, 0x00, 0x02, 0x0d, 0x00, 0x03, 0x0e, 0x38,
        0x05, 0x49, 0x13, 0x00, 0x00, 0x03, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00,
        0x00, 0x00,
    ];
    let mut debug_str = Vec::new();
    let struct_str = u32::try_from(debug_str.len()).expect("fits");
    debug_str.extend_from_slice(&[b'T'; 56]);
    debug_str.extend_from_slice(b"_leaf\0");
    let member_str = u32::try_from(debug_str.len()).expect("fits");
    debug_str.extend_from_slice(&[b'm'; 120]);
    debug_str.push(0);

    let mut dies = Vec::new();
    let int_at = u32::try_from(12 + dies.len()).expect("fits");
    dies.push(0x03);
    dies.extend_from_slice(b"int\0\x04\x05");
    let leaf_at = u32::try_from(12 + dies.len()).expect("fits");
    dies.push(0x01);
    dies.extend_from_slice(&struct_str.to_le_bytes());
    dies.extend_from_slice(&8u16.to_le_bytes());
    dies.push(0x02);
    dies.extend_from_slice(&member_str.to_le_bytes());
    dies.extend_from_slice(&0u16.to_le_bytes());
    dies.extend_from_slice(&int_at.to_le_bytes());
    dies.push(0x00);

    for k in 0..STRUCTS {
        let s_off = u32::try_from(debug_str.len()).expect("fits");
        debug_str.extend_from_slice(format!("S{:04}_{}", k, "X".repeat(50)).as_bytes());
        debug_str.push(0);
        dies.push(0x01);
        dies.extend_from_slice(&s_off.to_le_bytes());
        dies.extend_from_slice(&u16::try_from(MEMBERS * 8).expect("fits").to_le_bytes());
        for m in 0..MEMBERS {
            dies.push(0x02);
            dies.extend_from_slice(&member_str.to_le_bytes());
            dies.extend_from_slice(&u16::try_from(m * 8).expect("fits").to_le_bytes());
            dies.extend_from_slice(&leaf_at.to_le_bytes());
        }
        dies.push(0x00);
    }
    dies.push(0x00);
    let mut unit_body = Vec::new();
    unit_body.extend_from_slice(&5u16.to_le_bytes());
    unit_body.push(0x01);
    unit_body.push(8);
    unit_body.extend_from_slice(&0u32.to_le_bytes());
    unit_body.extend_from_slice(&dies);
    let mut info = u32::try_from(unit_body.len())
        .expect("fits")
        .to_le_bytes()
        .to_vec();
    info.extend_from_slice(&unit_body);

    let abbrev_at = 0x2000u64;
    let info_at = abbrev_at + from_usize(abbrev.len());
    let str_at = info_at + from_usize(info.len());
    let bytes = elfgen::build(
        elfgen::ET_EXEC,
        elfgen::EM_X86_64,
        0x1000,
        &[
            elfgen::Sec::new(
                ".text",
                elfgen::PROGBITS,
                elfgen::AX,
                0x1000,
                vec![0xc3; 16],
            ),
            elfgen::Sec::new(".debug_abbrev", elfgen::PROGBITS, 0, abbrev_at, abbrev),
            elfgen::Sec::new(".debug_info", elfgen::PROGBITS, 0, info_at, info),
            elfgen::Sec::new(".debug_str", elfgen::PROGBITS, 0, str_at, debug_str),
        ],
    );
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("dwarf.elf"), bytes));
    let p = loaded.expect("the ELF loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte DWARF ELF took {extra} bytes of heap"
    );
    assert!(!p.debug_types.is_empty(), "budgeted structs kept");
    assert!(p.debug_types.len() < STRUCTS, "excess structs skipped");
}

/// Long `_`-prefixed Mach-O `LC_DYLD_INFO` bind names preserve `...` after
/// stripping `_` and still deduplicate repeated binds after the `Names`
/// budget is spent.
#[test]
fn macho_dyld_long_import_keeps_ellipsis_and_deduplicates_past_budget() {
    let _one = serial();
    /// Preferred base of `__TEXT`.
    const TEXT: u64 = 0x1_0000_0000;
    /// Preferred base of `__DATA`.
    const DATA_VA: u64 = 0x1_0000_8000;
    /// Linked dylib load commands so one symbol name can bind across ordinals.
    const LIBS: u8 = 80;
    let mut text_seg = vec![0u8; 0x8000];
    text_seg[0x7f00..0x8000].fill(0xc3);
    let data_seg = vec![0u8; 0x1000];
    let segs = [
        machogen::Seg {
            name: "__TEXT",
            vmaddr: TEXT,
            fileoff: 0,
            bytes: text_seg,
            prot: machogen::RX,
            sections: vec![machogen::Sect {
                name: "__text",
                addr: TEXT + 0x7f00,
                size: 0x100,
                flags: machogen::CODE,
            }],
        },
        machogen::Seg {
            name: "__DATA",
            vmaddr: DATA_VA,
            fileoff: 0x8000,
            bytes: data_seg,
            prot: machogen::RW,
            sections: vec![machogen::Sect {
                name: "__got",
                addr: DATA_VA,
                size: 0x1000,
                flags: 0,
            }],
        },
    ];
    let mut ops = vec![0x51u8, 0x71, 0x00, 0x40];
    ops.extend_from_slice(format!("_imp000_{}", "🦀".repeat(300)).as_bytes());
    ops.push(0);
    for ord in 1..=LIBS {
        ops.extend_from_slice(&[0x20, ord, 0x90]);
    }
    let shared_raw = format!("_shared_{}", "C".repeat(300));
    ops.push(0x11);
    ops.push(0x40);
    ops.extend_from_slice(shared_raw.as_bytes());
    ops.push(0);
    ops.resize(ops.len() + 64, 0x90);
    ops.push(0x00);

    let bind_off = 0x9000u64;
    let mut extra: Vec<Vec<u8>> = (0..LIBS).map(|_| machogen::dylib("/l")).collect();
    extra.push(machogen::dyld_info((0, 0), (bind_off, ops.len()), (0, 0)));
    let mut bytes = machogen::build(machogen::X86_64, machogen::PIE, &segs, &extra);
    assert_eq!(bytes.len(), usize::try_from(bind_off).expect("fits"));
    bytes.extend_from_slice(&ops);
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("dyld.macho"), bytes));
    let p = loaded.expect("the Mach-O loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte Mach-O took {extra} bytes of heap"
    );
    let imports: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    let first_expected = format!("imp000_{}...", "🦀".repeat(OUTSIDE_MAX - 7));
    assert_eq!(imports.first().copied(), Some(first_expected.as_str()));
    let tail_name = *imports.last().expect("shared import emitted");
    assert!(
        tail_name.starts_with("<name "),
        "expected post-budget placeholder, got {tail_name}"
    );
    let shared_rows = imports.iter().filter(|&&n| n == tail_name).count();
    assert_eq!(
        shared_rows, 16,
        "repeated binds past budget deduplicate and obey SLOTS_PER_IMPORT"
    );
}

/// A function named in both `.dynsym` and `.symtab` gets one symbol.
///
/// Both tables name [`SYMBOLS`] functions with one string of [`NAME_LEN`]
/// bytes, which spends the name budget in `.dynsym`: a `.symtab` entry
/// matches its `.dynsym` twin by the name the table spells, not by the
/// placeholder the twin took.
#[test]
fn a_symtab_twin_of_a_placeholder_export_adds_no_second_symbol() {
    /// Where `.dynsym` sits, right after the code.
    const DYNSYM_AT: u64 = 0x1800;
    /// Where `.symtab` sits.
    const SYMTAB_AT: u64 = 0xd400;
    /// Where the string table both symbol tables share sits.
    const DYNSTR_AT: u64 = 0x1_9000;
    /// Where `.dynamic` sits, past the string table.
    const DYNAMIC_AT: u64 = 0x2_9008;
    /// Where the hash table that counts `.dynsym` sits, past `.dynamic`.
    const HASH_AT: u64 = 0x2_9100;
    let _one = serial();
    let mut table = vec![0u8; 24];
    for k in 0..SYMBOLS {
        table.extend(elfgen::sym(1, 0x12, 1, 0x1000 + from_usize(k)));
    }
    let mut strtab = vec![0u8];
    strtab.resize(1 + NAME_LEN, b'A');
    strtab.push(0);
    let strsz = from_usize(strtab.len());
    let dynamic = elfgen::dynamic(&[
        (4, HASH_AT),
        (6, DYNSYM_AT),
        (5, DYNSTR_AT),
        (10, strsz),
        (11, 24),
    ]);
    let nchain = u32::try_from(SYMBOLS + 1).expect("fits");
    let hash: Vec<u8> = [1, nchain, 0]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    let code = vec![0xc3; 0x800];
    let mut secs = vec![
        elfgen::Sec::new(".text", elfgen::PROGBITS, elfgen::AX, 0x1000, code),
        elfgen::Sec::new(
            ".dynsym",
            elfgen::DYNSYM,
            elfgen::A,
            DYNSYM_AT,
            table.clone(),
        ),
        elfgen::Sec::new(".symtab", elfgen::SYMTAB, 0, SYMTAB_AT, table),
        elfgen::Sec::new(".dynstr", elfgen::STRTAB, elfgen::A, DYNSTR_AT, strtab),
        elfgen::Sec::new(".dynamic", elfgen::DYNAMIC, elfgen::WA, DYNAMIC_AT, dynamic),
        elfgen::Sec::new(".hash", elfgen::PROGBITS, elfgen::A, HASH_AT, hash),
    ];
    for s in &mut secs[1..3] {
        s.link = 4;
        s.info = 1;
        s.entsize = 24;
    }
    secs[4].link = 4;
    secs[4].entsize = 16;
    let bytes = elfgen::build(elfgen::ET_DYN, elfgen::EM_X86_64, 0x1000, &secs);
    let p = Program::from_bytes(PathBuf::from("twins.so"), bytes).expect("the image loads");
    let mut per_addr: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    for s in &p.symbols {
        *per_addr.entry(s.addr).or_default() += 1;
    }
    assert_eq!(per_addr.len(), SYMBOLS);
    let doubled = per_addr.values().filter(|n| **n > 1).count();
    assert_eq!(doubled, 0, "{doubled} functions named twice");
    assert!(
        p.symbols.iter().any(|s| s.name.starts_with("<name ")),
        "the budget was spent in .dynsym"
    );
}

/// A Go `pclntab` whose functions all name one long string stays in the heap bar.
///
/// Its [`SYMBOLS`] functions name one string of 1000 four-byte characters
/// in a Go 1.20 table: each name is read
/// as its head and charged to the load's name budget, so past the budget
/// the functions take placeholders.
#[test]
fn go_functions_naming_one_long_string_load_within_the_heap_bar() {
    /// Where the code starts, which the table's entries count from.
    const TEXT: u64 = 0x1000;
    /// Where the table sits.
    const TABLE_AT: u64 = 0x3000;
    /// Bytes in one Go 1.20 `_func` record.
    const RECORD: usize = 44;
    let _one = serial();
    let mut name = "🦀".repeat(1000).into_bytes();
    name.push(0);
    let pcln = (72 + name.len()).next_multiple_of(8);
    let functab = (SYMBOLS + 1) * 8;
    let mut table = vec![0u8; pcln + functab + SYMBOLS * RECORD];
    table[..8].copy_from_slice(&[0xf1, 0xff, 0xff, 0xff, 0, 0, 1, 8]);
    let pcln64 = from_usize(pcln);
    let header = [
        from_usize(SYMBOLS),
        0,
        TEXT,
        72,
        pcln64,
        pcln64,
        pcln64,
        pcln64,
    ];
    for (k, v) in header.iter().enumerate() {
        put64(&mut table, 8 + k * 8, *v);
    }
    table[72..72 + name.len()].copy_from_slice(&name);
    for k in 0..SYMBOLS {
        let entry = u32::try_from(k).expect("fits");
        let record = functab + k * RECORD;
        put32(&mut table, pcln + k * 8, entry);
        put32(
            &mut table,
            pcln + k * 8 + 4,
            u32::try_from(record).expect("fits"),
        );
        put32(&mut table, pcln + record, entry);
    }
    put32(
        &mut table,
        pcln + SYMBOLS * 8,
        u32::try_from(SYMBOLS).expect("fits"),
    );
    let bytes = elfgen::build(
        elfgen::ET_EXEC,
        elfgen::EM_X86_64,
        TEXT,
        &[
            elfgen::Sec::new(
                ".text",
                elfgen::PROGBITS,
                elfgen::AX,
                TEXT,
                vec![0xc3; SYMBOLS],
            ),
            elfgen::Sec::new(".gopclntab", elfgen::PROGBITS, elfgen::A, TABLE_AT, table),
        ],
    );
    check_local_names("go.elf", bytes, SYMBOLS, "🦀");
}

/// An import named with a newline and a `# ` line forges no line of the
/// triage: the loader escapes the name before any report spells it.
#[test]
fn an_import_name_forges_no_triage_line() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x400];
    descriptor(&mut rdata, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x200);
    rdata[0xa0..0xa6].copy_from_slice(b"K.dll\0");
    let name = b"\0\0InternetOpenA\n# forged line\0";
    rdata[0x300..0x300 + name.len()].copy_from_slice(name);
    for table in [0x100, 0x200] {
        put64(&mut rdata, table, u64::from(RDATA + 0x300));
    }
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(IMPORT_DIR, RDATA, 40)],
    );
    let p = Program::from_bytes(PathBuf::from("forged.exe"), bytes)
        .unwrap_or_else(|e| panic!("a PE with an import table loads: {e}"));
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::triage(&p, &a, &o).spell();
    assert!(!out.lines().any(|l| l.starts_with("# forged")), "{out}");
    assert!(out.contains("InternetOpenA\\x0a# forged line"), "{out}");
}

/// Returns a raw image of `bytes`, mapped by no section.
///
/// # Arguments
///
/// * `bytes` - The file.
fn raw_image(bytes: Vec<u8>) -> Program {
    Program::raw(bytes, Arch::X86_64, 0, None, Vec::new())
}

/// A find over one long run is linear in the run.
///
/// A needle of the longest kept length over a 16 MiB run that holds it at
/// every place but the first is ranked in one pass, as fast as a needle of
/// one character over the same run within a small factor: a search testing
/// the whole needle at every place compared 256 times as many bytes.
#[test]
fn a_find_over_one_long_run_is_linear() {
    /// How many times the one-character needle's time the longest may take.
    const FACTOR: u32 = 8;
    let _serial = serial();
    let mut bytes = vec![b'b'];
    bytes.resize(16 << 20, b'a');
    bytes.push(0);
    let p = raw_image(bytes);
    let (a, o) = (Analysis::default(), Overlay::default());
    let walked = everywhere(&p, &a, &o, &Query::parse("zzzzz"), 10);
    assert!(walked.hits.is_empty());
    let timed = |text: &str| {
        #[expect(
            clippy::disallowed_methods,
            reason = "the test bounds the time a hostile text takes"
        )]
        let started = std::time::Instant::now();
        let found = everywhere(&p, &a, &o, &Query::parse(text), 10);
        assert_eq!(found.counted, [(HitKind::String, 1)], "{text}");
        started.elapsed()
    };
    let short = timed("a");
    let long = timed(&"a".repeat(NEEDLE_MAX));
    assert!(
        long <= short * FACTOR + std::time::Duration::from_millis(50),
        "a {NEEDLE_MAX}-character needle took {long:?}, one character {short:?}"
    );
}

/// A find matching every one of a million short strings counts them all
/// and holds only a kind's share of them: keeping every match before the
/// cut took dozens of bytes per byte of file.
#[test]
fn a_find_over_many_matches_holds_only_its_share() {
    let _serial = serial();
    let bytes = b"aaaaa\0".repeat(1 << 20);
    let size = bytes.len();
    let strings = size / 6;
    let p = raw_image(bytes);
    let (a, o) = (Analysis::default(), Overlay::default());
    let walked = everywhere(&p, &a, &o, &Query::parse("zzzzz"), 10);
    assert!(walked.hits.is_empty());
    let (found, extra) = measured(|| everywhere(&p, &a, &o, &Query::parse("a"), 1000));
    assert_eq!(found.counted, [(HitKind::String, strings)]);
    assert_eq!(found.hits.len(), KIND_MAX);
    println!("find: {size} byte file, {extra} bytes of heap beyond the walk");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a find over {strings} strings took {extra} bytes of heap"
    );
}

/// Builds an x64 image whose `main` calls `n` tiny functions.
///
/// Function `k` is a `lea rcx,[rip+target]` for each of its two targets,
/// then `ret`; `targets` gives them as offsets into `rdata`, the read-only
/// section after `.text`.
///
/// # Arguments
///
/// * `n` - How many functions.
/// * `rdata` - The read-only data.
/// * `targets` - The two offsets into `rdata` function `k` references.
fn referencing(n: usize, rdata: &[u8], targets: impl Fn(usize) -> [usize; 2]) -> Program {
    use borer_engine::program::Section;
    /// Bytes of each function: two `lea`s and a `ret`, padded.
    const SLOT: usize = 16;
    let base = 0x1000u64;
    let first = (5 * n + 1).next_multiple_of(SLOT);
    let text_len = (first + SLOT * n).next_multiple_of(0x1000);
    let rdata_va = base + from_usize(text_len);
    let mut bytes = vec![0xccu8; text_len];
    let rel = |end: usize, to: u64| {
        borer_engine::num::lo32(to.wrapping_sub(base + from_usize(end))).to_le_bytes()
    };
    for k in 0..n {
        let f = first + SLOT * k;
        bytes[5 * k] = 0xe8; // ASM: call f
        bytes[5 * k + 1..5 * k + 5].copy_from_slice(&rel(5 * k + 5, base + from_usize(f)));
        for (i, target) in targets(k).into_iter().enumerate() {
            let at = f + 7 * i;
            bytes[at..at + 3].copy_from_slice(&[0x48, 0x8d, 0x0d]); // ASM: lea rcx,[rip+target]
            let to = rdata_va + from_usize(target);
            bytes[at + 3..at + 7].copy_from_slice(&rel(at + 7, to));
        }
        bytes[f + 14] = 0xc3; // ASM: ret
    }
    bytes[5 * n] = 0xc3; // ASM: ret
    let rdata_len = rdata.len().next_multiple_of(0x1000);
    bytes.extend_from_slice(rdata);
    bytes.resize(text_len + rdata_len, 0);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(base),
        vec![
            Section::mapped(".text", base, 0, from_usize(text_len), false, true),
            Section::mapped(
                ".rdata",
                rdata_va,
                from_usize(text_len),
                from_usize(rdata_len),
                false,
                false,
            ),
        ],
    )
}

/// Functions in the chain of signatures.
const CHAINED: usize = 4096;

/// A chain of functions, each referencing its own signature and the one
/// before it, is named whole from a loaded image.
///
/// Only the last function references a signature no other does; naming
/// it leaves the one before it the last unnamed referrer of its own, and
/// so on down, so the chain is named one function per round. The work
/// that takes is bounded in `naming`'s own test, which counts its steps.
#[test]
fn a_chain_of_signatures_is_named_whole() {
    let _serial = serial();
    let sig = |k: usize| format!("void A::f{k:05}()\0");
    let width = sig(0).len();
    let rdata: String = (0..CHAINED).map(sig).collect();
    let p = referencing(CHAINED, rdata.as_bytes(), |k| {
        [width * k, width * k.saturating_sub(1)]
    });
    let a = Analysis::compute(&p);
    let named = a
        .functions
        .iter()
        .filter_map(|f| f.name.as_deref())
        .filter(|n| n.starts_with("A::f"))
        .count();
    assert_eq!(named, CHAINED);
}

/// Template signatures packed back to back.
const BOUND: usize = 2048;

/// Longest name a signature may give a function, in bytes.
const NAME_MAX: usize = 120;

/// Back-to-back template signatures name nothing longer than a name may
/// be, in the heap the file-size bar allows.
///
/// Each binds one parameter its class spells sixty-four times, and the
/// image takes at most a byte per signature byte over the same image
/// holding prose.
///
/// Spelling each binding into the class's arguments made names and heap
/// grow with the uses times the binding, past both bounds (C-208). The
/// read-only data is padded to a megabyte: two thousand functions take
/// their own heap, signatures or not.
#[test]
fn bound_signatures_stay_within_the_name_and_heap_bars() {
    let _serial = serial();
    let sig = |k: usize| {
        let head = format!("void A{k:04}<{}T>() [with T = ", "T,".repeat(63));
        format!("{head}{}]\0", "a".repeat(204 - head.len()))
    };
    let width = sig(0).len();
    let analyzed = |text: &dyn Fn(usize) -> String| {
        let mut rdata: String = (0..BOUND).map(text).collect();
        assert_eq!(rdata.len(), width * BOUND);
        rdata.push_str(&"\0".repeat((1 << 20) - rdata.len()));
        let p = referencing(BOUND, rdata.as_bytes(), |k| [width * k, width * k]);
        let (a, extra) = measured(|| Analysis::compute(&p));
        let longest = a
            .functions
            .iter()
            .filter_map(|f| f.name.as_ref())
            .map(String::len)
            .max();
        (p.bytes.len(), extra, longest)
    };
    let (_, plain, _) = analyzed(&|_| format!("{}\0", "a".repeat(width - 1)));
    let (size, extra, longest) = analyzed(&sig);
    println!("bound signatures: {size} byte file, {extra} bytes of heap, {plain} for prose");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size && extra <= plain + width * BOUND,
        "a {size} byte file took {extra} bytes of heap to analyze, {plain} for prose"
    );
    assert!(longest.is_none_or(|n| n <= NAME_MAX), "{longest:?}");
}
