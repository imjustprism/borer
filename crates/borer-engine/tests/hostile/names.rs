//! Shared long table names: the loader copies only a row's head and replaces
//! names past the per-load budget so total heap stays within the file-size bar.

use std::path::PathBuf;

use borer_engine::num::from_usize;
use borer_engine::program::{Program, SymbolKind};
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
/// sequential `name_<n>` placeholders and a matching `lenient` count.
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
        assert_eq!(*actual, format!("name_{}", k + 1));
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
    assert!(p.headers.libraries[0].starts_with("name_"));
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
        #[expect(
            clippy::disallowed_methods,
            reason = "the test bounds the time a hostile string table takes"
        )]
        let started = std::time::Instant::now();
        let loaded = Program::from_bytes(PathBuf::from("bad_shstr.elf"), bytes);
        let took = started.elapsed();
        assert!(loaded.is_err(), "quadratic permissive retry was skipped");
        assert!(
            took < std::time::Duration::from_secs(2),
            "{BAD_LEN} non-UTF-8 strtab bytes took {took:?}"
        );
    }
}

/// A 32-bit Mach-O with `43,690` `nlist` records all naming one `512 KiB`
/// string loads within two seconds and within the heap bar without scanning
/// `22.9 GB` of string bytes.
#[test]
fn macho32_many_nlists_naming_half_megabyte_string_load_fast() {
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
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time a hostile nlist table takes"
    )]
    let started = std::time::Instant::now();
    check_local_names("nlist32.macho", b, NLISTS, "A");
    let took = started.elapsed();
    assert!(
        took < std::time::Duration::from_secs(2),
        "{NLISTS} nlists on a {STR_LEN}-byte string took {took:?}"
    );
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
        tail_name.starts_with("name_"),
        "expected post-budget placeholder, got {tail_name}"
    );
    let shared_rows = imports.iter().filter(|&&n| n == tail_name).count();
    assert_eq!(
        shared_rows, 16,
        "repeated binds past budget deduplicate and obey SLOTS_PER_IMPORT"
    );
}
