//! A name many entries of a file's table share: the loader copies of it
//! for each entry only what a row shows, and replaces excess names once the
//! per-load name budget is spent, so the copies stay within the per-byte
//! heap bar.

use std::path::PathBuf;

use borer_engine::num::from_usize;
use borer_engine::program::{Program, SymbolKind};
use borer_engine::text::OUTSIDE_MAX;

use super::{
    CODE, DATA, IMPORT_DIR, LOAD_HEAP_PER_BYTE, Sec, descriptor, elfgen, machogen, measured, pe,
    put32, put64, serial, text,
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
fn assert_budgeted(p: &Program, names: &[&str], total: usize, shown: &str) {
    assert_eq!(names.len(), total);
    let kept = names.iter().take_while(|n| **n == shown).count();
    assert!(kept > 0 && kept < total, "kept {kept} of {total}");
    for (k, actual) in names[kept..].iter().enumerate() {
        assert_eq!(*actual, format!("name_{}", k + 1));
    }
    let cut = total - kept;
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

/// An ELF of [`SYMBOLS`] function symbols that all name one string of
/// [`NAME_LEN`] bytes loads within the heap bar, keeping budgeted heads and
/// replacing the excess deterministically.
#[test]
fn symbols_naming_one_long_string_load_within_the_heap_bar() {
    let _one = serial();
    let bytes = symtab_elf(SYMBOLS, &vec![b'A'; NAME_LEN], 0x1_0000);
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("names.elf"), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let shown = format!("{}...", "A".repeat(OUTSIDE_MAX));
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, SYMBOLS, &shown);
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
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("crab.elf"), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let shown = format!("{}...", "🦀".repeat(OUTSIDE_MAX));
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, SYMBOLS, &shown);
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
    assert_budgeted(&p, &names, IMPORTS, &shown);
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
    assert_budgeted(&p, &names[2..], IMPORTS - 2, &shown);
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
    let size = bytes.len();
    let (loaded, extra) = measured(|| Program::from_bytes(PathBuf::from("names.macho"), bytes));
    let p = loaded.expect("the image loads");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
    let shown = format!("{}...", "A".repeat(OUTSIDE_MAX));
    let names: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| s.name.as_str())
        .collect();
    assert_budgeted(&p, &names, SYMBOLS, &shown);
}
