//! Damaged headers built in memory: the loader answers them in bounded
//! time and memory, and keeps reading the sound ones the same way.
//!
//! A mutation campaign over kernel32 and borer.exe found the loader
//! trusting counts the file states: `.rdata` moved one byte in the file
//! named 6.8 million imports of 844 KB and took a gigabyte before the
//! analysis began; an export directory landing on garbage sized three
//! tables by its counts; a section whose memory size was two gigabytes was
//! thrown away with the code it held. Each case here is the header that
//! did it, rebuilt from scratch, with the bound it must now hold.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use borer_engine::analysis::Analysis;
use borer_engine::num::from_usize;
use borer_engine::program::{Program, SymbolKind};

/// Live heap bytes, kept by [`Counting`].
static LIVE: AtomicUsize = AtomicUsize::new(0);
/// Highest [`LIVE`] since the last [`measured`] began.
static PEAK: AtomicUsize = AtomicUsize::new(0);
/// One test at a time, since the counters are process-wide.
static SERIAL: Mutex<()> = Mutex::new(());

/// The system allocator with a live-bytes counter and a high-water mark.
struct Counting;

/// Adds `n` live bytes and raises the peak.
fn bump(n: usize) {
    let now = LIVE.fetch_add(n, Ordering::Relaxed) + n;
    PEAK.fetch_max(now, Ordering::Relaxed);
}

#[expect(
    unsafe_code,
    reason = "a global allocator is the one way to measure what a load allocates"
)]
// SAFETY: every method forwards to `System` unchanged and only counts bytes.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's `alloc` contract is passed on unchanged.
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            bump(layout.size());
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's `alloc_zeroed` contract is passed on unchanged.
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            bump(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from `System` through this allocator with `layout`.
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: `ptr` came from `System` through this allocator with `layout`.
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
            bump(new_size);
        }
        p
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// Runs `f` and reports the most heap it held beyond what was live before.
///
/// # Arguments
///
/// * `f` - The work to measure.
///
/// # Returns
///
/// The result and the extra bytes at the peak.
fn measured<T>(f: impl FnOnce() -> T) -> (T, usize) {
    let before = LIVE.load(Ordering::Relaxed);
    PEAK.store(before, Ordering::Relaxed);
    let out = f();
    (out, PEAK.load(Ordering::Relaxed).saturating_sub(before))
}

/// Takes the serial lock, poisoned or not.
fn serial() -> std::sync::MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Where the headers end and the first section's bytes begin.
const HEADERS: usize = 0x400;
/// The file alignment every section's bytes keep.
const FILE_ALIGN: usize = 0x200;
/// The preferred load address.
const IMAGE_BASE: u64 = 0x1_4000_0000;
/// Where the PE signature sits.
const PE_AT: usize = 0x80;
/// Bytes of the PE32+ optional header.
const OPTIONAL: usize = 240;
/// `IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ`.
const CODE: u32 = 0x6000_0020;
/// `IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ`.
const DATA: u32 = 0x4000_0040;
/// The export directory's slot.
const EXPORT_DIR: usize = 0;
/// The import directory's slot.
const IMPORT_DIR: usize = 1;
/// The certificate directory's slot; its address is a file offset.
const CERTIFICATE_DIR: usize = 4;

/// One section of a built image.
struct Sec {
    /// Its name, at most eight bytes.
    name: &'static str,
    /// Where it maps, relative to [`IMAGE_BASE`].
    rva: u32,
    /// Its bytes in the file.
    data: Vec<u8>,
    /// Its memory size as the table states it.
    vsize: u32,
    /// Its raw size as the table states it; `None` for the bytes' own
    /// length rounded up to the file alignment.
    raw_size: Option<u32>,
    /// `IMAGE_SCN_*` flags.
    chars: u32,
}

impl Sec {
    /// A section whose table row tells the truth about its bytes.
    fn sound(name: &'static str, rva: u32, data: Vec<u8>, chars: u32) -> Sec {
        let vsize = u32::try_from(data.len()).expect("a test section fits a u32");
        Sec {
            name,
            rva,
            data,
            vsize,
            raw_size: None,
            chars,
        }
    }
}

/// Writes a little-endian `u16`.
fn put16(b: &mut [u8], at: usize, v: u16) {
    b[at..at + 2].copy_from_slice(&v.to_le_bytes());
}

/// Writes a little-endian `u32`.
fn put32(b: &mut [u8], at: usize, v: u32) {
    b[at..at + 4].copy_from_slice(&v.to_le_bytes());
}

/// Writes a little-endian `u64`.
fn put64(b: &mut [u8], at: usize, v: u64) {
    b[at..at + 8].copy_from_slice(&v.to_le_bytes());
}

/// Builds a PE32+ image: DOS stub, headers, the section table and the
/// sections' bytes at file-aligned offsets, entered at the first byte of
/// the first section.
///
/// # Arguments
///
/// * `secs` - The sections, in table order.
/// * `dirs` - Data directory entries as `(slot, rva, size)`.
fn pe(secs: &[Sec], dirs: &[(usize, u32, u32)]) -> Vec<u8> {
    let mut b = vec![0u8; HEADERS];
    b[..2].copy_from_slice(b"MZ");
    put32(&mut b, 0x3c, u32::try_from(PE_AT).expect("fits"));
    b[PE_AT..PE_AT + 4].copy_from_slice(b"PE\0\0");
    let coff = PE_AT + 4;
    put16(&mut b, coff, 0x8664);
    put16(
        &mut b,
        coff + 2,
        u16::try_from(secs.len()).expect("few sections"),
    );
    put16(&mut b, coff + 16, u16::try_from(OPTIONAL).expect("fits"));
    put16(&mut b, coff + 18, 0x0022);
    let opt = coff + 20;
    put16(&mut b, opt, 0x20b);
    put32(&mut b, opt + 16, secs.first().map_or(0, |s| s.rva));
    put64(&mut b, opt + 24, IMAGE_BASE);
    put32(&mut b, opt + 32, 0x1000);
    put32(&mut b, opt + 36, u32::try_from(FILE_ALIGN).expect("fits"));
    put16(&mut b, opt + 48, 6);
    let image_end = secs
        .iter()
        .map(|s| s.rva.saturating_add(s.vsize.max(1)))
        .max()
        .unwrap_or(0x1000);
    put32(&mut b, opt + 56, image_end.div_ceil(0x1000) * 0x1000);
    put32(&mut b, opt + 60, u32::try_from(HEADERS).expect("fits"));
    put16(&mut b, opt + 68, 3);
    put64(&mut b, opt + 72, 0x10_0000);
    put64(&mut b, opt + 80, 0x1000);
    put64(&mut b, opt + 88, 0x10_0000);
    put64(&mut b, opt + 96, 0x1000);
    put32(&mut b, opt + 108, 16);
    for &(slot, rva, size) in dirs {
        put32(&mut b, opt + 112 + slot * 8, rva);
        put32(&mut b, opt + 112 + slot * 8 + 4, size);
    }
    let mut row = opt + OPTIONAL;
    let mut at = HEADERS;
    for s in secs {
        let raw = s.raw_size.unwrap_or_else(|| {
            u32::try_from(s.data.len().div_ceil(FILE_ALIGN) * FILE_ALIGN).expect("fits")
        });
        let name = s.name.as_bytes();
        b[row..row + name.len()].copy_from_slice(name);
        put32(&mut b, row + 8, s.vsize);
        put32(&mut b, row + 12, s.rva);
        put32(&mut b, row + 16, raw);
        put32(&mut b, row + 20, u32::try_from(at).expect("fits"));
        put32(&mut b, row + 36, s.chars);
        row += 40;
        at += s.data.len().div_ceil(FILE_ALIGN) * FILE_ALIGN;
    }
    assert!(row <= HEADERS, "the section table runs into the sections");
    for s in secs {
        b.extend_from_slice(&s.data);
        b.resize(b.len().div_ceil(FILE_ALIGN) * FILE_ALIGN, 0);
    }
    b
}

/// A `.text` of `mov eax, 1; ret` and `int3` padding.
fn text() -> Vec<u8> {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code
}

/// Loads `bytes` as a file called `hostile.exe`.
fn load(bytes: Vec<u8>) -> Program {
    Program::from_bytes(PathBuf::from("hostile.exe"), bytes)
        .expect("a PE with a section table loads")
}

/// Writes one import descriptor at `at`.
fn descriptor(b: &mut [u8], at: usize, lookup: u32, name: u32, iat: u32) {
    put32(b, at, lookup);
    put32(b, at + 12, name);
    put32(b, at + 16, iat);
}

/// An import table that names more entries than the file holds is refused.
///
/// Eight descriptors sharing one lookup table claim four times the words
/// of the file, and none of them becomes an import.
#[test]
fn an_import_table_past_what_fits_is_refused() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x1000];
    rdata[0xa0..0xa6].copy_from_slice(b"X.dll\0");
    for k in 0..8 {
        descriptor(
            &mut rdata,
            k * 20,
            RDATA + 0x100,
            RDATA + 0xa0,
            RDATA + 0x100,
        );
    }
    for word in (0x100..0xf00).step_by(8) {
        put64(&mut rdata, word, 0x8000_0000_0000_0001);
    }
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(IMPORT_DIR, RDATA, 180)],
    );
    let fits = from_usize(bytes.len() / 8);
    let p = load(bytes);
    let refused = p.headers.implausible_imports.expect("the table is refused");
    assert!(
        refused > fits,
        "refused at {refused}, past the {fits} words that fit"
    );
    assert!(
        !p.symbols.iter().any(|s| s.kind == SymbolKind::Import),
        "an import came out of a refused table"
    );
    assert!(p.headers.libraries.is_empty());
    assert!(
        p.summary().contains("import table implausible"),
        "the summary does not say the table was refused:\n{}",
        p.summary()
    );
}

/// A refused import table costs no memory.
///
/// One descriptor naming a lookup table of a quarter million words would
/// have become a quarter million imports; the load holds less than the
/// file again beyond the file.
#[test]
fn a_refused_import_table_allocates_nothing() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 2 << 20];
    rdata[0xa0..0xa6].copy_from_slice(b"X.dll\0");
    descriptor(&mut rdata, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x100);
    for word in (0x100..rdata.len()).step_by(8) {
        put64(&mut rdata, word, 0x8000_0000_0000_0001);
    }
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(IMPORT_DIR, RDATA, 40)],
    );
    let len = bytes.len();
    let (p, extra) = measured(|| load(bytes));
    assert!(p.headers.implausible_imports.is_some());
    assert!(
        extra < len,
        "the load of a {len}-byte file held {extra} bytes beyond the file"
    );
}

/// A sound import table is read as before: two names from one DLL, each
/// at its IAT slot, and the library listed.
#[test]
fn a_sound_import_table_is_still_read() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x400];
    descriptor(&mut rdata, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x200);
    rdata[0xa0..0xa6].copy_from_slice(b"K.dll\0");
    rdata[0x300..0x306].copy_from_slice(b"\0\0Foo\0");
    rdata[0x310..0x316].copy_from_slice(b"\0\0Bar\0");
    for table in [0x100, 0x200] {
        put64(&mut rdata, table, u64::from(RDATA + 0x300));
        put64(&mut rdata, table + 8, u64::from(RDATA + 0x310));
    }
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(IMPORT_DIR, RDATA, 40)],
    );
    let p = load(bytes);
    assert_eq!(p.headers.implausible_imports, None);
    assert_eq!(p.headers.libraries, vec!["K.dll".to_owned()]);
    let imports: Vec<(String, u64)> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| (s.name.clone(), s.addr))
        .collect();
    assert_eq!(
        imports,
        vec![
            (
                "K.dll!Foo".to_owned(),
                IMAGE_BASE + u64::from(RDATA) + 0x200
            ),
            (
                "K.dll!Bar".to_owned(),
                IMAGE_BASE + u64::from(RDATA) + 0x208
            ),
        ]
    );
}

/// Writes an export directory at `at` whose tables sit right after it.
///
/// # Arguments
///
/// * `b` - The section's bytes.
/// * `at` - Offset of the directory inside the section.
/// * `rva` - The section's RVA.
/// * `functions` - The address table's entry count as stated.
/// * `names` - The name pointer count as stated.
fn export_directory(b: &mut [u8], at: usize, rva: u32, functions: u32, names: u32) {
    let here = |off: usize| rva + u32::try_from(at + off).expect("fits");
    put32(b, at + 12, here(0x80));
    put32(b, at + 16, 1);
    put32(b, at + 20, functions);
    put32(b, at + 24, names);
    put32(b, at + 28, here(0x40));
    put32(b, at + 32, here(0x50));
    put32(b, at + 36, here(0x60));
    put32(b, at + 0x40, 0x1000);
    put32(b, at + 0x50, here(0x70));
    put16(b, at + 0x60, 0);
    b[at + 0x70..at + 0x74].copy_from_slice(b"Exp\0");
    b[at + 0x80..at + 0x86].copy_from_slice(b"T.dll\0");
}

/// An export directory past the ordinal space is not read.
///
/// It costs nothing and leaves the file as it was: the entry zeroed for
/// the parse is back, so a second load answers the same.
#[test]
fn an_export_table_past_the_ordinal_space_is_not_read() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 2 << 20];
    export_directory(&mut rdata, 0, RDATA, 0x7fff_ffff, 0x7fff_ffff);
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(EXPORT_DIR, RDATA, 0x100)],
    );
    let original = bytes.clone();
    let len = bytes.len();
    let (p, extra) = measured(|| load(bytes));
    assert_eq!(p.headers.implausible_exports, Some(0x7fff_ffff));
    assert!(
        !p.symbols.iter().any(|s| s.kind == SymbolKind::Export),
        "an export came out of a refused table"
    );
    assert!(
        extra < len,
        "the load of a {len}-byte file held {extra} bytes beyond the file"
    );
    assert!(
        p.bytes == original,
        "the file was not put back after the parse"
    );
    assert!(
        p.summary().contains("export table implausible"),
        "the summary does not say the table was refused:\n{}",
        p.summary()
    );
    let again = load(original);
    assert_eq!(again.summary(), p.summary(), "a second load differs");
}

/// A sound export table is read as before: one name at its entry.
#[test]
fn a_sound_export_table_is_still_read() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x400];
    export_directory(&mut rdata, 0, RDATA, 1, 1);
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(EXPORT_DIR, RDATA, 0x100)],
    );
    let p = load(bytes);
    assert_eq!(p.headers.implausible_exports, None);
    let exports: Vec<(String, u64)> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Export)
        .map(|s| (s.name.clone(), s.addr))
        .collect();
    assert_eq!(exports, vec![("Exp".to_owned(), IMAGE_BASE + 0x1000)]);
}

/// An export reached by its ordinal alone is listed as `Ordinal_<n>` beside the
/// named one.
///
/// An empty address-table slot is not one: the parser reads exports through the
/// name table, so a `NONAME` export was never listed at all.
#[test]
fn an_export_by_ordinal_alone_is_listed() {
    let _serial = serial();
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x400];
    export_directory(&mut rdata, 0, RDATA, 3, 1);
    put32(&mut rdata, 0x44, 0x1010);
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(EXPORT_DIR, RDATA, 0x100)],
    );
    let p = load(bytes);
    let exports: Vec<(String, u64)> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Export)
        .map(|s| (s.name.clone(), s.addr))
        .collect();
    assert_eq!(
        exports,
        vec![
            ("Exp".to_owned(), IMAGE_BASE + 0x1000),
            ("Ordinal_2".to_owned(), IMAGE_BASE + 0x1010)
        ]
    );
    assert!(p.summary().contains("exports: 2"), "{}", p.summary());
}

/// A DLL linked `/DELAYLOAD` is read out of the delay-load directory.
///
/// Each slot of its address table is an import `module!name` at the slot, by
/// name or by ordinal (`<module>_ord<n>` where no table names the export),
/// so the call through it is named as a call through an import is. The
/// directory was never read, so a delay-loaded API was missing from the
/// imports and its call sites named a thunk.
#[test]
fn delay_loaded_imports_are_imports() {
    let _serial = serial();
    /// The delay-load directory's slot.
    const DELAY_DIR: usize = 13;
    const RDATA: u32 = 0x2000;
    let mut rdata = vec![0u8; 0x400];
    put32(&mut rdata, 0x100, 1);
    put32(&mut rdata, 0x104, RDATA + 0x180);
    put32(&mut rdata, 0x108, RDATA + 0x1f0);
    put32(&mut rdata, 0x10c, RDATA + 0x200);
    put32(&mut rdata, 0x110, RDATA + 0x220);
    rdata[0x180..0x188].copy_from_slice(b"DLY.dll\0");
    put64(&mut rdata, 0x200, IMAGE_BASE + 0x1100);
    put64(&mut rdata, 0x208, IMAGE_BASE + 0x1100);
    put64(&mut rdata, 0x220, u64::from(RDATA + 0x240));
    put64(&mut rdata, 0x228, (1 << 63) | 7);
    rdata[0x242..0x247].copy_from_slice(b"Late\0");
    let mut code = text();
    // ASM: sub rsp, 0x28; call [rip+0x11f6] -> the first slot; add rsp, 0x28; ret
    code[..15].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xff, 0x15, 0xf6, 0x11, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, code, CODE),
            Sec::sound(".rdata", RDATA, rdata, DATA),
        ],
        &[(DELAY_DIR, RDATA + 0x100, 0x40)],
    );
    let p = load(bytes);
    let imports: Vec<(String, u64)> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| (s.name.clone(), s.addr))
        .collect();
    assert_eq!(
        imports,
        vec![
            ("DLY.dll!Late".to_owned(), IMAGE_BASE + 0x2200),
            ("DLY.dll!dly_ord7".to_owned(), IMAGE_BASE + 0x2208)
        ]
    );
    assert!(
        p.summary().contains("imports: 2 (2 delay-loaded)"),
        "{}",
        p.summary()
    );
    assert!(
        borer_engine::hashing::imphash(&p).is_none(),
        "the import hash reads the import table alone, as pefile's does"
    );
    let a = Analysis::compute(&p);
    let o = borer_engine::analysis::Overlay::default();
    let text = borer_engine::analysis::decompile::decompile(&p, &a, &o, IMAGE_BASE + 0x1000)
        .expect("the caller decompiles");
    assert!(text.contains("Late("), "{text}");
}

/// A section whose stated sizes the file cannot hold is left out of the
/// map, and costs nothing: a memory size of two gigabytes is never
/// materialized, since no read goes through a table row that lies.
#[test]
fn a_section_whose_sizes_cannot_be_true_is_not_mapped() {
    let _serial = serial();
    let bytes = pe(
        &[
            Sec {
                vsize: 0x8000_0000,
                raw_size: Some(0xffff_ffff),
                ..Sec::sound(".text", 0x1000, text(), CODE)
            },
            Sec::sound(".rdata", 0x2000, vec![0u8; 0x200], DATA),
        ],
        &[],
    );
    let len = bytes.len();
    let (p, extra) = measured(|| load(bytes));
    let names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(
        names,
        vec![".rdata"],
        "a row the file cannot hold was mapped"
    );
    assert!(
        !p.flat_fallback,
        "the sound section was thrown away with it"
    );
    assert!(
        extra < len.max(1 << 16),
        "the load of a {len}-byte file held {extra} bytes beyond the file"
    );
}

/// A section whose bytes begin past the end of the file has none and is
/// dropped; the rest load as usual.
#[test]
fn a_section_that_begins_past_the_file_is_dropped() {
    let _serial = serial();
    let mut bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", 0x2000, vec![0u8; 0x200], DATA),
        ],
        &[],
    );
    let second_row = PE_AT + 4 + 20 + OPTIONAL + 40;
    put32(&mut bytes, second_row + 20, 0x7fff_0000);
    let p = load(bytes);
    let names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, vec![".text"]);
    assert!(!p.flat_fallback);
}

/// A file cut in the middle of `.text`, as a truncated download is, keeps
/// the code before the cut.
///
/// The table is sound, so the row the end of the file cuts short is a
/// section with fewer bytes than it states, not garbage: `.text` maps with
/// the bytes the file holds and its functions are found, where it was
/// dropped and the file fell back to a flat mapping. The sections whose
/// bytes begin past the cut have none and are dropped.
#[test]
fn a_section_the_file_ends_inside_keeps_the_bytes_it_holds() {
    let _serial = serial();
    let mut code = vec![0xcc; 0x400];
    code[..11].copy_from_slice(&[
        0xe8, 0x0b, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0xc3,
    ]);
    code[0x10..0x16].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code[0x20..0x26].copy_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    let mut bytes = pe(
        &[
            Sec::sound(".text", 0x1000, code, CODE),
            Sec::sound(".rdata", 0x2000, vec![0u8; 0x200], DATA),
            Sec::sound(".data", 0x3000, vec![0u8; 0x200], DATA),
        ],
        &[],
    );
    let cut = HEADERS + 0x200;
    bytes.truncate(cut);
    let p = load(bytes);
    assert!(!p.flat_fallback, "the file fell back to a flat mapping");
    let mapped: Vec<(&str, u64, u64, u64)> = p
        .sections
        .iter()
        .map(|s| (s.name.as_str(), s.va.0, s.vsize, s.file_size))
        .collect();
    assert_eq!(mapped, vec![(".text", IMAGE_BASE + 0x1000, 0x400, 0x200)]);
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    for f in [0x1000, 0x1010, 0x1020] {
        assert!(
            entries.contains(&(IMAGE_BASE + f)),
            "{:#x} was not found: {entries:x?}",
            IMAGE_BASE + f
        );
    }
}

/// A damaged section count still drops the rows it runs into.
///
/// `NumberOfSections = 0xfff` runs the table out of the headers and over
/// `.rdata`, whose bytes here read as rows that start inside the file and
/// run past its end: the shape of a truncated section. Such a table ends
/// past `SizeOfHeaders`, so none of them is kept, where clamping every row
/// that runs past the end let 763 of them through on kernel32 and sent
/// discovery through them for minutes.
#[test]
fn a_damaged_section_count_does_not_clamp_its_garbage_rows() {
    let _serial = serial();
    /// Where the section table begins.
    const TABLE: usize = PE_AT + 4 + 20 + OPTIONAL;
    /// Where `.rdata`'s bytes begin: after the headers and one page of `.text`.
    const RDATA_AT: usize = HEADERS + 0x200;
    /// Rows the damaged count states.
    const ROWS: usize = 0xfff;
    let mut rdata = vec![0u8; (TABLE + ROWS * 40 - RDATA_AT).next_multiple_of(FILE_ALIGN)];
    let first = (RDATA_AT - TABLE).div_ceil(40);
    for k in first..ROWS {
        let row = TABLE + k * 40 - RDATA_AT;
        rdata[row..row + 8].copy_from_slice(b"garbage\0");
        put32(&mut rdata, row + 8, 0x1000);
        put32(&mut rdata, row + 12, 0x1000);
        put32(&mut rdata, row + 16, 0x0100_0000);
        put32(&mut rdata, row + 20, u32::try_from(HEADERS).expect("fits"));
        put32(&mut rdata, row + 36, CODE);
    }
    let mut bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".rdata", 0x2000, rdata, DATA),
        ],
        &[],
    );
    put16(&mut bytes, PE_AT + 6, u16::try_from(ROWS).expect("fits"));
    let p = load(bytes);
    let garbage = p.sections.iter().filter(|s| s.name == "garbage").count();
    assert_eq!(garbage, 0, "{garbage} garbage rows were kept");
    let backed: Vec<&str> = p
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(backed, vec![".text", ".rdata"]);
    assert!(!p.flat_fallback);
}

/// A walk through code no header declares stays linear in its length.
///
/// Without an exception table nothing declares where functions are, so
/// each is walked from its entry to its end, however long. Three questions
/// the walk asks at every call - which call a return address belongs to,
/// the straight line of instructions before the call, the instruction a
/// jump comes from - were answered by scanning every record of the walk so
/// far, and a function of sixteen thousand calls, each after eight argument
/// moves, scanned forty billion records: the discovery of a borer.exe whose
/// headers named no function ran for minutes. The same function is here,
/// and must be walked in the time a linear walk takes.
#[test]
fn a_long_walk_of_calls_stays_linear() {
    let _serial = serial();
    /// `mov r32, imm32` for eight registers.
    const MOVES: [&[u8]; 8] = [
        &[0xb8],
        &[0xb9],
        &[0xba],
        &[0xbb],
        &[0xbe],
        &[0xbf],
        &[0x41, 0xb8],
        &[0x41, 0xb9],
    ];
    /// Calls in the function, each after the eight moves.
    const CALLS: usize = 16_000;
    let mut code = vec![0xcc; 0x10];
    code[0] = 0xc3;
    let entry = code.len();
    for k in 0..CALLS {
        for (slot, mov) in MOVES.iter().enumerate() {
            code.extend_from_slice(mov);
            let imm = u32::try_from(k * 8 + slot).expect("fits");
            code.extend_from_slice(&imm.to_le_bytes());
        }
        let rel = -i32::try_from(code.len() + 5).expect("fits");
        code.push(0xe8);
        code.extend_from_slice(&rel.to_le_bytes());
    }
    code.push(0xc3);
    let mut text = Sec::sound(".text", 0x1000, code, CODE);
    text.rva = 0x1000;
    let mut bytes = pe(&[text], &[]);
    let opt = PE_AT + 4 + 20;
    put32(
        &mut bytes,
        opt + 16,
        0x1000 + u32::try_from(entry).expect("fits"),
    );
    let p = load(bytes);
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time a hostile image takes"
    )]
    let started = std::time::Instant::now();
    let a = Analysis::compute(&p);
    let took = started.elapsed();
    let long = a
        .function(IMAGE_BASE + 0x1000 + from_usize(entry))
        .expect("the entry is a function");
    assert_eq!(long.instr_count, CALLS * 9 + 1);
    assert_eq!(a.functions.len(), 2, "the helper and the function");
    assert!(
        took < std::time::Duration::from_secs(10),
        "a walk of {} instructions took {took:?}",
        long.instr_count
    );
}

/// Bytes appended after a signed PE's certificate table are overlay too.
///
/// The signature does not cover what follows its table, so a signed file
/// can carry an appended payload there and still verify. The overlay names
/// both runs, before the table and after it, and the certificate table
/// between them is neither.
#[test]
fn bytes_after_the_certificate_table_are_overlay() {
    let _serial = serial();
    let mut bytes = pe(&[Sec::sound(".text", 0x1000, text(), CODE)], &[]);
    let cert = bytes.len() + 0x10;
    let pe_dirs = PE_AT + 24 + 112;
    put32(
        &mut bytes,
        pe_dirs + CERTIFICATE_DIR * 8,
        u32::try_from(cert).expect("fits"),
    );
    put32(&mut bytes, pe_dirs + CERTIFICATE_DIR * 8 + 4, 0x18);
    bytes.extend_from_slice(&[0x5a; 0x10]);
    bytes.extend_from_slice(&0x18u32.to_le_bytes());
    bytes.extend_from_slice(&0x0200u16.to_le_bytes());
    bytes.extend_from_slice(&0x0002u16.to_le_bytes());
    bytes.extend_from_slice(&[0x30; 0x10]);
    bytes.extend_from_slice(b"appended after the signature");
    let p = load(bytes);
    let cert = from_usize(cert);
    assert_eq!(p.headers.certificates, Some((cert, 0x18)));
    assert_eq!(
        p.headers.overlay,
        [(cert - 0x10, 0x10), (cert + 0x18, 28)],
        "the overlay before the table and after it"
    );
    let notes = p.headers.render();
    assert!(
        notes.contains(&format!(
            "overlay 28 bytes @ {:#x} after the certificate table",
            cert + 0x18
        )),
        "{notes}"
    );
}

/// Header fields the Windows loader ignores do not refuse the file.
///
/// A damaged Rich header in the DOS stub and a data directory count past
/// sixteen each failed the parse, permissive mode included. The file loads, the
/// summary says what was read past, and the bytes are put back.
#[test]
fn fields_the_loader_ignores_do_not_refuse_the_file() {
    let _serial = serial();
    let mut bytes = pe(&[Sec::sound(".text", 0x1000, text(), CODE)], &[]);
    bytes[0x60..0x64].copy_from_slice(b"Rich");
    put32(&mut bytes, 0x64, 0x1234_5678);
    put32(&mut bytes, PE_AT + 24 + 108, 17);
    let original = bytes.clone();
    let p = load(bytes);
    assert!(
        p.bytes == original,
        "the file was not put back after the parse"
    );
    let summary = p.summary();
    assert!(
        summary.contains("# warning: the Rich header in the DOS stub is damaged; it is not read"),
        "{summary}"
    );
    assert!(
        summary.contains("# warning: the header states 17 data directories; the loader reads 16"),
        "{summary}"
    );
    assert_eq!(p.sections.len(), 1);
}

/// A fat Mach-O header naming four billion slices in a 14-byte file is
/// refused at once.
///
/// The fuzzer's first find: every entry past the end failed to read and
/// was skipped, one at a time, for all 0xfafe0000 of them. The table
/// stops at the first entry the file cannot hold.
#[test]
fn a_fat_header_counting_past_the_file_stops_at_the_end() {
    let bytes = vec![0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xfe, 0, 0, 0, 0, 1, 0, 0, 0];
    let err = Program::from_bytes(PathBuf::from("fat"), bytes).expect_err("no slice fits");
    assert!(err.to_string().contains("names no slice"), "{err}");
}

/// A Mach-O symbol table claiming billions of entries in a 173-byte file
/// reads no more than the file can hold.
///
/// The fuzzer's second find: each entry past the end failed and was
/// skipped, one at a time, for 23 seconds.
#[test]
fn a_symbol_count_past_the_file_stops_at_the_end() {
    let mut bytes = vec![
        0xfe, 0xed, 0xfa, 0xce, 0xc2, 0x00, 0x3e, 0x4d, 0xce, 0x44, 0x00, 0x7e, 0x44, 0x4d, 0x50,
        0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x14, 0xca, 0x5b, 0x4b, 0xed, 0x00, 0x00,
        0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x58, 0x58, 0x58, 0x58, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18,
    ];
    bytes.extend([0x18; 79]);
    bytes.extend([0; 23]);
    bytes.extend([0x20; 6]);
    bytes.extend([0xca, 0xff, 0x8f, 0x00, 0x00]);
    assert_eq!(bytes.len(), 173);
    let p = Program::from_bytes(PathBuf::from("thin"), bytes).expect("a lossy Mach-O loads");
    assert!(p.symbols.is_empty(), "{:?}", p.symbols);
}

/// An ELF section with no file bytes, placed past the end of the file,
/// is kept with nothing to cut.
///
/// The fuzzer's third find: the fit computed the bytes the file holds of
/// it as the file's length minus an offset beyond it, and overflowed.
#[test]
fn an_empty_section_past_the_file_is_not_cut() {
    let bytes = vec![
        0x7f, 0x45, 0x4c, 0x46, 0x02, 0x01, 0x2f, 0x2f, 0xca, 0xfe, 0xba, 0xbe, 0xfe, 0xba, 0x89,
        0x88, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x20,
        0x30, 0x3b, 0x40, 0x0a, 0x00, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x56, 0x5a, 0xff, 0x38, 0x38, 0x38, 0x38, 0x38,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x4f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x2f, 0x2f, 0x00,
    ];
    _ = Program::from_bytes(PathBuf::from("elf"), bytes);
}

/// Heap a load may take beyond the file's own bytes, per byte of file.
const LOAD_HEAP_PER_BYTE: usize = 8;

/// Loading a real binary, this test's own, takes heap bounded by its size.
///
/// The running test binary is a PE, ELF or Mach-O as the host builds it,
/// with tens of megabytes of debug sections, so the bound covers the
/// section table, symbols, DWARF and relocations a real file has.
#[test]
fn loading_a_real_binary_takes_heap_bounded_by_its_size() {
    let _one = serial();
    let path = std::env::current_exe().expect("the test binary has a path");
    let bytes = std::fs::read(&path).expect("the test binary is readable");
    let size = bytes.len();
    let (program, extra) = measured(|| Program::from_bytes_with(path, bytes, false, None));
    assert!(program.is_ok(), "the test binary loads");
    println!("load: {size} byte file, {extra} bytes of heap beyond it");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to load"
    );
}
