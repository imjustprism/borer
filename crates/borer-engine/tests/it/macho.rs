//! Mach-O tests on a hand-built x86-64 executable.
//!
//! The sections by segment and name, the symbol table's exports and locals, an import slot named
//! through the indirect symbol table, the linker's function starts as
//! function ranges, the header facts (linked libraries, heap NX, `FairPlay`
//! encryption), a decompile that names the import, and the same image
//! inside a fat container.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay, decompile::decompile};
use borer_engine::program::{Arch, BinaryFormat, Program, SymbolKind};

/// Where `__TEXT` is mapped.
const TEXT: u64 = 0x1_0000_0000;
/// `main`: `call [rip+got]; xor eax, eax; ret`.
const MAIN: u64 = TEXT + 0x300;
/// `helper`: `lea eax, [rdi+1]; ret`.
const HELPER: u64 = TEXT + 0x310;
/// The `__got` slot the loader binds `puts` to.
const GOT_PUTS: u64 = TEXT + 0x1000;
/// Size of the thin file.
const FILE_SIZE: usize = 0x2200;

/// Appends little-endian integers to a byte vector at fixed offsets.
struct Image(Vec<u8>);

impl Image {
    /// Writes bytes at a file offset.
    fn put(&mut self, off: usize, bytes: &[u8]) {
        self.0[off..off + bytes.len()].copy_from_slice(bytes);
    }

    /// Writes a little-endian `u32`.
    fn u32(&mut self, off: usize, v: u32) {
        self.put(off, &v.to_le_bytes());
    }

    /// Writes a little-endian `u64`.
    fn u64(&mut self, off: usize, v: u64) {
        self.put(off, &v.to_le_bytes());
    }

    /// Writes a NUL-padded 16-byte name.
    fn name(&mut self, off: usize, name: &str) {
        let mut raw = [0u8; 16];
        raw[..name.len()].copy_from_slice(name.as_bytes());
        self.put(off, &raw);
    }

    /// Writes an `LC_SEGMENT_64` with one section, returning the offset
    /// after it.
    #[expect(
        clippy::too_many_arguments,
        clippy::expect_used,
        reason = "a segment's fields, in a fixture that fits"
    )]
    fn segment(
        &mut self,
        off: usize,
        seg: &str,
        vmaddr: u64,
        vmsize: u64,
        fileoff: u64,
        filesize: u64,
        prot: u32,
        section: Option<(&str, u64, u64, u32, u32)>,
    ) -> usize {
        let nsects = u32::from(section.is_some());
        self.u32(off, 0x19); // LC_SEGMENT_64
        self.u32(off + 4, 72 + 80 * nsects);
        self.name(off + 8, seg);
        self.u64(off + 24, vmaddr);
        self.u64(off + 32, vmsize);
        self.u64(off + 40, fileoff);
        self.u64(off + 48, filesize);
        self.u32(off + 56, prot);
        self.u32(off + 60, prot);
        self.u32(off + 64, nsects);
        let mut next = off + 72;
        if let Some((name, addr, size, flags, reserved1)) = section {
            self.name(next, name);
            self.name(next + 16, seg);
            self.u64(next + 32, addr);
            self.u64(next + 40, size);
            self.u32(next + 48, u32::try_from(addr - TEXT).expect("in the file"));
            self.u32(next + 64, flags);
            self.u32(next + 68, reserved1);
            next += 80;
        }
        next
    }

    /// Writes an `LC_LOAD_DYLIB` naming `path`, returning the offset after
    /// it. The name sits inline at the command's start plus 24, padded to a
    /// multiple of eight.
    #[expect(
        clippy::expect_used,
        reason = "a fixture that does not fit has no useful recovery"
    )]
    fn dylib(&mut self, off: usize, path: &str) -> usize {
        let size = (24 + path.len() + 1).div_ceil(8) * 8;
        self.u32(off, 0xc); // LC_LOAD_DYLIB
        self.u32(off + 4, u32::try_from(size).expect("small"));
        self.u32(off + 8, 24);
        self.put(off + 24, path.as_bytes());
        self.0[off + 24 + path.len()] = 0;
        off + size
    }
}

/// Builds the thin image: a PIE with a non-executable heap, two linked
/// dylibs and a `FairPlay` encryption command, alongside the sections and
/// tables the loader reads.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not fit has no useful recovery"
)]
fn thin() -> Vec<u8> {
    let mut img = Image(vec![0u8; FILE_SIZE]);
    // Header: MH_MAGIC_64, x86-64, MH_EXECUTE, PIE, no-heap-execution.
    img.u32(0, 0xfeed_facf);
    img.u32(4, 0x0100_0007);
    img.u32(8, 3);
    img.u32(12, 2);
    img.u32(24, 0x0020_0000 | 0x0100_0000);
    let mut off = 32;
    off = img.segment(
        off,
        "__TEXT",
        TEXT,
        0x1000,
        0,
        0x1000,
        5,
        Some(("__text", MAIN, 0x40, 0x8000_0400, 0)),
    );
    off = img.segment(
        off,
        "__DATA_CONST",
        TEXT + 0x1000,
        0x1000,
        0x1000,
        0x1000,
        3,
        Some(("__got", GOT_PUTS, 8, 0x6, 0)),
    );
    off = img.segment(
        off,
        "__LINKEDIT",
        TEXT + 0x2000,
        0x1000,
        0x2000,
        0x200,
        1,
        None,
    );
    // LC_MAIN.
    img.u32(off, 0x8000_0028);
    img.u32(off + 4, 24);
    img.u64(off + 8, MAIN - TEXT);
    off += 24;
    // LC_SYMTAB: three nlist_64 at 0x2000, strings at 0x2100.
    img.u32(off, 0x2);
    img.u32(off + 4, 24);
    img.u32(off + 8, 0x2000);
    img.u32(off + 12, 3);
    img.u32(off + 16, 0x2100);
    img.u32(off + 20, 0x40);
    off += 24;
    // LC_DYSYMTAB: one indirect symbol at 0x2180.
    img.u32(off, 0xb);
    img.u32(off + 4, 80);
    img.u32(off + 56, 0x2180);
    img.u32(off + 60, 1);
    off += 80;
    // LC_FUNCTION_STARTS at 0x2190.
    img.u32(off, 0x26);
    img.u32(off + 4, 16);
    img.u32(off + 8, 0x2190);
    img.u32(off + 12, 8);
    off += 16;
    // Two LC_LOAD_DYLIBs: the linked libraries, in file order. goblin
    // lists the image itself first, so these must both survive.
    off = img.dylib(off, "/usr/lib/libSystem.B.dylib");
    off = img.dylib(off, "/usr/lib/libc++.1.dylib");
    // LC_ENCRYPTION_INFO_64: FairPlay-encrypted, cryptid 1.
    img.u32(off, 0x2c);
    img.u32(off + 4, 24);
    img.u32(off + 16, 1);
    off += 24;
    img.u32(16, 10);
    img.u32(20, u32::try_from(off - 32).expect("small"));
    // Code.
    let disp = u32::try_from(GOT_PUTS - (MAIN + 6)).expect("near");
    let mut main = vec![0xff, 0x15];
    main.extend_from_slice(&disp.to_le_bytes()); // ASM: call [rip+got]
    main.extend_from_slice(&[0x31, 0xc0, 0xc3]); // ASM: xor eax, eax; ret
    main.resize(0x10, 0xcc);
    main.extend_from_slice(&[0x8d, 0x47, 0x01, 0xc3]); // ASM: lea eax, [rdi+1]; ret
    img.put(0x300, &main);
    // Symbols: `_main` external in section 1, `_helper` local, `_puts` undefined.
    let strings = b"\0_main\0_helper\0_puts\0";
    img.put(0x2100, strings);
    for (k, (strx, n_type, sect, value)) in [
        (1u32, 0x0fu8, 1u8, MAIN),
        (7, 0x0e, 1, HELPER),
        (15, 0x01, 0, 0),
    ]
    .into_iter()
    .enumerate()
    {
        let at = 0x2000 + 16 * k;
        img.u32(at, strx);
        img.0[at + 4] = n_type;
        img.0[at + 5] = sect;
        img.u64(at + 8, value);
    }
    img.u32(0x2180, 2); // the got slot binds symbol 2, `_puts`
    img.put(0x2190, &[0x80, 0x06, 0x10, 0x00]); // ULEB128 0x300, 0x10, end
    img.0
}

/// Wraps the thin image in a fat container with one architecture.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not fit has no useful recovery"
)]
fn fat() -> Vec<u8> {
    let thin = thin();
    let mut out = vec![0u8; 0x1000 + thin.len()];
    out[..4].copy_from_slice(&0xcafe_babeu32.to_be_bytes());
    out[4..8].copy_from_slice(&1u32.to_be_bytes());
    out[8..12].copy_from_slice(&0x0100_0007u32.to_be_bytes());
    out[12..16].copy_from_slice(&3u32.to_be_bytes());
    out[16..20].copy_from_slice(&0x1000u32.to_be_bytes());
    out[20..24].copy_from_slice(&u32::try_from(thin.len()).expect("small").to_be_bytes());
    out[24..28].copy_from_slice(&12u32.to_be_bytes());
    out[0x1000..].copy_from_slice(&thin);
    out
}

/// Loads an image from bytes through a temporary file.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not load has no useful recovery"
)]
fn load(bytes: &[u8], name: &str) -> Program {
    let path = std::env::temp_dir().join(format!("borer-macho-{name}-{}", std::process::id()));
    std::fs::write(&path, bytes).expect("temp file");
    let p = Program::load(&path).expect("loads");
    let _ = std::fs::remove_file(&path);
    p
}

/// Checks everything the loader reads out of the image.
#[expect(
    clippy::panic,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]
fn check(p: &Program, shift: u64) {
    assert_eq!(p.format, BinaryFormat::MachO);
    assert_eq!(p.arch, Arch::X86_64);
    assert!(p.is_64);
    assert_eq!(p.entry, Some(MAIN));
    assert_eq!(p.image_base, TEXT);
    let text = p
        .sections
        .iter()
        .find(|s| s.name == "__TEXT,__text")
        .expect("the text section");
    assert!(text.executable && text.readable && !text.writable);
    assert_eq!(
        (text.va, text.vsize, text.file_off),
        (MAIN, 0x40, 0x300 + shift)
    );
    let got = p
        .sections
        .iter()
        .find(|s| s.name == "__DATA_CONST,__got")
        .expect("the got");
    assert!(!got.executable && got.writable);
    let sym = |name: &str| {
        p.symbols
            .iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("{name} not among {:?}", p.symbols))
    };
    assert_eq!(
        (sym("main").addr, sym("main").kind),
        (MAIN, SymbolKind::Export)
    );
    assert_eq!(
        (sym("helper").addr, sym("helper").kind),
        (HELPER, SymbolKind::Local)
    );
    assert_eq!(
        (sym("puts").addr, sym("puts").kind),
        (GOT_PUTS, SymbolKind::Import)
    );
    assert_eq!(
        p.function_ranges,
        vec![(MAIN, HELPER), (HELPER, MAIN + 0x40)]
    );
    assert_eq!(p.headers.kind, Some("executable"));
    assert!(p.headers.mitigations.contains(&"pie"));
    assert!(p.headers.mitigations.contains(&"nx"));
    assert_eq!(p.headers.fairplay, Some(true));
    assert_eq!(
        p.headers.libraries,
        vec![
            "/usr/lib/libSystem.B.dylib".to_owned(),
            "/usr/lib/libc++.1.dylib".to_owned()
        ]
    );
    assert_eq!(p.headers.unwind_functions, 2);
    let a = Analysis::compute(p);
    assert!(a.function(MAIN).is_some() && a.function(HELPER).is_some());
    let text = decompile(p, &a, &Overlay::default(), MAIN).expect("decompiles");
    assert!(text.contains("puts("), "{text}");
    let summary = p.summary();
    assert!(summary.contains("fairplay-encrypted"), "{summary}");
    assert!(
        summary.contains("libraries (2): /usr/lib/libSystem.B.dylib, /usr/lib/libc++.1.dylib"),
        "{summary}"
    );
}

/// A thin image reads whole.
#[test]
fn a_thin_image_reads_whole() {
    check(&load(&thin(), "thin"), 0);
}

/// The x86-64 slice of a fat file reads the same, its file offsets
/// shifted by the slice's.
#[test]
fn a_fat_file_reads_its_x86_64_slice() {
    check(&load(&fat(), "fat"), 0x1000);
}

/// A segment whose `nsects` claims more sections than its load command holds
/// reads only the ones it holds.
///
/// The count past them read the next load commands as sections, phantoms that
/// became fake code.
#[test]
fn a_section_count_past_the_command_reads_no_phantoms() {
    let mut bytes = thin();
    // SPEC: `__LINKEDIT` is the third segment command, after two 152-byte
    // ones from offset 32; its `nsects` sits 64 bytes in, and its
    // `cmdsize` of 72 holds no section header.
    let nsects = 32 + 152 + 152 + 64;
    bytes[nsects..nsects + 4].copy_from_slice(&2u32.to_le_bytes());
    let p = load(&bytes, "phantom");
    let names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, ["__TEXT,__text", "__DATA_CONST,__got"]);
    assert_eq!(p.headers.dropped_sections, 0);
}
