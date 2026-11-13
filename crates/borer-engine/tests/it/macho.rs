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
use borer_engine::num::{from_usize, lo32};
use borer_engine::program::{Arch, BinaryFormat, Program, SymbolKind};

/// Where `__TEXT` is mapped.
const TEXT: u64 = 0x1_0000_0000;
/// `main`: `call [rip+got]; xor eax, eax; ret`.
pub(crate) const MAIN: u64 = TEXT + 0x300;
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
        self.u32(off, 0x19);
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
        self.u32(off, 0xc);
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
pub(crate) fn thin() -> Vec<u8> {
    let mut img = Image(vec![0u8; FILE_SIZE]);
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
    img.u32(off, 0x8000_0028);
    img.u32(off + 4, 24);
    img.u64(off + 8, MAIN - TEXT);
    off += 24;
    img.u32(off, 0x2);
    img.u32(off + 4, 24);
    img.u32(off + 8, 0x2000);
    img.u32(off + 12, 3);
    img.u32(off + 16, 0x2100);
    img.u32(off + 20, 0x40);
    off += 24;
    img.u32(off, 0xb);
    img.u32(off + 4, 80);
    img.u32(off + 56, 0x2180);
    img.u32(off + 60, 1);
    off += 80;
    img.u32(off, 0x26);
    img.u32(off + 4, 16);
    img.u32(off + 8, 0x2190);
    img.u32(off + 12, 8);
    off += 16;
    off = img.dylib(off, "/usr/lib/libSystem.B.dylib");
    off = img.dylib(off, "/usr/lib/libc++.1.dylib");
    img.u32(off, 0x2c);
    img.u32(off + 4, 24);
    img.u32(off + 16, 1);
    off += 24;
    img.u32(16, 10);
    img.u32(20, u32::try_from(off - 32).expect("small"));
    let disp = u32::try_from(GOT_PUTS - (MAIN + 6)).expect("near");
    let mut main = vec![0xff, 0x15];
    main.extend_from_slice(&disp.to_le_bytes()); // ASM: call [rip+got]
    main.extend_from_slice(&[0x31, 0xc0, 0xc3]); // ASM: xor eax, eax; ret
    main.resize(0x10, 0xcc);
    main.extend_from_slice(&[0x8d, 0x47, 0x01, 0xc3]); // ASM: lea eax, [rdi+1]; ret
    img.put(0x300, &main);
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
    img.u32(0x2180, 2);
    img.put(0x2190, &[0x80, 0x06, 0x10, 0x00]);
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
        (text.va.0, text.vsize, text.file_off.0),
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
    let nsects = 32 + 152 + 152 + 64;
    bytes[nsects..nsects + 4].copy_from_slice(&2u32.to_le_bytes());
    let p = load(&bytes, "phantom");
    let names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, ["__TEXT,__text", "__DATA_CONST,__got"]);
    assert_eq!(p.headers.dropped_sections, 0);
}

/// A symbol table offset past the end of the file loads the rest of the image
/// leniently.
///
/// The summary says so; the strict parse refused the whole file.
#[test]
fn a_symbol_table_past_the_end_loads_leniently() {
    let mut bytes = thin();
    let at = bytes
        .windows(8)
        .position(|w| w == [0x02, 0, 0, 0, 24, 0, 0, 0])
        .expect("the image has an LC_SYMTAB");
    bytes[at + 8..at + 12].copy_from_slice(&0x1000_0000u32.to_le_bytes());
    let p = load(&bytes, "symoff");
    let names: Vec<&str> = p.sections.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, ["__TEXT,__text", "__DATA_CONST,__got"]);
    let summary = p.summary();
    assert!(
        summary.contains("# warning: the headers do not all parse ("),
        "{summary}"
    );
}

/// A fat file whose slice runs past the end of the file is refused in words
/// that say so.
///
/// It loaded as an image of no architecture, with nothing to say why.
#[test]
fn a_fat_slice_past_the_end_says_so() {
    let mut bytes = fat();
    bytes[20..24].copy_from_slice(&0x0010_0000u32.to_be_bytes());
    let path = std::env::temp_dir().join(format!("borer-macho-cut-{}", std::process::id()));
    std::fs::write(&path, &bytes).expect("temp file");
    let refused = Program::load(&path).expect_err("a cut slice is refused");
    drop(std::fs::remove_file(&path));
    let said = format!("{refused:#}");
    assert!(
        said.contains(
            "the fat file's x86-64 slice at 0x1000 runs to 0x101000, past the end of the file"
        ),
        "{said}"
    );
}

/// Bytes past everything a Mach-O image places are its overlay: past a
/// thin file's segments and symbol tables, and past a fat file's last slice.
///
/// Each image here ends where its `__LINKEDIT` does, or where data a load
/// command places past its one segment does (an object file's string table,
/// the indirect symbols, rebase opcodes, the function starts), and shows no
/// overlay, nor does a second slice after the one analyzed; with bytes
/// appended each names their offset and size once, in the summary's notes
/// and in one `overlay:` line. Mach-O reported none, so a trailer an agent
/// read facts from was never said to be appended.
#[test]
fn bytes_past_the_image_are_a_macho_overlay() {
    use crate::machogen::{self, CODE, RX, Sect, Seg, X86_64};
    let one = thin();
    let second = (0x1000 + one.len()).next_multiple_of(0x1000);
    let mut two = fat();
    two[4..8].copy_from_slice(&2u32.to_be_bytes());
    two[28..32].copy_from_slice(&0x0100_000cu32.to_be_bytes());
    two[36..40].copy_from_slice(&lo32(from_usize(second)).to_be_bytes());
    two[40..44].copy_from_slice(&lo32(from_usize(one.len())).to_be_bytes());
    two[44..48].copy_from_slice(&12u32.to_be_bytes());
    two.resize(second, 0);
    two.extend_from_slice(&one);
    let words = |all: &[u32]| -> Vec<u8> { all.iter().flat_map(|w| w.to_le_bytes()).collect() };
    let past = |command: Vec<u8>, data: usize| {
        let text = Seg {
            name: "__TEXT",
            vmaddr: TEXT,
            fileoff: 0,
            bytes: vec![0xc3; 0x1000],
            prot: RX,
            sections: vec![Sect {
                name: "__text",
                addr: TEXT + 0x400,
                size: 0x10,
                flags: CODE,
            }],
        };
        let mut b = machogen::build(X86_64, 0, &[text], &[command]);
        b.resize(0x1000 + data, 0);
        b
    };
    let mut object = past(words(&[2, 24, 0x1000, 1, 0x1010, 0x10]), 0);
    object.extend_from_slice(&1u32.to_le_bytes());
    object.extend_from_slice(&[0x0f, 1, 0, 0]);
    object.extend_from_slice(&(TEXT + 0x400).to_le_bytes());
    object.extend_from_slice(b"\0_f\0\0\0\0\0\0\0\0\0\0\0\0\0");
    let mut indirect = [0u32; 20];
    indirect[..2].copy_from_slice(&[0xb, 80]);
    indirect[14..16].copy_from_slice(&[0x1000, 2]);
    let cases = [
        ("thin", one),
        ("fat", fat()),
        ("two-slices", two),
        ("object", object),
        ("indirect", past(words(&indirect), 8)),
        (
            "rebase",
            past(machogen::dyld_info((0x1000, 8), (0, 0), (0, 0)), 8),
        ),
        ("starts", past(machogen::linkedit(0x26, 0x1000, 8), 8)),
    ];
    for (name, bytes) in cases {
        let end = bytes.len();
        let clean = load(&bytes, &format!("{name}-clean"));
        assert!(
            clean.headers.overlay.is_empty(),
            "{name}: {:?}",
            clean.headers.overlay
        );
        assert!(!clean.summary().contains("overlay"), "{}", clean.summary());
        let mut appended = bytes;
        appended.extend_from_slice(&[0x41; 0x123]);
        let p = load(&appended, &format!("{name}-appended"));
        assert_eq!(p.headers.overlay, [(from_usize(end), 0x123)], "{name}");
        let summary = p.summary();
        assert!(
            summary.contains(&format!("overlay 291 bytes @ {end:#x}")),
            "{summary}"
        );
        let lines: Vec<&str> = summary
            .lines()
            .filter(|l| l.starts_with("overlay:"))
            .collect();
        assert_eq!(
            lines,
            [format!(
                "overlay: no known signature: data, a payload or padding at {end:#x} (0x123 bytes), entropy 0.00"
            )],
            "{summary}"
        );
    }
}
/// A section's relocation entries are part of a Mach-O image.
///
/// An object file may keep them after its segment data and symbol tables;
/// they end the image there, so only bytes past them are overlay.
#[test]
fn a_section_relocation_table_ends_a_macho_image() {
    use crate::machogen::{self, CODE, RX, Sect, Seg, X86_64};
    let text = Seg {
        name: "__TEXT",
        vmaddr: TEXT,
        fileoff: 0,
        bytes: vec![0xc3; 0x1000],
        prot: RX,
        sections: vec![Sect {
            name: "__text",
            addr: TEXT + 0x400,
            size: 0x10,
            flags: CODE,
        }],
    };
    let mut bytes = machogen::build(X86_64, 0, &[text], &[]);
    let section = 32 + 72;
    bytes[section + 56..section + 60].copy_from_slice(&0x1000u32.to_le_bytes());
    bytes[section + 60..section + 64].copy_from_slice(&2u32.to_le_bytes());
    bytes.resize(0x1010, 0);
    let clean = load(&bytes, "relocations-clean");
    assert!(
        clean.headers.overlay.is_empty(),
        "{:?}",
        clean.headers.overlay
    );
    bytes.extend_from_slice(&[0x41; 0x20]);
    let p = load(&bytes, "relocations-appended");
    assert_eq!(p.headers.overlay, [(0x1010, 0x20)]);
}

/// Pointer sections sharing `reserved1 = 0` walk at most `nindirectsyms`
/// slots in total, and a repeated `nlist` index is named at most 16 times.
#[test]
fn indirect_pointer_sections_cap_walked_slots_and_per_nlist_copies() {
    use crate::machogen::{self, CODE, RW, RX, Sect, Seg, X86_64};
    /// Lazy-pointer sections sharing `reserved1 = 0`.
    const SECTIONS: usize = 16;
    /// Slots per lazy-pointer section, and entries in the indirect table.
    const SLOTS: usize = 256;
    let text = Seg {
        name: "__TEXT",
        vmaddr: TEXT,
        fileoff: 0,
        bytes: vec![0xc3; 0x1000],
        prot: RX,
        sections: vec![Sect {
            name: "__text",
            addr: TEXT + 0x900,
            size: 0x100,
            flags: CODE,
        }],
    };
    let ptr_sects: Vec<Sect> = (0..SECTIONS)
        .map(|k| Sect {
            name: "__la_symbol_ptr",
            addr: TEXT + 0x1000 + from_usize(k * SLOTS * 8),
            size: from_usize(SLOTS * 8),
            flags: 0x7,
        })
        .collect();
    let data = Seg {
        name: "__DATA",
        vmaddr: TEXT + 0x1000,
        fileoff: 0x1000,
        bytes: vec![0u8; SECTIONS * SLOTS * 8],
        prot: RW,
        sections: ptr_sects,
    };
    let symoff = 0x9000u32;
    let stroff = symoff + lo32(from_usize(SLOTS * 16));
    let indoff = stroff + 4;
    let n = lo32(from_usize(SLOTS));
    let words = |all: &[u32]| -> Vec<u8> { all.iter().flat_map(|w| w.to_le_bytes()).collect() };
    let symtab = words(&[0x2, 24, symoff, n, stroff, 4]);
    let mut dysym = [0u32; 20];
    dysym[..2].copy_from_slice(&[0xb, 80]);
    dysym[14..16].copy_from_slice(&[indoff, n]);
    let mut bytes = machogen::build(X86_64, 0, &[text, data], &[symtab, words(&dysym)]);
    for _ in 0..SLOTS {
        bytes.extend_from_slice(&1u32.to_le_bytes());
        bytes.extend_from_slice(&[0x01, 0, 0, 0]);
        bytes.extend_from_slice(&0u64.to_le_bytes());
    }
    bytes.extend_from_slice(b"\0_a\0");
    let ind_at = usize::try_from(indoff).unwrap_or(0);
    for k in 0..n {
        bytes.extend_from_slice(&k.to_le_bytes());
    }
    let distinct = Program::from_bytes(
        std::path::PathBuf::from("indirect-total-cap"),
        bytes.clone(),
    )
    .expect("the image loads");
    let imports: Vec<&str> = distinct
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(imports.len(), SLOTS);
    assert!(imports.iter().all(|&s| s == "a"));
    bytes[ind_at..ind_at + SLOTS * 4].fill(0);
    let shared = Program::from_bytes(std::path::PathBuf::from("indirect-per-nlist-cap"), bytes)
        .expect("the image loads");
    let shared_count = shared
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .count();
    assert_eq!(shared_count, 16);
}
