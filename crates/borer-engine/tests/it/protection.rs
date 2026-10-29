//! Packer identification from hand-built PEs: entry stubs, section names and
//! DOS-header markers name the family, and the report says which mark fired.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, render::protection_tsv};
use borer_engine::program::Program;
use std::path::PathBuf;

/// Where the headers end and the first section's bytes begin.
const HEADERS: usize = 0x400;
/// The file alignment every section's bytes keep.
const FILE_ALIGN: usize = 0x200;
/// The preferred load address.
pub(crate) const IMAGE_BASE: u64 = 0x1_4000_0000;
/// Where the PE signature sits.
pub(crate) const PE_AT: usize = 0x80;
/// Bytes of the PE32+ optional header.
const OPTIONAL: usize = 240;
/// Bytes of the PE32 optional header.
const OPTIONAL32: usize = 224;
/// The preferred load address of a PE32 image.
const IMAGE_BASE32: u64 = 0x40_0000;
/// `IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ`.
const CODE: u32 = 0x6000_0020;
/// `IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE`.
const DATA: u32 = 0xC000_0040;
/// Everything a packed stub wants: code that is also writable.
const WX: u32 = 0xE000_0040;

/// One section of a built image.
pub(crate) struct Sec {
    /// Its name, at most eight bytes.
    name: &'static str,
    /// Where it maps, relative to [`IMAGE_BASE`].
    rva: u32,
    /// Its bytes in the file.
    data: Vec<u8>,
    /// Its memory size as the table states it.
    vsize: u32,
    /// `IMAGE_SCN_*` flags.
    chars: u32,
}

/// A section whose table row tells the truth about its bytes, read-only code.
pub(crate) fn sec(name: &'static str, rva: u32, data: Vec<u8>) -> Sec {
    let vsize = u32::try_from(data.len()).expect("a test section fits a u32");
    Sec {
        name,
        rva,
        data,
        vsize,
        chars: CODE,
    }
}

/// A section of data, writable and not executable, whose table row tells
/// the truth about its bytes.
pub(crate) fn data(name: &'static str, rva: u32, data: Vec<u8>) -> Sec {
    Sec {
        chars: DATA,
        ..sec(name, rva, data)
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
/// sections' bytes at file-aligned offsets, entered at `entry_rva`.
///
/// # Arguments
///
/// * `secs` - The sections, in table order.
/// * `entry_rva` - The entry point, relative to [`IMAGE_BASE`].
pub(crate) fn pe(secs: &[Sec], entry_rva: u32) -> Vec<u8> {
    image(secs, entry_rva, true)
}

/// Builds an x86 PE32 image as [`pe`] builds a PE32+ one, loaded at
/// [`IMAGE_BASE32`].
///
/// # Arguments
///
/// * `secs` - The sections, in table order.
/// * `entry_rva` - The entry point, relative to [`IMAGE_BASE32`].
fn pe32(secs: &[Sec], entry_rva: u32) -> Vec<u8> {
    image(secs, entry_rva, false)
}

/// Builds a PE32+ x64 image when `wide`, else a PE32 x86 one.
///
/// # Arguments
///
/// * `secs` - The sections, in table order.
/// * `entry_rva` - The entry point, relative to the image base.
/// * `wide` - PE32+ for x64, else PE32 for x86.
fn image(secs: &[Sec], entry_rva: u32, wide: bool) -> Vec<u8> {
    let optional = if wide { OPTIONAL } else { OPTIONAL32 };
    let mut b = vec![0u8; HEADERS];
    b[..2].copy_from_slice(b"MZ");
    put32(&mut b, 0x3c, u32::try_from(PE_AT).expect("fits"));
    b[PE_AT..PE_AT + 4].copy_from_slice(b"PE\0\0");
    let coff = PE_AT + 4;
    put16(&mut b, coff, if wide { 0x8664 } else { 0x14c });
    put16(
        &mut b,
        coff + 2,
        u16::try_from(secs.len()).expect("few sections"),
    );
    put16(&mut b, coff + 16, u16::try_from(optional).expect("fits"));
    put16(&mut b, coff + 18, if wide { 0x0022 } else { 0x0102 });
    let opt = coff + 20;
    put16(&mut b, opt, if wide { 0x20b } else { 0x10b });
    put32(&mut b, opt + 16, entry_rva);
    if wide {
        put64(&mut b, opt + 24, IMAGE_BASE);
    } else {
        put32(&mut b, opt + 28, u32::try_from(IMAGE_BASE32).expect("fits"));
    }
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
    if wide {
        put64(&mut b, opt + 72, 0x10_0000);
        put64(&mut b, opt + 80, 0x1000);
        put64(&mut b, opt + 88, 0x10_0000);
        put64(&mut b, opt + 96, 0x1000);
        put32(&mut b, opt + 108, 16);
    } else {
        put32(&mut b, opt + 72, 0x10_0000);
        put32(&mut b, opt + 76, 0x1000);
        put32(&mut b, opt + 80, 0x10_0000);
        put32(&mut b, opt + 84, 0x1000);
        put32(&mut b, opt + 92, 16);
    }
    let mut row = opt + optional;
    let mut at = HEADERS;
    for s in secs {
        let raw = u32::try_from(s.data.len().div_ceil(FILE_ALIGN) * FILE_ALIGN).expect("fits");
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

/// Loads `bytes` and renders its protection report.
fn report(bytes: Vec<u8>) -> String {
    let p = Program::from_bytes(PathBuf::from("packed.exe"), bytes)
        .expect("a PE with a section table loads");
    let a = Analysis::compute(&p);
    protection_tsv(&p, &a)
}

/// The UPX stub's first bytes: `pushad; mov esi, imm32; lea edi, [esi+disp32];
/// push edi; or ecx, -1`, wildcards as they vary per packed file.
const UPX_STUB: [u8; 17] = [
    0x60, 0xbe, 0x78, 0x56, 0x34, 0x12, 0x8d, 0xbe, 0x00, 0x00, 0xff, 0xff, 0x57, 0x83, 0xcd, 0xff,
    0xeb,
];

/// A UPX layout, sections and entry stub both, names UPX with both as
/// evidence.
#[test]
fn upx_sections_and_entry_stub_name_upx() {
    let mut stub = vec![0xcc; 0x200];
    stub[..UPX_STUB.len()].copy_from_slice(&UPX_STUB);
    let vsize = u32::try_from(stub.len()).expect("fits");
    let bytes = pe(
        &[
            Sec {
                name: "UPX0",
                rva: 0x1000,
                data: vec![0; 0x10],
                vsize: 0x2000,
                chars: DATA,
            },
            Sec {
                name: "UPX1",
                rva: 0x3000,
                data: stub,
                vsize,
                chars: WX,
            },
        ],
        0x3000,
    );
    let out = report(bytes);
    assert!(out.contains("# protected: UPX"), "{out}");
    assert!(
        out.contains("UPX0 section; UPX1 section; entry stub at 0x140003000"),
        "{out}"
    );
    assert!(out.contains("pushad; mov esi"), "{out}");
}

/// A protector that only its section names give away: `VMProtect` with plain
/// code at the entry, no stub, is named from `.vmp0` and `.vmp1` alone.
#[test]
fn vmp_sections_alone_name_vmprotect() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(
        &[
            Sec {
                name: ".vmp0",
                rva: 0x1000,
                data: vec![0x41; 0x200],
                vsize: 0x200,
                chars: DATA,
            },
            sec(".vmp1", 0x3000, code),
        ],
        0x3000,
    );
    let out = report(bytes);
    assert!(out.contains("# protected: VMProtect"), "{out}");
    assert!(out.contains(".vmp0 section; .vmp1 section"), "{out}");
    assert!(!out.contains("entry stub"), "{out}");
}

/// An entry stub with nothing else: `ASPack`'s stub in ordinary section names
/// still names `ASPack`, which section names alone could not.
#[test]
fn aspack_entry_stub_names_aspack_without_telling_sections() {
    let mut code = vec![0xcc; 0x200];
    code[..13].copy_from_slice(&[
        0x60, 0xe8, 0x03, 0x00, 0x00, 0x00, 0xe9, 0xeb, 0x04, 0x5d, 0x45, 0x55, 0xc3,
    ]);
    let bytes = pe(
        &[
            sec(".text", 0x1000, code),
            Sec {
                name: ".data",
                rva: 0x3000,
                data: vec![0; 0x10],
                vsize: 0x10,
                chars: DATA,
            },
        ],
        0x1000,
    );
    let out = report(bytes);
    assert!(out.contains("# protected: ASPack"), "{out}");
    assert!(out.contains("entry stub at 0x140001000"), "{out}");
}

/// A tELock marker rebuilt into the DOS header names tELock.
#[test]
fn telock_marker_in_the_dos_header_names_telock() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut bytes = pe(&[sec(".text", 0x1000, code)], 0x1000);
    bytes[0x40..0x46].copy_from_slice(b"tELock");
    let out = report(bytes);
    assert!(out.contains("# protected: tELock"), "{out}");
    assert!(out.contains("tELock marker in the DOS header"), "{out}");
}

/// The `UPX!` mark UPX writes into the headers names UPX and the version
/// written before it, whatever the sections are called.
#[test]
fn a_upx_mark_in_the_headers_names_upx_and_its_version() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut bytes = pe(&[sec(".text", 0x1000, code)], 0x1000);
    bytes[0x3d0..0x3d9].copy_from_slice(b"4.22\0UPX!");
    let out = report(bytes);
    assert!(out.contains("# protected: UPX"), "{out}");
    assert!(
        out.contains("UPX! mark at 0x3d5 in the headers, written by UPX 4.22"),
        "{out}"
    );
}

/// An x86 `SteamStub` before 3.x is named by its stub, entered in `.bind`.
#[test]
fn an_early_steamstub_is_named_by_its_stub_in_bind() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut stub = vec![0xcc; 0x200];
    stub[..25].copy_from_slice(&[
        0x60, 0x81, 0xec, 0x00, 0x10, 0x00, 0x00, 0xbe, 0x0c, 0xd6, 0xc6, 0x00, 0xb9, 0x6b, 0x00,
        0x00, 0x00, 0x8d, 0xbd, 0x10, 0xfc, 0xff, 0xff, 0xf3, 0xa5,
    ]);
    let out = report(pe(
        &[sec(".text", 0x1000, code), sec(".bind", 0x2000, stub)],
        0x2000,
    ));
    assert!(out.contains("# protected: SteamStub"), "{out}");
    assert!(
        out.contains("an x86 SteamStub before 3.x); entry point in .bind"),
        "{out}"
    );
}

/// An x64 `SteamStub` 3.1 header before the entry point decodes to the app
/// id, the original entry point and whether the code is encrypted.
#[test]
fn a_steamstub_31_header_is_decoded() {
    let mut fields = [0u32; 60];
    fields[1] = 0xc0de_c0df;
    fields[0x20 / 4] = 0x1264;
    fields[0x38 / 4] = 4_001_890;
    for (flags, says) in [
        (0, "the code section is encrypted"),
        (4, "the code section is not encrypted"),
    ] {
        fields[0x3c / 4] = flags;
        let mut encoded = vec![0xb499_437d_u32];
        for f in &fields[1..] {
            let last = *encoded.last().expect("the key");
            encoded.push(f ^ last);
        }
        let mut bind: Vec<u8> = encoded.iter().flat_map(|w| w.to_le_bytes()).collect();
        bind.extend_from_slice(&[0xe8, 0, 0, 0, 0, 0x50, 0x53, 0x51, 0x52, 0x56, 0x57, 0x55]);
        bind.extend_from_slice(&[0x41, 0x50, 0x41, 0x51]);
        bind.resize(0x200, 0xcc);
        let out = report(pe(
            &[
                sec(".text", 0x1000, vec![0xc3; 0x200]),
                sec(".bind", 0x2000, bind),
            ],
            0x20f0,
        ));
        assert!(
            out.contains(&format!("SteamStub 3.1 header at 0x140002000, decoded: Steam app id 4001890, original entry point 0x140001264, {says}")),
            "{out}"
        );
    }
}

/// `MPRESS` names its sections with a leading dot, and they name it.
#[test]
fn dotted_mpress_sections_name_mpress() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let out = report(pe(
        &[
            sec(".MPRESS1", 0x1000, code),
            sec(".MPRESS2", 0x2000, vec![0; 0x200]),
        ],
        0x1000,
    ));
    assert!(
        out.contains("# - MPRESS: .MPRESS1 section; .MPRESS2 section"),
        "{out}"
    );
}

/// An entry whose first byte is off by one matches no stub and stays plain,
/// so one wrong byte cannot name a packer.
#[test]
fn a_changed_first_stub_byte_matches_nothing() {
    let mut stub = vec![0xcc; 0x200];
    let mut sig = UPX_STUB;
    sig[0] = 0x61;
    stub[..sig.len()].copy_from_slice(&sig);
    let bytes = pe(&[sec(".text", 0x1000, stub)], 0x1000);
    let out = report(bytes);
    assert!(out.contains("# plain:"), "{out}");
}

/// Fills `n` bytes with a xorshift stream, which reads at near-maximal
/// entropy, standing in for a compressed or encrypted section.
///
/// # Arguments
///
/// * `n` - How many bytes.
/// * `seed` - The stream's seed, so two sections differ.
fn high_entropy(n: usize, seed: u64) -> Vec<u8> {
    let mut x = seed | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            u8::try_from(x >> 56).expect("a byte")
        })
        .collect()
}

/// Triage states its blind spots: a packed verdict says the report
/// describes the stub, a high-entropy section is called out, and a TLS
/// callback is named as running before the entry.
///
/// # Panics
///
/// When a caveat the fixture should raise is missing.
#[test]
fn triage_states_its_blind_spots() {
    use borer_engine::analysis::Overlay;
    use borer_engine::analysis::render::triage_tsv;

    let mut stub = vec![0xcc; 0x40];
    stub[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(
        &[
            sec(".text", 0x1000, stub),
            Sec {
                name: ".data",
                rva: 0x2000,
                data: high_entropy(0x800, 0x1234),
                vsize: 0x800,
                chars: WX,
            },
        ],
        0x1000,
    );
    let mut p = Program::from_bytes(PathBuf::from("packed.exe"), bytes).expect("a PE loads");
    p.headers.tls_callbacks.push(0x1_4000_1000);
    let a = Analysis::compute(&p);
    let out = triage_tsv(&p, &a, &Overlay::default());
    assert!(
        out.contains("# blind spot: packed") || out.contains("# blind spot: protected"),
        "{out}"
    );
    assert!(out.contains("describe the stub, not the payload"), "{out}");
    assert!(
        out.contains("compressed or encrypted bytes") && out.contains(".data"),
        "{out}"
    );
    assert!(
        out.contains("imports resolved there stay unseen") || out.contains("import"),
        "{out}"
    );
    assert!(out.contains("TLS callback"), "{out}");
    assert!(out.contains("run before the entry point"), "{out}");
}

/// A plain, low-entropy image raises no entropy or packed blind spot, so
/// the caveat fires only where it should.
///
/// # Panics
///
/// When a plain image is called packed or its sections encrypted.
#[test]
fn a_plain_image_raises_no_entropy_blind_spot() {
    use borer_engine::analysis::Overlay;
    use borer_engine::analysis::render::triage_tsv;

    let mut code = vec![0x90u8; 0x400];
    code[0x3ff] = 0xc3;
    let bytes = pe(&[sec(".text", 0x1000, code)], 0x1000);
    let p = Program::from_bytes(PathBuf::from("plain.exe"), bytes).expect("a PE loads");
    let a = Analysis::compute(&p);
    let out = triage_tsv(&p, &a, &Overlay::default());
    assert!(!out.contains("compressed or encrypted bytes"), "{out}");
    assert!(!out.contains("# blind spot: packed"), "{out}");
    assert!(!out.contains("TLS callback"), "{out}");
}

/// Builds a PE whose first section holds no file bytes and states file
/// offset 0, the shape FSG writes, as an x86 PE32 entered at `entry_rva`.
///
/// # Arguments
///
/// * `stub` - Bytes written at the entry: into the headers when
///   `entry_rva` is below `0x400`, else at the start of the second section.
/// * `entry_rva` - The entry point, relative to [`IMAGE_BASE32`].
fn fsg_shape(stub: &[u8], entry_rva: u32) -> Vec<u8> {
    let mut body = high_entropy(0x800, 0x77);
    if entry_rva >= 0x8000 {
        body[..stub.len()].copy_from_slice(stub);
    }
    let mut bytes = pe32(
        &[
            Sec {
                name: "",
                rva: 0x1000,
                data: Vec::new(),
                vsize: 0x7000,
                chars: WX,
            },
            Sec {
                name: "",
                rva: 0x8000,
                data: body,
                vsize: 0x1000,
                chars: WX,
            },
        ],
        entry_rva,
    );
    let first_row = PE_AT + 24 + OPTIONAL32;
    bytes[first_row + 20..first_row + 24].fill(0);
    if entry_rva < 0x400 {
        let at = usize::try_from(entry_rva).expect("fits");
        bytes[at..at + stub.len()].copy_from_slice(stub);
    }
    bytes
}

/// FSG 2.0 enters its aPLib loop inside the headers, behind an empty first
/// section whose row says file offset 0; the stub still reads and names
/// FSG.
#[test]
fn fsg_20_entered_in_the_headers_names_fsg() {
    let stub = [
        0x87, 0x25, 0x50, 0xf2, 0x44, 0x00, 0x61, 0x94, 0x55, 0xa4, 0xb6, 0x80, 0xff, 0x13, 0x73,
        0xf9, 0x33, 0xc9, 0xff, 0x13, 0x73, 0x16, 0x33, 0xc0,
    ];
    let out = report(fsg_shape(&stub, 0x300));
    assert!(out.contains("# protected: FSG"), "{out}");
    assert!(out.contains("entry stub at 0x400300"), "{out}");
    assert!(out.contains("FSG 2.0's aPLib loop"), "{out}");
}

/// FSG 1.3x loads its table pointer, then runs the same aPLib loop from a
/// section, and names FSG.
#[test]
fn fsg_13_stub_in_a_section_names_fsg() {
    let stub = [
        0xbe, 0xa4, 0x01, 0x40, 0x00, 0xad, 0x93, 0xad, 0x97, 0xad, 0x56, 0x96, 0xb2, 0x80, 0xa4,
        0xb6, 0x80, 0xff, 0x13, 0x73, 0xf9,
    ];
    let out = report(fsg_shape(&stub, 0x8000));
    assert!(out.contains("# protected: FSG"), "{out}");
    assert!(out.contains("FSG 1.3x"), "{out}");
}

/// MPRESS's x86 stub names MPRESS with ordinary section names.
#[test]
fn mpress_entry_stub_names_mpress() {
    let mut code = vec![0xcc; 0x200];
    code[..25].copy_from_slice(&[
        0x60, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x58, 0x05, 0x5a, 0x0b, 0x00, 0x00, 0x8b, 0x30, 0x03,
        0xf0, 0x2b, 0xc0, 0x8b, 0xfe, 0x66, 0xad, 0xc1, 0xe0, 0x0c,
    ]);
    let out = report(pe32(&[sec(".text", 0x1000, code)], 0x1000));
    assert!(out.contains("# protected: MPRESS"), "{out}");
    assert!(out.contains("an x86 MPRESS 2.x stub"), "{out}");
}

/// Loads `bytes`, lets `edit` set what the builder cannot write, and
/// renders the protection report.
fn report_with(bytes: Vec<u8>, edit: impl FnOnce(&mut Program)) -> String {
    let mut p = Program::from_bytes(PathBuf::from("plain.exe"), bytes).expect("a PE loads");
    edit(&mut p);
    let a = Analysis::compute(&p);
    protection_tsv(&p, &a)
}

/// Import symbols by name.
fn imports(names: &[&str]) -> Vec<borer_engine::program::Symbol> {
    names
        .iter()
        .map(|n| borer_engine::program::Symbol {
            name: (*n).to_owned(),
            addr: 0,
            kind: borer_engine::program::SymbolKind::Import,
        })
        .collect()
}

/// An MSVC debug build: an empty writable and executable `.textbss` comes
/// first, the entry is in `.text`, a TLS callback runs and few functions
/// are imported. None of that is packing, so it stays plain.
#[test]
fn an_msvc_debug_layout_with_tls_is_plain() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(
        &[
            Sec {
                name: ".textbss",
                rva: 0x1000,
                data: Vec::new(),
                vsize: 0x10000,
                chars: WX,
            },
            sec(".text", 0x11000, code),
            data(".data", 0x12000, vec![0; 0x200]),
        ],
        0x11000,
    );
    let out = report_with(bytes, |p| p.headers.tls_callbacks.push(0x1_4001_1000));
    assert!(
        out.starts_with("# plain: no mark only packing leaves"),
        "{out}"
    );
    assert!(!out.contains("writable and executable"), "{out}");
    assert!(!out.contains("not the first code section"), "{out}");
    assert!(out.contains("TLS callback"), "{out}");
}

/// A packer that strips the code to an empty read-only `.text` and enters a
/// later high-entropy section still shows both marks: the empty section is
/// not bss, so it stays the first code section.
#[test]
fn an_empty_read_only_text_before_the_entry_is_still_first() {
    let mut body = high_entropy(0x800, 0x99);
    body[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(
        &[
            Sec {
                name: ".text",
                rva: 0x1000,
                data: Vec::new(),
                vsize: 0x2000,
                chars: CODE,
            },
            sec(".lxz", 0x3000, body),
        ],
        0x3000,
    );
    let out = report_with(bytes, |p| p.symbols = imports(&TWELVE_IMPORTS));
    assert!(out.starts_with("# packed"), "{out}");
    assert!(
        out.contains("entry point in .lxz, not the first code section"),
        "{out}"
    );
}

/// A .NET image imports `_CorExeMain` alone by design, which is no thin
/// import table.
#[test]
fn a_clr_image_with_one_import_is_not_thin() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xff, 0x25, 0x00, 0x20, 0x40, 0x00]);
    let bytes = pe(&[sec(".text", 0x1000, code)], 0x1000);
    let out = report_with(bytes, |p| {
        p.headers.directories.push("clr");
        p.symbols = imports(&["mscoree.dll!_CorExeMain"]);
    });
    assert!(out.starts_with("# plain: no packer marks"), "{out}");
}

/// A hand-assembled program whose one code section is writable, entered
/// there, is one fact: writable code holding the entry. It is not called
/// packed on that alone.
#[test]
fn an_entry_in_writable_code_is_one_mark() {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(
        &[Sec {
            chars: WX,
            ..sec(".text", 0x1000, code)
        }],
        0x1000,
    );
    let out = report_with(bytes, |p| p.symbols = imports(&TWELVE_IMPORTS));
    assert!(out.starts_with("# plain: one mark only"), "{out}");
    assert!(out.contains("writable and executable: .text"), "{out}");
    assert!(!out.contains("writable memory"), "{out}");
}

/// A Visual Basic program's `.text` holds P-code and forms the runtime
/// reads, so few functions in it, even at high entropy, say nothing of
/// packing.
#[test]
fn a_visual_basic_image_is_not_sparse_code() {
    let mut code = high_entropy(0x12000, 0x5b);
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let bytes = pe(&[sec(".text", 0x1000, code)], 0x1000);
    let vb = report_with(bytes.clone(), |p| {
        p.headers.libraries.push("MSVBVM60.DLL".to_owned());
        p.symbols = imports(&TWELVE_IMPORTS);
    });
    assert!(vb.starts_with("# plain: one mark only"), "{vb}");
    assert!(!vb.contains("functions in"), "{vb}");
    let native = report_with(bytes, |p| p.symbols = imports(&TWELVE_IMPORTS));
    assert!(native.starts_with("# packed"), "{native}");
    assert!(native.contains("functions in"), "{native}");
}

/// Enough imports that the table is not thin.
const TWELVE_IMPORTS: [&str; 12] = [
    "a!a", "a!b", "a!c", "a!d", "a!e", "a!f", "a!g", "a!h", "a!i", "a!j", "a!k", "a!l",
];

/// A dynamically linked GCC ELF enters `.text` after `.init` and `.plt`
/// and imports a few libc functions: neither is a mark.
#[test]
fn a_gcc_elf_entered_after_init_and_plt_is_plain() {
    use borer_engine::program::{Arch, BinaryFormat, Section};
    let mut bytes = vec![0u8; 0x1000];
    bytes.extend(std::iter::repeat_n(0xc3, 0x300));
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x40_0000,
        Some(0x40_1100),
        vec![
            Section::mapped(".init", 0x40_1000, 0x1000, 0x20, false, true),
            Section::mapped(".plt", 0x40_1020, 0x1020, 0x40, false, true),
            Section::mapped(".text", 0x40_1100, 0x1100, 0x200, false, true),
        ],
    );
    p.format = BinaryFormat::Elf;
    p.symbols = imports(&["puts", "strcmp", "__libc_start_main"]);
    let a = Analysis::compute(&p);
    let out = protection_tsv(&p, &a);
    assert!(out.starts_with("# plain: no packer marks"), "{out}");
}
