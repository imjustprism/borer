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
    put32(&mut b, opt + 16, entry_rva);
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
    let mut row = opt + OPTIONAL;
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
