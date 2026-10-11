//! Content hashes of a crafted PE: imphash against a hand-computed import
//! table, authentihash against a file with a checksum, a security directory
//! and a certificate table, both pinned to values an independent
//! implementation computed over the same bytes.
//!
//! The builder follows the hostile.rs pattern: every field the two hashes
//! read is placed where a real PE puts it, so the loader and the hash walk
//! the same image a tool would.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::hashing::{authentihash, hashes_tsv, imphash};
use borer_engine::program::{Program, SymbolKind};

/// Where the headers end and the first section's bytes begin.
const HEADERS: usize = 0x400;
/// The file alignment every section's bytes keep.
const FILE_ALIGN: usize = 0x200;
/// Where the PE signature sits.
const PE_AT: usize = 0x80;
/// Bytes of the PE32+ optional header.
const OPTIONAL: usize = 240;
/// The `.rdata` section's RVA.
const RDATA: u32 = 0x2000;
/// The import directory's slot.
const IMPORT_DIR: usize = 1;
/// The certificate directory's slot; its address is a file offset.
const CERTIFICATE_DIR: usize = 4;
/// Where the certificate table starts in the file.
const CERT_AT: usize = 0xa00;
/// Bytes of certificate-table junk after the sections.
const CERT_LEN: usize = 0x180;
/// Where the optional header begins in the file.
const OPT: usize = PE_AT + 4 + 20;

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

/// Writes one import descriptor at `at`.
fn descriptor(b: &mut [u8], at: usize, lookup: u32, name: u32, iat: u32) {
    put32(b, at, lookup);
    put32(b, at + 12, name);
    put32(b, at + 16, iat);
}

/// The `.rdata` bytes: descriptors for `KERNEL32.dll` (`CreateFileW`,
/// `ReadFile`) and `USER32.DLL` (`MessageBoxA`), their lookup and IAT
/// tables, and the hint/name entries.
fn rdata() -> Vec<u8> {
    let mut r = vec![0u8; 0x400];
    descriptor(&mut r, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x200);
    descriptor(&mut r, 20, RDATA + 0x120, RDATA + 0xb0, RDATA + 0x220);
    r[0xa0..0xad].copy_from_slice(b"KERNEL32.dll\0");
    r[0xb0..0xbb].copy_from_slice(b"USER32.DLL\0");
    put64(&mut r, 0x100, u64::from(RDATA + 0x300));
    put64(&mut r, 0x108, u64::from(RDATA + 0x310));
    put64(&mut r, 0x120, u64::from(RDATA + 0x320));
    put64(&mut r, 0x200, u64::from(RDATA + 0x300));
    put64(&mut r, 0x208, u64::from(RDATA + 0x310));
    put64(&mut r, 0x220, u64::from(RDATA + 0x320));
    r[0x300..0x30e].copy_from_slice(b"\0\0CreateFileW\0");
    r[0x310..0x31b].copy_from_slice(b"\0\0ReadFile\0");
    r[0x320..0x32e].copy_from_slice(b"\0\0MessageBoxA\0");
    r
}

/// Builds the PE32+ image both hashes read.
///
/// Headers with a junk checksum, an import directory for the `.rdata`
/// below, a security directory naming a certificate table appended after
/// the sections, a `.text` of `int3` padding entered by `mov eax, 1; ret`,
/// and the `.rdata` itself.
fn image() -> Vec<u8> {
    let mut b = vec![0u8; HEADERS];
    b[..2].copy_from_slice(b"MZ");
    put32(&mut b, 0x3c, u32::try_from(PE_AT).expect("fits"));
    b[PE_AT..PE_AT + 4].copy_from_slice(b"PE\0\0");
    let coff = PE_AT + 4;
    put16(&mut b, coff, 0x8664);
    put16(&mut b, coff + 2, 2);
    put16(&mut b, coff + 16, u16::try_from(OPTIONAL).expect("fits"));
    put16(&mut b, coff + 18, 0x0022);
    put16(&mut b, OPT, 0x20b);
    put32(&mut b, OPT + 16, 0x1000);
    put64(&mut b, OPT + 24, 0x1_4000_0000);
    put32(&mut b, OPT + 32, 0x1000);
    put32(&mut b, OPT + 36, u32::try_from(FILE_ALIGN).expect("fits"));
    put32(&mut b, OPT + 64, 0xdead_beef);
    put32(&mut b, OPT + 108, 16);
    put32(&mut b, OPT + 112 + IMPORT_DIR * 8, RDATA);
    put32(&mut b, OPT + 112 + IMPORT_DIR * 8 + 4, 60);
    put32(
        &mut b,
        OPT + 112 + CERTIFICATE_DIR * 8,
        u32::try_from(CERT_AT).expect("fits"),
    );
    put32(
        &mut b,
        OPT + 112 + CERTIFICATE_DIR * 8 + 4,
        u32::try_from(CERT_LEN).expect("fits"),
    );
    let mut row = OPT + OPTIONAL;
    for (name, rva, size, off) in [
        (".text", 0x1000u32, 0x200u32, HEADERS),
        (".rdata", RDATA, 0x400, HEADERS + 0x200),
    ] {
        let name = name.as_bytes();
        b[row..row + name.len()].copy_from_slice(name);
        put32(&mut b, row + 8, size);
        put32(&mut b, row + 12, rva);
        put32(&mut b, row + 16, size);
        put32(&mut b, row + 20, u32::try_from(off).expect("fits"));
        put32(
            &mut b,
            row + 36,
            if off == HEADERS {
                0x6000_0020
            } else {
                0x4000_0040
            },
        );
        row += 40;
    }
    let mut text = vec![0xccu8; 0x200];
    text[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    b.extend_from_slice(&text);
    b.extend_from_slice(&rdata());
    assert_eq!(
        b.len(),
        CERT_AT,
        "the sections end where the certificate table starts"
    );
    b.extend((0..CERT_LEN).map(|i| u8::try_from((i * 3 + 7) % 256).expect("fits")));
    b
}

/// Loads `bytes` as a file called `hashed.exe`.
fn load(bytes: Vec<u8>) -> Program {
    Program::from_bytes(PathBuf::from("hashed.exe"), bytes)
        .expect("a PE with a section table loads")
}

/// The hex of a digest.
fn hex(d: &[u8]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

/// The import hash of the crafted table, against the digest an independent
/// MD5 computed over the normalized sorted list
/// `kernel32.createfilew,kernel32.readfile,user32.messageboxa`.
#[test]
fn imphash_matches_the_hand_computed_table() {
    let p = load(image());
    let imports: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(
        imports,
        vec![
            "KERNEL32.dll!CreateFileW",
            "KERNEL32.dll!ReadFile",
            "USER32.DLL!MessageBoxA",
        ],
        "the loader read the crafted table"
    );
    assert_eq!(
        hex(&imphash(&p).expect("named imports")),
        "5d2b76cc545b1b171b01d814385ec978"
    );
}

/// A file with no named imports has no imphash, not the hash of an empty
/// list every such file would share.
#[test]
fn an_import_less_file_has_no_imphash() {
    let mut bytes = image();
    put32(&mut bytes, OPT + 112 + IMPORT_DIR * 8, 0);
    put32(&mut bytes, OPT + 112 + IMPORT_DIR * 8 + 4, 0);
    let p = load(bytes);
    assert!(imphash(&p).is_none());
}

/// The authentihash of the crafted image, against the digest an independent
/// SHA-256 computed over the same file with the checksum field, the security
/// directory entry and the certificate table excluded.
#[test]
fn authentihash_matches_the_independent_digest() {
    let p = load(image());
    assert_eq!(
        hex(&authentihash(&p).expect("a PE header")),
        "73c57db43e206b6881a8b2570cd3fe17beab89ef789c07dfdeb12b43c888c652"
    );
}

/// The authentihash ignores what signing changes without moving code.
///
/// That is the checksum field and the certificate table's bytes. The
/// security directory entry's own bytes are excluded too (the independent
/// digest above skipped them), but its values steer what is skipped, so a
/// value edit moves the digest by changing the geometry, not by being
/// hashed.
#[test]
fn authentihash_ignores_the_signature_and_moves_on_anything_else() {
    let checksum = OPT + 64;
    let base = authentihash(&load(image())).expect("a PE header");
    for (at, what) in [
        (checksum, "the checksum field"),
        (CERT_AT + 5, "a certificate byte"),
        (CERT_AT + CERT_LEN - 1, "the last certificate byte"),
    ] {
        let mut bytes = image();
        bytes[at] ^= 0xff;
        assert_eq!(
            authentihash(&load(bytes)).expect("a PE header"),
            base,
            "{what} moved the authentihash"
        );
    }
    let mut bytes = image();
    bytes[CERT_AT - 1] ^= 0xff;
    assert_ne!(
        authentihash(&load(bytes)).expect("a PE header"),
        base,
        "a byte before the certificate table did not move the authentihash"
    );
}

/// A file with no PE header has no authentihash.
#[test]
fn a_non_pe_file_has_no_authentihash() {
    let p = Program::from_bytes(PathBuf::from("raw.bin"), vec![0xc3; 64])
        .expect("raw bytes load as a program");
    assert!(authentihash(&p).is_none());
}

/// A certificate table whose size reaches past the file is clamped to it,
/// and the hash still answers.
#[test]
fn a_certificate_table_past_the_file_is_clamped() {
    let mut bytes = image();
    put32(&mut bytes, OPT + 112 + CERTIFICATE_DIR * 8 + 4, 0x7fff_ffff);
    let p = load(bytes);
    assert!(authentihash(&p).is_some());
}

/// An unsigned PE — a zeroed security directory entry, no table — hashes
/// the whole file minus the checksum field and the entry itself, against
/// the digest an independent SHA-256 computed over that stream.
#[test]
fn an_unsigned_pe_hashes_without_the_entry() {
    let mut bytes = image();
    put32(&mut bytes, OPT + 112 + CERTIFICATE_DIR * 8, 0);
    put32(&mut bytes, OPT + 112 + CERTIFICATE_DIR * 8 + 4, 0);
    let p = load(bytes);
    assert_eq!(
        hex(&authentihash(&p).expect("a PE header")),
        "188856183eb09a64c192988577ba8d02c5fe5ad8454597f44bc2bca1ea8bbe8b"
    );
}

/// The resource answer carries all three hashes.
#[test]
fn hashes_tsv_names_all_three() {
    let p = load(image());
    let out = hashes_tsv(&p);
    assert!(out.contains("imphash       5d2b76cc"), "{out}");
    assert!(out.contains("authentihash  73c57db4"), "{out}");
    assert!(out.starts_with("# content hashes of hashed.exe"), "{out}");
    assert!(out.contains("tlsh"), "{out}");
}
