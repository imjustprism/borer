//! Content hashes of a crafted PE.
//!
//! Imphash against a hand-computed import table, authentihash against a file with a checksum, a security directory
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

use borer_engine::hashing::{authentihash, hashes_tsv, imphash, tlsh};
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

/// The `.rdata` bytes of a table out of name order with imports by ordinal.
///
/// `USER32.DLL` (`MessageBoxA`), then `WS2_32.dll` (ordinal 115, which
/// `pefile` names `WSAStartup`; ordinal 999, which it does not name; and
/// `send` by name).
fn rdata_by_ordinal() -> Vec<u8> {
    /// The lookup entry's flag for an import by ordinal.
    const BY_ORDINAL: u64 = 1 << 63;
    let mut r = vec![0u8; 0x400];
    descriptor(&mut r, 0, RDATA + 0x100, RDATA + 0xa0, RDATA + 0x200);
    descriptor(&mut r, 20, RDATA + 0x120, RDATA + 0xb0, RDATA + 0x220);
    r[0xa0..0xab].copy_from_slice(b"USER32.DLL\0");
    r[0xb0..0xbb].copy_from_slice(b"WS2_32.dll\0");
    for (table, entries) in [
        (0x100, vec![u64::from(RDATA + 0x320)]),
        (
            0x120,
            vec![BY_ORDINAL | 115, BY_ORDINAL | 999, u64::from(RDATA + 0x300)],
        ),
    ] {
        for (k, v) in entries.iter().enumerate() {
            put64(&mut r, table + k * 8, *v);
            put64(&mut r, table + 0x100 + k * 8, *v);
        }
    }
    r[0x300..0x307].copy_from_slice(b"\0\0send\0");
    r[0x320..0x32e].copy_from_slice(b"\0\0MessageBoxA\0");
    r
}

/// Builds the PE32+ image both hashes read, with the first import table.
fn image() -> Vec<u8> {
    image_with(&rdata())
}

/// Builds the PE32+ image both hashes read.
///
/// Headers with a junk checksum, an import directory for the `.rdata`
/// given, a security directory naming a certificate table appended after
/// the sections, a `.text` of `int3` padding entered by `mov eax, 1; ret`,
/// and the `.rdata` itself.
///
/// # Arguments
///
/// * `rdata` - The `.rdata` bytes, `0x400` of them, descriptors first.
fn image_with(rdata: &[u8]) -> Vec<u8> {
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
    b.extend_from_slice(rdata);
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
/// MD5 computed over the normalized list, in table order,
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

/// The import hash keeps the table's order and names ordinals as `pefile`.
///
/// Pinned to the digest `pefile` 2024.8.26's `get_imphash` computed over
/// the same file:
/// `user32.messageboxa,ws2_32.wsastartup,ws2_32.ord999,ws2_32.send`. It
/// sorted the list and hashed `ORDINAL 115` as a name. The loader names
/// the ordinals for a reader (`WSAStartup`, `ws2_32_ord999`) and the hash
/// still names them as `pefile` does.
#[test]
fn imphash_keeps_table_order_and_names_ordinals_as_pefile_does() {
    let p = load(image_with(&rdata_by_ordinal()));
    let imports: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(
        imports,
        vec![
            "USER32.DLL!MessageBoxA",
            "WS2_32.dll!WSAStartup",
            "WS2_32.dll!ws2_32_ord999",
            "WS2_32.dll!send",
        ],
        "the loader read the crafted table"
    );
    assert_eq!(
        hex(&imphash(&p).expect("imports")),
        "c7216ad5d21e0b14fa56758a6344ebe0"
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

/// The resource answer carries all four hashes, TLSH as the `T1` string
/// its own function prints and borer's hash on a row of its own.
#[test]
fn hashes_tsv_names_all_three() {
    let p = load(image());
    let out = hashes_tsv(&p);
    assert!(out.contains("imphash       5d2b76cc"), "{out}");
    assert!(out.contains("authentihash  73c57db4"), "{out}");
    assert!(out.starts_with("# content hashes of hashed.exe"), "{out}");
    assert!(out.contains("tlsh"), "{out}");
    let t1 = tlsh(&p.bytes).expect("the image is varied enough").hex();
    assert!(out.contains(&format!("\ntlsh          {t1}\n")), "{out}");
    assert!(out.contains("\nborer-lsh     "), "{out}");
}

/// A file too short for TLSH says why on its row instead of a digest.
#[test]
fn a_short_file_has_no_tlsh() {
    let p =
        Program::from_bytes(PathBuf::from("short.bin"), b"short".to_vec()).expect("any bytes load");
    let out = hashes_tsv(&p);
    assert!(
        out.contains("\ntlsh          - (TLSH needs 50 bytes or more, of enough variety)\n"),
        "{out}"
    );
}

/// Encodes one DER element.
fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let len = u16::try_from(body.len()).expect("fits");
    let mut out = vec![tag];
    if len < 0x80 {
        out.push(u8::try_from(len).expect("fits"));
    } else {
        out.push(0x82);
        out.extend_from_slice(&len.to_be_bytes());
    }
    out.extend_from_slice(body);
    out
}

/// A DER name holding one common name.
fn common_name(value: &str) -> Vec<u8> {
    let pair = [tlv(0x06, &[0x55, 0x04, 0x03]), tlv(0x0c, value.as_bytes())].concat();
    tlv(0x30, &tlv(0x31, &tlv(0x30, &pair)))
}

/// A certificate with `serial` whose subject is `cn`, valid 2020 to 2030.
fn certificate(serial: u8, cn: &str) -> Vec<u8> {
    let alg = tlv(0x30, &tlv(0x06, SHA256_OID));
    let validity = [tlv(0x17, b"200101000000Z"), tlv(0x18, b"20301231235959Z")].concat();
    let tbs = [
        tlv(0xa0, &tlv(0x02, &[2])),
        tlv(0x02, &[serial]),
        alg.clone(),
        common_name("CA"),
        tlv(0x30, &validity),
        common_name(cn),
    ]
    .concat();
    tlv(0x30, &[tlv(0x30, &tbs), alg].concat())
}

/// SHA-256's object identifier.
const SHA256_OID: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];

/// An Authenticode `SignedData` over `digest` whose signer names serial 7,
/// the second of its two certificates.
fn pkcs7(digest: &[u8]) -> Vec<u8> {
    let spc = tlv(
        0x06,
        &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x82, 0x37, 0x02, 0x01, 0x04],
    );
    let digest_info = [tlv(0x30, &tlv(0x06, SHA256_OID)), tlv(0x04, digest)].concat();
    let indirect = tlv(0x30, &[tlv(0x30, &spc), tlv(0x30, &digest_info)].concat());
    let content = tlv(0x30, &[spc, tlv(0xa0, &indirect)].concat());
    let issuer_serial = [common_name("CA"), tlv(0x02, &[7])].concat();
    let signer = tlv(0x30, &[tlv(0x02, &[1]), tlv(0x30, &issuer_serial)].concat());
    let certs = [certificate(3, "Other"), certificate(7, "Example Corp")].concat();
    let signed = tlv(
        0x30,
        &[
            tlv(0x02, &[1]),
            tlv(0x31, &tlv(0x30, &tlv(0x06, SHA256_OID))),
            content,
            tlv(0xa0, &certs),
            tlv(0x31, &signer),
        ]
        .concat(),
    );
    let signed_data = [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x02];
    tlv(
        0x30,
        &[tlv(0x06, &signed_data), tlv(0xa0, &signed)].concat(),
    )
}

/// The crafted image with its certificate table holding a signature over
/// `digest`, cut to `keep` bytes of it.
fn signed_image(digest: &[u8], keep: usize) -> Vec<u8> {
    let mut bytes = image();
    let mut sig = pkcs7(digest);
    sig.truncate(keep);
    let table = &mut bytes[CERT_AT..CERT_AT + CERT_LEN];
    table.fill(0);
    put32(table, 0, u32::try_from(CERT_LEN).expect("fits"));
    put16(table, 4, 0x0200);
    put16(table, 6, 0x0002);
    table[8..8 + sig.len()].copy_from_slice(&sig);
    bytes
}

/// A signed file names its signer and matches its signed digest; an edit
/// after signing shows; a signature cut anywhere still loads as signed.
#[test]
fn a_signature_names_its_signer_and_judges_the_file() {
    let digest = authentihash(&load(signed_image(&[0; 32], usize::MAX))).expect("a PE header");
    let summary = load(signed_image(&digest, usize::MAX)).summary();
    assert!(summary.contains("signed by \"Example Corp\""), "{summary}");
    assert!(
        summary.contains("certificate valid 2020-01-01 to 2030-12-31"),
        "{summary}"
    );
    assert!(
        summary.contains("matches its signed sha256 digest"),
        "{summary}"
    );
    let mut edited = signed_image(&digest, usize::MAX);
    edited[HEADERS + 1] ^= 0xff;
    let summary = load(edited).summary();
    assert!(summary.contains("changed after signing"), "{summary}");
    let full = pkcs7(&digest).len();
    for keep in 0..full {
        let summary = load(signed_image(&digest, keep)).summary();
        assert!(
            summary.contains("signed") && !summary.contains("unsigned"),
            "{keep}: {summary}"
        );
    }
}

/// A signer's name cannot reorder the line that quotes it.
///
/// The name is read with its control characters replaced, so it ends no
/// line, but a right-to-left override passed and the summary quoted it as
/// the certificate spells it. The image is the signed one with the
/// signer's common name rewritten in place.
#[test]
fn a_signer_s_name_cannot_reorder_its_line() {
    let mut bytes = signed_image(&[0; 32], usize::MAX);
    let at = bytes
        .windows(12)
        .position(|w| w == b"Example Corp")
        .expect("the signer is named");
    bytes[at..at + 12].copy_from_slice("\u{202e}Corp, Inc".as_bytes());
    let summary = load(bytes).summary();
    assert!(
        summary.contains("signed by \"\\x202eCorp, Inc\""),
        "{summary}"
    );
}

/// A parser's refusal cannot forge a line of the summary through a name
/// it quotes.
///
/// The strict parse refuses an import whose address table maps nowhere,
/// and its message quotes the DLL's name as the file states it; the
/// warning that the headers were read leniently quoted the message, line
/// break and all.
#[test]
fn a_refusal_that_quotes_a_name_cannot_forge_a_warning() {
    let mut r = vec![0u8; 0x400];
    descriptor(&mut r, 0, RDATA + 0x100, RDATA + 0xa0, 0x7000_0000);
    r[0xa0..0xb9].copy_from_slice(b"K.dll\n# evidence: forged\0");
    put64(&mut r, 0x100, u64::from(RDATA + 0x300));
    r[0x300..0x306].copy_from_slice(b"\0\0Foo\0");
    let summary = load(image_with(&r)).summary();
    assert!(
        summary.contains("# warning: the headers do not all parse ("),
        "{summary}"
    );
    assert!(
        !summary.lines().any(|l| l.starts_with("# evidence")),
        "{summary}"
    );
}
