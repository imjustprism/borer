//! Wrapper payloads from hand-built PEs: each wrapper's own table is read
//! to its entries' offsets and sizes, and a plain image lists none.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::bundle::{bundles, bundles_tsv};
use borer_engine::program::Program;

use crate::protection::{PE_AT, data, pe, sec};

/// A `.text` of `mov eax, 1; ret` and `int3` padding.
pub(crate) fn text() -> Vec<u8> {
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code
}

/// A plain image, `.text` then a `.data` holding `bytes`, with `tail`
/// appended past its last section.
pub(crate) fn image(bytes: Vec<u8>, tail: &[u8]) -> Vec<u8> {
    let mut b = pe(
        &[sec(".text", 0x1000, text()), data(".data", 0x2000, bytes)],
        0x1000,
    );
    b.extend_from_slice(tail);
    b
}

/// Loads `bytes` as a file called `wrapped.exe`.
pub(crate) fn load(bytes: Vec<u8>) -> Program {
    Program::from_bytes(PathBuf::from("wrapped.exe"), bytes)
        .expect("a PE with a section table loads")
}

/// One `PyInstaller` table entry: lengths, flags, type and padded name.
pub(crate) fn toc_entry(pos: u32, len: u32, full: u32, kind: u8, name: &str) -> Vec<u8> {
    let mut e = Vec::new();
    let size = (18 + name.len() + 1).div_ceil(16) * 16;
    e.extend_from_slice(&u32::try_from(size).expect("fits").to_be_bytes());
    for v in [pos, len, full] {
        e.extend_from_slice(&v.to_be_bytes());
    }
    e.extend_from_slice(&[u8::from(len != full), kind]);
    e.extend_from_slice(name.as_bytes());
    e.resize(size, 0);
    e
}

/// A `PyInstaller` archive of an entry script `main` and a compressed
/// `PYZ-00.pyz`, ended by a cookie naming Python 3.11's library.
pub(crate) fn pyinstaller_archive() -> Vec<u8> {
    let mut pkg = b"print('hi')".to_vec();
    pkg.extend_from_slice(&[0x78; 0x20]);
    let toc_at = u32::try_from(pkg.len()).expect("fits");
    let mut toc = toc_entry(0, 11, 11, b's', "main");
    toc.extend(toc_entry(11, 0x20, 0x80, b'z', "PYZ-00.pyz"));
    let toc_len = u32::try_from(toc.len()).expect("fits");
    pkg.extend_from_slice(&toc);
    let pkg_len = u32::try_from(pkg.len() + 88).expect("fits");
    pkg.extend_from_slice(b"MEI\x0c\x0b\x0a\x0b\x0e");
    for v in [pkg_len, toc_at, toc_len, 311] {
        pkg.extend_from_slice(&v.to_be_bytes());
    }
    let mut lib = b"python311.dll".to_vec();
    lib.resize(64, 0);
    pkg.extend_from_slice(&lib);
    pkg
}

/// A `PyInstaller` archive is read from its cookie: the Python version, the
/// library, and each entry at its file offset, the entry script marked.
#[test]
fn a_pyinstaller_archive_lists_its_entries() {
    let pkg = pyinstaller_archive();
    let bytes = image(vec![0; 0x200], &pkg);
    let start = bytes.len() - pkg.len();
    let table = bundles_tsv(&load(bytes));
    assert!(
        table.contains(&format!(
            "PyInstaller payload at {start:#x} (Python 3.11, loads python311.dll): 2 entries"
        )),
        "{table}"
    );
    assert!(
        table.contains(&format!("{start:#x}\t0xb\t-\tscript\tmain")),
        "{table}"
    );
    assert!(
        table.contains(&format!(
            "{:#x}\t0x20\t0x80\tpyz archive\tPYZ-00.pyz",
            start + 11
        )),
        "{table}"
    );
}

/// The .NET bundle signature, in the order the apphost holds it.
pub(crate) const NET_BUNDLE: [u8; 32] = [
    0x8b, 0x12, 0x02, 0xb9, 0x6a, 0x61, 0x20, 0x38, 0x72, 0x7b, 0x93, 0x02, 0x14, 0xd7, 0xa0, 0x32,
    0x13, 0xf5, 0xb9, 0xe6, 0xef, 0xae, 0x33, 0x18, 0xee, 0x3b, 0x2d, 0xce, 0x24, 0xb3, 0x6a, 0xae,
];

/// A `BinaryWriter` string: one length byte, then the text.
fn net_string(text: &str) -> Vec<u8> {
    let mut s = vec![u8::try_from(text.len()).expect("short")];
    s.extend_from_slice(text.as_bytes());
    s
}

/// A .NET single-file bundle's manifest is read to each file it carries,
/// compressed ones with both sizes.
#[test]
fn a_dotnet_bundle_lists_its_files() {
    let mut marker = vec![0u8; 0x200];
    let host = image(marker.clone(), &[]);
    let manifest_at = u64::try_from(host.len()).expect("fits");
    marker[8..40].copy_from_slice(&NET_BUNDLE);
    marker[..8].copy_from_slice(&manifest_at.to_le_bytes());
    let mut m = Vec::new();
    for v in [6u32, 0, 3] {
        m.extend_from_slice(&v.to_le_bytes());
    }
    m.extend(net_string("abc123"));
    m.extend_from_slice(&[0; 40]);
    for (off, size, packed, kind, name) in [
        (0x1000u64, 0x400u64, 0u64, 1u8, "app.dll"),
        (0x1400, 0x900, 0x300, 2, "native.dll"),
        (0x1d00, 0x10, 0, 0, "a\tb\nfake row"),
    ] {
        for v in [off, size, packed] {
            m.extend_from_slice(&v.to_le_bytes());
        }
        m.push(kind);
        m.extend(net_string(name));
    }
    let table = bundles_tsv(&load(image(marker.clone(), &m)));
    assert!(
        table.contains("manifest 6.0 (.NET 6 or later), bundle id abc123"),
        "{table}"
    );
    assert!(
        table.contains("0x1000\t0x400\t-\tassembly\tapp.dll"),
        "{table}"
    );
    assert!(
        table.contains("0x1400\t0x300\t0x900\tnative binary\tnative.dll"),
        "{table}"
    );
    assert!(
        table.contains("0x1d00\t0x10\t-\tother\ta\\x09b\\x0afake row\n"),
        "{table}"
    );
}

/// An NSIS first header in the appended data names the installer, its
/// data's extent and its compression.
#[test]
fn an_nsis_first_header_is_read() {
    let mut first = vec![0u8; 4];
    first.extend_from_slice(&[0xef, 0xbe, 0xad, 0xde]);
    first.extend_from_slice(b"NullsoftInst");
    first.extend_from_slice(&0x5000u32.to_le_bytes());
    first.extend_from_slice(&0x300u32.to_le_bytes());
    first.extend_from_slice(&[0x5d, 0, 0, 0x80, 0]);
    let bytes = image(vec![0; 0x200], &first);
    let at = bytes.len() - first.len();
    let table = bundles_tsv(&load(bytes));
    assert!(
        table.contains(&format!(
            "NSIS payload at {at:#x} (LZMA, solid; the script header unpacks to 0x5000 bytes"
        )),
        "{table}"
    );
    assert!(
        table.contains(&format!("{at:#x}\t0x300\t-\tdata\tinstaller data")),
        "{table}"
    );
}

/// An Inno Setup loader table gives the setup blocks' offsets in file
/// order, each running to the next, and the data block it points at gives
/// the version.
#[test]
fn an_inno_setup_table_gives_its_blocks() {
    let mut sect = vec![0u8; 0x200];
    sect[..12].copy_from_slice(b"rDlPtS\xcd\xe6\xd7\x7b\x0b\x2a");
    let host_len = image(sect.clone(), &[]).len();
    let data0 = u32::try_from(host_len).expect("fits");
    let mut tail = b"Inno Setup Setup Data (6.3.0)".to_vec();
    tail.resize(0x100, 0);
    let total = data0 + 0x100;
    let exe = data0 + 0x80;
    for (i, v) in [1, total, exe, 0x1000, 0, data0, 0].into_iter().enumerate() {
        sect[12 + i * 4..16 + i * 4].copy_from_slice(&u32::to_le_bytes(v));
    }
    let bytes = image(sect, &tail);
    let table = bundles_tsv(&load(bytes));
    assert!(
        table.contains("Inno Setup payload at 0x600 (Inno Setup Setup Data (6.3.0)): 2 entries"),
        "{table}"
    );
    assert!(
        table.contains(&format!("{data0:#x}\t0x80\t-\tsetup data\tsetup-0")),
        "{table}"
    );
    assert!(
        table.contains(&format!("{exe:#x}\t0x80\t0x1000\tsetup data\tsetup.e32")),
        "{table}"
    );
}

/// A resource directory of one RCDATA entry per `(name, bytes)`, mapped at
/// `rva`, with the bytes behind the tree.
pub(crate) fn rcdata(rva: u32, items: &[(&str, &[u8])]) -> Vec<u8> {
    let n = items.len();
    let l3 = 40 + 8 * n;
    let leaves = l3 + 24 * n;
    let names = leaves + 16 * n;
    let mut b = vec![0u8; names];
    let put = |b: &mut Vec<u8>, at: usize, v: u32| b[at..at + 4].copy_from_slice(&v.to_le_bytes());
    b[14] = 1;
    put(&mut b, 16, 10);
    put(&mut b, 20, 0x8000_0000 | 24);
    b[24 + 12] = u8::try_from(n).expect("few");
    let mut name_offs = Vec::new();
    for (name, _) in items {
        name_offs.push(b.len());
        b.extend_from_slice(&u16::try_from(name.len()).expect("short").to_le_bytes());
        for u in name.encode_utf16() {
            b.extend_from_slice(&u.to_le_bytes());
        }
    }
    b.resize(b.len().div_ceil(4) * 4, 0);
    for (i, (_, bytes)) in items.iter().enumerate() {
        let at = |v: usize| u32::try_from(v).expect("fits");
        put(&mut b, 40 + 8 * i, 0x8000_0000 | at(name_offs[i]));
        put(&mut b, 44 + 8 * i, 0x8000_0000 | at(l3 + 24 * i));
        b[l3 + 24 * i + 14] = 1;
        put(&mut b, l3 + 24 * i + 16, 0x409);
        put(&mut b, l3 + 24 * i + 20, at(leaves + 16 * i));
        let here = at(b.len());
        put(&mut b, leaves + 16 * i, rva + here);
        put(&mut b, leaves + 16 * i + 4, at(bytes.len()));
        b.extend_from_slice(bytes);
    }
    b
}

/// An image whose `.rsrc` holds `items` as named RCDATA, its directory set.
pub(crate) fn with_resources(items: &[(&str, &[u8])]) -> Vec<u8> {
    let tree = rcdata(0x3000, items);
    let len = u32::try_from(tree.len()).expect("fits");
    let mut b = pe(
        &[
            sec(".text", 0x1000, text()),
            data(".data", 0x2000, vec![0; 0x200]),
            data(".rsrc", 0x3000, tree),
        ],
        0x1000,
    );
    let dir = PE_AT + 24 + 112 + 2 * 8;
    b[dir..dir + 4].copy_from_slice(&0x3000u32.to_le_bytes());
    b[dir + 4..dir + 8].copy_from_slice(&len.to_le_bytes());
    b
}

/// An `AutoIt` script resource is a payload entry at its file offset; a
/// `SCRIPT` resource with no `AU3!` record is not `AutoIt`'s.
#[test]
fn an_autoit_script_resource_is_a_payload() {
    let mut script = vec![0xa3; 16];
    script.extend_from_slice(b"AU3!EA06");
    let table = bundles_tsv(&load(with_resources(&[("SCRIPT", &script)])));
    assert!(table.contains("AutoIt payload at 0x"), "{table}");
    assert!(table.contains("\t0x18\t-\tscript\t10/SCRIPT"), "{table}");
    let other = bundles_tsv(&load(with_resources(&[("SCRIPT", b"var x = 1;")])));
    assert!(other.is_empty(), "{other}");
}

/// No payload is listed for a plain image.
#[test]
fn a_plain_image_has_no_payload() {
    assert!(bundles(&load(image(vec![0; 0x200], &[]))).is_empty());
}
