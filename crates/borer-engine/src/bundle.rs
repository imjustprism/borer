//! Payloads a wrapper carries inside the program it ships as.
//!
//! A `PyInstaller` archive, a .NET single-file bundle, an NSIS or Inno Setup
//! installer's data, an `AutoIt` script or a py2exe script resource, each
//! read from its own table to the offset and size of every entry.
//!
//! Nothing is decompressed, extracted or run. The bytes are untrusted:
//! every read is bounds-checked, each table is read for at most
//! [`ENTRIES_MAX`] entries, and the searches for a marker cover at most
//! [`SCAN_MAX`] bytes.

use std::fmt::Write as _;

use crate::fileinfo::{find, forward, reversed};
use crate::num::{from_usize, saturating_usize, u32_le, u64_le};
use crate::program::Program;
use crate::rsrc::{RCDATA, Resource};
use crate::text::one_line;

/// Most entries one table is read for.
const ENTRIES_MAX: usize = 1 << 14;
/// Bytes a search for a marker reads.
const SCAN_MAX: usize = 256 << 20;
/// Bytes at the end of the file searched for the `PyInstaller` cookie: the
/// archive ends the file, before any certificate table.
const COOKIE_TAIL: usize = 1 << 20;
/// Longest entry name read.
const NAME_MAX: usize = 512;
/// Bytes at the start of a script resource the `AU3!` record is looked for in.
const AU3_HEAD: usize = 64;
/// Rows a listing shows before the rest are counted.
const ROWS_SHOWN: usize = 200;

/// One entry of a payload: a file, a module, a block of data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Its name or path, as the table spells it.
    pub name: String,
    /// What it is (`script`, `assembly`, `setup data`, ...).
    pub kind: &'static str,
    /// The file offset of its bytes.
    pub off: u64,
    /// How many bytes it takes in the file.
    pub size: u64,
    /// Its size once decompressed, when the table states one that differs.
    pub unpacked: Option<u64>,
}

/// A wrapper's payload and the entries its table lists.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bundle {
    /// The wrapper (`PyInstaller`, `.NET single-file bundle`, ...).
    pub wrapper: &'static str,
    /// What the table says about the wrapper's version, the runtime it
    /// carries, or how it compresses, when it says it.
    pub about: Option<String>,
    /// The file offset of the table or header the entries were read from.
    pub off: u64,
    /// The entries, in table order.
    pub entries: Vec<Entry>,
    /// How many entries the table declares, when that is more than were read.
    pub declared: Option<u64>,
}

/// Reads a big-endian `u32` at `at`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - The offset of the value's first byte.
fn u32_be(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_be_bytes(
        b.get(at..at.checked_add(4)?)?.try_into().ok()?,
    ))
}

/// A NUL-ended ASCII text at `at`, at most `max` bytes.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Where the text starts.
/// * `max` - Most bytes read.
fn c_text(b: &[u8], at: usize, max: usize) -> String {
    b.get(at..)
        .unwrap_or_default()
        .iter()
        .take(max)
        .take_while(|&&c| c != 0)
        .map(|&c| {
            if c.is_ascii_graphic() || c == b' ' {
                char::from(c)
            } else {
                '?'
            }
        })
        .collect()
}

/// The `PyInstaller` archive cookie, back to front ([`reversed`]).
const MEI_COOKIE: [u8; 8] = reversed(b"MEI\x0c\x0b\x0a\x0b\x0e");
/// Bytes of a `PyInstaller` 2.1+ cookie: magic, four lengths, the Python
/// library's name.
const COOKIE_LEN: usize = 88;
/// Bytes of a `PyInstaller` 2.0 cookie, which has no library name.
const COOKIE_LEN_OLD: usize = 24;
/// Bytes of a `PyInstaller` table entry before its name.
const TOC_HEAD: usize = 18;

/// What a `PyInstaller` table entry's type character says it is.
///
/// # Arguments
///
/// * `c` - The type character.
fn pyi_kind(c: u8) -> &'static str {
    match c {
        b's' => "script",
        b'm' => "module",
        b'M' => "package",
        b'b' => "binary",
        b'z' => "pyz archive",
        b'Z' => "zip",
        b'x' => "data",
        b'o' => "option",
        b'd' => "dependency",
        b'n' => "symlink",
        b'l' => "splash",
        _ => "other",
    }
}

/// Reads a `PyInstaller` archive from the cookie that ends it: the Python
/// version, the library it loads, and every table entry.
///
/// # Arguments
///
/// * `bytes` - The file.
fn pyinstaller(bytes: &[u8]) -> Option<Bundle> {
    let tail_from = bytes.len().saturating_sub(COOKIE_TAIL);
    let magic = forward(&MEI_COOKIE);
    let at = tail_from
        + bytes
            .get(tail_from..)?
            .windows(magic.len())
            .rposition(|w| w == magic.as_slice())?;
    let lib = c_text(bytes, at + COOKIE_LEN_OLD, 64);
    let new = lib.contains("python") || lib.contains("Python");
    let cookie_end = at + if new { COOKIE_LEN } else { COOKIE_LEN_OLD };
    let pkg_len = saturating_usize(u64::from(u32_be(bytes, at + 8)?));
    let toc = saturating_usize(u64::from(u32_be(bytes, at + 12)?));
    let toc_len = saturating_usize(u64::from(u32_be(bytes, at + 16)?));
    let pyvers = u32_be(bytes, at + 20)?;
    let start = cookie_end.checked_sub(pkg_len)?;
    let table =
        bytes.get(start.checked_add(toc)?..start.checked_add(toc)?.checked_add(toc_len)?)?;
    let mut entries = Vec::new();
    let mut pos = 0usize;
    while pos + TOC_HEAD <= table.len() && entries.len() < ENTRIES_MAX {
        let len = saturating_usize(u64::from(u32_be(table, pos)?));
        if len < TOC_HEAD {
            break;
        }
        let data = start.saturating_add(saturating_usize(u64::from(u32_be(table, pos + 4)?)));
        let size = u64::from(u32_be(table, pos + 8)?);
        let full = u64::from(u32_be(table, pos + 12)?);
        let kind = pyi_kind(*table.get(pos + 17)?);
        let name = c_text(table, pos + TOC_HEAD, (len - TOC_HEAD).min(NAME_MAX));
        entries.push(Entry {
            name,
            kind,
            off: from_usize(data),
            size,
            unpacked: (full != size).then_some(full),
        });
        pos = pos.saturating_add(len);
    }
    let (major, minor) = if pyvers >= 100 {
        (pyvers / 100, pyvers % 100)
    } else {
        (pyvers / 10, pyvers % 10)
    };
    let about = if new {
        format!("Python {major}.{minor}, loads {lib}")
    } else {
        format!("Python {major}.{minor}, a PyInstaller 2.0 cookie")
    };
    Some(Bundle {
        wrapper: "PyInstaller",
        about: Some(about),
        off: from_usize(start),
        entries,
        declared: None,
    })
}

/// The .NET single-file bundle signature, back to front ([`reversed`]).
///
/// It is the SHA-256 of `.net core bundle`; the apphost holds it, preceded
/// by the bundle manifest's file offset, zero in a host that carries no
/// bundle.
const NET_BUNDLE: [u8; 32] = reversed(&[
    0x8b, 0x12, 0x02, 0xb9, 0x6a, 0x61, 0x20, 0x38, 0x72, 0x7b, 0x93, 0x02, 0x14, 0xd7, 0xa0, 0x32,
    0x13, 0xf5, 0xb9, 0xe6, 0xef, 0xae, 0x33, 0x18, 0xee, 0x3b, 0x2d, 0xce, 0x24, 0xb3, 0x6a, 0xae,
]);

/// A string a .NET `BinaryWriter` wrote: a 7-bit encoded length, then
/// UTF-8. Returns it and the offset after it.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Where the length starts.
fn dotnet_string(b: &[u8], at: usize) -> Option<(String, usize)> {
    let mut len = 0usize;
    let mut p = at;
    for shift in [0, 7, 14, 21] {
        let byte = *b.get(p)?;
        p += 1;
        len |= usize::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            let text = b.get(p..p.checked_add(len)?)?;
            let shown = String::from_utf8_lossy(text.get(..text.len().min(NAME_MAX))?);
            return Some((shown.into_owned(), p + len));
        }
    }
    None
}

/// What a .NET bundle entry's type byte says it is.
///
/// # Arguments
///
/// * `t` - The type byte.
fn net_kind(t: u8) -> &'static str {
    match t {
        1 => "assembly",
        2 => "native binary",
        3 => "deps.json",
        4 => "runtimeconfig.json",
        5 => "symbols",
        _ => "other",
    }
}

/// Where a .NET apphost's bundle marker sits and the manifest offset beside
/// it: zero for a host that carries no bundle.
///
/// # Arguments
///
/// * `bytes` - The file.
///
/// # Returns
///
/// `(marker offset, manifest offset)`, or `None` when no apphost marker is
/// in the file.
#[must_use]
pub fn dotnet_marker(bytes: &[u8]) -> Option<(usize, u64)> {
    let scan = bytes.get(..bytes.len().min(SCAN_MAX))?;
    let at = find(scan, &forward(&NET_BUNDLE))?;
    Some((at, u64_le(bytes, at.checked_sub(8)?)?))
}

/// Reads a .NET single-file bundle's manifest: the bundle format version
/// and every file in it.
///
/// # Arguments
///
/// * `bytes` - The file.
fn dotnet_bundle(bytes: &[u8]) -> Option<Bundle> {
    let (_, header) = dotnet_marker(bytes)?;
    let mut at = saturating_usize(header);
    if at == 0 {
        return None;
    }
    let major = u32_le(bytes, at)?;
    let minor = u32_le(bytes, at + 4)?;
    let count = u32_le(bytes, at + 8)?;
    let (id, next) = dotnet_string(bytes, at + 12)?;
    at = next + if major >= 2 { 40 } else { 0 };
    let mut entries = Vec::new();
    for _ in 0..saturating_usize(u64::from(count)).min(ENTRIES_MAX) {
        let off = u64_le(bytes, at)?;
        let size = u64_le(bytes, at + 8)?;
        let (packed, rest) = if major >= 6 {
            (u64_le(bytes, at + 16)?, at + 24)
        } else {
            (0, at + 16)
        };
        let kind = net_kind(*bytes.get(rest)?);
        let (name, next) = dotnet_string(bytes, rest + 1)?;
        at = next;
        entries.push(Entry {
            name,
            kind,
            off,
            size: if packed == 0 { size } else { packed },
            unpacked: (packed != 0).then_some(size),
        });
    }
    let runtime = match major {
        1 => ".NET Core 3",
        2 => ".NET 5",
        _ => ".NET 6 or later",
    };
    Some(Bundle {
        wrapper: ".NET single-file bundle",
        about: Some(format!(
            "manifest {major}.{minor} ({runtime}), bundle id {id}"
        )),
        off: header,
        declared: (from_usize(entries.len()) < u64::from(count)).then_some(u64::from(count)),
        entries,
    })
}

/// The NSIS first header's signature and magic, back to front
/// ([`reversed`]); four bytes of flags precede it.
const NSIS_FIRST: [u8; 16] = reversed(b"\xef\xbe\xad\xdeNullsoftInst");

/// Reads an NSIS installer's first header.
///
/// It says where the data starts, how big it is, and how the script header
/// is compressed. The script and the file names are inside that compressed
/// header and are not listed.
///
/// # Arguments
///
/// * `bytes` - The file.
fn nsis(bytes: &[u8]) -> Option<Bundle> {
    let scan = bytes.get(..bytes.len().min(SCAN_MAX))?;
    let at = find(scan, &forward(&NSIS_FIRST))?.checked_sub(4)?;
    let header = u32_le(bytes, at + 20)?;
    let total = u32_le(bytes, at + 24)?;
    let body = at + 28;
    let lzma = |o: usize| bytes.get(o..o + 3) == Some(&[0x5d, 0, 0][..]);
    let solid = lzma(body) || u32_le(bytes, body).is_none_or(|w| w & 0x8000_0000 == 0);
    let method = if lzma(body) || (!solid && lzma(body + 4)) {
        "LZMA"
    } else {
        "zlib or bzip2"
    };
    Some(Bundle {
        wrapper: "NSIS",
        about: Some(format!(
            "{method}, {}; the script header unpacks to {header:#x} bytes and names the files",
            if solid { "solid" } else { "not solid" }
        )),
        off: from_usize(at),
        entries: vec![Entry {
            name: "installer data".to_owned(),
            kind: "data",
            off: from_usize(at),
            size: u64::from(total),
            unpacked: None,
        }],
        declared: None,
    })
}

/// The Inno Setup loader's offset table IDs, back to front ([`reversed`]),
/// with the bytes between each ID and the table's total size: 5.1.5 and
/// later put a revision word there, earlier releases nothing.
const INNO_TABLES: [([u8; 12], usize); 2] = [
    (reversed(b"rDlPtS\xcd\xe6\xd7\x7b\x0b\x2a"), 4),
    (reversed(b"rDlPtS02\x87\x65\x56\x78"), 0),
];
/// The text an Inno Setup data block opens with, back to front ([`reversed`]).
const INNO_DATA: [u8; 23] = reversed(b"Inno Setup Setup Data (");

/// Reads an Inno Setup loader's offset table: where the compressed setup
/// program, the setup data and the file data start.
///
/// Each block runs to the next one's start, the last to the total size the
/// table states.
///
/// # Arguments
///
/// * `bytes` - The file.
fn inno(bytes: &[u8]) -> Option<Bundle> {
    let scan = bytes.get(..bytes.len().min(SCAN_MAX))?;
    let (at, skip) = INNO_TABLES
        .iter()
        .find_map(|(id, skip)| Some((find(scan, &forward(id))?, *skip)))?;
    let word = |i: usize| u32_le(bytes, at + 12 + skip + i * 4).map(u64::from);
    let (total, exe, exe_len, data0, data1) = (word(0)?, word(1)?, word(2)?, word(4)?, word(5)?);
    let end = total.min(from_usize(bytes.len()));
    let version = bytes
        .get(saturating_usize(data0)..)
        .filter(|b| b.starts_with(&forward(&INNO_DATA)))
        .map(|b| c_text(b, 0, 64).trim_end_matches(' ').to_owned());
    let mut blocks = [
        (
            "setup.e32 (the setup program, compressed)",
            exe,
            Some(exe_len),
        ),
        (
            "setup-0 (setup script and file list, compressed)",
            data0,
            None,
        ),
        ("setup-1 (the files, compressed)", data1, None),
    ];
    blocks.sort_by_key(|b| b.1);
    let starts: Vec<u64> = blocks.iter().map(|b| b.1).collect();
    let entries = blocks
        .iter()
        .filter(|(_, off, _)| *off > 0 && *off < end)
        .map(|&(name, off, unpacked)| Entry {
            name: name.to_owned(),
            kind: "setup data",
            off,
            size: starts
                .iter()
                .copied()
                .find(|&s| s > off)
                .unwrap_or(end)
                .min(end)
                - off,
            unpacked,
        })
        .collect();
    Some(Bundle {
        wrapper: "Inno Setup",
        about: Some(version.unwrap_or_else(|| "data version not read".to_owned())),
        off: from_usize(at),
        entries,
        declared: None,
    })
}

/// The payloads resources carry: an `AutoIt` script, an RCDATA `SCRIPT`
/// whose first bytes hold an `AU3!` record, and py2exe's script and Python
/// library.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `res` - The image's resources ([`crate::rsrc::resources`]).
fn in_resources(bytes: &[u8], res: &[Resource]) -> Vec<Bundle> {
    let entry = |r: &Resource, kind| Entry {
        name: format!("{}/{}", r.kind, r.name),
        kind,
        off: r.off,
        size: r.len,
        unpacked: None,
    };
    let mut out = Vec::new();
    let script = res.iter().find(|r| {
        r.kind == RCDATA && r.name == "SCRIPT" && {
            let start = saturating_usize(r.off);
            let len = saturating_usize(r.len).min(AU3_HEAD);
            bytes
                .get(start..start.saturating_add(len))
                .is_some_and(|head| find(head, b"AU3!").is_some())
        }
    });
    if let Some(r) = script {
        out.push(Bundle {
            wrapper: "AutoIt",
            about: Some("an AU3! script record, encrypted".to_owned()),
            off: r.off,
            entries: vec![entry(r, "script")],
            declared: None,
        });
    }
    let py: Vec<Entry> = res
        .iter()
        .filter(|r| r.kind == "PYTHONSCRIPT" || r.kind.to_ascii_uppercase().ends_with(".DLL"))
        .take(ENTRIES_MAX)
        .map(|r| {
            entry(
                r,
                if r.kind == "PYTHONSCRIPT" {
                    "script"
                } else {
                    "binary"
                },
            )
        })
        .collect();
    if py.iter().any(|e| e.kind == "script") {
        out.push(Bundle {
            wrapper: "py2exe",
            about: py
                .iter()
                .find(|e| e.kind == "binary")
                .map(|e| format!("carries {}", e.name)),
            off: py.first().map_or(0, |e| e.off),
            entries: py,
            declared: None,
        });
    }
    out
}

/// Every wrapper payload the file carries, each with its entries.
///
/// # Arguments
///
/// * `p` - The loaded file.
///
/// # Returns
///
/// The payloads in a fixed order (`PyInstaller`, .NET bundle, NSIS, Inno
/// Setup, then resource payloads); empty when there are none.
#[must_use]
pub fn bundles(p: &Program) -> Vec<Bundle> {
    let bytes = p.bytes.as_slice();
    let mut out: Vec<Bundle> = [
        pyinstaller(bytes),
        dotnet_bundle(bytes),
        nsis(bytes),
        inno(bytes),
    ]
    .into_iter()
    .flatten()
    .collect();
    out.extend(in_resources(bytes, &crate::rsrc::resources(p)));
    out
}

/// How many entries a payload lists, and how many its table declares when
/// that is more: `3 entries`, `1 entry`, `200 entries of 9000 declared`.
///
/// # Arguments
///
/// * `b` - The payload.
#[must_use]
pub fn entry_count(b: &Bundle) -> String {
    format!(
        "{} entr{}{}",
        b.entries.len(),
        if b.entries.len() == 1 { "y" } else { "ies" },
        b.declared
            .map_or_else(String::new, |d| format!(" of {d} declared"))
    )
}

/// The line a payload's table is headed by: the wrapper, where its table
/// is, what the table says about it, and how many entries it lists.
///
/// # Arguments
///
/// * `b` - The payload.
fn headline(b: &Bundle) -> String {
    format!(
        "{} payload at {:#x}{}: {}",
        b.wrapper,
        b.off,
        b.about
            .as_ref()
            .map_or_else(String::new, |a| format!(" ({})", one_line(a))),
        entry_count(b)
    )
}

/// The payloads as tables, one per wrapper: offset, size, unpacked size,
/// kind and name of each entry.
///
/// # Arguments
///
/// * `p` - The loaded file.
///
/// # Returns
///
/// The tables, each headed by its [`headline`] and capped at
/// [`ROWS_SHOWN`] rows with `showing N of M`; empty when there are none.
#[must_use]
pub fn bundles_tsv(p: &Program) -> String {
    let mut out = String::new();
    for b in bundles(p) {
        let _ = writeln!(
            out,
            "# payload: {}, showing {} of {}\noff\tsize\tunpacked\tkind\tname",
            headline(&b),
            b.entries.len().min(ROWS_SHOWN),
            b.entries.len()
        );
        for e in b.entries.iter().take(ROWS_SHOWN) {
            let _ = writeln!(
                out,
                "{:#x}\t{:#x}\t{}\t{}\t{}",
                e.off,
                e.size,
                e.unpacked
                    .map_or_else(|| "-".to_owned(), |u| format!("{u:#x}")),
                e.kind,
                one_line(&e.name)
            );
        }
    }
    out
}
