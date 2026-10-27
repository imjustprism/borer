//! The mod SDK's classes as a ReClass.NET project (`.rcnet`).
//!
//! The file is a zip holding one `Data.xml`, the schema ReClass.NET reads
//! (`DataExchange/ReClass/ReClassNetFile.*.cs` at ReClassNET/ReClass.NET
//! `a02fcb9b`). ReClass.NET stores no offsets: a node sits where the nodes
//! before it end, so every gap between known fields is a run of hex nodes,
//! up to 64 KiB a run, where the class's nodes stop. A class's
//! uuid is derived from its name, so the same SDK writes the same bytes. A
//! class a global singleton points at takes that global as its address.

use std::fmt::Write as _;

use super::{Class, Evidence, Part, Sdk, Ty, parts, xml};

/// The file version ReClass.NET writes (`FileVersion`, 1.1).
const FILE_VERSION: u32 = 0x0001_0001;

/// The one entry of the archive ReClass.NET opens.
const ENTRY: &str = "Data.xml";

/// A zip's local file header signature.
const LOCAL: u32 = 0x0403_4b50;
/// A zip's central directory header signature.
const CENTRAL: u32 = 0x0201_4b50;
/// A zip's end of central directory signature.
const END: u32 = 0x0605_4b50;
/// Bytes of the three headers of a one-entry zip, besides the name twice.
const HEADERS: usize = 30 + 46 + 22;

/// Longest run of bytes a class spells in hex nodes, one per 8 bytes:
/// past it a class's nodes stop, so a stated struct of a gigabyte does not
/// become a hundred million nodes.
const HEX_MAX: u64 = 0x1_0000;

/// Returns the classes of the SDK as a ReClass.NET project.
///
/// # Arguments
///
/// * `sdk` - What [`super::build`] gathered.
///
/// # Returns
///
/// The `.rcnet` file's bytes: a zip of one stored `Data.xml`.
///
/// # Errors
///
/// When the XML is too big for a zip without its 64-bit extension.
pub fn reclass(sdk: &Sdk) -> anyhow::Result<Vec<u8>> {
    stored_zip(ENTRY, data_xml(sdk).as_bytes())
}

/// Returns the project's `Data.xml`.
///
/// # Arguments
///
/// * `sdk` - The classes.
#[must_use]
pub fn data_xml(sdk: &Sdk) -> String {
    let platform = if sdk.word == 8 { "x64" } else { "x86" };
    let mut out = format!(
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<reclass version=\"{FILE_VERSION}\" type=\"{platform}\">\n  <classes>\n"
    );
    for c in &sdk.classes {
        let mut comment = c.parent.as_ref().map_or_else(String::new, |p| {
            format!("parent {p} (its fields are flattened in); ")
        });
        let _ = match c.size {
            super::Size::Stated(n) => write!(comment, "size {n:#x} (stated)"),
            super::Size::AtLeast(n) => write!(comment, "size at least {n:#x}"),
        };
        for note in &c.notes {
            let _ = write!(comment, "; {note}");
        }
        let parts = parts(c, sdk.word);
        let run = |p: &Part<'_>| match p {
            Part::Pad(off, len) => Some((*off, *len)),
            Part::Field(f) => match f.ty {
                Ty::Bytes(n, _) => Some((f.off, n)),
                _ => None,
            },
            Part::Skipped(_) => None,
        };
        let stop = parts
            .iter()
            .position(|p| run(p).is_some_and(|(_, len)| len > HEX_MAX));
        if let Some((off, len)) = stop.and_then(|i| parts.get(i)).and_then(run) {
            let _ = write!(
                comment,
                "; the nodes stop at +{off:#x}, where {len:#x} bytes run past the {HEX_MAX:#x} a project spells in hex nodes"
            );
        }
        let _ = writeln!(
            out,
            "    <class uuid=\"{}\" name=\"{}\" comment=\"{}\" address=\"{}\">",
            uuid(&c.name),
            xml(&c.name),
            xml(&comment),
            xml(&address(sdk, c))
        );
        nodes(&mut out, sdk, c, &parts[..stop.unwrap_or(parts.len())]);
        out.push_str("    </class>\n");
    }
    out.push_str("  </classes>\n</reclass>\n");
    out
}

/// Writes a class's nodes: its fields in order and hex nodes between them.
///
/// # Arguments
///
/// * `out` - The XML being written.
/// * `sdk` - For the pointer width and the classes pointed at.
/// * `class` - The class, whose vtable slots its vtable node lists.
/// * `parts` - Its bytes in order, up to where the nodes stop.
fn nodes(out: &mut String, sdk: &Sdk, class: &Class, parts: &[Part<'_>]) {
    for &part in parts {
        let Part::Field(f) = part else {
            if let Part::Pad(_, len) = part {
                hex(out, "", "", len);
            }
            continue;
        };
        let name = xml(&f.name);
        let comment = match &f.evidence {
            Evidence::Stated => String::new(),
            e => xml(&e.to_string()),
        };
        let open = |kind: &str| {
            format!(
                "      <node type=\"{kind}\" name=\"{name}\" comment=\"{comment}\" hidden=\"false\""
            )
        };
        match &f.ty {
            Ty::Int { bytes, signed } => {
                let sign = if *signed { "" } else { "U" };
                let bits = u32::from(*bytes).saturating_mul(8);
                let _ = writeln!(out, "{} />", open(&format!("{sign}Int{bits}Node")));
            }
            Ty::Float => {
                let _ = writeln!(out, "{} />", open("FloatNode"));
            }
            Ty::Double => {
                let _ = writeln!(out, "{} />", open("DoubleNode"));
            }
            Ty::Ptr(to) => match to.as_ref().and_then(|n| sdk.class(n)) {
                Some(target) => {
                    let _ = writeln!(
                        out,
                        "{}>\n        <node type=\"ClassInstanceNode\" name=\"\" comment=\"\" hidden=\"false\" reference=\"{}\" />\n      </node>",
                        open("PointerNode"),
                        uuid(&target.name)
                    );
                }
                None => {
                    let _ = writeln!(out, "{} />", open("PointerNode"));
                }
            },
            Ty::VTable => {
                let _ = writeln!(out, "{}>", open("VirtualMethodTableNode"));
                for (_, method) in &class.slots {
                    let _ = writeln!(
                        out,
                        "        <method name=\"{}\" comment=\"\" hidden=\"false\" />",
                        xml(method)
                    );
                }
                out.push_str("      </node>\n");
            }
            Ty::Bytes(n, what) => hex(out, &name, &xml(what), *n),
        }
    }
}

/// Writes `len` bytes as hex nodes, the widest first; the first is named.
///
/// # Arguments
///
/// * `out` - The XML being written.
/// * `name` - The first node's name, XML-escaped.
/// * `comment` - The first node's comment, XML-escaped.
/// * `len` - Bytes to cover.
fn hex(out: &mut String, name: &str, comment: &str, len: u64) {
    let mut left = len;
    let mut first = true;
    for width in [8u64, 4, 2, 1] {
        while left >= width {
            let (n, c) = if first { (name, comment) } else { ("", "") };
            let _ = writeln!(
                out,
                "      <node type=\"Hex{}Node\" name=\"{n}\" comment=\"{c}\" hidden=\"false\" />",
                width.saturating_mul(8)
            );
            first = false;
            left -= width;
        }
    }
}

/// Returns a class's address formula: the global singleton holding it,
/// else `0`.
///
/// # Arguments
///
/// * `sdk` - The globals.
/// * `class` - The class.
fn address(sdk: &Sdk, class: &Class) -> String {
    sdk.globals
        .iter()
        .find_map(|g| match &g.ty {
            Ty::Ptr(Some(n)) if *n == class.name => {
                Some(format!("[<{}> + {:X}]", sdk.module, sdk.rva(g.va)))
            }
            Ty::Bytes(_, n) if *n == class.name => {
                Some(format!("<{}> + {:X}", sdk.module, sdk.rva(g.va)))
            }
            _ => None,
        })
        .unwrap_or_else(|| "0".to_owned())
}

/// Returns a uuid derived from a class name, spelled as a GUID.
///
/// Two 64-bit FNV-1a hashes of the name, from two offset bases, make the
/// sixteen bytes; the version and variant bits mark it a name-based uuid.
///
/// # Arguments
///
/// * `name` - The class name.
#[must_use]
pub fn uuid(name: &str) -> String {
    let fnv = |basis: u64| {
        name.bytes().fold(basis, |h, b| {
            (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
        })
    };
    let hi = (fnv(0xcbf2_9ce4_8422_2325) & !0xf000) | 0x5000;
    let lo = (fnv(0x6c62_272e_07bb_0142) & !(0xc << 60)) | (0x8 << 60);
    format!(
        "{:08x}-{:04x}-{:04x}-{:04x}-{:012x}",
        hi >> 32,
        (hi >> 16) & 0xffff,
        hi & 0xffff,
        lo >> 48,
        lo & 0xffff_ffff_ffff
    )
}

/// Returns a zip archive holding one file, stored without compression.
///
/// The entry's time is the zip epoch, 1980-01-01 00:00, so the bytes never
/// depend on the clock.
///
/// # Arguments
///
/// * `name` - The entry's name.
/// * `data` - Its bytes.
///
/// # Errors
///
/// When `data` or `name` is too big for a zip without its 64-bit
/// extension (4 GiB, 64 KiB).
pub fn stored_zip(name: &str, data: &[u8]) -> anyhow::Result<Vec<u8>> {
    let size = u32::try_from(data.len())
        .map_err(|_| anyhow::anyhow!("{} bytes do not fit a zip entry", data.len()))?;
    let name_len = u16::try_from(name.len())
        .map_err(|_| anyhow::anyhow!("a zip entry name of {} bytes", name.len()))?;
    let crc = crate::carve::crc32(data);
    let common = |out: &mut Vec<u8>| {
        for half in [20u16, 0, 0, 0, 0x0021] {
            out.extend_from_slice(&half.to_le_bytes());
        }
        for word in [crc, size, size] {
            out.extend_from_slice(&word.to_le_bytes());
        }
        out.extend_from_slice(&name_len.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes());
    };
    let mut out = Vec::with_capacity(
        data.len()
            .saturating_add(name.len().saturating_mul(2))
            .saturating_add(HEADERS),
    );
    out.extend_from_slice(&LOCAL.to_le_bytes());
    common(&mut out);
    out.extend_from_slice(name.as_bytes());
    out.extend_from_slice(data);
    let directory = u32::try_from(out.len())
        .map_err(|_| anyhow::anyhow!("{} bytes do not fit a zip", out.len()))?;
    out.extend_from_slice(&CENTRAL.to_le_bytes());
    out.extend_from_slice(&20u16.to_le_bytes());
    common(&mut out);
    for half in [0u16, 0, 0] {
        out.extend_from_slice(&half.to_le_bytes());
    }
    for word in [0u32, 0] {
        out.extend_from_slice(&word.to_le_bytes());
    }
    out.extend_from_slice(name.as_bytes());
    let directory_len = u32::try_from(out.len())
        .map_err(|_| anyhow::anyhow!("{} bytes do not fit a zip", out.len()))?
        .saturating_sub(directory);
    out.extend_from_slice(&END.to_le_bytes());
    for half in [0u16, 0, 1, 1] {
        out.extend_from_slice(&half.to_le_bytes());
    }
    for word in [directory_len, directory] {
        out.extend_from_slice(&word.to_le_bytes());
    }
    out.extend_from_slice(&0u16.to_le_bytes());
    Ok(out)
}
