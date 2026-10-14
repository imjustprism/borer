//! Programs and containers embedded in a file, found by their signatures,
//! kept only when the headers behind each signature validate, and sized by
//! what those headers state.
//!
//! Nothing is decompressed or extracted. A container (zip, gzip, xz, 7z,
//! cab, squashfs, cpio, uImage, cramfs, an Android boot image) is listed
//! with what its header says; a program (PE, ELF, Mach-O) is listed so the
//! loader can open the bytes it spans as a program of its own
//! ([`crate::program::Program::load`] reads `<file>@<offset>`). A signature
//! alone proves nothing, so each format's fixed fields are checked: `MZ`
//! must lead through `e_lfanew` to `PE\0\0` and a known machine, an xz, 7z
//! or uImage header must carry its own CRC, a cab's reserved fields must be
//! zero, and so on. Bytes the headers do not explain but that read as
//! random are listed too, from the windowed entropy scan
//! ([`crate::entropy::high_entropy_regions`]): what is packed, compressed
//! or encrypted with no signature to say which.
//!
//! The bytes are untrusted: every read is bounds-checked, the signature
//! scan covers at most [`SCAN_MAX`] bytes and keeps at most [`FOUND_MAX`]
//! finds, and the forward searches for an end record share one budget
//! ([`SEARCH_FUEL`]).

use std::fmt::Write as _;

use crate::num::{from_usize, saturating_usize};
use crate::program::{BinaryFormat, Program};
use crate::text::quoted;

/// Bytes of a file the signature scan reads; past them nothing is listed.
pub const SCAN_MAX: usize = 256 << 20;
/// Most embedded programs and containers one scan keeps.
pub const FOUND_MAX: usize = 4096;
/// Bytes the forward searches for an end record (a zip's central directory
/// end, an xz footer, a cpio trailer) may read in one scan, all together, so
/// a file of many headers cannot make the scan quadratic.
pub const SEARCH_FUEL: usize = 64 << 20;
/// Rows the listing shows before the rest are counted.
const ROWS_SHOWN: usize = 200;
/// Entropy window of the profile, in bytes.
const WINDOW: usize = 1024;
/// Bits per byte a window may read under random data and still count.
///
/// Deflate and packed code read a little under what random data reads at
/// in a [`WINDOW`]; code and text read whole bits under it.
const MARGIN: f64 = 0.6;
/// Furthest past `e_lfanew`'s field the `PE\0\0` signature may sit.
const PE_HEADER_MAX: usize = 0x1_0000;
/// Most sections a PE declares (the loader's own limit).
const PE_SECTIONS_MAX: usize = 96;
/// Most slices a fat Mach-O may declare and still be read as one.
const FAT_SLICES_MAX: u32 = 32;
/// Most load commands a Mach-O may declare and still be read as one.
const MACHO_COMMANDS_MAX: u32 = 4096;
/// Most entries a cpio walk reads before it stops counting.
const CPIO_ENTRIES_MAX: usize = 1 << 16;
/// Longest name a container header spells that the identity quotes.
const NAME_MAX: usize = 64;
/// The reflected CRC-32 polynomial (IEEE 802.3), as zip, xz, 7z and
/// U-Boot use it.
const CRC32_POLY: u32 = 0xedb8_8320;

/// What an embedded region is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Kind {
    /// A PE image: `MZ`, `e_lfanew`, `PE\0\0` and a known machine.
    Pe,
    /// An ELF image.
    Elf,
    /// A Mach-O image for one architecture.
    MachO,
    /// A fat Mach-O, one image per architecture.
    FatMachO,
    /// A zip archive, from its first local file header.
    Zip,
    /// A gzip stream.
    Gzip,
    /// An xz stream.
    Xz,
    /// A 7z archive.
    SevenZip,
    /// A Microsoft cabinet.
    Cab,
    /// A squashfs 4 filesystem image.
    Squashfs,
    /// A cpio archive in the `newc` format.
    Cpio,
    /// A U-Boot legacy image.
    UImage,
    /// A cramfs filesystem image.
    Cramfs,
    /// An Android boot image.
    AndroidBoot,
}

impl Kind {
    /// The short name the listing's `kind` column spells.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Kind::Pe => "pe",
            Kind::Elf => "elf",
            Kind::MachO => "macho",
            Kind::FatMachO => "fat-macho",
            Kind::Zip => "zip",
            Kind::Gzip => "gzip",
            Kind::Xz => "xz",
            Kind::SevenZip => "7z",
            Kind::Cab => "cab",
            Kind::Squashfs => "squashfs",
            Kind::Cpio => "cpio",
            Kind::UImage => "uimage",
            Kind::Cramfs => "cramfs",
            Kind::AndroidBoot => "android-boot",
        }
    }

    /// Tells whether the loader can open the region as a program.
    #[must_use]
    pub fn is_program(self) -> bool {
        match self {
            Kind::Pe | Kind::Elf | Kind::MachO | Kind::FatMachO => true,
            Kind::Zip
            | Kind::Gzip
            | Kind::Xz
            | Kind::SevenZip
            | Kind::Cab
            | Kind::Squashfs
            | Kind::Cpio
            | Kind::UImage
            | Kind::Cramfs
            | Kind::AndroidBoot => false,
        }
    }
}

/// How many bytes an embedded region spans.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Size {
    /// The headers state it (the end of the last section, segment or
    /// record), cut at the end of the file.
    Stated(u64),
    /// No header states it (a gzip stream ends where its deflate data
    /// does), so it is the high-entropy run that opens at the header.
    Run(u64),
    /// No header states it and no high-entropy run opens at the header.
    Unknown,
}

impl Size {
    /// The size as the listing's `size` column spells it: hex, `~hex` for
    /// one read off an entropy run, `-` for none.
    #[must_use]
    pub fn shown(self) -> String {
        match self {
            Size::Stated(n) => format!("{n:#x}"),
            Size::Run(n) => format!("~{n:#x}"),
            Size::Unknown => "-".to_owned(),
        }
    }
}

/// One embedded program or container.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Child {
    /// File offset of its first byte.
    pub off: u64,
    /// How many bytes it spans.
    pub size: Size,
    /// What it is.
    pub kind: Kind,
    /// One line naming it: the architecture and type of a program, the
    /// entry count or name of a container.
    pub identity: String,
}

/// What a format's check says of the bytes at a candidate offset.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Found {
    /// What it is.
    kind: Kind,
    /// The bytes its headers state it spans, `None` when they state none.
    len: Option<u64>,
    /// One line naming it.
    identity: String,
}

/// Reads a little-endian `u16`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn le16(b: &[u8], at: usize) -> Option<u16> {
    Some(u16::from_le_bytes(*b.get(at..)?.first_chunk::<2>()?))
}

/// Reads a little-endian `u32`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn le32(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(*b.get(at..)?.first_chunk::<4>()?))
}

/// Reads a little-endian `u64`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn le64(b: &[u8], at: usize) -> Option<u64> {
    Some(u64::from_le_bytes(*b.get(at..)?.first_chunk::<8>()?))
}

/// Reads a big-endian `u32`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn be32(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_be_bytes(*b.get(at..)?.first_chunk::<4>()?))
}

/// Reads a `u32` in the byte order a header states.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
/// * `big` - Whether the order is big-endian.
fn u32_in(b: &[u8], at: usize, big: bool) -> Option<u32> {
    if big { be32(b, at) } else { le32(b, at) }
}

/// Reads a `u64` in the byte order a header states.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
/// * `big` - Whether the order is big-endian.
fn u64_in(b: &[u8], at: usize, big: bool) -> Option<u64> {
    let raw = *b.get(at..)?.first_chunk::<8>()?;
    Some(if big {
        u64::from_be_bytes(raw)
    } else {
        u64::from_le_bytes(raw)
    })
}

/// Reads a `u16` in the byte order a header states.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
/// * `big` - Whether the order is big-endian.
fn u16_in(b: &[u8], at: usize, big: bool) -> Option<u16> {
    let raw = *b.get(at..)?.first_chunk::<2>()?;
    Some(if big {
        u16::from_be_bytes(raw)
    } else {
        u16::from_le_bytes(raw)
    })
}

/// The CRC-32 zip, xz, 7z and U-Boot headers carry, over `data`.
///
/// # Arguments
///
/// * `data` - The bytes the CRC covers.
#[must_use]
fn crc32(data: &[u8]) -> u32 {
    let mut crc = u32::MAX;
    for &byte in data {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (CRC32_POLY & (crc & 1).wrapping_neg());
        }
    }
    !crc
}

/// A NUL-terminated or NUL-padded name in a header, quoted, or `None` when
/// it is empty or not printable text.
///
/// # Arguments
///
/// * `raw` - The field's bytes.
fn header_name(raw: &[u8]) -> Option<String> {
    let end = raw.iter().position(|c| *c == 0).unwrap_or(raw.len());
    let name = raw.get(..end.min(NAME_MAX))?;
    (!name.is_empty() && name.iter().all(|c| (0x20..0x7f).contains(c)))
        .then(|| quoted(&String::from_utf8_lossy(name)))
}

/// `s` when `n` is not one, for a count's noun.
///
/// # Arguments
///
/// * `n` - The count.
fn plural(n: u64) -> &'static str {
    if n == 1 { "" } else { "s" }
}

/// Bytes a count of `page`-byte pages covers when `len` bytes are rounded
/// up to whole pages.
///
/// # Arguments
///
/// * `len` - The bytes.
/// * `page` - The page size, non-zero.
fn pages(len: u32, page: u64) -> u64 {
    u64::from(len).div_ceil(page).saturating_mul(page)
}

// ---- programs ----

/// Checks a PE header at the start of `b`.
///
/// `MZ`, then `e_lfanew` leading to `PE\0\0` within [`PE_HEADER_MAX`], a
/// known machine, one to [`PE_SECTIONS_MAX`] sections and an optional
/// header of the PE32 or PE32+ magic large enough to hold its fixed
/// fields. The size is the furthest a section's file bytes, the headers or
/// the certificate table reach.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn pe(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"MZ") {
        return None;
    }
    let at = usize::try_from(le32(b, 0x3c)?).ok()?;
    if at > PE_HEADER_MAX || b.get(at..at + 4)? != b"PE\0\0" {
        return None;
    }
    let machine = match le16(b, at + 4)? {
        0x14c => "x86",
        0x8664 => "x86-64",
        0xaa64 => "arm64",
        0x1c0 | 0x1c2 | 0x1c4 => "arm",
        0x200 => "ia64",
        0xebc => "efi-bytecode",
        _ => return None,
    };
    let sections = usize::from(le16(b, at + 6)?);
    if !(1..=PE_SECTIONS_MAX).contains(&sections) {
        return None;
    }
    let opt_size = usize::from(le16(b, at + 20)?);
    let dll = le16(b, at + 22)? & 0x2000 != 0;
    let opt = at + 24;
    // SPEC: PE32's fixed fields end at 96 bytes and PE32+'s at 112, where
    // the data directory count and the directories follow.
    let (bits, fixed) = match le16(b, opt)? {
        0x10b => ("PE32", 96),
        0x20b => ("PE32+", 112),
        _ => return None,
    };
    if opt_size < fixed {
        return None;
    }
    let mut end = u64::from(le32(b, opt + 60)?);
    let table = opt + opt_size;
    for k in 0..sections {
        let row = table + 40 * k;
        let raw_size = le32(b, row + 16)?;
        if raw_size > 0 {
            end = end.max(u64::from(le32(b, row + 20)?) + u64::from(raw_size));
        }
    }
    // SPEC: the certificate table is directory 4, and its address is a
    // file offset; it trails the sections in a signed image.
    if le32(b, opt + fixed - 4).is_some_and(|count| count > 4)
        && let (Some(cert), Some(cert_size)) =
            (le32(b, opt + fixed + 32), le32(b, opt + fixed + 36))
        && cert > 0
        && cert_size > 0
    {
        end = end.max(u64::from(cert) + u64::from(cert_size));
    }
    let subsystem = match le16(b, opt + 68)? {
        1 => ", native",
        2 => ", gui",
        3 => ", console",
        10..=13 => ", efi",
        _ => "",
    };
    let role = if dll {
        "dll"
    } else if subsystem == ", native" {
        "driver"
    } else {
        "exe"
    };
    let n = from_usize(sections);
    Some(Found {
        kind: Kind::Pe,
        len: Some(end),
        identity: format!(
            "{bits} {machine} {role}{subsystem}, {n} section{}",
            plural(n)
        ),
    })
}

/// Checks an ELF header at the start of `b`.
///
/// The class, byte order and version bytes, a type from relocatable to
/// core, `e_version` one and the header size the class states. The size is
/// the furthest the program headers, the section headers, a segment's or a
/// section's file bytes reach.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn elf(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"\x7fELF") {
        return None;
    }
    let wide = match b.get(4)? {
        1 => false,
        2 => true,
        _ => return None,
    };
    let big = match b.get(5)? {
        1 => false,
        2 => true,
        _ => return None,
    };
    if *b.get(6)? != 1 || u32_in(b, 20, big)? != 1 {
        return None;
    }
    let kind = match u16_in(b, 16, big)? {
        1 => "relocatable",
        2 => "executable",
        3 => "shared object",
        4 => "core",
        _ => return None,
    };
    let machine = match u16_in(b, 18, big)? {
        2 | 0x2b => "sparc".to_owned(),
        3 => "x86".to_owned(),
        8 => "mips".to_owned(),
        0x14 => "ppc".to_owned(),
        0x15 => "ppc64".to_owned(),
        0x16 => "s390".to_owned(),
        0x28 => "arm".to_owned(),
        0x3e => "x86-64".to_owned(),
        0xb7 => "arm64".to_owned(),
        0xf3 => "riscv".to_owned(),
        other => format!("machine {other:#x}"),
    };
    // SPEC: the ELF32 and ELF64 header layouts (System V gABI 4.1).
    let (word, ehsize, phent, shent) = if wide {
        (8usize, 64u16, 56u16, 64u16)
    } else {
        (4, 52, 32, 40)
    };
    let field = |at: usize| -> Option<u64> {
        if wide {
            u64_in(b, at, big)
        } else {
            u32_in(b, at, big).map(u64::from)
        }
    };
    let phoff = field(24 + word)?;
    let shoff = field(24 + 2 * word)?;
    let tail = 28 + 3 * word;
    if u16_in(b, tail, big)? != ehsize {
        return None;
    }
    let phnum = u16_in(b, tail + 4, big)?;
    let shnum = u16_in(b, tail + 8, big)?;
    if (phnum > 0 && u16_in(b, tail + 2, big)? != phent)
        || (shnum > 0 && u16_in(b, tail + 6, big)? != shent)
    {
        return None;
    }
    let mut end = u64::from(ehsize)
        .max(phoff.saturating_add(u64::from(phnum) * u64::from(phent)))
        .max(shoff.saturating_add(u64::from(shnum) * u64::from(shent)));
    let at = |table: u64, k: u64, entry: u16, field_at: u64| {
        table
            .checked_add(k * u64::from(entry) + field_at)
            .and_then(|r| usize::try_from(r).ok())
    };
    // SPEC: p_offset and p_filesz sit at 4 and 16 of an ELF32 program
    // header, at 8 and 32 of an ELF64 one.
    let (off_at, size_at) = if wide { (8, 32) } else { (4, 16) };
    for k in 0..u64::from(phnum) {
        let (Some(off), Some(size)) = (
            at(phoff, k, phent, off_at).and_then(field),
            at(phoff, k, phent, size_at).and_then(field),
        ) else {
            break;
        };
        end = end.max(off.saturating_add(size));
    }
    // SPEC: sh_type at 4; sh_offset and sh_size at 16 and 20 (ELF32), 24
    // and 32 (ELF64). `SHT_NOBITS` (8) holds no file bytes.
    let (off_at, size_at) = if wide { (24, 32) } else { (16, 20) };
    for k in 0..u64::from(shnum) {
        let (Some(kind), Some(off), Some(size)) = (
            at(shoff, k, shent, 4).and_then(|r| u32_in(b, r, big)),
            at(shoff, k, shent, off_at).and_then(field),
            at(shoff, k, shent, size_at).and_then(field),
        ) else {
            break;
        };
        if kind != 8 {
            end = end.max(off.saturating_add(size));
        }
    }
    let class = if wide { "ELF64" } else { "ELF32" };
    let order = if big { "big-endian" } else { "little-endian" };
    let n = u64::from(shnum);
    Some(Found {
        kind: Kind::Elf,
        len: Some(end),
        identity: format!(
            "{class} {machine} {kind} ({order}), {n} section{}",
            plural(n)
        ),
    })
}

/// Names a Mach-O CPU type, or `None` for one borer does not know.
///
/// # Arguments
///
/// * `cpu` - The `cputype` field.
fn macho_cpu(cpu: u32) -> Option<&'static str> {
    match cpu {
        7 => Some("x86"),
        0x0100_0007 => Some("x86-64"),
        12 => Some("arm"),
        0x0100_000c => Some("arm64"),
        0x0200_000c => Some("arm64_32"),
        18 => Some("ppc"),
        0x0100_0012 => Some("ppc64"),
        _ => None,
    }
}

/// Checks a single-architecture Mach-O header at the start of `b`.
///
/// Either magic in either byte order, a known CPU, a file type from object
/// to kext and one to [`MACHO_COMMANDS_MAX`] load commands that fit the
/// bytes. The size is the furthest a segment's file bytes reach.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn macho(b: &[u8]) -> Option<Found> {
    let (wide, big) = match be32(b, 0)? {
        0xfeed_face => (false, true),
        0xfeed_facf => (true, true),
        0xcefa_edfe => (false, false),
        0xcffa_edfe => (true, false),
        _ => return None,
    };
    let cpu = macho_cpu(u32_in(b, 4, big)?)?;
    let kind = match u32_in(b, 12, big)? {
        1 => "object".to_owned(),
        2 => "execute".to_owned(),
        6 => "dylib".to_owned(),
        7 => "dylinker".to_owned(),
        8 => "bundle".to_owned(),
        other @ (3..=5 | 9..=12) => format!("file type {other}"),
        _ => return None,
    };
    let commands = u32_in(b, 16, big)?;
    let header = if wide { 32usize } else { 28 };
    let room = usize::try_from(u32_in(b, 20, big)?).ok()?;
    if commands == 0 || commands > MACHO_COMMANDS_MAX || b.len() < header.checked_add(room)? {
        return None;
    }
    let mut end = from_usize(header + room);
    let mut at = header;
    for _ in 0..commands {
        let (Some(cmd), Some(size)) = (u32_in(b, at, big), u32_in(b, at + 4, big)) else {
            return None;
        };
        let size = usize::try_from(size).ok()?;
        if size < 8 || at.saturating_add(size) > header + room {
            return None;
        }
        // SPEC: LC_SEGMENT (1) carries fileoff and filesize as u32 at 32 and
        // 36; LC_SEGMENT_64 (0x19) as u64 at 40 and 48.
        let span = match cmd {
            1 => u32_in(b, at + 32, big)
                .zip(u32_in(b, at + 36, big))
                .map(|(o, s)| u64::from(o) + u64::from(s)),
            0x19 => u64_in(b, at + 40, big)
                .zip(u64_in(b, at + 48, big))
                .map(|(o, s)| o.saturating_add(s)),
            _ => None,
        };
        end = end.max(span.unwrap_or(0));
        at += size;
    }
    let bits = if wide { "64" } else { "32" };
    let n = u64::from(commands);
    Some(Found {
        kind: Kind::MachO,
        len: Some(end),
        identity: format!("Mach-O {bits} {cpu} {kind}, {n} load command{}", plural(n)),
    })
}

/// Checks a fat Mach-O header at the start of `b`.
///
/// `cafebabe` (which a Java class file shares), one to
/// [`FAT_SLICES_MAX`] slices, each of a known CPU whose bytes open with a
/// Mach-O magic, which no class file has. The size is the furthest a slice
/// reaches.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn fat_macho(b: &[u8]) -> Option<Found> {
    if be32(b, 0)? != 0xcafe_babe {
        return None;
    }
    let count = be32(b, 4)?;
    if count == 0 || count > FAT_SLICES_MAX {
        return None;
    }
    let mut end = 0u64;
    let mut cpus = Vec::new();
    for k in 0..usize::try_from(count).ok()? {
        let row = 8 + 20 * k;
        let cpu = macho_cpu(be32(b, row)?)?;
        let off = be32(b, row + 8)?;
        let size = be32(b, row + 12)?;
        let magic = be32(b, usize::try_from(off).ok()?)?;
        if !matches!(magic, 0xfeed_face | 0xfeed_facf | 0xcefa_edfe | 0xcffa_edfe) {
            return None;
        }
        end = end.max(u64::from(off) + u64::from(size));
        cpus.push(cpu);
    }
    let n = u64::from(count);
    Some(Found {
        kind: Kind::FatMachO,
        len: Some(end),
        identity: format!("fat Mach-O, {n} slice{} ({})", plural(n), cpus.join(", ")),
    })
}

// ---- containers ----

/// Checks a zip local file header at the start of `b`, and looks forward
/// for the end of central directory record that closes the archive.
///
/// The header's version, compression method and name are checked; the end
/// record counts when its central directory ends where the record starts,
/// its offset counted from the archive's start or, as a self-extractor
/// writes it, from the file's. Without one the archive is a fragment,
/// listed with no size.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
/// * `start` - The candidate's file offset, for an offset counted from
///   the file's start.
/// * `fuel` - The scan's search budget, spent here.
fn zip(b: &[u8], start: usize, fuel: &mut usize) -> Option<Found> {
    if !b.starts_with(b"PK\x03\x04") || *b.get(4)? > 63 {
        return None;
    }
    // SPEC: APPNOTE.TXT 4.4.5's compression methods.
    if !matches!(
        le16(b, 8)?,
        0..=6 | 8 | 9 | 12 | 14 | 18 | 19 | 93 | 95..=99
    ) {
        return None;
    }
    let name_len = usize::from(le16(b, 26)?);
    let name = b.get(30..30 + name_len)?;
    if name_len == 0 || name.contains(&0) {
        return None;
    }
    let first = header_name(name).unwrap_or_else(|| "a name that is not text".to_owned());
    let mut at = 30 + name_len;
    let close = loop {
        let window = b.get(at..)?;
        let budget = window.len().min(*fuel);
        let Some(hit) = window
            .get(..budget)?
            .windows(4)
            .position(|w| w == b"PK\x05\x06")
        else {
            *fuel -= budget;
            break None;
        };
        *fuel -= hit + 4;
        let eocd = at + hit;
        let entries = le16(b, eocd + 10);
        let cd_size = le32(b, eocd + 12).and_then(|v| usize::try_from(v).ok());
        let cd_off = le32(b, eocd + 16).and_then(|v| usize::try_from(v).ok());
        let comment = le16(b, eocd + 20).map(usize::from);
        if let (Some(entries), Some(cd_size), Some(cd_off), Some(comment)) =
            (entries, cd_size, cd_off, comment)
            && let Some(cd_start) = eocd.checked_sub(cd_size)
            && (cd_start == cd_off || Some(cd_start) == cd_off.checked_sub(start))
        {
            break Some((eocd + 22 + comment, entries));
        }
        at = eocd + 4;
    };
    Some(match close {
        Some((len, entries)) => {
            let n = u64::from(entries);
            Found {
                kind: Kind::Zip,
                len: Some(from_usize(len)),
                identity: format!(
                    "zip archive, {n} entr{}, first {first}",
                    if n == 1 { "y" } else { "ies" }
                ),
            }
        }
        None => Found {
            kind: Kind::Zip,
            len: None,
            identity: format!(
                "zip local header {first} with no end record after it: a fragment or a truncated archive"
            ),
        },
    })
}

/// Checks a gzip header at the start of `b`.
///
/// Deflate as the method, no reserved flag set, a known extra-flags value
/// and operating system, and a first deflate block of a defined type. The
/// stream states no compressed length, so none is given.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn gzip(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"\x1f\x8b\x08") {
        return None;
    }
    let flags = *b.get(3)?;
    if flags & 0xe0 != 0 || !matches!(b.get(8)?, 0 | 2 | 4) || !matches!(b.get(9)?, 0..=13 | 255) {
        return None;
    }
    // SPEC: RFC 1952 2.3: FEXTRA (4) carries a length-prefixed field, FNAME
    // (8) and FCOMMENT (16) NUL-terminated text, FHCRC (2) two bytes.
    let mut at = 10usize;
    if flags & 4 != 0 {
        at += 2 + usize::from(le16(b, at)?);
    }
    let mut name = None;
    if flags & 8 != 0 {
        let len = b.get(at..)?.iter().position(|c| *c == 0)?;
        name = header_name(b.get(at..at + len)?);
        at += len + 1;
    }
    if flags & 16 != 0 {
        at += b.get(at..)?.iter().position(|c| *c == 0)? + 1;
    }
    if flags & 2 != 0 {
        at += 2;
    }
    // SPEC: RFC 1951 3.2.3: BTYPE 3 is reserved.
    if (b.get(at)? >> 1) & 3 == 3 {
        return None;
    }
    Some(Found {
        kind: Kind::Gzip,
        len: None,
        identity: match name {
            Some(n) => format!("gzip stream (deflate) of {n}"),
            None => "gzip stream (deflate)".to_owned(),
        },
    })
}

/// Checks an xz stream header at the start of `b` by its CRC, and looks
/// forward for the stream footer whose flags and CRC match it.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
/// * `fuel` - The scan's search budget, spent here.
fn xz(b: &[u8], fuel: &mut usize) -> Option<Found> {
    if !b.starts_with(b"\xfd7zXZ\x00") {
        return None;
    }
    let flags = b.get(6..8)?;
    if flags[0] != 0 || flags[1] & 0xf0 != 0 || le32(b, 8)? != crc32(flags) {
        return None;
    }
    let check = match flags[1] {
        0 => "no check",
        1 => "crc32",
        4 => "crc64",
        10 => "sha-256",
        _ => "a reserved check",
    };
    // SPEC: the 12-byte footer is CRC32, backward size, the header's flags
    // and `YZ`; its CRC covers the backward size and the flags.
    let mut at = 12usize;
    let end = loop {
        let window = b.get(at..)?;
        let budget = window.len().min(*fuel);
        let Some(hit) = window.get(..budget)?.windows(2).position(|w| w == b"YZ") else {
            *fuel -= budget;
            break None;
        };
        *fuel -= hit + 2;
        let yz = at + hit;
        if let Some(footer) = yz.checked_sub(10).and_then(|f| b.get(f..yz + 2))
            && yz >= 22
            && footer.get(8..10) == Some(flags)
            && le32(footer, 0) == footer.get(4..10).map(crc32)
        {
            break Some(yz + 2);
        }
        at = yz + 2;
    };
    Some(Found {
        kind: Kind::Xz,
        len: end.map(from_usize),
        identity: match end {
            Some(_) => format!("xz stream, {check}"),
            None => format!("xz stream, {check}, no footer found"),
        },
    })
}

/// Checks a 7z signature header at the start of `b` by its start header
/// CRC; the size is the next header's end.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn seven_zip(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"7z\xbc\xaf\x27\x1c") || *b.get(6)? != 0 {
        return None;
    }
    if le32(b, 8)? != crc32(b.get(12..32)?) {
        return None;
    }
    let len = le64(b, 12)?.checked_add(le64(b, 20)?)?.checked_add(32)?;
    Some(Found {
        kind: Kind::SevenZip,
        len: Some(len),
        identity: format!("7z archive, format 0.{}", b.get(7)?),
    })
}

/// Checks a cabinet header at the start of `b`: zero reserved fields,
/// version 1.3, at least one folder and one file, and a file table inside
/// the stated size.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn cab(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"MSCF") {
        return None;
    }
    let size = le32(b, 8)?;
    if le32(b, 4)? != 0
        || le32(b, 12)? != 0
        || le32(b, 20)? != 0
        || le32(b, 16)? >= size
        || b.get(24..26)? != [3, 1]
    {
        return None;
    }
    let folders = u64::from(le16(b, 26)?);
    let files = u64::from(le16(b, 28)?);
    if folders == 0 || files == 0 {
        return None;
    }
    Some(Found {
        kind: Kind::Cab,
        len: Some(u64::from(size)),
        identity: format!(
            "cabinet, {files} file{} in {folders} folder{}",
            plural(files),
            plural(folders)
        ),
    })
}

/// Checks a squashfs 4.0 superblock at the start of `b`: the block size a
/// power of two from 4 KiB to 1 MiB that the block log states, a known
/// compressor; the size is `bytes_used`.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn squashfs(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"hsqs") || le16(b, 28)? != 4 || le16(b, 30)? != 0 {
        return None;
    }
    let block = le32(b, 12)?;
    if !block.is_power_of_two()
        || !(0x1000..=0x10_0000).contains(&block)
        || u32::from(le16(b, 22)?) != block.trailing_zeros()
    {
        return None;
    }
    let compressor = match le16(b, 20)? {
        1 => "gzip",
        2 => "lzma",
        3 => "lzo",
        4 => "xz",
        5 => "lz4",
        6 => "zstd",
        _ => return None,
    };
    let inodes = u64::from(le32(b, 4)?);
    Some(Found {
        kind: Kind::Squashfs,
        len: Some(le64(b, 40)?),
        identity: format!(
            "squashfs 4.0, {compressor}, {inodes} inode{}, {} KiB blocks",
            plural(inodes),
            block >> 10
        ),
    })
}

/// Reads one `newc` cpio header at the start of `b`.
///
/// # Arguments
///
/// * `b` - The bytes from the header.
///
/// # Returns
///
/// The entry's name and the bytes to the next header (header, name and
/// data, each padded to four), or `None` when the header is not one.
fn cpio_entry(b: &[u8]) -> Option<(&[u8], usize)> {
    if !(b.starts_with(b"070701") || b.starts_with(b"070702")) {
        return None;
    }
    let field = |k: usize| -> Option<usize> {
        let text = std::str::from_utf8(b.get(6 + 8 * k..14 + 8 * k)?).ok()?;
        usize::from_str_radix(text, 16).ok()
    };
    // SPEC: the 13 fields are eight hex digits each; filesize is the 7th
    // and namesize the 12th, the name counting its NUL.
    let size = field(6)?;
    let name_size = field(11)?;
    for k in 0..13 {
        field(k)?;
    }
    let name = b.get(110..110usize.checked_add(name_size)?)?;
    let (last, text) = name.split_last()?;
    if *last != 0 || text.is_empty() || text.contains(&0) {
        return None;
    }
    let data = (110 + name_size).next_multiple_of(4);
    Some((text, data.checked_add(size)?.checked_next_multiple_of(4)?))
}

/// Checks a `newc` cpio archive at the start of `b` and walks its entries
/// to the `TRAILER!!!` that ends it.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
/// * `fuel` - The scan's search budget, spent here.
fn cpio(b: &[u8], fuel: &mut usize) -> Option<Found> {
    let (first, _) = cpio_entry(b)?;
    let first = header_name(first).unwrap_or_else(|| "a name that is not text".to_owned());
    let mut at = 0usize;
    let mut entries = 0u64;
    let end = loop {
        let Some((name, step)) = b.get(at..).and_then(cpio_entry) else {
            break None;
        };
        if step > *fuel || entries >= from_usize(CPIO_ENTRIES_MAX) {
            break None;
        }
        *fuel -= step;
        let Some(next) = at.checked_add(step) else {
            break None;
        };
        at = next;
        if name == b"TRAILER!!!" {
            break Some(at);
        }
        entries += 1;
    };
    Some(Found {
        kind: Kind::Cpio,
        len: end.map(from_usize),
        identity: match end {
            Some(_) => format!(
                "cpio archive (newc), {entries} entr{}, first {first}",
                if entries == 1 { "y" } else { "ies" }
            ),
            None => format!("cpio archive (newc), first {first}, no trailer found"),
        },
    })
}

/// Checks a U-Boot legacy image header at the start of `b` by its header
/// CRC; the size is the header and the payload it states.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn uimage(b: &[u8]) -> Option<Found> {
    if be32(b, 0)? != 0x2705_1956 {
        return None;
    }
    let mut header = *b.first_chunk::<64>()?;
    header[4..8].fill(0);
    if be32(b, 4)? != crc32(&header) {
        return None;
    }
    // SPEC: U-Boot's include/image.h: IH_ARCH_*, IH_TYPE_*, IH_COMP_*.
    let arch = match b.get(29)? {
        2 => "arm".to_owned(),
        3 => "x86".to_owned(),
        5 => "mips".to_owned(),
        7 => "ppc".to_owned(),
        22 => "arm64".to_owned(),
        24 => "x86-64".to_owned(),
        26 => "riscv".to_owned(),
        other => format!("arch {other}"),
    };
    let kind = match b.get(30)? {
        1 => "standalone program".to_owned(),
        2 => "kernel".to_owned(),
        3 => "ramdisk".to_owned(),
        4 => "multi-file image".to_owned(),
        5 => "firmware".to_owned(),
        6 => "script".to_owned(),
        7 => "filesystem".to_owned(),
        8 => "device tree".to_owned(),
        other => format!("type {other}"),
    };
    let comp = match b.get(31)? {
        0 => "uncompressed".to_owned(),
        1 => "gzip".to_owned(),
        2 => "bzip2".to_owned(),
        3 => "lzma".to_owned(),
        4 => "lzo".to_owned(),
        5 => "lz4".to_owned(),
        6 => "zstd".to_owned(),
        other => format!("compression {other}"),
    };
    let name = header_name(b.get(32..64)?).map_or_else(String::new, |n| format!(" {n}"));
    Some(Found {
        kind: Kind::UImage,
        len: Some(u64::from(be32(b, 12)?) + 64),
        identity: format!("uImage{name}, {arch} {kind}, {comp}"),
    })
}

/// Checks a cramfs superblock at the start of `b`, in either byte order:
/// the magic and the `Compressed ROMFS` signature; the size is the one it
/// states.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn cramfs(b: &[u8]) -> Option<Found> {
    let big = match le32(b, 0)? {
        0x28cd_3d45 => false,
        0x453d_cd28 => true,
        _ => return None,
    };
    if b.get(16..32)? != b"Compressed ROMFS" {
        return None;
    }
    let files = u64::from(u32_in(b, 44, big)?);
    let name = header_name(b.get(48..64)?).map_or_else(String::new, |n| format!(" {n}"));
    Some(Found {
        kind: Kind::Cramfs,
        len: Some(u64::from(u32_in(b, 4, big)?)),
        identity: format!("cramfs{name}, {files} file{}", plural(files)),
    })
}

/// Checks an Android boot image header at the start of `b`.
///
/// A header version from 0 to 4 and, before version 3, a page size that is
/// a power of two from 2 KiB to 64 KiB. The size is the header page and the
/// pages of every part the version lists.
///
/// # Arguments
///
/// * `b` - The bytes from the candidate offset.
fn android_boot(b: &[u8]) -> Option<Found> {
    if !b.starts_with(b"ANDROID!") {
        return None;
    }
    let version = le32(b, 40)?;
    let kernel = le32(b, 8)?;
    // SPEC: AOSP's bootimg.h: versions 0 to 2 keep the page size at 36 and
    // the ramdisk size at 16; 1 adds the recovery dtbo at 1632 and 2 the
    // dtb at 1648; 3 and 4 fix the page at 4096 with the ramdisk size at
    // 12, and 4 adds a signature whose size sits at 1580.
    let (page, parts) = match version {
        0..=2 => {
            let page = le32(b, 36)?;
            if !page.is_power_of_two() || !(0x800..=0x1_0000).contains(&page) {
                return None;
            }
            let mut parts = vec![kernel, le32(b, 16)?, le32(b, 24)?];
            if version >= 1 {
                parts.push(le32(b, 1632)?);
            }
            if version == 2 {
                parts.push(le32(b, 1648)?);
            }
            (u64::from(page), parts)
        }
        3 | 4 => {
            let mut parts = vec![kernel, le32(b, 12)?];
            if version == 4 {
                parts.push(le32(b, 1580)?);
            }
            (4096, parts)
        }
        _ => return None,
    };
    let len = parts
        .iter()
        .fold(page, |sum, part| sum.saturating_add(pages(*part, page)));
    let ramdisk = parts.get(1).copied().unwrap_or(0);
    Some(Found {
        kind: Kind::AndroidBoot,
        len: Some(len),
        identity: format!(
            "Android boot image v{version}, kernel {kernel:#x} bytes, ramdisk {ramdisk:#x} bytes, page {page:#x}"
        ),
    })
}

// ---- scanning ----

/// Runs every format's check at one offset.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `off` - The candidate offset.
/// * `fuel` - The scan's search budget.
///
/// # Returns
///
/// What starts there, its size cut at the end of the file with the cut
/// said in the identity, or `None` when no check passes.
fn check_at(bytes: &[u8], off: usize, fuel: &mut usize) -> Option<Child> {
    let b = bytes.get(off..)?;
    let found = match *b.first()? {
        b'M' => pe(b).or_else(|| cab(b)),
        0x7f => elf(b),
        0xfe | 0xce | 0xcf => macho(b),
        0xca => fat_macho(b),
        b'P' => zip(b, off, fuel),
        0x1f => gzip(b),
        0xfd => xz(b, fuel),
        b'7' => seven_zip(b),
        b'h' => squashfs(b),
        b'0' => cpio(b, fuel),
        0x27 => uimage(b),
        0x45 | 0x28 => cramfs(b),
        b'A' => android_boot(b),
        _ => None,
    }?;
    let left = from_usize(b.len());
    let (size, identity) = match found.len {
        Some(len) if len > left => (
            Size::Stated(left),
            format!(
                "{}; truncated: the headers state {len:#x} bytes and {left:#x} remain",
                found.identity
            ),
        ),
        Some(len) => (Size::Stated(len), found.identity),
        None => (Size::Unknown, found.identity),
    };
    Some(Child {
        off: from_usize(off),
        size,
        kind: found.kind,
        identity,
    })
}

/// Finds the program or container that starts at one file offset.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `off` - The file offset.
///
/// # Returns
///
/// What starts there, or `None` when nothing validates at that offset.
#[must_use]
pub fn at(bytes: &[u8], off: u64) -> Option<Child> {
    let mut fuel = SEARCH_FUEL;
    check_at(bytes, usize::try_from(off).ok()?, &mut fuel)
}

/// Finds every embedded program and container in a file, in file order.
///
/// Every offset of the first [`SCAN_MAX`] bytes is tried; a container of
/// stated size (an archive, a filesystem image) is listed and its bytes
/// skipped, since what it holds is compressed or is its own business,
/// while a program's bytes are scanned on, since a resource or an overlay
/// inside it is where a dropper keeps its payload.
///
/// # Arguments
///
/// * `bytes` - The whole file.
///
/// # Returns
///
/// At most [`FOUND_MAX`] children, by offset.
#[must_use]
pub fn scan(bytes: &[u8]) -> Vec<Child> {
    let mut fuel = SEARCH_FUEL;
    let mut out = Vec::new();
    let end = bytes.len().min(SCAN_MAX);
    let mut off = 0usize;
    while off < end && out.len() < FOUND_MAX {
        let Some(child) = check_at(bytes, off, &mut fuel) else {
            off += 1;
            continue;
        };
        off = match child.size {
            Size::Stated(len) if !child.kind.is_program() && len > 0 => {
                off.saturating_add(saturating_usize(len))
            }
            Size::Stated(_) | Size::Run(_) | Size::Unknown => off + 1,
        };
        out.push(child);
    }
    out
}

/// One row of the listing: an embedded region or a high-entropy run no
/// header explains.
#[derive(Debug, Clone, PartialEq)]
enum Row {
    /// A program or container a header names.
    Child(Child),
    /// A run of high-entropy windows: its offset, length and mean entropy.
    Random(u64, u64, f64),
}

impl Row {
    /// The row's file offset, which orders the listing.
    fn off(&self) -> u64 {
        match self {
            Row::Child(c) => c.off,
            Row::Random(off, ..) => *off,
        }
    }
}

/// Lists the programs and containers a file holds, and the high-entropy
/// runs no header explains, as the `borer://children` answer.
///
/// The children come from [`scan`]; the loaded file itself, the program at
/// offset 0 of a file that loaded as one, is not its own child. The
/// entropy profile is [`crate::entropy::high_entropy_regions`] over
/// [`WINDOW`]-byte windows, at [`MARGIN`] under what random data reads at:
/// a run that opens at a stream whose header states no length (gzip) is
/// that stream's extent, read as `~size`; one inside a container is the
/// container's compressed data and not listed again; one in the
/// certificate table is the signature; any other is listed as `entropy`:
/// packed, compressed or encrypted bytes with no header to say which.
///
/// # Arguments
///
/// * `program` - The loaded file.
///
/// # Returns
///
/// A header saying what was found and how to open a program row, the
/// column names, then at most [`ROWS_SHOWN`] rows by offset under a
/// `# showing N of M` line when there are more.
#[must_use]
pub fn children_tsv(program: &Program) -> String {
    let bytes = &program.bytes;
    let mut children: Vec<Child> = scan(bytes)
        .into_iter()
        .filter(|c| c.off != 0 || program.format == BinaryFormat::Raw)
        .collect();
    let threshold = crate::entropy::ceiling(WINDOW) - MARGIN;
    let runs: Vec<(u64, u64, f64)> =
        crate::entropy::high_entropy_regions(program, WINDOW, threshold)
            .into_iter()
            .filter(|r| r.encoding.is_none())
            .map(|r| (r.off, r.len, r.entropy))
            .collect();
    let mut rows: Vec<Row> = Vec::new();
    for (off, len, entropy) in runs {
        let end = off.saturating_add(len);
        let window = from_usize(WINDOW);
        if let Some(c) = children.iter_mut().find(|c| {
            c.size == Size::Unknown
                && c.off.saturating_add(window) > off
                && c.off < off.saturating_add(window).min(end)
        }) {
            c.size = Size::Run(end - c.off);
            continue;
        }
        let inside = children.iter().any(|c| {
            !c.kind.is_program()
                && match c.size {
                    Size::Stated(n) | Size::Run(n) => {
                        c.off <= off && end <= c.off.saturating_add(n)
                    }
                    Size::Unknown => false,
                }
        });
        let signature = program
            .headers
            .certificates
            .is_some_and(|(c, n)| c <= off && end <= c.saturating_add(n));
        if !inside && !signature {
            rows.push(Row::Random(off, len, entropy));
        }
    }
    let found = children.len();
    let random = rows.len();
    rows.extend(children.into_iter().map(Row::Child));
    rows.sort_by_key(Row::off);
    let path = program.path.display();
    let mut out = format!(
        "# children of {path}: {found} program{} or container{} by signature, {random} high-entropy run{} with none\n# load_binary path={path}@<off> opens a program row as a program of its own; containers are listed, not extracted\n",
        plural(from_usize(found)),
        plural(from_usize(found)),
        plural(from_usize(random))
    );
    if bytes.len() > SCAN_MAX {
        let _ = writeln!(
            out,
            "# the signature scan read the first {SCAN_MAX:#x} of {:#x} bytes",
            bytes.len()
        );
    }
    if rows.len() > ROWS_SHOWN {
        let _ = writeln!(out, "# showing {ROWS_SHOWN} of {}", rows.len());
    }
    out.push_str("off\tsize\tkind\tidentity\n");
    for row in rows.iter().take(ROWS_SHOWN) {
        let _ = match row {
            Row::Child(c) => writeln!(
                out,
                "{:#x}\t{}\t{}\t{}",
                c.off,
                c.size.shown(),
                c.kind.name(),
                c.identity
            ),
            Row::Random(off, len, entropy) => writeln!(
                out,
                "{off:#x}\t{len:#x}\tentropy\t{entropy:.2} bits/byte and no header: packed, compressed or encrypted"
            ),
        };
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Kind, Size, at, crc32, scan};

    /// The CRC is the IEEE one zip and xz use: its check value over the
    /// nine ASCII digits.
    ///
    /// # Panics
    ///
    /// When the CRC is another.
    #[test]
    fn crc32_matches_the_check_value() {
        assert_eq!(crc32(b"123456789"), 0xcbf4_3926);
    }

    /// An xz header whose CRC holds is listed with its footer's extent; the
    /// same header with one bit of its CRC flipped is not.
    ///
    /// # Panics
    ///
    /// When the stream is not found or the forgery is.
    #[test]
    fn an_xz_stream_is_sized_by_its_footer_and_a_bad_crc_refused() {
        let flags = [0u8, 4];
        let mut stream = b"\xfd7zXZ\x00".to_vec();
        stream.extend_from_slice(&flags);
        stream.extend_from_slice(&crc32(&flags).to_le_bytes());
        stream.extend_from_slice(&[0x55; 40]);
        let backward = 7u32.to_le_bytes();
        let mut tail = backward.to_vec();
        tail.extend_from_slice(&flags);
        stream.extend_from_slice(&crc32(&tail).to_le_bytes());
        stream.extend_from_slice(&tail);
        stream.extend_from_slice(b"YZ");
        let mut file = vec![0u8; 16];
        file.extend_from_slice(&stream);
        file.extend_from_slice(&[0u8; 16]);
        let found = at(&file, 16).expect("the stream validates");
        assert_eq!(found.kind, Kind::Xz);
        assert_eq!(found.size, Size::Stated(64));
        assert!(found.identity.contains("crc64"), "{}", found.identity);
        file[16 + 8] ^= 1;
        assert!(scan(&file).is_empty());
    }
}
