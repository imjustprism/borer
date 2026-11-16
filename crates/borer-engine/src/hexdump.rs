//! Classic 16-bytes-per-row hexdump rendering.

use crate::num::from_usize;
use crate::program::BinaryFormat;

/// Renders `bytes` as a hexdump whose first byte sits at address `base`.
///
/// Each row is `address  hex-bytes |ascii|`; the ASCII column shows
/// non-printable bytes as `.`, so the text is safe to paste anywhere.
///
/// # Arguments
///
/// * `bytes` - The bytes to render, 16 per row.
/// * `base` - Virtual address of `bytes[0]`, printed as the row address.
///
/// # Returns
///
/// The rendered rows, each terminated by a newline; empty for empty input.
pub fn hexdump(bytes: &[u8], base: u64) -> String {
    let known: Vec<Option<u8>> = bytes.iter().copied().map(Some).collect();
    hexdump_sparse(&known, base)
}

/// Renders bytes some of which nothing backs as a hexdump whose first byte
/// sits at address `base`.
///
/// A known byte renders as [`hexdump`] renders it; an unknown one renders
/// as `??` in the hex column and a space in the ASCII column, so an
/// unmapped address never reads as a zero byte.
///
/// # Arguments
///
/// * `bytes` - The bytes to render, 16 per row, `None` where nothing backs
///   the address.
/// * `base` - Virtual address of `bytes[0]`, printed as the row address.
///
/// # Returns
///
/// The rendered rows, each terminated by a newline; empty for empty input.
pub fn hexdump_sparse(bytes: &[Option<u8>], base: u64) -> String {
    let mut out = String::with_capacity(bytes.len() / 16 * 80 + 80);
    for (row, chunk) in bytes.chunks(16).enumerate() {
        let addr = base.wrapping_add(from_usize(row * 16));
        let mut hexpart = String::with_capacity(49);
        for (i, b) in chunk.iter().enumerate() {
            if i == 8 {
                hexpart.push(' ');
            }
            match b {
                Some(b) => hexpart.push_str(&format!("{b:02x} ")),
                None => hexpart.push_str("?? "),
            }
        }
        let ascii: String = chunk
            .iter()
            .map(|b| match *b {
                Some(b) if (0x20..=0x7e).contains(&b) => b as char,
                Some(_) => '.',
                None => ' ',
            })
            .collect();
        out.push_str(&format!("{addr:#012x}  {hexpart:<49} |{ascii}|\n"));
    }
    out
}

/// Most bytes one hexdump shows.
pub const HEXDUMP_MAX: usize = 4096;

/// What backs one run of addresses in a hexdump.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HexFill {
    /// The bytes the file holds there.
    Bytes(Vec<u8>),
    /// Inside a section, but the file holds no bytes for it: a tail the
    /// loader fills with zeros, or a file cut short.
    Unbacked,
    /// No section and no header maps these addresses.
    Unmapped,
}

/// One run of a hexdump's addresses with one backing and one section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HexSpan {
    /// Address of the run's first byte.
    pub va: u64,
    /// Bytes in the run.
    pub len: usize,
    /// Name of the section holding the run; `None` for the headers or no
    /// section at all.
    pub section: Option<String>,
    /// What backs the run.
    pub fill: HexFill,
}

/// The addresses a hexdump asked for, as runs in address order that cover
/// them all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HexRows {
    /// Address of the first byte asked for.
    pub va: u64,
    /// The runs, each starting where the one before ends.
    pub spans: Vec<HexSpan>,
}

impl HexRows {
    /// Returns the dump as the `hexdump` tool and the CLI print it: the
    /// bytes of the first run, the file's bytes from `va` within its
    /// section.
    ///
    /// # Returns
    ///
    /// A `# va..end section` header covering those bytes, then their rows
    /// ([`hexdump`]); `None` when the file holds no bytes at `va`.
    #[must_use]
    pub fn spell(&self) -> Option<String> {
        let first = self.spans.first()?;
        let HexFill::Bytes(bytes) = &first.fill else {
            return None;
        };
        let sec = first
            .section
            .as_deref()
            .map_or_else(String::new, |s| format!(" {s}"));
        Some(format!(
            "# {:#x}..{:#x}{sec}\n{}",
            self.va,
            self.va.wrapping_add(from_usize(bytes.len())),
            hexdump(bytes, self.va)
        ))
    }
}

/// Returns the addresses from `va` as a hexdump's runs: the file's bytes
/// section by section, a section's addresses the file holds no bytes for,
/// and addresses nothing maps, each a run of its own.
///
/// A run the file holds no bytes for ends where any section, or a PE's
/// mapped headers, begins, so the bytes there are read as such.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Address of the first byte.
/// * `len` - Bytes asked for, at most [`HEXDUMP_MAX`]; the runs stop at
///   the top of the address space.
///
/// # Returns
///
/// The runs covering `va` onward.
#[must_use]
pub fn hex_rows(program: &crate::program::Program, va: u64, len: usize) -> HexRows {
    let end = va.saturating_add(from_usize(len.min(HEXDUMP_MAX)));
    let mut spans = Vec::new();
    let mut at = va;
    while at < end {
        let want = usize::try_from(end - at).unwrap_or(HEXDUMP_MAX);
        let found = program.section_at(at);
        let holding = found.or_else(|| program.zero_fill_at(at));
        let next = || {
            program
                .sections
                .iter()
                .map(|s| s.va.0)
                .chain((program.format == BinaryFormat::Pe).then_some(program.image_base))
                .filter(|&start| start > at)
                .fold(end, u64::min)
        };
        let (run, fill, section) = match (program.read_va_upto(at, want), holding) {
            (Some(bytes), _) => (
                from_usize(bytes.len()),
                HexFill::Bytes(bytes.to_vec()),
                found,
            ),
            (None, Some(s)) => (
                s.va.0
                    .saturating_add(s.vsize.max(s.file_size))
                    .min(next())
                    .saturating_sub(at),
                HexFill::Unbacked,
                Some(s),
            ),
            (None, None) => (next().saturating_sub(at), HexFill::Unmapped, None),
        };
        if run == 0 {
            break;
        }
        spans.push(HexSpan {
            va: at,
            len: usize::try_from(run).unwrap_or(HEXDUMP_MAX),
            section: section.map(|s| s.name.clone()),
            fill,
        });
        at = at.saturating_add(run);
    }
    HexRows { va, spans }
}

/// Renders up to `max` bytes of the file at a file offset, rows addressed
/// by file offset.
///
/// The dump of bytes no section maps (an overlay, the headers, a file with
/// no sections), which have no virtual address to dump them at. The header
/// says where the first byte loads when a section does map it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `off` - File offset of the first byte.
/// * `max` - Most bytes shown; the dump stops at the end of the file.
///
/// # Returns
///
/// The `# off` header line and the rows.
///
/// # Errors
///
/// When `off` is at or past the end of the file, naming the file's size.
pub fn file_hexdump(
    program: &crate::program::Program,
    off: u64,
    max: usize,
) -> Result<String, String> {
    let bytes = program.read_off_upto(off, max).ok_or_else(|| {
        format!(
            "file offset {off:#x} is past the end of the file ({:#x} bytes)",
            program.bytes.len()
        )
    })?;
    let mapped = program.offset_to_va(off).map_or_else(
        || "no section maps it".to_owned(),
        |va| format!("it loads at {va:#x}"),
    );
    Ok(format!(
        "# off {off:#x}..{:#x}, rows by file offset; {mapped}\n{}",
        off + from_usize(bytes.len()),
        hexdump(bytes, off)
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Arch, Program, Section};

    /// Builds a program of three sections: `.text` at 0x1000 and `.data`
    /// at 0x1010, each 16 file bytes and adjacent, then `.bss` at 0x1020,
    /// 16 bytes the file holds none of; nothing maps 0x1030 on.
    fn sections() -> (Vec<u8>, Program) {
        let bytes: Vec<u8> = (b'A'..b'A' + 0x20).collect();
        let mut bss = Section::mapped(".bss", 0x1020, 0x20, 0x10, true, false);
        bss.file_size = 0;
        let all = vec![
            Section::mapped(".text", 0x1000, 0, 0x10, false, true),
            Section::mapped(".data", 0x1010, 0x10, 0x10, true, false),
            bss,
        ];
        let p = Program::raw(bytes.clone(), Arch::X86_64, 0x1000, None, all);
        (bytes, p)
    }

    /// A range across adjacent sections holds every byte, each under its
    /// own section, and a section's addresses without file bytes and
    /// addresses nothing maps are runs of their own kinds.
    ///
    /// # Panics
    ///
    /// When a byte is missed, put under the wrong section, or a run's kind
    /// differs.
    #[test]
    fn hex_rows_read_across_sections() {
        let (bytes, p) = sections();
        let span = |va: u64, len: usize, section: Option<&str>, fill: HexFill| HexSpan {
            va,
            len,
            section: section.map(str::to_owned),
            fill,
        };
        assert_eq!(
            hex_rows(&p, 0x1008, 0x10).spans,
            [
                span(
                    0x1008,
                    8,
                    Some(".text"),
                    HexFill::Bytes(bytes[8..0x10].to_vec())
                ),
                span(
                    0x1010,
                    8,
                    Some(".data"),
                    HexFill::Bytes(bytes[0x10..0x18].to_vec())
                ),
            ]
        );
        assert_eq!(
            hex_rows(&p, 0x1018, 0x20).spans,
            [
                span(
                    0x1018,
                    8,
                    Some(".data"),
                    HexFill::Bytes(bytes[0x18..].to_vec())
                ),
                span(0x1020, 0x10, Some(".bss"), HexFill::Unbacked),
                span(0x1030, 8, None, HexFill::Unmapped),
            ]
        );
    }

    /// A run without file bytes stops where a file-backed section begins
    /// inside it, and one nothing maps stops at a PE's mapped headers.
    ///
    /// # Panics
    ///
    /// When the bytes there are hidden under the run before them.
    #[test]
    fn hex_rows_stop_where_bytes_begin() {
        let mut tbss = Section::mapped(".tbss", 0x2000, 0, 0x100, true, false);
        tbss.file_size = 0;
        let data = Section::mapped(".data", 0x2010, 0, 0x10, true, false);
        let bytes: Vec<u8> = (0..0x10).collect();
        let p = Program::raw(bytes.clone(), Arch::X86_64, 0, None, vec![tbss, data]);
        let spans = hex_rows(&p, 0x2000, 0x20).spans;
        assert_eq!(spans.len(), 2, "{spans:?}");
        assert_eq!((spans[0].len, &spans[0].fill), (0x10, &HexFill::Unbacked));
        assert_eq!(spans[1].fill, HexFill::Bytes(bytes));
        assert_eq!(spans[1].section.as_deref(), Some(".data"));

        let base = 0x1_4000_0000;
        let mut image = vec![0u8; 0x210];
        image[..2].copy_from_slice(b"MZ");
        let text = Section::mapped(".text", base + 0x1000, 0x200, 0x10, false, true);
        let mut pe = Program::raw(image, Arch::X86_64, base, None, vec![text]);
        pe.format = BinaryFormat::Pe;
        let spans = hex_rows(&pe, base - 8, 0x10).spans;
        assert_eq!(spans.len(), 2, "{spans:?}");
        assert_eq!((spans[0].len, &spans[0].fill), (8, &HexFill::Unmapped));
        assert_eq!((spans[1].va, spans[1].section.as_deref()), (base, None));
        assert!(
            matches!(&spans[1].fill, HexFill::Bytes(b) if b.starts_with(b"MZ")),
            "{spans:?}"
        );
    }

    /// The text is the dump the tool printed: the file's bytes from the
    /// address within its section, the next section's left out, and none
    /// for an address without file bytes.
    ///
    /// # Panics
    ///
    /// When the text differs.
    #[test]
    fn hex_rows_spell_the_first_section_s_bytes() {
        let (bytes, p) = sections();
        assert_eq!(
            hex_rows(&p, 0x1008, 0x10).spell().as_deref(),
            Some(
                "# 0x1008..0x1010 .text\n0x0000001008  49 4a 4b 4c 4d 4e 4f 50                           |IJKLMNOP|\n"
            )
        );
        assert_eq!(
            hex_rows(&p, 0x1010, 0x10).spell(),
            Some(format!(
                "# 0x1010..0x1020 .data\n{}",
                hexdump(&bytes[0x10..], 0x1010)
            ))
        );
        assert_eq!(hex_rows(&p, 0x1020, 4).spell(), None);
        assert_eq!(hex_rows(&p, 0x9000, 4).spell(), None);
    }
}
