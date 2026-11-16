//! Classic 16-bytes-per-row hexdump rendering.

use crate::num::from_usize;

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

/// The bytes at an address as a hexdump's rows hold them, with the section
/// they are in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HexRows {
    /// Address of the first byte.
    pub va: u64,
    /// Name of the section holding `va`; `None` outside every section.
    pub section: Option<String>,
    /// One entry per byte asked for: the bytes the file backs from `va`
    /// within its section, then `None` for each past them.
    pub bytes: Vec<Option<u8>>,
}

impl HexRows {
    /// Returns the rows of 16 bytes, each with its address; the last may be
    /// short.
    pub fn rows(&self) -> impl Iterator<Item = (u64, &[Option<u8>])> {
        self.bytes
            .chunks(16)
            .enumerate()
            .map(|(i, row)| (self.va.wrapping_add(from_usize(i * 16)), row))
    }

    /// Returns how many bytes from `va` the file backs.
    #[must_use]
    pub fn mapped(&self) -> usize {
        self.bytes.iter().take_while(|b| b.is_some()).count()
    }

    /// Returns the dump as the `hexdump` tool and the CLI print it.
    ///
    /// # Returns
    ///
    /// A `# va..end section` header covering the bytes the file backs, then
    /// their rows ([`hexdump_sparse`]); `None` when it backs none.
    #[must_use]
    pub fn spell(&self) -> Option<String> {
        let mapped = self.mapped();
        if mapped == 0 {
            return None;
        }
        let sec = self
            .section
            .as_deref()
            .map_or_else(String::new, |s| format!(" {s}"));
        Some(format!(
            "# {:#x}..{:#x}{sec}\n{}",
            self.va,
            self.va.wrapping_add(from_usize(mapped)),
            hexdump_sparse(&self.bytes[..mapped], self.va)
        ))
    }
}

/// Returns the bytes at `va` as a hexdump's rows hold them.
///
/// The bytes are those the file backs from `va` within the section holding
/// it ([`crate::program::Program::read_va_upto`]): a range that runs off
/// the section's end, or off the file, is that many `None` past them, so an
/// unmapped byte never reads as a zero.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Address of the first byte.
/// * `len` - Bytes asked for, at most [`HEXDUMP_MAX`].
///
/// # Returns
///
/// The bytes and the section, `None` for every byte when nothing backs
/// `va`.
#[must_use]
pub fn hex_rows(program: &crate::program::Program, va: u64, len: usize) -> HexRows {
    let len = len.min(HEXDUMP_MAX);
    let mut bytes: Vec<Option<u8>> = program
        .read_va_upto(va, len)
        .unwrap_or_default()
        .iter()
        .copied()
        .map(Some)
        .collect();
    bytes.resize(len, None);
    HexRows {
        va,
        section: program.section_at(va).map(|s| s.name.clone()),
        bytes,
    }
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

    /// Rows across a section's end hold its bytes, then `None` for each
    /// past it, under the section's name; the text is the dump the tool
    /// printed of the bytes the file backs, and an address nothing backs
    /// has no text.
    ///
    /// # Panics
    ///
    /// When a byte, the section or the text differs.
    #[test]
    fn hex_rows_end_with_none_past_the_section() {
        let bytes: Vec<u8> = (b'A'..b'A' + 0x20).collect();
        let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
        let p = Program::raw(bytes.clone(), Arch::X86_64, 0x1000, None, vec![text]);
        let rows = hex_rows(&p, 0x1018, 0x10);
        assert_eq!(rows.section.as_deref(), Some(".text"));
        assert_eq!(rows.mapped(), 8);
        let want: Vec<Option<u8>> = bytes[0x18..]
            .iter()
            .copied()
            .map(Some)
            .chain([None; 8])
            .collect();
        assert_eq!(rows.bytes, want);
        let starts: Vec<u64> = rows.rows().map(|(va, _)| va).collect();
        assert_eq!(starts, [0x1018]);
        assert_eq!(
            rows.spell().as_deref(),
            Some(
                "# 0x1018..0x1020 .text\n0x0000001018  59 5a 5b 5c 5d 5e 5f 60                           |YZ[\\]^_`|\n"
            )
        );
        let whole = hex_rows(&p, 0x1000, 0x20);
        assert_eq!(whole.rows().count(), 2);
        assert_eq!(
            whole.spell(),
            Some(format!(
                "# 0x1000..0x1020 .text\n{}",
                hexdump(&bytes, 0x1000)
            ))
        );
        let nothing = hex_rows(&p, 0x9000, 4);
        assert_eq!((nothing.section.as_deref(), nothing.mapped()), (None, 0));
        assert_eq!(nothing.bytes, [None; 4]);
        assert_eq!(hex_rows(&p, 0x9000, 4).spell(), None);
    }
}
