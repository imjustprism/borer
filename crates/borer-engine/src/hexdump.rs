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
