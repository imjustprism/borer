//! String literals in the text: what the bytes at an address read as in C,
//! printed only where they read back to those bytes.

use super::*;
use crate::strings::{cstr_text_at, wide_run_start, wstr_text_at};

/// Renders the literal at `addr` compactly.
///
/// A signature or source-path string is read in full (up to 512 bytes) and
/// shortened by [`expr::compact_literal`]; anything else is the capped
/// [`string_at`] text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - The literal's address.
/// * `own_name` - Bare name of the function being rendered.
pub(super) fn literal_at(program: &Program, addr: u64, own_name: &str) -> Option<String> {
    /// Longest signature or path read in full.
    const FULL: usize = 512;
    if program.section_at(addr).is_none_or(|s| s.executable) {
        return None;
    }
    if let Some(literal) = crate::analysis::qt::literal(program, addr) {
        return Some(literal);
    }
    if let Some((_, raw)) = cstr_at(program, addr, 4, FULL) {
        let quoted = format!("\"{}\"", raw.replace('\\', "\\\\").replace('"', "\\\""));
        let compact = expr::compact_literal(&quoted, own_name);
        if compact != quoted {
            return Some(compact);
        }
    }
    string_at(program, addr)
}

/// Reads the quoted string literal at a mapped, non-executable address.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - Address of the candidate string.
///
/// # Returns
///
/// `"text"` or `L"text"` with backslashes and quotes escaped as C does,
/// capped at 120 characters and at least four long, or shorter in read-only
/// data when a terminator follows (`"%d"`, `";"`); `None` when no string
/// lives there or the address is code.
///
/// A wide literal in read-only data reads as a one-character narrow string
/// followed by its own high byte, so `L"SHA256"` renders as `"S"` unless the
/// two candidates are weighed against each other. The wide reading wins when
/// the narrow one is shorter than a literal's minimum and the wide one is
/// longer still, which is the only shape where a narrow reading carries less
/// than the bytes hold. Both readings run over the tab, newline and carriage
/// return a literal escapes, so `L"%ws%ws %ws:\n"` keeps its newline and
/// is not cut to the narrow `"%"`. A lone terminator reads as `""` only
/// beside another literal: right after one, or right before a run of text
/// that ends in its own terminator, not before one printable byte and
/// binary (a jump table's first entry). A literal that does not read back to the
/// image's bytes through the text's own tokenizer ([`round_trips`]) is not
/// printed.
fn string_at(program: &Program, addr: u64) -> Option<String> {
    /// Shortest run accepted as a literal in writable data, where a small
    /// object's first bytes may happen to read as text.
    const MIN: usize = 4;
    /// Shortest run accepted in read-only data, where the empty string is a
    /// lone terminator and reads as `""`.
    const MIN_RODATA: usize = 1;
    /// Longest text rendered.
    const CAP: usize = 120;
    let section = program.section_at(addr)?;
    if section.executable {
        return None;
    }
    let terminated_at = |at: u64, len: usize| {
        len >= CAP
            || u64::try_from(len)
                .ok()
                .and_then(|n| program.read_va_upto(at.wrapping_add(n), 1))
                .is_some_and(|b| b.first() == Some(&0))
    };
    if !section.writable
        && let Some(head) = program.read_va_upto(addr, 1)
        && head.first() == Some(&0)
    {
        let after_a_literal = addr
            .checked_sub(2)
            .and_then(|at| program.read_va(at, 2))
            .is_some_and(|b| {
                b.first().is_some_and(|c| (0x20..0x7f).contains(c)) && b.get(1) == Some(&0)
            });
        let next = addr.wrapping_add(1);
        let before_a_literal =
            cstr_text_at(program, next, 1, CAP).is_some_and(|(len, _)| terminated_at(next, len));
        return (before_a_literal || after_a_literal).then(|| String::from("\"\""));
    }
    let min = if section.writable { MIN } else { MIN_RODATA };
    let terminated = |len: usize| terminated_at(addr, len);
    let sanitize = |t: String| crate::strings::escape_text(&t);
    let narrow = cstr_text_at(program, addr, min, CAP).filter(|&(len, _)| terminated(len));
    if narrow.as_ref().is_some_and(|(len, _)| *len < MIN)
        && addr.is_multiple_of(4)
        && program
            .read_va_upto(addr.wrapping_add(2), 2)
            .is_some_and(|b| b.iter().all(|c| *c == 0))
        && program
            .read_va_upto(addr.wrapping_add(4), 4)
            .is_some_and(|b| b.iter().any(|c| *c != 0))
    {
        return None;
    }
    let run = wide_run_start(program, addr)
        .then(|| wstr_text_at(program, addr, min.max(2), CAP))
        .flatten();
    let wide_len = run.as_ref().map_or(0, |(len, _)| *len);
    let wide = run.filter(|&(len, _)| terminated(len.saturating_mul(2)));
    let literal = match (narrow, wide) {
        (Some((n, _)), Some((w, t))) if n < MIN && w > n => format!("L\"{}\"", sanitize(t)),
        (Some((n, _)), None) if n < MIN && wide_len >= TABLE_UNITS => return None,
        (Some((_, t)), _) => format!("\"{}\"", sanitize(t)),
        (None, Some((_, t))) => format!("L\"{}\"", sanitize(t)),
        (None, None) => return None,
    };
    round_trips(program, addr, &literal).then_some(literal)
}

/// Fewest wide characters, past a one-character narrow reading, that make
/// the bytes a table of 16-bit values in [`string_at`].
const TABLE_UNITS: usize = 3;

/// Tells whether a literal reads back, as the C it is printed in, to the
/// bytes the image holds where it was read.
///
/// The tokenizer the text's own readers use ([`ctext::tokens`]) decodes
/// its escapes and its encoding
/// (`L"..."` as UTF-16LE), and the bytes must be the image's, terminator
/// included; a literal cut at its cap (ending `...`) must be a prefix of
/// them.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - Where the literal was read.
/// * `literal` - The literal as printed, quotes and prefix included.
fn round_trips(program: &Program, addr: u64, literal: &str) -> bool {
    /// What a literal cut at its cap ends with inside its quotes.
    const CUT: &str = "...\"";
    let (whole, cut) = match literal.strip_suffix(CUT) {
        Some(head) => (format!("{head}\""), true),
        None => (literal.to_owned(), false),
    };
    let Ok(toks) = ctext::tokens(&whole) else {
        return false;
    };
    let [ctext::Tok::Str(bytes)] = toks.as_slice() else {
        return false;
    };
    let unit = if literal.starts_with('L') { 2 } else { 1 };
    let held = if cut {
        bytes.get(..bytes.len().saturating_sub(unit))
    } else {
        Some(bytes.as_slice())
    };
    held.is_some_and(|held| {
        program
            .read_va(addr, held.len())
            .is_some_and(|image| image == held)
    })
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    /// A pointer whose low bytes read as text is not a string.
    ///
    /// A vtable install stores `&vtable`, and a vtable's first function pointer
    /// (here `0x1402d6424`) begins with the printable bytes `$d-@` then a
    /// non-zero byte. A four-character run that is not null-terminated is no C
    /// string, so it does not render as `"$d-@"`; a genuine terminated literal
    /// still does.
    #[test]
    fn a_pointer_reading_as_text_is_not_a_string() {
        let mut bytes = vec![0u8; 0x2000];
        bytes[0x1000..0x1008].copy_from_slice(&0x0000_0001_402d_6424u64.to_le_bytes());
        bytes[0x1010..0x1016].copy_from_slice(b"hello\0");
        let sections = vec![crate::program::Section {
            name: ".rdata".to_owned(),
            va: crate::program::Va(0x2000),
            vsize: 0x1000,
            file_off: crate::program::FileOff(0x1000),
            file_size: 0x1000,
            readable: true,
            writable: false,
            executable: false,
        }];
        let section_index = crate::program::Program::index_sections(&sections);
        let p = crate::program::Program {
            path: std::path::PathBuf::new(),
            bytes,
            format: crate::program::BinaryFormat::Raw,
            arch: crate::program::Arch::X86_64,
            is_64: true,
            entry: None,
            image_base: 0,
            sections,
            section_index,
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: crate::headers::Headers::default(),
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            debug_typedefs: std::collections::BTreeMap::new(),
            debug_globals: Vec::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
            relocs: crate::reloc::Relocs::default(),
            go: None,
            clr: None,
            parent: None,
            modes: crate::isa::a32::Modes::default(),
        };
        assert_eq!(
            super::string_at(&p, 0x2000),
            None,
            "a pointer's printable low bytes rendered as a string"
        );
        assert_eq!(super::string_at(&p, 0x2010).as_deref(), Some("\"hello\""));
    }

    /// A zero byte is the empty string only beside another literal.
    ///
    /// The last byte of a pointer followed by a bytecode table (`00 03 00
    /// 5a`) is no string pool, so it keeps its address, nor is a jump
    /// table whose first offset reads `00 '0'` and then binary (`00 30 98
    /// ff`); a terminator the next literal follows (`00 "AB" 00`) or the
    /// previous one ends is `""`.
    #[test]
    fn a_zero_before_a_table_is_no_empty_string() {
        use crate::program::{Arch, Program, Section};
        let mut bytes = vec![0u8; 0x1000];
        bytes[0x10..0x14].copy_from_slice(&[0x00, 0x03, 0x00, 0x5a]);
        bytes[0x20..0x24].copy_from_slice(b"\0AB\0");
        bytes[0x30..0x34].copy_from_slice(b"AB\0\0");
        bytes[0x40..0x44].copy_from_slice(&[0x00, 0x30, 0x98, 0xff]);
        let rdata = Section::mapped(".rdata", 0x2000, 0, 0x1000, false, false);
        let p = Program::raw(bytes, Arch::X86_64, 0, None, vec![rdata]);
        assert_eq!(super::string_at(&p, 0x2010), None);
        assert_eq!(super::string_at(&p, 0x2020).as_deref(), Some("\"\""));
        assert_eq!(super::string_at(&p, 0x2033).as_deref(), Some("\"\""));
        assert_eq!(super::string_at(&p, 0x2040), None);
    }
}
