//! Rust's source locations read off the calls that hand them over.
//!
//! A Rust panic (and any function marked `#[track_caller]`) is handed the
//! address of a `core::panic::Location`, a `&str` naming the source file
//! followed by the line and column, which the text prints as a bare
//! address (`panic_bounds_check(a1, a2, 0x1427605b8)`). The location is
//! read back from the image and written beside the call (`// at
//! core/src/slice/mod.rs:1015:32`). A path under a cargo registry keeps
//! the crate and its file (`rhai-1.26.1/src/parser.rs`), one in the
//! standard library its own (`core/src/slice/mod.rs`).

use crate::program::Program;

/// Longest source path a location is read with, in bytes.
const PATH_MAX: u64 = 512;
/// Highest line a location may name.
const LINE_MAX: u32 = 10_000_000;
/// Highest column a location may name.
const COLUMN_MAX: u32 = 100_000;

/// The source path a location names, shortened to what identifies it.
///
/// # Arguments
///
/// * `raw` - The path as compiled in, either separator.
fn short_path(raw: &str) -> String {
    let path = raw.replace('\\', "/");
    if let Some((_, rest)) = path.split_once("/registry/src/")
        && let Some((_, krate)) = rest.split_once('/')
    {
        return krate.to_owned();
    }
    if (path.contains("/rustlib/") || path.starts_with("/rustc/"))
        && let Some((_, rest)) = path.split_once("/library/")
    {
        return rest.to_owned();
    }
    path
}

/// Reads the `core::panic::Location` at `addr`: the file's `&str` (its
/// address and length), then the line and the column as 32-bit words.
///
/// # Arguments
///
/// * `program` - The image.
/// * `addr` - Where the location may sit.
///
/// # Returns
///
/// `path:line:column`, or `None` when the bytes there are no location: a
/// file that is no readable text ending in `.rs`, or a line or column out
/// of range.
pub(super) fn location_at(program: &Program, addr: u64) -> Option<String> {
    /// Bytes of a location: a pointer, a length, two 32-bit words.
    const SIZE: usize = 24;
    let raw = program.read_va(addr, SIZE)?;
    let word = |at: usize| -> Option<u64> {
        Some(u64::from_le_bytes(raw.get(at..at + 8)?.try_into().ok()?))
    };
    let half = |at: usize| -> Option<u32> {
        Some(u32::from_le_bytes(raw.get(at..at + 4)?.try_into().ok()?))
    };
    let (ptr, len, line, column) = (word(0)?, word(8)?, half(16)?, half(20)?);
    if !(4..=PATH_MAX).contains(&len) || !(1..=LINE_MAX).contains(&line) || column > COLUMN_MAX {
        return None;
    }
    let bytes = program.read_va(ptr, usize::try_from(len).ok()?)?;
    let file = std::str::from_utf8(bytes).ok()?;
    if !file.ends_with(".rs") || file.chars().any(char::is_control) {
        return None;
    }
    Some(format!("{}:{line}:{column}", short_path(file)))
}

/// The callee a statement calls, when the statement is a call: `f(...)`,
/// `v = f(...)` or `return f(...)`.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn callee(t: &str) -> Option<&str> {
    let call = t
        .strip_prefix("return ")
        .or_else(|| t.split_once(" = ").map(|(_, c)| c))
        .unwrap_or(t);
    let (name, _) = call.split_once('(')?;
    (!name.is_empty()
        && name
            .chars()
            .all(|c| super::line::is_ident_char(c) || c == ':' || c == '~'))
    .then_some(name)
}

/// Writes the source location each call is handed beside it.
///
/// A call's arguments are read left to right and the first constant
/// address holding a location ([`location_at`]) is written as `// at
/// path:line:column`.
///
/// # Arguments
///
/// * `body` - The function's body.
/// * `program` - The image the locations are read from.
pub(super) fn annotate(body: &str, program: &Program) -> String {
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        out.push_str(&with_location(line, program));
        out.push('\n');
    }
    out
}

/// A call line with the location its arguments hand over written beside
/// it, or the line as it was.
///
/// # Arguments
///
/// * `line` - One line of the body.
/// * `program` - The image the locations are read from.
fn with_location(line: &str, program: &Program) -> String {
    let t = line.trim_start();
    let call = t
        .strip_prefix("if (")
        .and_then(|r| r.rsplit_once(") "))
        .map_or(t, |(_, c)| c);
    if !t.ends_with(';') || callee(call).is_none() || line.contains("//") {
        return line.to_owned();
    }
    let args = call.split_once('(').map_or("", |(_, a)| a);
    let at = args
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter_map(|w| w.strip_prefix("0x"))
        .filter_map(|h| u64::from_str_radix(h, 16).ok())
        .find_map(|a| location_at(program, a));
    match at {
        Some(at) => format!("{line}  // at {at}"),
        None => line.to_owned(),
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{annotate, location_at, short_path};
    use crate::program::{Arch, Program, Section};

    /// An image holding a file name at `0x2000` and a location naming it
    /// at `0x2100`.
    fn image() -> Program {
        let mut bytes = vec![0u8; 0x200];
        let file = br"C:\Users\me\.cargo\registry\src\index.crates.io-1949cf8c6b5b557f\rhai-1.26.1\src\parser.rs";
        bytes[..file.len()].copy_from_slice(file);
        let len = u64::try_from(file.len()).expect("a short path");
        bytes[0x100..0x108].copy_from_slice(&0x2000u64.to_le_bytes());
        bytes[0x108..0x110].copy_from_slice(&len.to_le_bytes());
        bytes[0x110..0x114].copy_from_slice(&1015u32.to_le_bytes());
        bytes[0x114..0x118].copy_from_slice(&32u32.to_le_bytes());
        let data = Section::mapped(".rdata", 0x2000, 0, 0x200, false, false);
        Program::raw(bytes, Arch::X86_64, 0, None, vec![data])
    }

    /// A location reads back as its crate's path, line and column, and
    /// bytes that are no location read as none.
    #[test]
    fn a_location_reads_back_as_path_line_and_column() {
        let p = image();
        assert_eq!(
            location_at(&p, 0x2100).as_deref(),
            Some("rhai-1.26.1/src/parser.rs:1015:32")
        );
        assert_eq!(location_at(&p, 0x2000), None);
        assert_eq!(
            short_path("/rustc/abc/library/core/src/slice/mod.rs"),
            "core/src/slice/mod.rs"
        );
    }

    /// A call handed a location carries it beside it; a constant that is
    /// no location leaves its line as it was.
    #[test]
    fn a_call_handed_a_location_carries_it() {
        let p = image();
        let body = "if (a1 >= a3) {\n  panic_bounds_check(a1, a3, 0x2100);\n}\nreturn f(0x2000);\n";
        assert_eq!(
            annotate(body, &p),
            "if (a1 >= a3) {\n  panic_bounds_check(a1, a3, 0x2100);  // at rhai-1.26.1/src/parser.rs:1015:32\n}\nreturn f(0x2000);\n"
        );
    }
}
