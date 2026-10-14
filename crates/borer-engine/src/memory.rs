//! Typed memory reads: integers, floats, pointers and strings at an address,
//! rendered one value per row for an agent that asks "what is at X as T".

use std::borrow::Cow;

use crate::num::{from_usize, lo8, lo16, lo32};
use crate::program::Program;
use crate::strings::{SCAN_MAX, cstr_in, wstr_in};

/// Value interpretation for [`read_values`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Unsigned 8-bit integer.
    U8,
    /// Unsigned 16-bit integer.
    U16,
    /// Unsigned 32-bit integer.
    U32,
    /// Unsigned 64-bit integer.
    U64,
    /// Signed 8-bit integer.
    I8,
    /// Signed 16-bit integer.
    I16,
    /// Signed 32-bit integer.
    I32,
    /// Signed 64-bit integer.
    I64,
    /// IEEE-754 single precision.
    F32,
    /// IEEE-754 double precision.
    F64,
    /// Word-sized pointer (4 or 8 bytes by architecture).
    Ptr,
    /// NUL-terminated printable ASCII string.
    CStr,
    /// UTF-16LE string.
    WStr,
}

impl Kind {
    /// Parses a kind name as typed by an agent.
    ///
    /// # Arguments
    ///
    /// * `s` - A name from [`Kind::NAMES`] or a common alias (`byte`,
    ///   `dword`, `int`, `float`, `pointer`, `string`, `wide`, ...); case and
    ///   surrounding whitespace are ignored.
    ///
    /// # Returns
    ///
    /// The kind, or `None` for an unknown name.
    pub fn parse(s: &str) -> Option<Kind> {
        Some(match s.trim().to_ascii_lowercase().as_str() {
            "u8" | "byte" => Kind::U8,
            "u16" | "word" => Kind::U16,
            "u32" | "dword" => Kind::U32,
            "u64" | "qword" => Kind::U64,
            "i8" => Kind::I8,
            "i16" => Kind::I16,
            "i32" | "int" => Kind::I32,
            "i64" => Kind::I64,
            "f32" | "float" => Kind::F32,
            "f64" | "double" => Kind::F64,
            "ptr" | "pointer" => Kind::Ptr,
            "cstr" | "str" | "string" | "ascii" => Kind::CStr,
            "wstr" | "utf16" | "wide" => Kind::WStr,
            _ => return None,
        })
    }

    /// The canonical kind names, space separated, for tool descriptions.
    pub const NAMES: &'static str = "u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 ptr cstr wstr";

    /// Returns the size of one value in bytes; of one character for a
    /// string, whose length is only known once read.
    ///
    /// # Arguments
    ///
    /// * `word` - Pointer size of the architecture (4 or 8).
    pub(crate) fn size(self, word: usize) -> usize {
        match self {
            Kind::U8 | Kind::I8 | Kind::CStr => 1,
            Kind::U16 | Kind::I16 | Kind::WStr => 2,
            Kind::U32 | Kind::I32 | Kind::F32 => 4,
            Kind::U64 | Kind::I64 | Kind::F64 => 8,
            Kind::Ptr => word,
        }
    }
}

/// One decoded value.
#[derive(Debug, Clone, PartialEq)]
pub struct Value {
    /// Where the value starts: a virtual address, or a file offset for a
    /// read by offset ([`read_values_at_offset`]).
    pub at: u64,
    /// Rendered value: hex for unsigned integers and pointers, decimal for
    /// signed ones, quoted text for strings.
    pub text: String,
    /// For pointers: the pointed-to address, so callers can name it.
    pub target: Option<u64>,
    /// Bytes consumed, including the terminator for strings.
    pub size: usize,
}

/// Renders one fixed-width value as [`Value::text`], with the address a
/// pointer holds as [`Value::target`].
///
/// An unsigned integer is hex alone: `0x48 (72)` spelled the value twice,
/// and the hex is what a reader compares against an offset or a flag. A
/// float is the shortest text that reads back as the value, at the
/// value's own width: `Debug` switches to an exponent for very large and
/// very small magnitudes, where `Display` spells every digit of a 180-digit
/// expansion.
///
/// # Arguments
///
/// * `kind` - The interpretation; a string kind renders empty, since a
///   string is read by its length rather than as a word.
/// * `raw` - The value's bytes, assembled little-endian.
///
/// # Returns
///
/// The text, and the target of a pointer.
pub(crate) fn scalar_text(kind: Kind, raw: u64) -> (String, Option<u64>) {
    let text = match kind {
        Kind::U8 | Kind::U16 | Kind::U32 | Kind::U64 => format!("{raw:#x}"),
        Kind::I8 => i64::from(lo8(raw).cast_signed()).to_string(),
        Kind::I16 => i64::from(lo16(raw).cast_signed()).to_string(),
        Kind::I32 => i64::from(lo32(raw).cast_signed()).to_string(),
        Kind::I64 => raw.cast_signed().to_string(),
        Kind::F32 => format!("{:?}", f32::from_bits(lo32(raw))),
        Kind::F64 => format!("{:?}", f64::from_bits(raw)),
        Kind::Ptr => return (format!("{raw:#x}"), Some(raw)),
        Kind::CStr | Kind::WStr => String::new(),
    };
    (text, None)
}

/// Longest string rendered in full.
const STR_CAP: usize = 200;

/// Decodes `count` consecutive values of `kind` starting at `va`.
///
/// Decoding stops early at the end of the mapped bytes; string kinds also stop
/// at the first unmapped or empty string.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the first value.
/// * `kind` - How to interpret the bytes.
/// * `count` - Maximum number of values.
///
/// # Returns
///
/// The values in address order, at least one.
///
/// # Errors
///
/// Returns a message naming the address and the mapped sections when not
/// even the first value could be read, and how to read the bytes no section
/// maps when the file has some.
pub fn read_values(
    program: &Program,
    va: u64,
    kind: Kind,
    count: usize,
) -> Result<Vec<Value>, String> {
    read_values_with(
        program,
        |at, max| program.read_va_upto(at, max).map(Cow::Borrowed),
        va,
        kind,
        count,
        |first| match first {
            None => format!(
                "address {va:#x} is not mapped to file bytes; sections: {}{}",
                program.section_list(),
                by_offset_hint(program)
            ),
            Some(first) => refusal(kind, first, &format!("{va:#x}"), program, || {
                format!("; sections: {}", program.section_list())
            }),
        },
    )
}

/// Decodes `count` consecutive values of `kind` starting at a file offset.
///
/// The read for bytes no section maps: an overlay, the headers, a file the
/// loader found no sections in. Each [`Value::at`] is a file offset.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `off` - File offset of the first value.
/// * `kind` - How to interpret the bytes.
/// * `count` - Maximum number of values.
///
/// # Returns
///
/// The values in file order, at least one.
///
/// # Errors
///
/// Returns a message naming the offset and the file size when not even the
/// first value could be read.
pub fn read_values_at_offset(
    program: &Program,
    off: u64,
    kind: Kind,
    count: usize,
) -> Result<Vec<Value>, String> {
    read_values_with(
        program,
        |at, max| program.read_off_upto(at, max).map(Cow::Borrowed),
        off,
        kind,
        count,
        |first| match first {
            None => format!(
                "file offset {off:#x} is past the end of the file; the file is {:#x} bytes",
                program.bytes.len()
            ),
            Some(first) => refusal(kind, first, &format!("off:{off:#x}"), program, || {
                format!("; the file is {:#x} bytes", program.bytes.len())
            }),
        },
    )
}

/// Decodes values through a reader, the caller saying why none decoded.
///
/// # Arguments
///
/// * `program` - The loaded image, for the word size.
/// * `read` - Reads up to a number of bytes at a position; `None` where
///   nothing is readable.
/// * `start` - Position of the first value, in `read`'s terms.
/// * `kind` - How to interpret the bytes.
/// * `count` - Maximum number of values.
/// * `why` - Builds the error from the byte at the start, or `None` when
///   not even it reads.
///
/// # Returns
///
/// The values in order, at least one.
///
/// # Errors
///
/// Whatever `why` builds, when not even the first value decodes.
fn read_values_with<'a>(
    program: &Program,
    read: impl Fn(u64, usize) -> Option<Cow<'a, [u8]>>,
    start: u64,
    kind: Kind,
    count: usize,
    why: impl FnOnce(Option<u8>) -> String,
) -> Result<Vec<Value>, String> {
    let out = decode(&read, program.is_64, start, kind, count);
    if !out.is_empty() {
        return Ok(out);
    }
    // INVARIANT: an address that maps to no file bytes and one that maps to
    // bytes that are not the kind asked for are two different answers, and
    // the reader acts differently on each.
    let first = read(start, 1).and_then(|b| b.first().copied());
    Err(why(first))
}

/// Says how to read the bytes no section maps, for an error about an
/// address no section maps.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// A clause to append to the error, empty when the sections cover the
/// whole file.
pub fn by_offset_hint(program: &Program) -> String {
    match program.unmapped().first() {
        None => String::new(),
        Some(_) if program.sections.is_empty() => {
            "; the file's bytes are read by file offset, as off:0x0".to_owned()
        }
        Some((off, bytes)) => format!(
            "; bytes no section maps are read by file offset, as off:{off:#x} ({:#x} bytes there)",
            bytes.len()
        ),
    }
}

/// The refusal of a read whose first byte is there but whose first value
/// did not decode.
///
/// # Arguments
///
/// * `kind` - The kind asked for.
/// * `first` - The byte at the start.
/// * `at` - The start as the caller wrote it.
/// * `program` - The loaded image, for the word size.
/// * `room` - The clause that says what is readable, for a short read.
///
/// # Returns
///
/// The message.
fn refusal(
    kind: Kind,
    first: u8,
    at: &str,
    program: &Program,
    room: impl FnOnce() -> String,
) -> String {
    match kind {
        Kind::CStr | Kind::WStr => not_text(kind, first, at),
        _ => format!(
            "fewer than {} bytes are mapped at {at}{}",
            kind.size(if program.is_64 { 8 } else { 4 }),
            room()
        ),
    }
}

/// The refusal of a string read whose first byte is there but is not text.
///
/// # Arguments
///
/// * `kind` - The string kind asked for.
/// * `first` - The byte at the start.
/// * `at` - The start as the caller wrote it.
///
/// # Returns
///
/// The message.
pub(crate) fn not_text(kind: Kind, first: u8, at: &str) -> String {
    format!(
        "no {kind:?} at {at}: the byte there is {first:#04x}, not printable text; read it as u8 or hexdump it"
    )
}

/// Decodes up to `count` values from the bytes `read` returns.
///
/// The file's bytes and a running process's both decode here, so a value
/// reads the same from either: a string runs to its terminator up to
/// [`SCAN_MAX`] bytes whatever `count` is, the first string starts at the
/// first byte (a leading NUL is no string), and padding is stepped over
/// only between strings.
///
/// # Arguments
///
/// * `read` - Reads up to a number of bytes at a position, borrowed from
///   the file or read from a process; `None` where nothing is readable.
/// * `is_64` - Pointers are eight bytes, not four.
/// * `start` - Position of the first value, in `read`'s terms.
/// * `kind` - How to interpret the bytes.
/// * `count` - Maximum number of values.
///
/// # Returns
///
/// The values in order; empty when not even the first decodes.
pub(crate) fn decode<'a>(
    read: impl Fn(u64, usize) -> Option<Cow<'a, [u8]>>,
    is_64: bool,
    start: u64,
    kind: Kind,
    count: usize,
) -> Vec<Value> {
    /// Most padding bytes stepped over between two strings: a string pool
    /// aligns each literal, and the run of zeros after a terminator is that
    /// alignment, not the end of the pool.
    const PAD_MAX: u64 = 16;
    let size = kind.size(if is_64 { 8 } else { 4 });
    let exact = |at: u64| read(at, size).filter(|b| b.len() == size);
    let mut out = Vec::with_capacity(count);
    let mut cur = start;
    for _ in 0..count {
        if matches!(kind, Kind::CStr | Kind::WStr) && !out.is_empty() {
            let mut skipped = 0;
            while skipped < PAD_MAX && exact(cur).is_some_and(|b| b.iter().all(|x| *x == 0)) {
                cur = cur.wrapping_add(from_usize(size));
                skipped += from_usize(size);
            }
        }
        let v = match kind {
            Kind::CStr => match read(cur, SCAN_MAX).and_then(|raw| cstr_in(&raw, 1, STR_CAP)) {
                Some((len, text)) => Value {
                    at: cur,
                    text: format!("\"{}\" (len {len})", text.replace('"', "\\\"")),
                    target: None,
                    size: len + 1,
                },
                None => break,
            },
            Kind::WStr => match read(cur, SCAN_MAX * 2).and_then(|raw| wstr_in(&raw, 1, STR_CAP)) {
                Some((len, text)) => Value {
                    at: cur,
                    text: format!("L\"{}\" (len {len})", text.replace('"', "\\\"")),
                    target: None,
                    size: (len + 1) * 2,
                },
                None => break,
            },
            _ => {
                let Some(bytes) = exact(cur) else {
                    break;
                };
                let (text, target) = scalar_text(kind, le_word(&bytes));
                Value {
                    at: cur,
                    text,
                    target,
                    size,
                }
            }
        };
        cur = cur.wrapping_add(from_usize(v.size));
        out.push(v);
    }
    out
}

/// Assembles up to eight little-endian bytes into a `u64`.
///
/// # Arguments
///
/// * `bytes` - The value's bytes, least significant first; extra bytes are ignored.
pub(crate) fn le_word(bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .take(8)
        .rev()
        .fold(0u64, |acc, b| (acc << 8) | u64::from(*b))
}
