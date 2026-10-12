//! Typed reads of data at rest: a user type laid over the image's bytes,
//! one row per value, the static twin of a live object read.
//!
//! An agent that knows a table's record type (from a header, a stated
//! struct or a recovered layout) reads it here instead of decoding words
//! by hand: each scalar renders at its width, a nested struct as its
//! fields under a dotted path, an enum by its member name, a `char` array
//! as quoted text, and a pointer with what it points at (the text a `char`
//! pointer holds, else the function, global or section).

use super::{Analysis, Overlay, name_of};
use crate::analysis::utypes::{TypeExpr, UserType, width_of};
use crate::memory::{Kind, le_word, scalar_text};
use crate::num::from_usize;
use crate::program::Program;
use crate::strings::{cstr_text_at, escape_text, literal_byte};
use std::fmt::Write as _;

/// Most rows one typed read prints; the header counts the rest.
pub const TYPED_ROWS_MAX: usize = 256;

/// Most bytes one typed read lays its type over; a larger type is read for
/// its first this many bytes and the header says so.
pub const TYPED_BYTES_MAX: u64 = 1 << 16;

/// Longest text a `char` array or a `char` pointer renders before `...`.
const TEXT_MAX: usize = 120;

/// Most bytes a `u8` array shows in its one row before `...`.
const HEX_MAX: usize = 32;

/// Deepest nesting of structs by value a read follows; past it a row says
/// so rather than walking a chain a hand-edited project made long.
const NEST_MAX: usize = 16;

/// Most values a read visits, rendered or only counted: what keeps an array
/// of empty structs, which spans no bytes, from walking for ever.
const FUEL: usize = 1 << 20;

/// Names what a pointer read from the image points at: the function
/// holding the address, a name the agent gave it, a symbol, else the
/// section.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, when one is built, for functions and symbols.
/// * `o` - User names.
/// * `target` - The address the pointer holds.
///
/// # Returns
///
/// The name, or `None` when the address is in no section.
#[must_use]
pub fn pointee_name(p: &Program, a: Option<&Analysis>, o: &Overlay, target: u64) -> Option<String> {
    if let Some(a) = a
        && let Some(f) = a.function_at(target)
    {
        return Some(name_of(a, o, f.entry));
    }
    if let Some(n) = o.names.get(&target) {
        return Some(n.clone());
    }
    if let Some(a) = a
        && let Some(s) = a.symbol_at(p, target)
    {
        return Some(crate::search::demangled_name(&s.name));
    }
    p.section_at(target).map(|s| s.name.clone())
}

/// One rendered value.
struct Row {
    /// Where the value starts.
    at: u64,
    /// Its path from the read's start: `[0].pos.x`, `name`, or `-` for the
    /// whole of a scalar read.
    path: String,
    /// Its type as stated.
    ty: String,
    /// Its value as text.
    value: String,
}

/// A read in progress: the bytes the type lies over, and the rows so far.
struct Walk<'a> {
    /// The loaded image.
    p: &'a Program,
    /// The analysis, for naming pointers.
    a: Option<&'a Analysis>,
    /// The user types and names.
    o: &'a Overlay,
    /// The bytes from the read's start, as many as are mapped up to the cap.
    bytes: &'a [u8],
    /// Where the bytes start.
    base: u64,
    /// The image's pointer width in bytes.
    word: u64,
    /// The rows rendered, at most [`TYPED_ROWS_MAX`].
    rows: Vec<Row>,
    /// Every row the read holds, rendered or not.
    total: usize,
    /// Values left to visit ([`FUEL`]).
    fuel: usize,
}

impl Walk<'_> {
    /// Records one row, keeping its text while there is room.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the value starts.
    /// * `path` - Its path.
    /// * `ty` - Its type as stated.
    /// * `value` - Its value, built only when there is room for it.
    fn row(&mut self, at: u64, path: &str, ty: &str, value: impl FnOnce(&Self) -> String) {
        self.total += 1;
        if self.rows.len() < TYPED_ROWS_MAX {
            let value = value(self);
            self.rows.push(Row {
                at,
                path: if path.is_empty() { "-" } else { path }.to_owned(),
                ty: ty.to_owned(),
                value,
            });
        }
    }

    /// The bytes of a value, when all of them are inside the read.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the value starts.
    /// * `len` - Its width in bytes.
    fn bytes_at(&self, at: u64, len: u64) -> Option<&[u8]> {
        let start = usize::try_from(at.checked_sub(self.base)?).ok()?;
        let end = start.checked_add(usize::try_from(len).ok()?)?;
        self.bytes.get(start..end)
    }

    /// The first address past the bytes of the read.
    fn end(&self) -> u64 {
        self.base.saturating_add(from_usize(self.bytes.len()))
    }

    /// Renders the value of `ty` at `at` under `path`.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the value starts.
    /// * `path` - Its path from the read's start.
    /// * `ty` - Its type as stated.
    /// * `depth` - How many structs by value enclose it.
    fn value(&mut self, at: u64, path: &str, ty: &TypeExpr, depth: usize) {
        if self.fuel == 0 || at >= self.end() {
            return;
        }
        self.fuel -= 1;
        let o = self.o;
        let shown = ty.spell();
        match resolved(o, ty) {
            TypeExpr::Named(n) => match o.types.get(n) {
                Some(UserType::Struct(s)) => {
                    if depth >= NEST_MAX {
                        self.row(at, path, &shown, |_| {
                            format!("(nested past {NEST_MAX} structs; read at {at:#x})")
                        });
                        return;
                    }
                    for (off, f) in &s.fields {
                        let inner = if path.is_empty() {
                            f.name.clone()
                        } else {
                            format!("{path}.{}", f.name)
                        };
                        self.value(at.saturating_add(*off), &inner, &f.ty, depth + 1);
                    }
                }
                Some(UserType::Enum(e)) => {
                    let Some(raw) = self.bytes_at(at, e.size).map(le_word) else {
                        return;
                    };
                    let member = e.values.iter().find(|(v, _)| *v == raw);
                    self.row(at, path, &shown, |_| {
                        member.map_or_else(|| format!("{raw:#x} (no member)"), |(_, m)| m.clone())
                    });
                }
                Some(UserType::Alias(_)) | None => {
                    self.row(at, path, &shown, |_| "(names no type)".to_owned());
                }
            },
            TypeExpr::Array(inner, n) => self.array(at, path, &shown, inner, *n, depth),
            TypeExpr::Ptr(inner) => {
                let Some(raw) = self.bytes_at(at, self.word).map(le_word) else {
                    return;
                };
                let text = matches!(resolved(o, inner), TypeExpr::Char);
                self.row(at, path, &shown, |w| w.pointer(raw, text));
            }
            TypeExpr::Char => {
                let Some(&b) = self.bytes_at(at, 1).and_then(<[u8]>::first) else {
                    return;
                };
                self.row(at, path, &shown, |_| {
                    if (0x20..0x7f).contains(&b) && b != b'\'' && b != b'\\' {
                        format!("'{}'", char::from(b))
                    } else {
                        format!("{b:#x}")
                    }
                });
            }
            scalar @ (TypeExpr::U8
            | TypeExpr::U16
            | TypeExpr::U32
            | TypeExpr::U64
            | TypeExpr::I8
            | TypeExpr::I16
            | TypeExpr::I32
            | TypeExpr::I64
            | TypeExpr::F32
            | TypeExpr::F64) => {
                let Some((kind, len)) = kind_of(scalar) else {
                    return;
                };
                let Some(raw) = self.bytes_at(at, len).map(le_word) else {
                    return;
                };
                self.row(at, path, &shown, |_| scalar_text(kind, raw).0);
            }
        }
    }

    /// Renders an array: a `char` array as its text, a `u8` array as its
    /// bytes, anything else value by value under `path[i]`.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the array starts.
    /// * `path` - Its path.
    /// * `shown` - Its type as stated.
    /// * `inner` - The type of its values.
    /// * `n` - How many values it holds.
    /// * `depth` - How many structs by value enclose it.
    fn array(&mut self, at: u64, path: &str, shown: &str, inner: &TypeExpr, n: u64, depth: usize) {
        let bytes: Option<fn(&[u8]) -> String> = match resolved(self.o, inner) {
            TypeExpr::Char => Some(text_of),
            TypeExpr::U8 => Some(hex_of),
            TypeExpr::U16
            | TypeExpr::U32
            | TypeExpr::U64
            | TypeExpr::I8
            | TypeExpr::I16
            | TypeExpr::I32
            | TypeExpr::I64
            | TypeExpr::F32
            | TypeExpr::F64
            | TypeExpr::Ptr(_)
            | TypeExpr::Array(..)
            | TypeExpr::Named(_) => None,
        };
        if let Some(render) = bytes {
            let available = self.end().saturating_sub(at).min(n);
            let Some(raw) = self.bytes_at(at, available) else {
                return;
            };
            let value = render(raw);
            self.row(at, path, shown, |_| value);
            return;
        }
        let Some(stride) = width_of(&self.o.types, inner, self.word) else {
            self.row(at, path, shown, |_| "(its values have no size)".to_owned());
            return;
        };
        for i in 0..n {
            let Some(item) = stride.checked_mul(i).and_then(|o| at.checked_add(o)) else {
                return;
            };
            if self.fuel == 0 || item >= self.end() {
                return;
            }
            self.value(item, &format!("{path}[{i}]"), inner, depth);
        }
    }

    /// Renders a pointer: its value, then what it points at.
    ///
    /// # Arguments
    ///
    /// * `raw` - The address it holds.
    /// * `text` - It is a `char` pointer, whose target reads as text first.
    fn pointer(&self, raw: u64, text: bool) -> String {
        if raw == 0 {
            return "0x0".to_owned();
        }
        if text && let Some((_, s)) = cstr_text_at(self.p, raw, 1, TEXT_MAX) {
            return format!("{raw:#x} -> \"{}\"", escape_text(&s));
        }
        match pointee_name(self.p, self.a, self.o, raw) {
            Some(name) => format!("{raw:#x} -> {name}"),
            None => format!("{raw:#x}"),
        }
    }
}

/// Follows names through typedefs to the type they stand for.
///
/// # Arguments
///
/// * `o` - The user types.
/// * `ty` - The type as stated.
///
/// # Returns
///
/// The first type that is not a typedef's name; a name nothing defines,
/// or a chain that loops, stays the name it is.
fn resolved<'t>(o: &'t Overlay, ty: &'t TypeExpr) -> &'t TypeExpr {
    let mut current = ty;
    for _ in 0..=crate::analysis::utypes::TYPES_MAX {
        let TypeExpr::Named(n) = current else {
            return current;
        };
        match o.types.get(n) {
            Some(UserType::Alias(inner)) => current = inner,
            Some(UserType::Struct(_) | UserType::Enum(_)) | None => return current,
        }
    }
    current
}

/// The read kind and width of a scalar of the language.
///
/// # Arguments
///
/// * `ty` - The type; a pointer, an array, a name and `char` are not
///   scalars here.
fn kind_of(ty: &TypeExpr) -> Option<(Kind, u64)> {
    Some(match ty {
        TypeExpr::U8 => (Kind::U8, 1),
        TypeExpr::U16 => (Kind::U16, 2),
        TypeExpr::U32 => (Kind::U32, 4),
        TypeExpr::U64 => (Kind::U64, 8),
        TypeExpr::I8 => (Kind::I8, 1),
        TypeExpr::I16 => (Kind::I16, 2),
        TypeExpr::I32 => (Kind::I32, 4),
        TypeExpr::I64 => (Kind::I64, 8),
        TypeExpr::F32 => (Kind::F32, 4),
        TypeExpr::F64 => (Kind::F64, 8),
        TypeExpr::Char | TypeExpr::Ptr(_) | TypeExpr::Array(..) | TypeExpr::Named(_) => {
            return None;
        }
    })
}

/// Quotes a `char` array's text: the bytes up to its first NUL, a byte a
/// literal cannot hold as `\xNN`, cut at [`TEXT_MAX`].
///
/// # Arguments
///
/// * `raw` - The array's bytes.
fn text_of(raw: &[u8]) -> String {
    let len = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    let mut out = String::from("\"");
    for &b in raw.iter().take(len.min(TEXT_MAX)) {
        if literal_byte(b) {
            out.push_str(&escape_text(&char::from(b).to_string()));
        } else {
            let _ = write!(out, "\\x{b:02x}");
        }
    }
    out.push('"');
    if len > TEXT_MAX {
        out.push_str("...");
    }
    out
}

/// Spells a `u8` array's bytes in hex, cut at [`HEX_MAX`].
///
/// # Arguments
///
/// * `raw` - The array's bytes.
fn hex_of(raw: &[u8]) -> String {
    let mut out = raw
        .iter()
        .take(HEX_MAX)
        .map(|b| format!("{b:02x}"))
        .collect::<Vec<_>>()
        .join(" ");
    if raw.len() > HEX_MAX {
        out.push_str(" ...");
    }
    out
}

/// Renders a user type laid over the image's bytes at an address, one row
/// per value.
///
/// Each row is `address path type value`: a struct's fields under their
/// names (`pos.x` for a nested one), an array's values under `[i]`, an
/// enum by its member's name (`0x5 (no member)` for a value it does not
/// name), a `char` array as quoted text up to its NUL, a `u8` array as its
/// bytes, and a pointer as its value with what it points at. The type is
/// read over at most [`TYPED_BYTES_MAX`] bytes and as many as are mapped;
/// the header says when either cut it, and counts the rows past
/// [`TYPED_ROWS_MAX`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, when one is built, for naming pointers.
/// * `o` - The user types and names.
/// * `va` - Where the value starts.
/// * `ty` - Its type; `Rec[4]` reads four records.
///
/// # Returns
///
/// A `# showing N of M rows` header naming the type, the address and the
/// bytes read, then the rows.
///
/// # Errors
///
/// When the type names nothing defined, or no byte at the address is
/// mapped.
pub fn typed_tsv(
    p: &Program,
    a: Option<&Analysis>,
    o: &Overlay,
    va: u64,
    ty: &TypeExpr,
) -> Result<String, String> {
    let word: u64 = if p.is_64 { 8 } else { 4 };
    let size = width_of(&o.types, ty, word).ok_or_else(|| {
        format!(
            "the type {} names nothing defined; set_type(name=..., fields=[...]) first",
            ty.spell()
        )
    })?;
    let want = size.min(TYPED_BYTES_MAX);
    let bytes = p
        .read_va_upto(va, usize::try_from(want).unwrap_or(0).max(1))
        .filter(|b| !b.is_empty())
        .ok_or_else(|| {
            format!(
                "address {va:#x} is not mapped to file bytes; sections: {}",
                p.section_list()
            )
        })?;
    let bytes = bytes
        .get(..usize::try_from(want).unwrap_or(0))
        .unwrap_or(bytes);
    let mut walk = Walk {
        p,
        a,
        o,
        bytes,
        base: va,
        word,
        rows: Vec::new(),
        total: 0,
        fuel: FUEL,
    };
    walk.value(va, "", ty, 0);
    let read = from_usize(bytes.len());
    let section = p
        .section_at(va)
        .map_or_else(String::new, |s| format!(" in {}", s.name));
    let mut out = format!(
        "# showing {} of {} rows: {} at {va:#x}{section}, {size:#x} bytes",
        walk.rows.len(),
        walk.total,
        ty.spell()
    );
    if read < size {
        let why = if read == TYPED_BYTES_MAX {
            "the cap"
        } else {
            "where the mapped bytes end"
        };
        let _ = write!(
            out,
            "; read {read:#x} ({why}), read at {:#x} for the rest",
            va.saturating_add(read)
        );
    }
    if walk.fuel == 0 {
        out.push_str("; stopped after visiting too many values");
    }
    out.push('\n');
    let path_w = walk.rows.iter().map(|r| r.path.len()).max().unwrap_or(0);
    let ty_w = walk.rows.iter().map(|r| r.ty.len()).max().unwrap_or(0);
    for r in &walk.rows {
        let _ = writeln!(
            out,
            "{:<12} {:<path_w$} {:<ty_w$} {}",
            format!("{:#x}", r.at),
            r.path,
            r.ty,
            r.value
        );
    }
    Ok(out)
}
