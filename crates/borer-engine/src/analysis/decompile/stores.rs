//! Runs of stores read as the library call a compiler expanded them from:
//! constant bytes that spell a string are a `strcpy` or a `memcpy` of a
//! literal.
//!
//! A compiler writes a short string into a buffer as a few wide constant
//! stores, and obfuscated code builds one on its stack a byte at a time so
//! it never sits in the image. Either way the text shows a run of
//! constants whose bytes, laid out in memory, spell the string. The run
//! becomes one call with the literal; a run on the stack makes the slots
//! it fills one `char` array, which is what the source declared.

use super::ctext::{self, Tok};
use super::vars::{declaration, parts};
use super::*;

/// Fewest stores a run takes before its bytes count as a string, so one
/// wide constant that happens to read as text stays a number.
const STRING_STORES: usize = 2;

/// Fewest characters a run's string has.
const STRING_CHARS: usize = 4;

/// Most stores one run takes.
const RUN_MAX: usize = 64;

/// What a store is relative to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Base<'t> {
    /// The frame: offsets are a slot's, `local_18` at `-0x18`.
    Frame,
    /// The address a pointer variable holds.
    Pointer(&'t str),
}

/// One store a run is made of: where its bytes land and what they are.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Store<'t> {
    /// What the offset is relative to.
    base: Base<'t>,
    /// Byte offset of the first byte from the base.
    off: i64,
    /// Width in bytes.
    width: u8,
}

/// Rewrites each run of constant stores that spells a string as one
/// `strcpy` or `memcpy` of a literal.
///
/// A run is consecutive statements at one depth, each assigning a constant
/// to one or more places that are all relative to the same base: a frame
/// slot (`local_18`, `*(uint64_t*)&local_18`) or a pointer variable
/// (`*(uint64_t*)a1`, `*(uint16_t*)(a1 + 8)`). Laid out little-endian, a
/// later store over an earlier one's bytes, the bytes must cover one range
/// with no gap and read as at least [`STRING_CHARS`] characters a C
/// literal can hold, from at least [`STRING_STORES`] stores. Text ending
/// in one terminator is `strcpy(dst, "text")`; text with no terminator is
/// `memcpy(dst, "text", n)`. Anything else is left alone.
///
/// On the frame the slots the range covers become one `char` array named
/// after the first, which must start the range; every slot must lie inside
/// it, the others may be named nowhere else, and the first only by its
/// address, which the array's name is. A pointer's run writes through the
/// pointer as the stores did.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those runs rewritten.
pub(super) fn store_strings(text: &str) -> String {
    let Some(p) = parts(text) else {
        return text.to_owned();
    };
    let decls: BTreeMap<&str, &str> = p
        .head
        .get(p.decls..)
        .unwrap_or_default()
        .iter()
        .filter_map(|d| declaration(d))
        .flat_map(|(ty, items)| {
            items
                .into_iter()
                .filter(|(stars, _)| stars.is_empty())
                .map(move |(_, n)| (n, ty))
        })
        .collect();
    let mut head: Vec<String> = p.head.iter().map(|l| (*l).to_owned()).collect();
    let mut body: Vec<String> = p.body.iter().map(|l| (*l).to_owned()).collect();
    let mut changed = false;
    let mut i = 0;
    while i < body.len() {
        match string_run(&body, i, &decls) {
            Some((end, rewrite)) => {
                if let Some((line, arrays)) = rewrite.apply(&body, i, end, &decls) {
                    body.splice(i..end, [line]);
                    declare_arrays(&mut head, &mut body, &arrays);
                    changed = true;
                }
                i += 1;
            }
            None => i += 1,
        }
    }
    if !changed {
        return text.to_owned();
    }
    let mut out = head.join("\n");
    out.push_str("\n\n");
    out.push_str(&body.join("\n"));
    out.push('\n');
    out
}

/// A run's string and where it goes.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Rewrite<'t> {
    /// What the bytes are relative to.
    base: Base<'t>,
    /// Offset of the first byte.
    lo: i64,
    /// The bytes, in order.
    bytes: Vec<u8>,
}

/// One frame array a rewrite declares: its name, the slots it replaces,
/// and its length in bytes.
type Array = (String, Vec<String>, usize);

impl Rewrite<'_> {
    /// The call that writes the run's bytes, and the frame array it needs.
    ///
    /// # Arguments
    ///
    /// * `body` - The body's lines.
    /// * `from` - The run's first line.
    /// * `to` - Just past its last line.
    /// * `decls` - The declared names and their types.
    ///
    /// # Returns
    ///
    /// The line, and the array to declare (none for a pointer's run);
    /// `None` when the frame's slots do not make one array.
    fn apply(
        &self,
        body: &[String],
        from: usize,
        to: usize,
        decls: &BTreeMap<&str, &str>,
    ) -> Option<(String, Vec<Array>)> {
        let len = self.bytes.len();
        let (text, terminated) = match self.bytes.split_last() {
            Some((0, chars)) => (chars, true),
            _ => (self.bytes.as_slice(), false),
        };
        let (dest, arrays) = match self.base {
            Base::Pointer(p) => {
                let at = if self.lo == 0 {
                    p.to_owned()
                } else {
                    format!(
                        "({p} + {})",
                        expr::render_const(self.lo.cast_unsigned(), true)
                    )
                };
                (format!("(char*){at}"), Vec::new())
            }
            Base::Frame => {
                let (name, covered) = frame_slots(decls, self.lo, len)?;
                let others: Vec<&str> = covered.iter().copied().filter(|n| *n != name).collect();
                let outside = body
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| *k < from || *k >= to);
                for (_, line) in outside {
                    if others.iter().any(|o| !word_positions(line, o).is_empty()) {
                        return None;
                    }
                    let taken = word_positions(line, name)
                        .into_iter()
                        .all(|at| line.get(..at).is_some_and(|h| h.ends_with('&')));
                    if !taken {
                        return None;
                    }
                }
                (
                    name.to_owned(),
                    vec![(
                        name.to_owned(),
                        covered.into_iter().map(str::to_owned).collect(),
                        len,
                    )],
                )
            }
        };
        let literal = crate::strings::escape_text(&String::from_utf8_lossy(text));
        let pad = pad_of(body.get(from)?);
        let line = if terminated {
            format!("{pad}strcpy({dest}, \"{literal}\");")
        } else {
            format!("{pad}memcpy({dest}, \"{literal}\", {len});")
        };
        Some((line, arrays))
    }
}

/// The frame slot that starts at `lo` and every declared slot the `len`
/// bytes from there touch, when each lies inside them.
///
/// # Arguments
///
/// * `decls` - The declared names and their types.
/// * `lo` - The first byte's frame offset.
/// * `len` - How many bytes.
///
/// # Returns
///
/// The first slot's name and all the slots', the first among them.
fn frame_slots<'t>(
    decls: &BTreeMap<&'t str, &'t str>,
    lo: i64,
    len: usize,
) -> Option<(&'t str, Vec<&'t str>)> {
    let hi = lo.checked_add(i64::try_from(len).ok()?)?;
    let mut first = None;
    let mut covered = Vec::new();
    for (name, ty) in decls {
        let Some(off) = slot_of(name) else {
            continue;
        };
        let size = i64::from(type_bytes(ty)?);
        if off + size <= lo || off >= hi {
            continue;
        }
        if off < lo || off + size > hi {
            return None;
        }
        if off == lo {
            first = Some(*name);
        }
        covered.push(*name);
    }
    Some((first?, covered))
}

/// Declares each frame array a rewrite made, in place of the slots it
/// covers, and spells the first slot's address as the array's name.
///
/// # Arguments
///
/// * `head` - The header lines, declarations included, edited in place.
/// * `body` - The body, edited in place.
/// * `arrays` - Each array's name, the slots it replaces, and its length.
fn declare_arrays(head: &mut Vec<String>, body: &mut [String], arrays: &[Array]) {
    for (name, slots, len) in arrays {
        let mut last = None;
        for (k, line) in head.iter_mut().enumerate() {
            let Some((ty, items)) = declaration(line) else {
                continue;
            };
            last = Some(k);
            let kept: Vec<String> = items
                .iter()
                .filter(|(stars, n)| !stars.is_empty() || !slots.iter().any(|s| s == n))
                .map(|(stars, n)| format!("{stars}{n}"))
                .collect();
            if kept.len() != items.len() {
                *line = if kept.is_empty() {
                    String::new()
                } else {
                    format!("{ty} {};", kept.join(", "))
                };
            }
        }
        let at = last.map_or(head.len(), |k| k + 1);
        head.insert(at, format!("char {name}[{len}];"));
        head.retain(|l| !l.is_empty());
        let address = format!("&{name}");
        for line in body.iter_mut() {
            if line.contains(&address) {
                *line = rename_word(line, &address, name);
            }
        }
    }
}

/// The run of constant stores that starts at line `i`, when its bytes
/// spell a string.
///
/// # Arguments
///
/// * `body` - The body's lines.
/// * `i` - The first line.
/// * `decls` - The declared names and their types.
///
/// # Returns
///
/// Just past the run's last line, and its string.
fn string_run<'t>(
    body: &'t [String],
    i: usize,
    decls: &BTreeMap<&str, &str>,
) -> Option<(usize, Rewrite<'t>)> {
    let pad = indent_of(body.get(i)?);
    let (first, _) = constant_stores(body.get(i)?, decls)?;
    let base = first.first()?.base;
    let mut bytes: BTreeMap<i64, u8> = BTreeMap::new();
    let mut stores = 0;
    let mut end = i;
    while let Some(line) = body.get(end).filter(|l| indent_of(l) == pad) {
        let Some((targets, value)) = constant_stores(line, decls) else {
            break;
        };
        if stores >= RUN_MAX || targets.iter().any(|t| t.base != base) {
            break;
        }
        for t in &targets {
            for k in 0..t.width {
                let byte = value.checked_shr(u32::from(k) * 8).unwrap_or(0) & 0xff;
                bytes.insert(t.off + i64::from(k), u8::try_from(byte).ok()?);
            }
            stores += 1;
        }
        end += 1;
    }
    let (&lo, _) = bytes.first_key_value()?;
    let run: Vec<u8> = bytes.values().copied().collect();
    let contiguous = bytes
        .keys()
        .enumerate()
        .all(|(k, off)| i64::try_from(k).is_ok_and(|k| lo + k == *off));
    let text = match run.split_last() {
        Some((0, chars)) => chars,
        _ => run.as_slice(),
    };
    let spells = text.len() >= STRING_CHARS
        && text.iter().all(|b| crate::strings::literal_byte(*b))
        && stores >= STRING_STORES;
    (contiguous && spells).then_some((
        end,
        Rewrite {
            base,
            lo,
            bytes: run,
        },
    ))
}

/// Reads a statement that assigns one constant to stores: `local_18 = 47;`,
/// `local_18 = local_14 = 47;`, `*(uint64_t*)a1 = 0x6c6c6568;`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `decls` - The declared names and their types.
///
/// # Returns
///
/// Each place written and the constant, or `None` when the statement is
/// anything else.
fn constant_stores<'t>(
    line: &'t str,
    decls: &BTreeMap<&str, &str>,
) -> Option<(Vec<Store<'t>>, u64)> {
    let body = line.trim().strip_suffix(';')?;
    let mut parts: Vec<&str> = body.split(" = ").collect();
    let value = signed_const(parts.pop()?)?;
    if parts.is_empty() {
        return None;
    }
    let stores = parts
        .into_iter()
        .map(|t| store_at(t, decls))
        .collect::<Option<Vec<Store<'t>>>>()?;
    Some((stores, value))
}

/// Reads a constant: a number, a character literal (`'dcba'` is
/// `0x64636261`), a negative one as its two's complement.
///
/// # Arguments
///
/// * `t` - The text.
fn signed_const(t: &str) -> Option<u64> {
    match ctext::tokens(t.trim()).ok()?.as_slice() {
        [Tok::Int(v, _)] => Some(*v),
        [Tok::Punct("-"), Tok::Int(v, _)] => Some(v.wrapping_neg()),
        _ => None,
    }
}

/// Reads the place a store writes: a declared frame slot, a typed store to
/// a slot's address, or a typed store through a pointer variable at a
/// constant offset.
///
/// # Arguments
///
/// * `target` - The left-hand side.
/// * `decls` - The declared names and their types.
fn store_at<'t>(target: &'t str, decls: &BTreeMap<&str, &str>) -> Option<Store<'t>> {
    let target = target.trim();
    if let Some(off) = slot_of(target) {
        let width = type_bytes(decls.get(target)?)?;
        return Some(Store {
            base: Base::Frame,
            off,
            width,
        });
    }
    let rest = target.strip_prefix("*(")?;
    let (ty, addr) = rest.split_once("*)")?;
    let width = type_bytes(ty)?;
    if let Some(slot) = addr.strip_prefix('&') {
        let off = slot_of(slot).filter(|_| decls.contains_key(slot))?;
        return Some(Store {
            base: Base::Frame,
            off,
            width,
        });
    }
    let (p, off) = match addr.strip_prefix('(').and_then(|a| a.strip_suffix(')')) {
        Some(sum) => {
            let (p, k) = sum.split_once(" + ")?;
            (p, i64::try_from(parse_const(k)?).ok()?)
        }
        None => (addr, 0),
    };
    (is_ident(p) && slot_of(p).is_none()).then_some(Store {
        base: Base::Pointer(p),
        off,
        width,
    })
}

/// The frame offset a `local_N` slot names: `N` bytes below the frame's
/// base.
///
/// # Arguments
///
/// * `name` - A name.
fn slot_of(name: &str) -> Option<i64> {
    let hex = name.strip_prefix("local_")?;
    let n = u64::from_str_radix(hex, 16).ok()?;
    i64::try_from(n).ok().map(i64::wrapping_neg)
}

/// The width in bytes of an integer type a store or a slot has.
///
/// # Arguments
///
/// * `ty` - The type.
///
/// # Returns
///
/// 1, 2, 4 or 8, or `None` for any other type.
fn type_bytes(ty: &str) -> Option<u8> {
    match ty {
        "uint8_t" | "int8_t" | "char" => Some(1),
        "uint16_t" | "int16_t" => Some(2),
        "uint32_t" | "int32_t" => Some(4),
        "uint64_t" | "int64_t" => Some(8),
        _ => None,
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::store_strings;

    /// A string built on the stack a byte at a time, two slots sharing a
    /// byte, is a `strcpy` into one `char` array, and the call's address
    /// of the first slot is the array.
    #[test]
    fn a_stack_string_is_a_strcpy() {
        let text = concat!(
            "// signature: void f()\n",
            "uint8_t local_18, local_17, local_16, local_15, local_14;\n",
            "\n",
            "local_18 = 104;\n",
            "local_17 = 105;\n",
            "local_16 = local_15 = 33;\n",
            "local_14 = 0;\n",
            "return use(&local_18);\n",
        );
        let out = store_strings(text);
        assert!(out.contains("char local_18[5];"), "{out}");
        assert!(out.contains("strcpy(local_18, \"hi!!\");"), "{out}");
        assert!(out.contains("return use(local_18);"), "{out}");
        assert!(!out.contains("uint8_t"), "{out}");
    }

    /// Overlapping wide stores through a pointer spell their string in
    /// memory order; a slot read elsewhere, or a lone wide store, keeps the
    /// stores.
    #[test]
    fn wide_stores_through_a_pointer_are_one_strcpy() {
        let text = concat!(
            "// signature: void f(uint64_t a1)\n",
            "uint64_t local_18;\n",
            "uint16_t local_10;\n",
            "\n",
            "*(uint64_t*)(a1 + 5) = 0x646c726f77202c;\n",
            "*(uint64_t*)a1 = 0x77202c6f6c6c6568;\n",
            "local_18 = 0x7974742f7665642f;\n",
            "local_10 = 49;\n",
            "use(&local_18, local_10);\n",
            "*(uint64_t*)a1 = 0x6f6c6c6568;\n",
            "return;\n",
        );
        let out = store_strings(text);
        assert!(
            out.contains("strcpy((char*)a1, \"hello, world\");"),
            "{out}"
        );
        assert!(out.contains("local_18 = 0x7974742f7665642f;"), "{out}");
        assert!(out.contains("*(uint64_t*)a1 = 0x6f6c6c6568;"), "{out}");
    }
}
