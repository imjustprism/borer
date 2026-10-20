//! Runs of stores read as the library call a compiler expanded them from.
//!
//! Constant bytes that spell a string are a `strcpy` or a `memcpy` of a
//! literal, and wide moves from one object to another are a `memcpy`.
//!
//! A compiler writes a short string into a buffer as a few wide constant
//! stores, and obfuscated code builds one on its stack a byte at a time so
//! it never sits in the image. Either way the text shows a run of
//! constants whose bytes, laid out in memory, spell the string. A
//! structure assignment is a run of 8- or 16-byte moves, each from the
//! source to the same place in the destination. Each run becomes one call;
//! a run that writes the stack makes the slots it fills one array, which
//! is what the source declared.

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

/// Fewest bytes a run of moves copies before it counts as one object's
/// copy: two 8-byte moves.
const COPY_BYTES: usize = 16;

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

/// One frame array a rewrite declares: its element type, its name, the
/// slots it replaces, and its length in bytes; a temporary whose
/// declaration goes is one with no name.
type Array = (&'static str, String, Vec<String>, usize);

/// A rewrite of the run starting at a line: just past its last line, the
/// line that replaces it, and the frame arrays it declares.
type Rewritten = (usize, String, Vec<Array>);

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
    rewrite_runs(text, |body, i, decls| {
        let (end, rewrite) = string_run(body, i, decls)?;
        let (line, arrays) = rewrite.apply(body, i, end, decls)?;
        Some((end, line, arrays))
    })
}

/// Rewrites each run of moves from one object to the same places in
/// another as one `memcpy`.
///
/// A run is consecutive statements at one depth, each a move of 8 or 16
/// bytes (`*(uint64_t*)(a1 + 8) = *(uint64_t*)(a2 + 8);`) or half of one
/// through a temporary the run alone names (`var1 = *(uint128_t*)a2;`
/// before `*(uint128_t*)a1 = var1;`). Every move reads one base and writes
/// another at the same distance from where each starts, the moves cover
/// one range of at least [`COPY_BYTES`] with no gap and no byte twice, and
/// there are two or more: `memcpy(dst, src, n)`, the structure assignment
/// it compiles from. A destination on the frame makes the slots one
/// `uint8_t` array, as for a string ([`store_strings`]). The temporaries'
/// declarations go with the run.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those runs rewritten.
pub(super) fn copy_runs(text: &str) -> String {
    rewrite_runs(text, |body, i, decls| {
        let (end, run) = copy_run(body, i, decls)?;
        run.apply(body, i, end, decls)
    })
}

/// Rewrites the runs one rule reads, a declaration's slots and all.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
/// * `rule` - Reads the run starting at a body line, given the body and
///   the declared names with their types.
///
/// # Returns
///
/// The text with each run the rule reads replaced.
fn rewrite_runs(
    text: &str,
    rule: impl Fn(&[String], usize, &BTreeMap<&str, &str>) -> Option<Rewritten>,
) -> String {
    let Some(p) = parts(text) else {
        return text.to_owned();
    };
    let mut decls: BTreeMap<&str, &str> = p
        .head
        .get(p.decls..)
        .unwrap_or_default()
        .iter()
        .filter_map(|d| declaration(d))
        .flat_map(|(ty, items)| {
            items
                .into_iter()
                .map(move |(stars, n)| (n, pointee(ty, stars)))
        })
        .collect();
    let params = p
        .head
        .iter()
        .find_map(|h| h.strip_prefix("// signature: "))
        .and_then(|sig| sig.split_once('(')?.1.strip_suffix(')'));
    for param in params.unwrap_or_default().split(", ") {
        if let Some((ty, name)) = param.rsplit_once(' ') {
            let bare = name.trim_start_matches('*');
            let stars = name.get(..name.len() - bare.len()).unwrap_or("");
            decls.entry(bare).or_insert(pointee(ty.trim_end(), stars));
        }
    }
    let mut head: Vec<String> = p.head.iter().map(|l| (*l).to_owned()).collect();
    let mut body: Vec<String> = p.body.iter().map(|l| (*l).to_owned()).collect();
    let mut changed = false;
    let mut i = 0;
    while i < body.len() {
        if let Some((end, line, arrays)) = rule(&body, i, &decls) {
            body.splice(i..end, [line]);
            declare_arrays(&mut head, &mut body, &arrays);
            changed = true;
        }
        i += 1;
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
            Base::Pointer(p) => (at(p, self.lo, decls, "char*"), Vec::new()),
            Base::Frame => {
                let array = frame_array(body, (from, to), decls, (self.lo, len), "char")?;
                (array.1.clone(), vec![array])
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

/// The type a declaration gives a name, a pointer's as what the run
/// needs of it: `void *`, `char *`, or `*` for any other pointer.
///
/// # Arguments
///
/// * `ty` - The declared type, without the stars.
/// * `stars` - The name's stars.
fn pointee<'t>(ty: &'t str, stars: &str) -> &'t str {
    match (stars, ty.trim_end_matches(" *")) {
        ("", _) if !ty.ends_with('*') => ty,
        ("" | "*", "void") => "void *",
        ("" | "*", "char") => "char *",
        _ => "*",
    }
}

/// The address `off` bytes past a pointer variable as a call's pointer
/// argument: `p`, or `(p + 0x10)`, cast to `cast` unless the variable is
/// declared one, or one converting to it.
///
/// # Arguments
///
/// * `p` - The variable.
/// * `off` - The offset.
/// * `decls` - The declared names and their types.
/// * `cast` - The argument's pointer type: `char*` or `void*`.
fn at(p: &str, off: i64, decls: &BTreeMap<&str, &str>, cast: &str) -> String {
    let addr = if off == 0 {
        p.to_owned()
    } else {
        format!("({p} + {})", expr::render_const(off.cast_unsigned(), true))
    };
    let ty = decls.get(p).copied().unwrap_or("");
    let fits = ty == "void *" || ty == "char *" || (cast == "void*" && ty == "*");
    if fits && off == 0 {
        addr
    } else {
        format!("({cast}){addr}")
    }
}

/// The array a run's frame bytes make of the slots they cover.
///
/// The slots must start at the run's first byte and lie inside its bytes
/// ([`frame_slots`]); outside the run's lines the others may be named
/// nowhere and the first only by its address, which the array's name is.
///
/// # Arguments
///
/// * `body` - The body's lines.
/// * `(from, to)` - The run's first line and just past its last.
/// * `decls` - The declared names and their types.
/// * `(lo, len)` - The first byte's frame offset and how many bytes.
/// * `elem` - The array's element type.
///
/// # Returns
///
/// The array, or `None` when the slots make none.
fn frame_array(
    body: &[String],
    (from, to): (usize, usize),
    decls: &BTreeMap<&str, &str>,
    (lo, len): (i64, usize),
    elem: &'static str,
) -> Option<Array> {
    let (name, covered) = frame_slots(decls, lo, len)?;
    let outside = body
        .iter()
        .enumerate()
        .filter(|(k, _)| *k < from || *k >= to);
    for (_, line) in outside {
        if covered
            .iter()
            .any(|o| *o != name && !word_positions(line, o).is_empty())
        {
            return None;
        }
        let taken = word_positions(line, name)
            .into_iter()
            .all(|at| line.get(..at).is_some_and(|h| h.ends_with('&')));
        if !taken {
            return None;
        }
    }
    Some((
        elem,
        name.to_owned(),
        covered.into_iter().map(str::to_owned).collect(),
        len,
    ))
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
        let size = match *ty {
            "void *" | "char *" | "*" => 8,
            other => i64::from(type_bytes(other).unwrap_or(1)),
        };
        if off + size <= lo || off >= hi {
            continue;
        }
        type_bytes(ty)?;
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
/// * `arrays` - Each array's element type, name, the slots it replaces,
///   and its length; one with no name only drops its slots.
fn declare_arrays(head: &mut Vec<String>, body: &mut [String], arrays: &[Array]) {
    for (elem, name, slots, len) in arrays {
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
        if !name.is_empty() {
            let at = last.map_or(head.len(), |k| k + 1);
            head.insert(at, format!("{elem} {name}[{len}];"));
        }
        head.retain(|l| !l.is_empty());
        if name.is_empty() {
            continue;
        }
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

/// A run of moves read off the text: what each move writes and reads, by
/// base and offset, and the temporaries it moves through.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CopyRun<'t> {
    /// Each move's destination and source, of one width.
    moves: Vec<(Store<'t>, Store<'t>)>,
    /// The temporaries the moves go through.
    temps: Vec<&'t str>,
}

impl CopyRun<'_> {
    /// The `memcpy` the run is, with the frame array and the temporaries'
    /// declarations it replaces.
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
    /// The rewrite, or `None` when the moves are no one copy.
    fn apply(
        &self,
        body: &[String],
        from: usize,
        to: usize,
        decls: &BTreeMap<&str, &str>,
    ) -> Option<Rewritten> {
        let (first_dst, first_src) = self.moves.first()?;
        let (dst_base, src_base) = (first_dst.base, first_src.base);
        if dst_base == src_base || self.moves.len() < 2 {
            return None;
        }
        let shift = first_src.off - first_dst.off;
        let mut covered: BTreeMap<i64, u8> = BTreeMap::new();
        for (d, s) in &self.moves {
            if d.base != dst_base || s.base != src_base || s.off - d.off != shift {
                return None;
            }
            if covered.insert(d.off, d.width).is_some() {
                return None;
            }
        }
        let (&lo, _) = covered.first_key_value()?;
        let mut next = lo;
        for (off, width) in &covered {
            if *off != next {
                return None;
            }
            next += i64::from(*width);
        }
        let len = usize::try_from(next - lo).ok()?;
        if len < COPY_BYTES {
            return None;
        }
        let elsewhere = body
            .iter()
            .enumerate()
            .filter(|(k, _)| *k < from || *k >= to)
            .any(|(_, line)| {
                self.temps
                    .iter()
                    .any(|t| !word_positions(line, t).is_empty())
            });
        if elsewhere {
            return None;
        }
        let source = match src_base {
            Base::Pointer(p) => at(p, lo + shift, decls, "void*"),
            Base::Frame => return None,
        };
        let mut arrays: Vec<Array> = self
            .temps
            .iter()
            .map(|t| ("", String::new(), vec![(*t).to_owned()], 0))
            .collect();
        let dest = match dst_base {
            Base::Pointer(p) => at(p, lo, decls, "void*"),
            Base::Frame => {
                let array = frame_array(body, (from, to), decls, (lo, len), "uint8_t")?;
                let name = array.1.clone();
                arrays.push(array);
                name
            }
        };
        let pad = pad_of(body.get(from)?);
        let n = expr::render_const(u64::try_from(len).ok()?, true);
        Some((to, format!("{pad}memcpy({dest}, {source}, {n});"), arrays))
    }
}

/// The run of moves that starts at line `i`.
///
/// # Arguments
///
/// * `body` - The body's lines.
/// * `i` - The first line.
/// * `decls` - The declared names and their types.
///
/// # Returns
///
/// Just past the run's last line, and its moves; `None` when a temporary
/// it loads is not stored inside it.
fn copy_run<'t>(
    body: &'t [String],
    i: usize,
    decls: &BTreeMap<&str, &str>,
) -> Option<(usize, CopyRun<'t>)> {
    let pad = indent_of(body.get(i)?);
    let mut moves = Vec::new();
    let mut temps = Vec::new();
    let mut held: BTreeMap<&str, Store<'t>> = BTreeMap::new();
    let mut bases: (Option<Base<'t>>, Option<Base<'t>>) = (None, None);
    let mut end = i;
    while let Some(line) = body.get(end).filter(|l| indent_of(l) == pad) {
        let Some((lhs, rhs)) = line
            .trim()
            .strip_suffix(';')
            .and_then(|t| t.split_once(" = "))
        else {
            break;
        };
        if moves.len() >= RUN_MAX || rhs.contains(" = ") {
            break;
        }
        let source = store_at(rhs, decls);
        let same = |seen: &mut Option<Base<'t>>, b: Base<'t>| *seen.get_or_insert(b) == b;
        if vars::is_var_name(lhs)
            && let Some(s) = source.clone()
            && decls.get(lhs).and_then(|ty| type_bytes(ty)) == Some(s.width)
            && !held.contains_key(lhs)
        {
            if !same(&mut bases.1, s.base) {
                break;
            }
            held.insert(lhs, s);
            temps.push(lhs);
        } else if let Some(d) = store_at(lhs, decls) {
            let Some(s) = held.get(rhs).cloned().or(source) else {
                break;
            };
            if s.width != d.width
                || !matches!(d.width, 8 | 16)
                || !same(&mut bases.0, d.base)
                || !same(&mut bases.1, s.base)
            {
                break;
            }
            held.remove(rhs);
            moves.push((d, s));
        } else {
            break;
        }
        end += 1;
    }
    (held.is_empty() && !moves.is_empty()).then_some((end, CopyRun { moves, temps }))
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

/// Reads the place a store writes or a load reads: a declared frame slot,
/// a typed access to a slot's address, or a typed access through a
/// pointer variable at a constant offset.
///
/// # Arguments
///
/// * `target` - The place as the text spells it.
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
/// 1, 2, 4, 8 or 16, or `None` for any other type.
fn type_bytes(ty: &str) -> Option<u8> {
    match ty {
        "uint8_t" | "int8_t" | "char" => Some(1),
        "uint16_t" | "int16_t" => Some(2),
        "uint32_t" | "int32_t" => Some(4),
        "uint64_t" | "int64_t" => Some(8),
        "uint128_t" => Some(16),
        _ => None,
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{copy_runs, store_strings};

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

    /// Wide moves from one pointer's object to another's, one through a
    /// temporary, are one `memcpy`; moves into the frame make the slots one
    /// array the call fills.
    #[test]
    fn wide_moves_between_objects_are_a_memcpy() {
        let text = concat!(
            "// signature: void f(uint64_t a1, uint64_t a2)\n",
            "uint128_t var1, local_28, local_18;\n",
            "\n",
            "var1 = *(uint128_t*)a2;\n",
            "*(uint128_t*)(a1 + 0x10) = *(uint128_t*)(a2 + 0x10);\n",
            "*(uint128_t*)a1 = var1;\n",
            "local_28 = *(uint128_t*)a1;\n",
            "local_18 = *(uint128_t*)(a1 + 0x10);\n",
            "return use(&local_28);\n",
        );
        let out = copy_runs(text);
        assert!(out.contains("memcpy((void*)a1, (void*)a2, 0x20);"), "{out}");
        assert!(out.contains("memcpy(local_28, (void*)a1, 0x20);"), "{out}");
        assert!(out.contains("uint8_t local_28[32];"), "{out}");
        assert!(out.contains("return use(local_28);"), "{out}");
        assert!(!out.contains("var1"), "{out}");
    }

    /// Moves between two places of one object, moves with a gap, and moves
    /// through a temporary read after the run stay as they are.
    #[test]
    fn moves_that_are_no_one_copy_stay() {
        let text = concat!(
            "// signature: void f(uint64_t a1, uint64_t a2)\n",
            "uint64_t var1;\n",
            "\n",
            "*(uint64_t*)a1 = *(uint64_t*)(a1 + 8);\n",
            "*(uint64_t*)(a1 + 8) = *(uint64_t*)(a1 + 0x10);\n",
            "sub_1();\n",
            "*(uint64_t*)a1 = *(uint64_t*)a2;\n",
            "*(uint64_t*)(a1 + 0x10) = *(uint64_t*)(a2 + 0x10);\n",
            "sub_1();\n",
            "var1 = *(uint64_t*)a2;\n",
            "*(uint64_t*)(a1 + 8) = *(uint64_t*)(a2 + 8);\n",
            "*(uint64_t*)a1 = var1;\n",
            "return var1;\n",
        );
        assert_eq!(copy_runs(text), text);
    }
}
