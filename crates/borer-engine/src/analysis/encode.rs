//! Encodings: what a serializer writes onto its stream, field by field, the
//! outbound half of a wire protocol.
//!
//! A message class encodes itself by taking its stream and handing it one
//! value at a time: a fixed bit count from a buffer it filled from a field,
//! a run of bytes under a length it wrote first, or a helper that writes a
//! whole member (a vector, an array with its count, a string). Some
//! encoders pack every field into one local buffer first and hand the
//! stream the buffer once; the buffer's layout is then the wire layout.
//! This module reads an encoder's pseudo-C for each of those shapes and
//! lists the fields in wire order with their widths and the object field
//! each came from, following helpers into the members they write.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::classes::{FieldLabel, deref_pointee, field_labels};
use super::schema::{
    closing_bound, header_bound, ident_char, is_loop_header, mirror_names, param_class, split_args,
};
use super::{Analysis, Overlay, name_of, plain_text_cached, resolve};
use crate::fxmap::FxHashMap;
use crate::program::Program;

/// Helpers followed below the encoder itself.
const DEPTH_MAX: usize = 6;
/// Most fields one encoding lists, nested ones included.
const FIELDS_MAX: usize = 512;
/// Widest single write taken as a bit count rather than a stray constant.
const BITS_MAX: u64 = 4096;
/// Lines searched back for where a written value came from: an encoder
/// that packs a buffer fills it well above the one write, guards between.
const SOURCE_BACK: usize = 40;
/// Assignments followed back through registers to a field.
const HOPS_MAX: usize = 4;
/// Longest expression quoted as a source when it names no single field.
const EXPR_MAX: usize = 48;
/// Farthest a local may lie inside an object a helper built at another
/// local: a string built at `&local_48` has its length at `local_10`.
const OBJECT_SPAN_MAX: u64 = 0x100;
/// Identifiers a field can hang off: the object and the parameters.
const BASES: [&str; 9] = ["this", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8"];
/// Call names that hand back one element of a container by index, the
/// text after the container's name: `operator []`, `AtIndex`, `At`.
const ELEMENT_ACCESSORS: [&str; 5] = [
    "::operator [](",
    "AtIndex(",
    "::At(",
    "::ElementAt(",
    "::Get(",
];
/// A stream type naming a reader: the other direction, which
/// [`super::schema`] covers.
const READER_MARK: &str = "Reader";

/// One value an encoder puts on the wire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Write {
    /// Its place on the wire: `3`, or `3.2` inside a member a helper wrote.
    pub order: String,
    /// What it is: `u32`, `bit`, `f32`, `bytes`, `struct`, or `u120`.
    pub kind: String,
    /// Bits on the wire, `0` when the helper decides.
    pub bits: u64,
    /// Where the value came from: `this+0x20`, `this->startTick`, an
    /// expression when several fields feed it, or `?`.
    pub source: String,
    /// How it reached the stream: `vtable[21]`, a helper's name, or
    /// `packed` for a component of a buffer written whole.
    pub via: String,
    /// The loop bound the write repeats under, when it does.
    pub repeat: Option<String>,
    /// The values a helper writes in turn: the members of a struct.
    pub children: Vec<Write>,
    /// The field's name when the object's class names it, else empty.
    pub name: String,
}

/// What one function writes onto its stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Encoding {
    /// The function.
    pub entry: u64,
    /// The parameter the stream arrives in, when an accessor names it.
    pub stream: String,
    /// The writes in wire order.
    pub fields: Vec<Write>,
}

/// One write as the text states it, before helpers are followed.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Raw {
    /// A fixed bit count from a buffer variable.
    Bits {
        /// The bit count.
        bits: u64,
        /// The variable the buffer is, without its `&`.
        buffer: String,
    },
    /// A run of bytes from a pointer under a count read from a field.
    Run {
        /// The pointer expression.
        pointer: String,
        /// The count as a field: `this+0x58`.
        count: String,
    },
    /// A helper handed the stream and one member.
    Helper {
        /// The helper as the text names it.
        callee: String,
        /// Index of the member among its arguments.
        index: usize,
        /// The member argument as written.
        arg: String,
    },
}

/// One write with where it sits in the text.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Site {
    /// Zero-based line index.
    line: usize,
    /// The write.
    raw: Raw,
    /// The loop bound around it, when any.
    repeat: Option<String>,
}

/// Tells whether `word` is something a value passes through on its way
/// to the stream: a register, a temporary, a local or a home slot.
///
/// # Arguments
///
/// * `word` - An identifier.
fn is_carrier(word: &str) -> bool {
    if let Some(n) = word
        .strip_prefix("tmp_")
        .or_else(|| word.strip_prefix("xmm"))
        .or_else(|| word.strip_prefix("home_"))
        .or_else(|| word.strip_prefix("local_"))
    {
        return !n.is_empty() && n.chars().all(|c| c.is_ascii_alphanumeric());
    }
    matches!(
        word,
        "rax" | "rbx" | "rcx" | "rdx" | "rsi" | "rdi" | "rbp" | "rsp"
    ) || word
        .strip_prefix('r')
        .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
}

/// Every identifier in `expr`, in order.
///
/// # Arguments
///
/// * `expr` - The text.
fn identifiers(expr: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut at = 0;
    while at < expr.len() {
        let rest = &expr[at..];
        let len = rest.find(|c: char| !ident_char(c)).unwrap_or(rest.len());
        if len == 0 {
            at += rest.chars().next().map_or(1, char::len_utf8);
            continue;
        }
        let word = &rest[..len];
        if word.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
            out.push(word);
        }
        at += len;
    }
    out
}

/// Parses a decimal or `0x` hexadecimal number at the start of `s`.
///
/// # Arguments
///
/// * `s` - The text.
///
/// # Returns
///
/// The value and the bytes it took, `0x` included, or `None`.
fn number(s: &str) -> Option<(u64, usize)> {
    let t = s.trim_start();
    let lead = s.len() - t.len();
    let (digits, radix, prefix) = match t.strip_prefix("0x") {
        Some(h) => (h, 16, 2),
        None => (t, 10, 0),
    };
    let len = digits
        .find(|c: char| !c.is_ascii_hexdigit())
        .unwrap_or(digits.len());
    if len == 0 {
        return None;
    }
    let v = u64::from_str_radix(&digits[..len], radix).ok()?;
    Some((v, lead + prefix + len))
}

/// Spells an offset as the tables do.
///
/// # Arguments
///
/// * `off` - The offset.
fn offset_text(off: u64) -> String {
    format!("{off:#x}")
}

/// Every field `expr` reads or takes the address of, as `base+0x20` or
/// `base->name`, in order, duplicates kept.
///
/// `*(uint32_t*)(this + 0x58)`, `this + 48` and `this->field_0x58` all
/// name `this+0x58`; `this->startTick` stays a name.
///
/// # Arguments
///
/// * `expr` - The text.
fn field_tokens(expr: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = expr.as_bytes();
    let mut at = 0;
    while at < expr.len() {
        let rest = &expr[at..];
        let len = rest.find(|c: char| !ident_char(c)).unwrap_or(rest.len());
        if len == 0 {
            at += 1;
            continue;
        }
        let word = &rest[..len];
        let bounded = at == 0 || !ident_char(char::from(bytes[at - 1]));
        at += len;
        if !bounded || !BASES.contains(&word) {
            continue;
        }
        let after = &expr[at..];
        if let Some(tail) = after.strip_prefix(" + ") {
            if let Some((off, _)) = number(tail) {
                out.push(format!("{word}+{}", offset_text(off)));
            }
        } else if let Some(tail) = after.strip_prefix("->") {
            let len = tail.find(|c: char| !ident_char(c)).unwrap_or(tail.len());
            let member = &tail[..len];
            if let Some(hex) = member.strip_prefix("field_0x")
                && let Ok(off) = u64::from_str_radix(hex, 16)
            {
                out.push(format!("{word}+{}", offset_text(off)));
            } else if !member.is_empty() {
                out.push(format!("{word}->{member}"));
            }
        }
    }
    out
}

/// The one field `expr` amounts to, when it does.
///
/// A bare read (`this->field_0x20`, `*(uint16_t*)(this + 0x58)`), a scaled
/// or masked read of one field, or a small-string select
/// (`this->field_0x50 != 0 ? this->field_0x50 : this + 32`) each name one
/// field; anything else with fields in it is quoted when short.
///
/// # Arguments
///
/// * `expr` - The right side of an assignment, or an argument.
///
/// # Returns
///
/// The field, a short expression, or `None` when `expr` reads no field.
fn field_of(expr: &str) -> Option<String> {
    let fields = field_tokens(expr);
    let Some(first) = fields.first().cloned() else {
        let words = identifiers(expr);
        let bases: Vec<&str> = words
            .iter()
            .copied()
            .filter(|w| BASES.contains(w))
            .collect();
        return match bases.as_slice() {
            [one] if !words.iter().any(|w| is_carrier(w)) => Some((*one).to_owned()),
            _ => None,
        };
    };
    if fields.iter().all(|f| *f == first) || expr.contains("!= 0 ?") {
        return Some(first);
    }
    let mut short = compact_expr(expr.trim().trim_end_matches(';'));
    if short.len() > EXPR_MAX {
        short.truncate(EXPR_MAX.saturating_sub(1));
        short.push('…');
    }
    Some(short)
}

/// Spells every field read in `expr` the short way: `*(uint32_t*)(this +
/// 0x50)` and `this->field_0x50` both become `this+0x50`.
///
/// # Arguments
///
/// * `expr` - The text.
fn compact_expr(expr: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let mut rest = expr;
    while let Some(at) = rest.find("*(") {
        let (head, tail) = rest.split_at(at);
        let replaced = tail.find("*)(").and_then(|close| {
            let inner = &tail[close + 3..];
            let end = inner.find(')')?;
            let tokens = field_tokens(&inner[..end]);
            let [field] = tokens.as_slice() else {
                return None;
            };
            Some((field.clone(), close + 3 + end + 1))
        });
        out.push_str(head);
        match replaced {
            Some((field, len)) => {
                out.push_str(&field);
                rest = &tail[len..];
            }
            None => {
                out.push_str("*(");
                rest = &tail[2..];
            }
        }
    }
    out.push_str(rest);
    let mut text = String::with_capacity(out.len());
    let mut rest = out.as_str();
    while let Some(at) = rest.find("->field_0x") {
        let (head, tail) = rest.split_at(at);
        let hex_len = tail["->field_0x".len()..]
            .find(|c: char| !c.is_ascii_hexdigit())
            .unwrap_or(tail.len() - "->field_0x".len());
        text.push_str(head);
        text.push('+');
        text.push_str(&tail["->field_".len()..tail.len().min("->field_0x".len() + hex_len)]);
        rest = &tail["->field_0x".len() + hex_len..];
    }
    text.push_str(rest);
    text
}

/// The container an element came from, when `expr` indexes one:
/// `Util::Array<T>::operator [](a2, rbx)` and
/// `Util::Dictionary<K,V>::KeyValuePairAtIndex(a2, rdi)` hand back `a2[i]`.
///
/// # Arguments
///
/// * `expr` - The right side of an assignment.
fn element_of(expr: &str) -> Option<String> {
    let (at, len) = ELEMENT_ACCESSORS
        .iter()
        .find_map(|name| expr.find(name).map(|at| (at, name.len())))?;
    let args = args_at(expr, at + len - 1)?;
    let base = args
        .first()
        .map(|a| a.trim())
        .filter(|a| BASES.contains(a))
        .unwrap_or("");
    Some(format!("{base}[i]"))
}

/// The last carrier a value was copied from before the trail runs cold:
/// `home_0 = local_10` where nothing assigns `local_10` but the helper
/// that built an object around it.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the write.
/// * `var` - The variable the stream was handed.
///
/// # Returns
///
/// The carrier and the line it was last seen assigned on.
fn source_chain_end(lines: &[&str], at: usize, var: &str) -> Option<(String, usize)> {
    let mut want = var.to_owned();
    let mut end = at;
    let mut last: Option<(String, usize)> = None;
    for _ in 0..HOPS_MAX {
        let from = end.saturating_sub(SOURCE_BACK);
        let Some((k, expr)) = (from..end)
            .rev()
            .find_map(|k| assigned_to(lines[k], &want).map(|e| (k, e)))
        else {
            break;
        };
        let words = identifiers(expr);
        let carriers: Vec<&str> = words
            .iter()
            .copied()
            .filter(|w| is_carrier(w) && *w != want)
            .collect();
        match carriers.as_slice() {
            [one] => {
                want = (*one).to_owned();
                end = k;
                last = Some((want.clone(), k));
            }
            _ => break,
        }
    }
    last.or_else(|| is_carrier(var).then(|| (var.to_owned(), at)))
}

/// A carrier plus a constant (`rbx + 8`): the member at that offset of
/// whatever the carrier holds, an element of a container most often.
///
/// # Arguments
///
/// * `expr` - The right side of an assignment.
fn carrier_plus(expr: &str) -> Option<(&str, u64)> {
    let (lhs, rhs) = expr.trim().split_once(" + ")?;
    let lhs = lhs.trim();
    if !is_carrier(lhs) {
        return None;
    }
    let (off, len) = number(rhs)?;
    (len == rhs.trim().len()).then_some((lhs, off))
}

/// The expression assigned to `var` on `line`, whether it is the only
/// target or one of a chain (`rdi = home_0 = *(uint32_t*)(a2 + 8);`).
///
/// # Arguments
///
/// * `line` - The trimmed line.
/// * `var` - The variable.
fn assigned_to<'l>(line: &'l str, var: &str) -> Option<&'l str> {
    let head = format!("{var} = ");
    let at = line.find(&head)?;
    if at > 0 && ident_char(char::from(line.as_bytes()[at - 1])) {
        return None;
    }
    let before = line[..at].trim();
    if !(before.is_empty() || before.ends_with('=')) {
        return None;
    }
    let mut value = line[at + head.len()..].trim().trim_end_matches(';');
    while let Some((target, rest)) = value.split_once(" = ")
        && !target.is_empty()
        && target.chars().all(ident_char)
    {
        value = rest.trim();
    }
    Some(value)
}

/// The field the value in `var` came from, followed back through the
/// carriers it passed.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the write; the search runs back from there.
/// * `var` - The variable the stream was handed.
fn source_of(lines: &[&str], at: usize, var: &str) -> Option<String> {
    let mut want = var.to_owned();
    let mut end = at;
    for _ in 0..HOPS_MAX {
        let from = end.saturating_sub(SOURCE_BACK);
        let found = (from..end)
            .rev()
            .find_map(|k| assigned_to(lines[k], &want).map(|e| (k, e)));
        let (k, expr) = found?;
        if let Some(element) = element_of(expr) {
            return Some(element);
        }
        if let Some(field) = field_of(expr) {
            return Some(field);
        }
        if let Some((carrier, off)) = carrier_plus(expr)
            && let Some(base) = source_of(lines, k, carrier)
        {
            return Some(format!("{base}+{off:#x}"));
        }
        let words = identifiers(expr);
        if words.is_empty() {
            end = k;
            continue;
        }
        let carriers: Vec<&str> = words
            .into_iter()
            .filter(|w| is_carrier(w) && *w != want)
            .collect();
        match carriers.as_slice() {
            [one] => {
                want = (*one).to_owned();
                end = k;
            }
            _ => return None,
        }
    }
    None
}

/// The helper that filled `var` through an out argument, with the field
/// it was handed.
///
/// `sub_1409a79ac(this, this + 48, &local_18, ...)` fills `local_18` from
/// `this+0x30`. A helper handed only other locals is followed through
/// them: a string built into one buffer and copied into another still
/// came from the field the first was built from.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the write.
/// * `var` - The buffer variable.
fn out_arg_source(lines: &[&str], at: usize, var: &str) -> Option<(String, String)> {
    out_arg_source_below(lines, at, var, HOPS_MAX)
}

/// [`out_arg_source`] with the hops through other locals still allowed.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the write.
/// * `var` - The buffer variable.
/// * `hops` - Locals still followed.
fn out_arg_source_below(
    lines: &[&str],
    at: usize,
    var: &str,
    hops: usize,
) -> Option<(String, String)> {
    let needle = format!("&{var}");
    let from = at.saturating_sub(SOURCE_BACK);
    let exact = (from..at).rev().find_map(|k| {
        let line = lines[k];
        let pos = line.find(&needle)?;
        if line[pos + needle.len()..].starts_with(|c: char| ident_char(c)) {
            return None;
        }
        let open = line[..pos].rfind('(')?;
        let callee = line[..open]
            .rsplit(|c: char| !(ident_char(c) || c == ':'))
            .next()?;
        if callee.is_empty() || !callee.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
            return None;
        }
        let args = args_at(line, open)?;
        if let Some(field) = args
            .iter()
            .filter(|a| !BASES.contains(&a.as_str()))
            .find_map(|a| field_of(a))
        {
            return Some((field, callee.to_owned()));
        }
        let below = hops.checked_sub(1)?;
        args.iter()
            .filter_map(|a| a.strip_prefix('&'))
            .filter(|other| *other != var && is_carrier(other))
            .find_map(|other| out_arg_source_below(lines, k, other, below))
            .map(|(field, _)| (field, callee.to_owned()))
    });
    exact.or_else(|| {
        let inside = var
            .strip_prefix("local_")
            .and_then(|h| u64::from_str_radix(h, 16).ok())?;
        let mut best: Option<(u64, &str)> = None;
        for (k, line) in lines.iter().enumerate().take(at).skip(from) {
            let mut rest = *line;
            while let Some(pos) = rest.find("&local_") {
                let hex: String = rest[pos + "&local_".len()..]
                    .chars()
                    .take_while(char::is_ascii_hexdigit)
                    .collect();
                rest = &rest[pos + 1..];
                let Ok(base) = u64::from_str_radix(&hex, 16) else {
                    continue;
                };
                if base > inside
                    && base - inside <= OBJECT_SPAN_MAX
                    && best.is_none_or(|(b, _)| base < b)
                {
                    best = Some((base, lines[k]));
                }
            }
        }
        let (base, _) = best?;
        let below = hops.checked_sub(1)?;
        out_arg_source_below(lines, at, &format!("local_{base:x}"), below)
    })
}

/// The declared type of each variable, from the declaration lines above
/// the body.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
fn declared_types(lines: &[&str]) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for line in lines {
        if line.starts_with("//") || line.is_empty() {
            continue;
        }
        let Some(decl) = line.strip_suffix(';') else {
            break;
        };
        if decl.contains('=') || decl.contains('(') {
            break;
        }
        let Some((ty, names)) = decl.split_once(' ') else {
            break;
        };
        if !(ty.ends_with("_t") || matches!(ty, "float" | "double")) {
            break;
        }
        for name in names.split(',') {
            out.insert(name.trim().to_owned(), ty.to_owned());
        }
    }
    out
}

/// The loop bound enclosing each line, by brace tracking.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
fn loop_bounds(lines: &[&str]) -> Vec<Option<String>> {
    /// One open block: a loop's bound once known, or not a loop.
    struct Open {
        /// The bound, when the header stated it.
        bound: Option<String>,
        /// Whether the block is a loop at all.
        is_loop: bool,
        /// Lines inside, to receive a `do { } while` bound at the close.
        lines: Vec<usize>,
    }
    let mut out: Vec<Option<String>> = vec![None; lines.len()];
    let mut stack: Vec<Open> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        if line.starts_with("//") {
            continue;
        }
        let closes = line.starts_with('}');
        if closes && let Some(done) = stack.pop() {
            let bound = if done.is_loop && done.bound.is_none() {
                closing_bound(line)
            } else {
                done.bound
            };
            if bound.is_some() {
                for k in done.lines {
                    if out[k].is_none() {
                        out[k].clone_from(&bound);
                    }
                }
            }
        }
        let inherited = stack.iter().rev().find_map(|o| o.bound.clone());
        if let Some(b) = inherited
            && out[i].is_none()
        {
            out[i] = Some(b);
        }
        for open in &mut stack {
            open.lines.push(i);
        }
        let body = if closes {
            line.trim_start_matches('}').trim_start()
        } else {
            line
        };
        if body.ends_with('{') {
            let header = body.trim_end_matches('{').trim();
            stack.push(Open {
                bound: header_bound(header),
                is_loop: is_loop_header(header),
                lines: Vec::new(),
            });
        }
    }
    out
}

/// The identifiers that carry the stream in this text: what an accessor
/// returned, copies of it, and the objects virtual writes go through.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `streams` - Text a stream class contains, from `[types] stream`.
///
/// # Returns
///
/// The stream variables, and the parameter the accessor took when one did.
fn stream_vars(lines: &[&str], streams: &[&str]) -> (Vec<String>, Option<String>) {
    let mut vars: Vec<String> = Vec::new();
    let mut param = None;
    for line in lines {
        if line.starts_with("//") {
            continue;
        }
        if let Some(class) = deref_pointee(line)
            && streams.iter().any(|t| class.contains(t))
        {
            if class.contains(READER_MARK) {
                continue;
            }
            if let Some((lhs, rest)) = line.split_once(" = ")
                && identifiers(lhs).len() == 1
            {
                vars.push(lhs.trim().to_owned());
                if param.is_none()
                    && let Some(open) = rest.find(">::operator ->(")
                {
                    let inner = &rest[open + ">::operator ->(".len()..];
                    let arg = inner.split([')', ',']).next().unwrap_or("").trim();
                    if BASES.contains(&arg) {
                        param = Some(arg.to_owned());
                    }
                }
            }
            continue;
        }
        if let Some(pos) = line.find("->vtable[")
            && let Some(open) = line[pos..].find("](").map(|p| p + pos + 1)
            && args_at(line, open).is_some_and(|args| classify(&args).is_some())
        {
            let obj = &line[..pos];
            if let Some(base) = identifiers(obj)
                .into_iter()
                .find(|w| BASES.contains(w) || is_carrier(w))
                && !vars.iter().any(|v| v == base)
            {
                vars.push(base.to_owned());
            }
        }
        if let Some((lhs, rhs)) = line.split_once(" = ")
            && let Some(rhs) = rhs.strip_suffix(';')
            && identifiers(lhs).len() == 1
            && identifiers(rhs).len() == 1
            && rhs.trim() == identifiers(rhs)[0]
            && vars.iter().any(|v| v == rhs.trim())
            && !vars.iter().any(|v| v == lhs.trim())
        {
            vars.push(lhs.trim().to_owned());
        }
    }
    (vars, param)
}

/// Reads a write off an argument list once the stream itself is dropped:
/// a buffer and a bit count, or a pointer and a count read from a field.
///
/// # Arguments
///
/// * `args` - The remaining arguments.
fn classify(args: &[String]) -> Option<Raw> {
    match args {
        [buffer, width] if buffer.starts_with('&') => {
            let (bits, len) = number(width)?;
            if len != width.trim().len() || !(1..=BITS_MAX).contains(&bits) {
                return None;
            }
            Some(Raw::Bits {
                bits,
                buffer: buffer.trim_start_matches('&').to_owned(),
            })
        }
        [pointer, count] => {
            if number(count).is_some() || pointer.starts_with('&') {
                return None;
            }
            let fields = field_tokens(count);
            let built = identifiers(pointer).iter().any(|w| is_carrier(w));
            let count = match fields.as_slice() {
                [field] => field.clone(),
                [] if built && is_carrier(count.trim()) => count.trim().to_owned(),
                _ => return None,
            };
            Some(Raw::Run {
                pointer: pointer.clone(),
                count,
            })
        }
        _ => None,
    }
}

/// The argument list of the call whose `(` is at `open`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `open` - Index of the opening parenthesis.
fn args_at(line: &str, open: usize) -> Option<Vec<String>> {
    let mut depth = 0i32;
    for (k, b) in line.bytes().enumerate().skip(open) {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(split_args(&line[open + 1..k]));
                }
            }
            _ => {}
        }
    }
    None
}

/// Every write one line makes, in order.
///
/// # Arguments
///
/// * `line` - The trimmed line.
/// * `streams` - The stream variables.
fn writes_on_line(line: &str, streams: &[String]) -> Vec<Raw> {
    let mut out = Vec::new();
    let is_stream = |a: &str| streams.iter().any(|s| s == a.trim());
    if let Some(pos) = line.find("->vtable[")
        && let Some(open) = line[pos..].find("](").map(|p| p + pos + 1)
        && let Some(args) = args_at(line, open)
        && let Some(raw) = classify(&args)
    {
        out.push(raw);
        return out;
    }
    if let Some(pos) = line.rfind("))(")
        && let Some(args) = args_at(line, pos + 2)
    {
        let rest: Vec<String> = args
            .iter()
            .filter(|a| !is_stream(a) && !identifiers(a).iter().any(|w| is_stream(w)))
            .cloned()
            .collect();
        if rest.len() < args.len()
            && let Some(raw) = classify(&rest)
        {
            out.push(raw);
            return out;
        }
    }
    let mut at = 0;
    while let Some(open) = line[at..].find('(').map(|p| p + at) {
        at = open + 1;
        let name_start = line[..open]
            .char_indices()
            .rev()
            .take_while(|(_, c)| ident_char(*c) || matches!(c, ':' | '<' | '>' | ','))
            .last()
            .map_or(open, |(k, _)| k);
        let name = &line[name_start..open];
        if name.is_empty()
            || !name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            || name.contains("::operator")
            || name.ends_with('>')
        {
            continue;
        }
        let Some(args) = args_at(line, open) else {
            continue;
        };
        if args.len() < 2 || !is_stream(&args[0]) {
            continue;
        }
        let member = args.iter().enumerate().skip(1).find(|(_, a)| {
            !field_tokens(a).is_empty()
                || a.starts_with('&')
                || identifiers(a).iter().any(|w| is_carrier(w))
        });
        if let Some((index, arg)) = member {
            out.push(Raw::Helper {
                callee: name.to_owned(),
                index,
                arg: arg.clone(),
            });
        }
    }
    out
}

/// Every write a function's text makes, in order, with the loop each is
/// in.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
/// * `stream_types` - Text a stream class contains, from `[types] stream`.
///
/// # Returns
///
/// The writes, the stream variables, and the parameter the stream came in.
fn sites_in(text: &str, stream_types: &[&str]) -> (Vec<Site>, Vec<String>, Option<String>) {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let (streams, param) = stream_vars(&lines, stream_types);
    let bounds = loop_bounds(&lines);
    let mut sites = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        if line.starts_with("//") {
            continue;
        }
        for raw in writes_on_line(line, &streams) {
            sites.push(Site {
                line: i,
                raw,
                repeat: bounds[i].clone(),
            });
        }
    }
    (sites, streams, param)
}

/// The kind of a fixed write: `bit`, `f32` for a float buffer, else `u<bits>`.
///
/// # Arguments
///
/// * `bits` - The bit count.
/// * `declared` - The buffer's declared type, when any.
fn fixed_kind(bits: u64, declared: Option<&str>) -> String {
    match (bits, declared) {
        (1, _) => "bit".to_owned(),
        (32, Some("float")) => "f32".to_owned(),
        (64, Some("double")) => "f64".to_owned(),
        (n, _) => format!("u{n}"),
    }
}

/// The locals a buffer written whole is made of, in address order, each
/// with its width: `&local_18` written as 120 bits spans the locals from
/// `local_18` up to fifteen bytes above it.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `buffer` - The buffer variable.
/// * `bits` - The bit count written.
///
/// # Returns
///
/// `(local, bytes)` pairs, or none when the buffer is not a frame local
/// or nothing else lies inside it.
pub(crate) fn packed_components(lines: &[&str], buffer: &str, bits: u64) -> Vec<(String, u64)> {
    let Some(base) = buffer
        .strip_prefix("local_")
        .and_then(|h| u64::from_str_radix(h, 16).ok())
    else {
        return Vec::new();
    };
    let bytes = bits.div_ceil(8);
    let low = base.saturating_sub(bytes);
    let mut offsets: Vec<u64> = Vec::new();
    for line in lines {
        for word in identifiers(line) {
            if let Some(h) = word.strip_prefix("local_")
                && let Ok(off) = u64::from_str_radix(h, 16)
                && off > low
                && off <= base
                && !offsets.contains(&off)
            {
                offsets.push(off);
            }
        }
    }
    offsets.sort_unstable_by(|a, b| b.cmp(a));
    if offsets.len() < 2 {
        return Vec::new();
    }
    offsets
        .iter()
        .enumerate()
        .map(|(i, &off)| {
            let next = offsets.get(i + 1).copied().unwrap_or(low);
            (format!("local_{off:x}"), off - next)
        })
        .collect()
}

/// One recovery's inputs and the helpers it has followed.
struct Ctx<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Discovery results.
    analysis: &'a Analysis,
    /// Names in force.
    overlay: &'a Overlay,
    /// The overlay's fingerprint, keying the shared decompilation memo.
    overlay_key: u64,
    /// Helpers followed so far, by callee and member index.
    memo: RefCell<FxHashMap<(String, usize), Vec<Write>>>,
}

impl<'a> Ctx<'a> {
    /// Opens a recovery over one program.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - Discovery results.
    /// * `overlay` - Names in force.
    fn new(program: &'a Program, analysis: &'a Analysis, overlay: &'a Overlay) -> Self {
        Ctx {
            program,
            analysis,
            overlay,
            overlay_key: overlay.fingerprint(),
            memo: RefCell::new(FxHashMap::default()),
        }
    }

    /// What `entry` writes onto its stream.
    ///
    /// # Arguments
    ///
    /// * `entry` - The encoder's entry.
    /// * `class` - The object's class when known, for field names.
    fn encoding(&self, entry: u64, class: Option<&str>) -> Option<Encoding> {
        let text = plain_text_cached(
            self.program,
            self.analysis,
            self.overlay,
            self.overlay_key,
            entry,
        )?;
        let (sites, _, param) = sites_in(&text, &self.analysis.packs.list("types", "stream"));
        if sites.is_empty() {
            return None;
        }
        let lines: Vec<&str> = text.lines().map(str::trim).collect();
        let mut fields = self.writes_of(&lines, &sites, DEPTH_MAX);
        let object = class.map(str::to_owned).or_else(|| param_class(&text));
        if let Some(class) = object {
            let labels = field_labels(self.program, self.analysis, self.overlay, &class);
            let own = labels.values().any(|l| matches!(l, FieldLabel::Member(_)));
            let borrowed = if own {
                Vec::new()
            } else {
                mirror_names(self.program, self.analysis, self.overlay, &class)
            };
            if borrowed.is_empty() {
                for f in &mut fields {
                    if let Some(off) = this_offset(&f.source)
                        && let Some(label) = labels.get(&off)
                    {
                        f.name = label.to_string();
                    }
                }
            } else {
                let groups = logical_groups(&fields);
                for (f, g) in fields.iter_mut().zip(groups) {
                    if let Some(n) = borrowed.get(g) {
                        f.name.clone_from(n);
                    }
                }
            }
        }
        Some(Encoding {
            entry,
            stream: param.unwrap_or_default(),
            fields,
        })
    }

    /// Turns the sites of one text into writes, following helpers.
    ///
    /// # Arguments
    ///
    /// * `lines` - The text's lines, trimmed.
    /// * `sites` - Its writes.
    /// * `depth` - Helpers still allowed below.
    fn writes_of(&self, lines: &[&str], sites: &[Site], depth: usize) -> Vec<Write> {
        let types = declared_types(lines);
        let mut out: Vec<Write> = Vec::new();
        for site in sites {
            if out.len() >= FIELDS_MAX {
                break;
            }
            let mut writes = match &site.raw {
                Raw::Bits { bits, buffer } => {
                    let parts = if *bits > 64 {
                        packed_components(lines, buffer, *bits)
                    } else {
                        Vec::new()
                    };
                    if parts.is_empty() {
                        vec![Write {
                            order: String::new(),
                            kind: fixed_kind(*bits, types.get(buffer).map(String::as_str)),
                            bits: *bits,
                            source: source_of(lines, site.line, buffer)
                                .or_else(|| {
                                    out_arg_source(lines, site.line, buffer).map(|(f, _)| f)
                                })
                                .or_else(|| {
                                    let (carrier, _) = source_chain_end(lines, site.line, buffer)?;
                                    out_arg_source(lines, site.line, &carrier).map(|(f, _)| f)
                                })
                                .unwrap_or_else(|| "?".to_owned()),
                            via: "stream".to_owned(),
                            repeat: site.repeat.clone(),
                            children: Vec::new(),
                            name: String::new(),
                        }]
                    } else {
                        parts
                            .into_iter()
                            .map(|(local, bytes)| {
                                let (source, via) = match source_of(lines, site.line, &local) {
                                    Some(s) => (s, "packed".to_owned()),
                                    None => out_arg_source(lines, site.line, &local).map_or_else(
                                        || ("?".to_owned(), "packed".to_owned()),
                                        |(f, helper)| (f, format!("packed via {helper}")),
                                    ),
                                };
                                Write {
                                    order: String::new(),
                                    kind: fixed_kind(bytes * 8, None),
                                    bits: bytes * 8,
                                    source,
                                    via,
                                    repeat: site.repeat.clone(),
                                    children: Vec::new(),
                                    name: String::new(),
                                }
                            })
                            .collect()
                    }
                }
                Raw::Run { pointer, count } => {
                    let source = field_of(pointer)
                        .or_else(|| {
                            identifiers(pointer)
                                .into_iter()
                                .find(|w| is_carrier(w))
                                .and_then(|w| {
                                    source_of(lines, site.line, w).or_else(|| {
                                        out_arg_source(lines, site.line, w).map(|(f, _)| f)
                                    })
                                })
                        })
                        .unwrap_or_else(|| "?".to_owned());
                    let count = if is_carrier(count) {
                        source_of(lines, site.line, count)
                            .or_else(|| out_arg_source(lines, site.line, count).map(|(f, _)| f))
                            .unwrap_or_else(|| "?".to_owned())
                    } else {
                        count.clone()
                    };
                    vec![Write {
                        order: String::new(),
                        kind: format!("bytes[{count}]"),
                        bits: 0,
                        source,
                        via: "stream".to_owned(),
                        repeat: site.repeat.clone(),
                        children: Vec::new(),
                        name: String::new(),
                    }]
                }
                Raw::Helper { callee, index, arg } => {
                    let source = field_of(arg)
                        .or_else(|| {
                            let var = arg.trim_start_matches('&');
                            source_of(lines, site.line, var)
                                .or_else(|| out_arg_source(lines, site.line, var).map(|(f, _)| f))
                        })
                        .or_else(|| {
                            let (carrier, off) = carrier_plus(arg)?;
                            source_of(lines, site.line, carrier).map(|b| format!("{b}+{off:#x}"))
                        })
                        .unwrap_or_else(|| "?".to_owned());
                    let children = if depth == 0 {
                        Vec::new()
                    } else {
                        self.follow(callee, *index, depth - 1)
                    };
                    let (kind, bits) = match children.as_slice() {
                        [] => ("?".to_owned(), 0),
                        [one] if one.repeat.is_none() => (one.kind.clone(), one.bits),
                        [len, run] if is_string(len, run) => ("string".to_owned(), 0),
                        _ => ("struct".to_owned(), 0),
                    };
                    vec![Write {
                        order: String::new(),
                        kind,
                        bits,
                        source,
                        via: callee.clone(),
                        repeat: site.repeat.clone(),
                        children,
                        name: String::new(),
                    }]
                }
            };
            if let Some(bound) = &site.repeat
                && is_carrier(bound)
                && let Some(field) = source_of(lines, site.line, bound)
            {
                for w in &mut writes {
                    w.repeat = Some(field.clone());
                }
            }
            out.append(&mut writes);
        }
        for (i, w) in out.iter_mut().enumerate() {
            renumber(w, &(i + 1).to_string());
        }
        out
    }

    /// What a helper writes of the member at argument `index`, once per
    /// helper and index.
    ///
    /// # Arguments
    ///
    /// * `callee` - The helper as the text names it.
    /// * `index` - The member's argument index.
    /// * `depth` - Helpers still allowed below.
    fn follow(&self, callee: &str, index: usize, depth: usize) -> Vec<Write> {
        let key = (callee.to_owned(), index);
        if let Some(w) = self.memo.borrow().get(&key) {
            return w.clone();
        }
        self.memo.borrow_mut().insert(key.clone(), Vec::new());
        let found = self.follow_uncached(callee, index, depth);
        self.memo.borrow_mut().insert(key, found.clone());
        found
    }

    /// Reads a helper's text for what it writes of one member.
    ///
    /// # Arguments
    ///
    /// * `callee` - The helper as the text names it.
    /// * `index` - The member's argument index.
    /// * `depth` - Helpers still allowed below.
    fn follow_uncached(&self, callee: &str, index: usize, depth: usize) -> Vec<Write> {
        let Ok(entry) = resolve(self.program, self.analysis, self.overlay, callee) else {
            return Vec::new();
        };
        let Some(text) = plain_text_cached(
            self.program,
            self.analysis,
            self.overlay,
            self.overlay_key,
            entry,
        ) else {
            return Vec::new();
        };
        let (sites, _, _) = sites_in(&text, &self.analysis.packs.list("types", "stream"));
        if sites.is_empty() {
            return Vec::new();
        }
        let lines: Vec<&str> = text.lines().map(str::trim).collect();
        let member = format!("a{}", index + 1);
        let mut writes = self.writes_of(&lines, &sites, depth);
        for w in &mut writes {
            relativize(w, &member);
        }
        writes
    }

    /// The virtual of a class that writes the most, with its encoding.
    ///
    /// # Arguments
    ///
    /// * `class` - The qualified class name.
    fn class_encoding(&self, class: &str) -> Option<(u64, Encoding)> {
        let info = self.analysis.classes.by_name.get(class)?;
        let mut best: Option<((usize, usize), (u64, Encoding))> = None;
        for &entry in &info.slots {
            let Some(e) = self.encoding(entry, Some(class)) else {
                continue;
            };
            let score = weight(&e.fields);
            if score.0 == 0 {
                continue;
            }
            if best.as_ref().is_none_or(|(s, _)| score > *s) {
                best = Some((score, (entry, e)));
            }
        }
        best.map(|(_, found)| found)
    }
}

/// The logical field each top-level write belongs to, by index.
///
/// A run of bytes under the length written just before it is the same
/// string as that length, so a mirror class's names, one per field, land
/// on both.
///
/// # Arguments
///
/// * `fields` - The top-level writes in wire order.
fn logical_groups(fields: &[Write]) -> Vec<usize> {
    let mut out = Vec::with_capacity(fields.len());
    let mut group = 0usize;
    for (i, f) in fields.iter().enumerate() {
        let continues = i > 0
            && f.kind
                .strip_prefix("bytes[")
                .and_then(|k| k.strip_suffix(']'))
                .is_some_and(|count| fields[i - 1].source == count);
        if i > 0 && !continues {
            group += 1;
        }
        out.push(group);
    }
    out
}

/// Whether two writes are a string: a length, then the bytes under it.
///
/// # Arguments
///
/// * `len` - The first write.
/// * `run` - The second.
fn is_string(len: &Write, run: &Write) -> bool {
    len.bits > 0
        && len.bits <= 32
        && len.repeat.is_none()
        && run.kind == format!("bytes[{}]", len.source)
}

/// Numbers a write and its children under `order`.
///
/// # Arguments
///
/// * `w` - The write.
/// * `order` - Its number.
fn renumber(w: &mut Write, order: &str) {
    w.order = order.to_owned();
    for (i, c) in w.children.iter_mut().enumerate() {
        renumber(c, &format!("{order}.{}", i + 1));
    }
}

/// Rewrites a helper's sources relative to the member it was handed:
/// `a2+0x4` becomes `+0x4`.
///
/// # Arguments
///
/// * `w` - The write.
/// * `member` - The helper's parameter holding the member.
fn relativize(w: &mut Write, member: &str) {
    if let Some(rest) = w.source.strip_prefix(member)
        && (rest.starts_with('+') || rest.starts_with("->") || rest.starts_with('['))
    {
        w.source = rest.to_owned();
    } else if w.source == member {
        w.source = "+0x0".to_owned();
    }
    if let Some(r) = &w.repeat
        && let Some(rest) = r.strip_prefix(member)
        && (rest.starts_with('+') || rest.starts_with("->"))
    {
        w.repeat = Some(rest.to_owned());
    }
    if let Some(inner) = w
        .kind
        .strip_prefix("bytes[")
        .and_then(|k| k.strip_suffix(']'))
        && let Some(rest) = inner.strip_prefix(member)
    {
        if rest.is_empty() {
            w.kind = "bytes[+0x0]".to_owned();
        } else if rest.starts_with('+') || rest.starts_with("->") {
            w.kind = format!("bytes[{rest}]");
        }
    }
    for c in &mut w.children {
        relativize(c, member);
    }
}

/// The object offset a source names, when it is `this+0x..`.
///
/// # Arguments
///
/// * `source` - The source text.
fn this_offset(source: &str) -> Option<u64> {
    let off = source.strip_prefix("this+")?;
    super::parse_addr(off)
}

/// How many writes a list holds, children included.
///
/// # Arguments
///
/// * `fields` - The writes.
fn count(fields: &[Write]) -> usize {
    fields.iter().map(|f| 1 + count(&f.children)).sum()
}

/// How many writes came to something (a width, a run, or a member a
/// helper was followed into), children included, then how many writes
/// there are at all: what a class's virtuals are ranked by.
///
/// # Arguments
///
/// * `fields` - The writes.
fn weight(fields: &[Write]) -> (usize, usize) {
    fields.iter().fold((0, 0), |(known, all), f| {
        let (below_known, below_all) = weight(&f.children);
        let counted = usize::from(f.kind != "?") + below_known;
        (known + counted, all + 1 + below_all)
    })
}

/// Bits the fixed writes of a list add up to, children included; runs and
/// unknown helpers add nothing.
///
/// # Arguments
///
/// * `fields` - The writes.
fn fixed_bits(fields: &[Write]) -> u64 {
    fields
        .iter()
        .map(|f| {
            if f.children.is_empty() {
                f.bits
            } else {
                fixed_bits(&f.children)
            }
        })
        .sum()
}

/// What `entry` writes onto its stream.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The encoder's entry.
///
/// # Returns
///
/// The encoding, or `None` when the function does not decompile or hands
/// its stream nothing.
#[must_use]
pub fn encoding_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Encoding> {
    Ctx::new(program, analysis, overlay).encoding(entry, None)
}

/// The virtual of `class` that writes the most onto a stream, with what
/// it writes.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `class` - The qualified class name.
#[must_use]
pub fn encoding_for_class(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<(u64, Encoding)> {
    Ctx::new(program, analysis, overlay).class_encoding(class)
}

/// The source of a write as the compact form spells it: `+0x20` for an
/// object field, else the source itself.
///
/// # Arguments
///
/// * `source` - The source text.
fn compact_source(source: &str) -> String {
    match source.strip_prefix("this") {
        Some(rest) if rest.starts_with('+') || rest.starts_with("->") => rest.to_owned(),
        _ => source.to_owned(),
    }
}

/// Spells writes on one line: `u32@+0x20 bytes[+0x58]@+0x50 bit@+0xe0`,
/// a helper's members in braces, a repeat as `*bound`.
///
/// # Arguments
///
/// * `fields` - The writes.
#[must_use]
pub fn compact_writes(fields: &[Write]) -> String {
    /// Most writes spelled out on one line.
    const COMPACT_MAX: usize = 12;
    let mut parts: Vec<String> = fields
        .iter()
        .take(COMPACT_MAX)
        .map(|f| {
            let src = compact_source(&f.source);
            let kind = match f
                .kind
                .strip_prefix("bytes[")
                .and_then(|k| k.strip_suffix(']'))
            {
                Some(count) => format!("bytes[{}]", compact_source(count)),
                None => f.kind.clone(),
            };
            let src = if f.name.is_empty() {
                src
            } else {
                format!("{src}={}", f.name)
            };
            let repeat = f
                .repeat
                .as_deref()
                .map_or(String::new(), |r| format!("*{r}"));
            if f.children.len() > 1 && f.kind == "struct" {
                let inner: Vec<String> = f
                    .children
                    .iter()
                    .take(COMPACT_MAX)
                    .map(|c| format!("{}{}", c.kind, c.source))
                    .collect();
                format!("{kind}@{src}{repeat}{{{}}}", inner.join(","))
            } else {
                format!("{kind}@{src}{repeat}")
            }
        })
        .collect();
    if fields.len() > COMPACT_MAX {
        parts.push(format!("+{} more", fields.len() - COMPACT_MAX));
    }
    parts.join(" ")
}

/// Appends the rows of `fields`, numbering nested ones under their parent.
///
/// # Arguments
///
/// * `out` - The table so far.
/// * `fields` - The writes.
fn render_writes(out: &mut String, fields: &[Write]) {
    for f in fields {
        let bits = if f.bits == 0 {
            "-".to_owned()
        } else {
            f.bits.to_string()
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{bits}\t{}\t{}\t{}\t{}",
            f.order,
            f.kind,
            f.source,
            f.via,
            f.repeat.as_deref().unwrap_or("-"),
            f.name
        );
        render_writes(out, &f.children);
    }
}

/// Renders one encoding as a `#`-headed table.
///
/// # Arguments
///
/// * `analysis` - For the encoder's name.
/// * `overlay` - Names in force.
/// * `e` - The encoding.
/// * `class` - The class the table is for, or empty.
fn render_encoding(analysis: &Analysis, overlay: &Overlay, e: &Encoding, class: &str) -> String {
    let name = name_of(analysis, overlay, e.entry);
    let subject = if class.is_empty() {
        name
    } else {
        format!("{class} through {name}")
    };
    let stream = if e.stream.is_empty() {
        String::new()
    } else {
        format!(" from {}", e.stream)
    };
    let mut out = format!(
        "# {subject} @ {:#x} writes {} fields{stream}: {} bits fixed\n",
        e.entry,
        count(&e.fields),
        fixed_bits(&e.fields)
    );
    out.push_str("order\tkind\tbits\tsource\tvia\trepeat\tname\n");
    render_writes(&mut out, &e.fields);
    out
}

/// Renders what a function writes onto its stream.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The encoder's entry.
///
/// # Returns
///
/// The table, or `None` when the function hands its stream nothing.
#[must_use]
pub fn encoding_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let e = encoding_of(program, analysis, overlay, entry)?;
    Some(render_encoding(analysis, overlay, &e, ""))
}

/// Renders what a class writes onto its stream through the virtual that
/// writes the most.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `class` - The qualified class name.
///
/// # Returns
///
/// The table, or `None` when no virtual of the class writes a stream.
#[must_use]
pub fn class_encoding_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<String> {
    let (_, e) = encoding_for_class(program, analysis, overlay, class)?;
    Some(render_encoding(analysis, overlay, &e, class))
}

/// Renders every class whose virtual at `slot` returns a constant, with
/// what its writing virtual puts on the wire: the outbound protocol as one
/// table, ordered by the constant.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn encodings_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let rows = super::vtables::slot_rows(
        program,
        analysis,
        slot,
        filter,
        || Ctx::new(program, analysis, overlay),
        |ctx, c| ctx.class_encoding(&c.class),
    );
    let total = rows.len();
    let written = rows.iter().filter(|r| r.found.is_some()).count();
    let shown = total.min(limit);
    let mut out = format!(
        "# {total} classes answer virtual {slot} with a constant, {written} of them encode a record, showing {shown}\n"
    );
    out.push_str("value\tclass\tencoder\twrites\tbits\tfields\n");
    for row in rows.into_iter().take(limit) {
        let (value, class) = (row.value, row.class);
        match row.found {
            Some((entry, e)) => {
                let _ = writeln!(
                    out,
                    "{value:#x}\t{class}\t{entry:#x}\t{}\t{}\t{}",
                    count(&e.fields),
                    fixed_bits(&e.fields),
                    compact_writes(&e.fields)
                );
            }
            None => {
                let _ = writeln!(out, "{value:#x}\t{class}\t-\t0\t0\t");
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A string-carrying encoder as decompiled: a length in
    /// bits, the bytes under it, and a flag masked from a register.
    const UNLOCK: &str = "// Cmd::Open::Encode @ 0x1409738d8: 83 instructions
// signature: uint64_t Cmd::Open::Encode(Cmd::Open *this, uint64_t a2)
uint16_t home_0;
uint64_t rax, rbx, rdi;

class_141212308::Encode(this, a2);
rax = Core::Ptr<Network::BitWriter>::operator ->(a2);
rbx = rax;
rdi = (this->field_0x50 != 0 ? this->field_0x50 : this + 32);
home_0 = *(uint16_t*)(this + 0x58);
(*(uint64_t*)(rax + 0x30))->vtable[21](&home_0, 16);
(*(uint64_t*)(rbx + 0x30))->vtable[12](rdi, *(uint32_t*)(this + 0x58));
rbx = this->field_0xe0;
rax = Core::Ptr<Network::BitWriter>::operator ->(a2);
home_0 = ((rbx != 1) - 1) & 0xff;
return (*(uint64_t*)(rax + 0x30))->vtable[21](&home_0, 1);
";

    /// An encoder that packs every field into one local buffer and hands
    /// the stream the buffer once.
    const MOVE: &str = "// Cmd::Move::Encode @ 0x1409a786c
// signature: void Cmd::Move::Encode(Cmd::Move *this, const Core::Ptr<Network::BitWriter> &a2)
uint16_t local_b;
uint32_t local_f;
uint64_t rax, local_18, local_14, local_16;
uint8_t local_12, local_11, local_10;

class_141212308::Encode(this, a2);
local_18 = local_10 = local_f = local_b = 0;
sub_1409a79ac(this, this + 48, &local_18, &local_16, &local_14);
local_12 = (int64_t)(this->field_0x40 * 0.25f * 256.0f) & 0xff;
local_11 = (int64_t)((this->field_0x44 + 3.1415927f) / 6.2831855f * 256.0f) & 0xff;
local_10 = (int64_t)((this->field_0x48 + 3.1415927f) / 6.2831855f * 256.0f) & 0xff;
local_f = this->startTick;
if (local_f > this->endTick) {
  assert_failed(\"this->startTick <= this->endTick\", \"commands/movecommand.cc\", 62, __FUNCSIG__);
}
rax = this->endTick - this->startTick;
if (rax > 0xffff) {
  sub_140ccdc5c(\"ERROR: Cannot encode a move command that lasts more than 65535 ticks!\");
  rax = 0xffff;
}
local_b = rax & 0xffff;
rax = Core::Ptr<Network::BitWriter>::operator ->(a2);
(*(uint64_t*)(rax + 0x30))->vtable[21](&local_18, 120);
return;
";

    /// An encoder that builds a string into one local, copies it into
    /// another and hands a helper the copy.
    const COPIED: &str = "// signature: uint64_t X::Encode(X *this, uint64_t a2)
uint32_t local_40, local_3c, home_0;
uint64_t rax, rdx, rbx, rdi, local_48, local_38;

rax = Core::Ptr<Network::BitWriter>::operator ->(a2);
rbx = rax;
sub_140cddd3c(this + 24, &local_38);
local_48 = local_40 = local_3c = 0;
sub_1400cb6dc(&local_48, &local_38, 16);
sub_14083800c(rbx, &local_48);
return;
";

    /// A helper writing a string atom: a string is built at one local from
    /// the atom, its length sits inside that object at another local, and
    /// the bytes run under that length.
    const ATOM: &str = "// signature: uint64_t sub_140838790(uint64_t *a1, uint64_t *a2)
uint16_t home_0;
uint32_t local_10, local_c;
uint64_t rax, local_18;
uint8_t local_48;

local_48 = local_18 = local_10 = local_c = 0;
sub_140ccfdf0(&local_48, *(uint64_t*)a2);
home_0 = local_10;
(*(uint64_t*)(a1 + 0x30))->vtable[21](&home_0, 16);
rax = (*(uint64_t*)(a1 + 0x30))->vtable[12]((local_18 != 0 ? local_18 : &local_48), local_10);
return rax;
";

    /// A helper writing a dictionary: its count, then per pair the key and
    /// the value at eight past the pair.
    const PAIRS: &str = "// signature: void sub_14094fb20(uint64_t *a1, uint32_t *a2)
uint32_t home_0;
uint64_t rax, rbx, rbp, rdi;

rbp = home_0 = *(uint32_t*)(a2 + 8);
(*(uint64_t*)(a1 + 0x30))->vtable[21](&home_0, 32);
rdi = 0;
if ((int32_t)(rbp) > 0) {
  do {
    rax = Util::Dictionary<Util::Text,Record>::KeyValuePairAtIndex(a2, rdi);
    rbx = rax;
    sub_140838790(a1, rax);
    sub_140a843a8(a1, rbx + 8);
    rdi += 1;
  } while ((int32_t)rdi < (int32_t)rbp);
}
return;
";

    /// A helper writing an array: its count, then one element per turn of
    /// a loop through another helper.
    const ARRAY: &str = "// sub_14094fe84 @ 0x14094fe84
// signature: void sub_14094fe84(uint64_t *a1, uint32_t *a2)
uint32_t home_0;
uint64_t rax, rbx, rdi;

rdi = home_0 = *(uint32_t*)(a2 + 8);
(*(uint64_t*)(a1 + 0x30))->vtable[21](&home_0, 32);
rbx = 0;
if ((int32_t)(rdi) > 0) {
  do {
    rax = Util::Array<Kind::Id>::operator [](a2, rbx);
    IO::Adapter<Network::BitWriter,Kind::Id>::Write(a1, rax);
    rbx += 1;
  } while ((int32_t)rbx < (int32_t)rdi);
}
return;
";

    /// Field tokens normalise every spelling of an object field.
    ///
    /// # Panics
    ///
    /// When a spelling is read wrongly.
    #[test]
    fn field_tokens_normalise_spellings() {
        assert_eq!(field_tokens("*(uint16_t*)(this + 0x58)"), ["this+0x58"]);
        assert_eq!(field_tokens("this + 48"), ["this+0x30"]);
        assert_eq!(field_tokens("this->field_0xe0"), ["this+0xe0"]);
        assert_eq!(field_tokens("this->startTick"), ["this->startTick"]);
        assert_eq!(
            field_tokens("(this->field_0x50 != 0 ? this->field_0x50 : this + 32)"),
            ["this+0x50", "this+0x50", "this+0x20"]
        );
        assert!(field_tokens("rax & 0xffff").is_empty());
        assert_eq!(
            field_of("(this->field_0x50 != 0 ? this->field_0x50 : this + 32)").as_deref(),
            Some("this+0x50")
        );
        assert_eq!(
            field_of("this->endTick - this->startTick").as_deref(),
            Some("this->endTick - this->startTick")
        );
        assert_eq!(
            field_of("*(uint32_t*)(this + 0x50) - *(uint32_t*)(this + 0x4c)").as_deref(),
            Some("this+0x50 - this+0x4c")
        );
        assert_eq!(
            compact_expr("(this->field_0x40 * 0.25f) & 0xff"),
            "(this+0x40 * 0.25f) & 0xff"
        );
    }

    /// A string encoder yields its length, its bytes and its flag, the
    /// flag traced back through the register it was masked from.
    ///
    /// # Panics
    ///
    /// When a write disagrees with the text.
    #[test]
    fn a_string_encoder_lists_length_bytes_and_flag() {
        let (sites, streams, param) = sites_in(UNLOCK, crate::pack::defaults("types", "stream"));
        assert_eq!(param.as_deref(), Some("a2"));
        assert!(streams.iter().any(|s| s == "rbx"), "{streams:?}");
        let raws: Vec<&Raw> = sites.iter().map(|s| &s.raw).collect();
        assert_eq!(raws.len(), 3, "{raws:?}");
        assert_eq!(
            *raws[0],
            Raw::Bits {
                bits: 16,
                buffer: "home_0".to_owned()
            }
        );
        assert_eq!(
            *raws[1],
            Raw::Run {
                pointer: "rdi".to_owned(),
                count: "this+0x58".to_owned()
            }
        );
        let lines: Vec<&str> = UNLOCK.lines().map(str::trim).collect();
        assert_eq!(
            source_of(&lines, sites[0].line, "home_0").as_deref(),
            Some("this+0x58")
        );
        assert_eq!(
            source_of(&lines, sites[1].line, "rdi").as_deref(),
            Some("this+0x50")
        );
        assert_eq!(
            source_of(&lines, sites[2].line, "home_0").as_deref(),
            Some("this+0xe0")
        );
        assert!(sites.iter().all(|s| s.repeat.is_none()));
    }

    /// A packed buffer written whole is split into its locals by address,
    /// each with the width up to the next and the field or helper that
    /// filled it.
    ///
    /// # Panics
    ///
    /// When a component disagrees with the text.
    #[test]
    fn a_packed_buffer_is_split_into_its_locals() {
        let (sites, _, _) = sites_in(MOVE, crate::pack::defaults("types", "stream"));
        assert_eq!(sites.len(), 1, "{sites:?}");
        let Raw::Bits { bits, buffer } = &sites[0].raw else {
            panic!("a bits write");
        };
        assert_eq!((*bits, buffer.as_str()), (120, "local_18"));
        let lines: Vec<&str> = MOVE.lines().map(str::trim).collect();
        let parts = packed_components(&lines, buffer, *bits);
        let widths: Vec<u64> = parts.iter().map(|(_, w)| *w).collect();
        assert_eq!(widths, [2, 2, 2, 1, 1, 1, 4, 2], "{parts:?}");
        assert_eq!(parts[0].0, "local_18");
        assert_eq!(parts[7].0, "local_b");
        assert_eq!(
            out_arg_source(&lines, sites[0].line, "local_18"),
            Some(("this+0x30".to_owned(), "sub_1409a79ac".to_owned()))
        );
        assert_eq!(
            source_of(&lines, sites[0].line, "local_12").as_deref(),
            Some("this+0x40")
        );
        assert_eq!(
            source_of(&lines, sites[0].line, "local_f").as_deref(),
            Some("this->startTick")
        );
        assert_eq!(
            source_of(&lines, sites[0].line, "local_b").as_deref(),
            Some("this->endTick - this->startTick"),
            "the clamp to 0xffff is not where the value came from"
        );
        let (sites, _, _) = sites_in(COPIED, crate::pack::defaults("types", "stream"));
        assert_eq!(sites.len(), 1, "{sites:?}");
        let lines: Vec<&str> = COPIED.lines().map(str::trim).collect();
        assert_eq!(
            out_arg_source(&lines, sites[0].line, "local_48"),
            Some(("this+0x18".to_owned(), "sub_1400cb6dc".to_owned()))
        );
    }

    /// An array helper writes its count off the stream's own parameter and
    /// hands each element to another helper inside the loop.
    ///
    /// # Panics
    ///
    /// When a write disagrees with the text.
    #[test]
    fn an_array_helper_writes_a_count_and_repeats() {
        let (sites, streams, param) = sites_in(ARRAY, crate::pack::defaults("types", "stream"));
        assert_eq!(param, None);
        assert_eq!(streams, ["a1"]);
        assert_eq!(sites.len(), 2, "{sites:?}");
        assert_eq!(
            sites[0].raw,
            Raw::Bits {
                bits: 32,
                buffer: "home_0".to_owned()
            }
        );
        assert_eq!(
            sites[1].raw,
            Raw::Helper {
                callee: "IO::Adapter<Network::BitWriter,Kind::Id>::Write".to_owned(),
                index: 1,
                arg: "rax".to_owned()
            },
            "a template writer keeps the commas in its name"
        );
        assert_eq!(sites[1].repeat.as_deref(), Some("rdi"));
        let lines: Vec<&str> = ARRAY.lines().map(str::trim).collect();
        assert_eq!(
            source_of(&lines, sites[1].line, "rax").as_deref(),
            Some("a2[i]"),
            "an element names its array"
        );
        assert_eq!(field_of("a2 & 0xff").as_deref(), Some("a2"));
        assert_eq!(field_of("*(float*)a2").as_deref(), Some("a2"));
        assert_eq!(field_of("rax & 0xff"), None);
        assert_eq!(
            source_of(&lines, sites[0].line, "home_0").as_deref(),
            Some("a2+0x8")
        );
    }

    /// A decoder's accessor names a reader, so its calls are not writes,
    /// and a virtual call that is not a write does not make its object a
    /// stream.
    ///
    /// # Panics
    ///
    /// When a read is taken for a write.
    #[test]
    fn a_reader_opens_no_encoding() {
        let decoder = "// signature: void X::Decode(X *this, uint64_t a2)

rax = Core::Ptr<Network::SafeBitReader>::operator ->(a2);
sub_140cca7cc(rax, this + 0x20);
(a1->field_0x30)->vtable[5](this, rax);
";
        let (sites, streams, param) = sites_in(decoder, crate::pack::defaults("types", "stream"));
        assert!(sites.is_empty(), "{sites:?}");
        assert!(streams.is_empty(), "{streams:?}");
        assert_eq!(param, None);
    }

    /// A string's length and its bytes are one logical field, so a mirror
    /// class's names fall on both, and the next name on the next write.
    ///
    /// # Panics
    ///
    /// When the grouping differs.
    #[test]
    fn a_length_and_its_bytes_are_one_logical_field() {
        let leaf = |kind: &str, source: &str| Write {
            order: String::new(),
            kind: kind.to_owned(),
            bits: 0,
            source: source.to_owned(),
            via: "stream".to_owned(),
            repeat: None,
            children: Vec::new(),
            name: String::new(),
        };
        let fields = vec![
            leaf("u16", "this+0x58"),
            leaf("bytes[this+0x58]", "this+0x50"),
            leaf("u16", "this+0x98"),
            leaf("bytes[this+0x98]", "this+0x90"),
            leaf("bit", "this+0xe0"),
        ];
        assert_eq!(logical_groups(&fields), [0, 0, 1, 1, 2]);
    }

    /// A string built around a local from the atom handed in names that
    /// atom for its length and its bytes.
    ///
    /// # Panics
    ///
    /// When a source disagrees with the text.
    #[test]
    fn an_atom_written_as_a_string_names_the_atom() {
        let (sites, _, _) = sites_in(ATOM, crate::pack::defaults("types", "stream"));
        assert_eq!(sites.len(), 2, "{sites:?}");
        assert_eq!(
            sites[1].raw,
            Raw::Run {
                pointer: "(local_18 != 0 ? local_18 : &local_48)".to_owned(),
                count: "local_10".to_owned()
            }
        );
        let lines: Vec<&str> = ATOM.lines().map(str::trim).collect();
        assert_eq!(
            out_arg_source(&lines, sites[0].line, "local_10"),
            Some(("a2".to_owned(), "sub_140ccfdf0".to_owned())),
            "the length lies inside the string built at local_48"
        );
        assert_eq!(
            source_chain_end(&lines, sites[0].line, "home_0"),
            Some(("local_10".to_owned(), 8))
        );
        assert_eq!(
            assigned_to("local_48 = local_18 = local_10 = local_c = 0;", "local_18"),
            Some("0"),
            "a chain hands back its value"
        );
        let leaf = |kind: &str, source: &str, bits: u64| Write {
            order: String::new(),
            kind: kind.to_owned(),
            bits,
            source: source.to_owned(),
            via: "stream".to_owned(),
            repeat: None,
            children: Vec::new(),
            name: String::new(),
        };
        assert!(is_string(
            &leaf("u16", "a2", 16),
            &leaf("bytes[a2]", "a2", 0)
        ));
        assert!(!is_string(
            &leaf("u16", "a2", 16),
            &leaf("bytes[a3]", "a2", 0)
        ));
    }

    /// A dictionary pair names its container as an element, and the value
    /// at eight past the pair names the element's member.
    ///
    /// # Panics
    ///
    /// When a source disagrees with the text.
    #[test]
    fn a_dictionary_pair_and_its_member_name_the_container() {
        let (sites, _, _) = sites_in(PAIRS, crate::pack::defaults("types", "stream"));
        assert_eq!(sites.len(), 3, "{sites:?}");
        let lines: Vec<&str> = PAIRS.lines().map(str::trim).collect();
        assert_eq!(
            source_of(&lines, sites[1].line, "rax").as_deref(),
            Some("a2[i]")
        );
        assert_eq!(
            source_of(&lines, sites[2].line, "rbx").as_deref(),
            Some("a2[i]"),
            "the pair itself"
        );
        assert_eq!(carrier_plus("rbx + 8"), Some(("rbx", 8)));
        assert_eq!(carrier_plus("this + 8"), None);
        let Raw::Helper { arg, .. } = &sites[2].raw else {
            panic!("a helper write");
        };
        assert_eq!(arg, "rbx + 8");
    }

    /// The compact form spells kinds at offsets, members in braces and a
    /// repeat as a star.
    ///
    /// # Panics
    ///
    /// When the spelling differs.
    #[test]
    fn compact_writes_spell_kinds_at_offsets() {
        let leaf = |kind: &str, source: &str, bits: u64| Write {
            order: String::new(),
            kind: kind.to_owned(),
            bits,
            source: source.to_owned(),
            via: "stream".to_owned(),
            repeat: None,
            children: Vec::new(),
            name: String::new(),
        };
        let mut member = leaf("struct", "this+0x60", 0);
        member.children = vec![leaf("f32", "+0x0", 32), leaf("f32", "+0x4", 32)];
        let mut each = leaf("u8", "?", 8);
        each.repeat = Some("n".to_owned());
        let run = leaf("bytes[this+0x58]", "this+0x50", 0);
        let fields = vec![leaf("u32", "this+0x20", 32), member, each, run];
        assert_eq!(
            compact_writes(&fields),
            "u32@+0x20 struct@+0x60{f32+0x0,f32+0x4} u8@?*n bytes[+0x58]@+0x50"
        );
        assert_eq!(count(&fields), 6);
        assert_eq!(fixed_bits(&fields), 32 + 64 + 8);
    }
}
