//! What a function reads off a stream, as the record it fills: the wire
//! schema of a deserializer, recovered from its pseudo-C and the readers it
//! calls.
//!
//! A deserializer is a sequence of calls that hand the same stream to a
//! reader along with somewhere to put the value: `read(a1, &count)`,
//! `read(a1, a2 + 8)`. The stream is the argument most calls pass first; the
//! readers are classified by what they write through their out pointer, down
//! to the primitive that pulls a fixed number of bits off the stream, and a
//! reader that itself reads several fields into its out pointer is a nested
//! record. A loop around a read repeats it, and the loop's bound names the
//! count it was read from. Nothing here knows the engine's type names: the
//! width and the depth of the write are the classification, and a type word
//! the reader's own text carries (`Guid`, `Blob`, `StringAtom`) is only a
//! hint beside it.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::classes::{class_of, deref_call, field_names};
use super::encode::{literal, packed_components};
use super::{Analysis, Overlay, name_of, plain_text_cached, resolve};
use crate::fxmap::FxHashMap;
use crate::program::Program;

/// Deepest chain of readers followed from a field to its primitive.
const DEPTH_MAX: usize = 8;
/// Most fields one schema reports, nested ones included.
const FIELDS_MAX: usize = 512;
/// Widest buffer read off a stream in one call and split into its parts.
const PACKED_BITS_MAX: u64 = 4096;
/// Lines searched forward from a packed read for where each part goes.
const SINK_FORWARD: usize = 60;
/// Parameter names a stream or an out pointer can be called in the text.
const PARAMS: [&str; 9] = ["this", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8"];
/// Words before a `(` that are not calls.
const NOT_CALLS: [&str; 8] = [
    "if", "while", "for", "return", "switch", "sizeof", "do", "else",
];

/// One call in a function's pseudo-C, in text order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    /// One-based line number.
    pub line: usize,
    /// The callee as the text names it.
    pub callee: String,
    /// The arguments, each trimmed.
    pub args: Vec<String>,
    /// The bound of the innermost loop around the call, when it is in one.
    pub repeat: Option<String>,
}

/// One field a deserializer reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// Its place in the record: `3`, or `3.2` inside a nested record.
    pub order: String,
    /// Where the value goes, as the text says: `&count`, `[+0x8]`.
    pub dest: String,
    /// What it is: `u32`, `atom`, `guid`, `struct`, `bytes12`, or `?`.
    pub kind: String,
    /// Bytes written, `0` when unknown.
    pub bytes: usize,
    /// The reader called.
    pub via: String,
    /// The loop bound the read repeats under, when it does.
    pub repeat: Option<String>,
    /// The reads its reader makes in turn: the members of a nested record.
    pub children: Vec<Field>,
    /// The field's source name when the object's class names it, `~Name`
    /// when borrowed from the class the object mirrors, else empty.
    pub name: String,
}

/// The record one function reads off its stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schema {
    /// The function.
    pub entry: u64,
    /// The parameter the stream arrives in.
    pub stream: String,
    /// The fields in read order.
    pub fields: Vec<Field>,
}

/// The argument list of the call whose `(` is at `open`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `open` - Index of the opening parenthesis.
pub(crate) fn args_at(line: &str, open: usize) -> Option<Vec<String>> {
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

/// Splits `s` on commas outside parentheses and brackets.
///
/// # Arguments
///
/// * `s` - The argument list without its outer parentheses.
pub(crate) fn split_args(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(s[start..i].trim().to_owned());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        out.push(last.to_owned());
    }
    out
}

/// Tells whether `c` can be part of a callee name.
///
/// # Arguments
///
/// * `c` - The character.
fn name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '<' | '>')
}

/// Tells whether `c` continues an identifier.
///
/// # Arguments
///
/// * `c` - The character.
pub(crate) fn ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Tells whether a block header opens a loop: `while (...)`, `for (...)`
/// or `do`.
///
/// # Arguments
///
/// * `header` - The line before its `{`, trimmed.
pub(crate) fn is_loop_header(header: &str) -> bool {
    header.starts_with("while (")
        || header.starts_with("for (")
        || header == "do"
        || header.starts_with("do ")
}

/// The bound a loop header states: the condition of a `while (...)` or
/// the middle clause of a `for (...; ...; ...)`, as [`bound_of`] reads it.
///
/// # Arguments
///
/// * `header` - The line before its `{`, trimmed.
///
/// # Returns
///
/// The bound, or `None` for a `do` or a block that is no loop.
pub(crate) fn header_bound(header: &str) -> Option<String> {
    header
        .strip_prefix("while (")
        .and_then(|r| r.rsplit_once(')'))
        .map(|(c, _)| bound_of(c))
        .or_else(|| {
            header
                .strip_prefix("for (")
                .and_then(|r| r.split(';').nth(1))
                .map(bound_of)
        })
}

/// The bound a `} while (...)` line states for the `do` block it closes.
///
/// # Arguments
///
/// * `line` - The closing line, trimmed.
pub(crate) fn closing_bound(line: &str) -> Option<String> {
    line.split_once("while (")
        .and_then(|(_, r)| r.rsplit_once(')'))
        .map(|(c, _)| bound_of(c))
}

/// The calls on one line, in order: each `name(args)` with a balanced
/// argument list.
///
/// # Arguments
///
/// * `line` - The line.
/// * `line_no` - Its number.
/// * `repeat` - The enclosing loop bound.
fn calls_on_line(line: &str, line_no: usize, repeat: Option<&str>) -> Vec<Call> {
    let bytes = line.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(open) = line[i..].find('(').map(|p| p + i) {
        let name_start = line[..open]
            .char_indices()
            .rev()
            .take_while(|(_, c)| name_char(*c))
            .last()
            .map_or(open, |(k, _)| k);
        let name = &line[name_start..open];
        let mut depth = 0i32;
        let mut close = None;
        for (k, b) in bytes.iter().enumerate().skip(open) {
            match b {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(k);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else {
            break;
        };
        if !name.is_empty()
            && name
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && !NOT_CALLS.contains(&name)
        {
            out.push(Call {
                line: line_no,
                callee: name.to_owned(),
                args: split_args(&line[open + 1..close]),
                repeat: repeat.map(str::to_owned),
            });
        }
        i = open + 1;
    }
    out
}

/// The count a loop condition compares against: the right side of its
/// comparison with casts stripped, or the whole condition otherwise.
///
/// # Arguments
///
/// * `cond` - The condition text.
pub(crate) fn bound_of(cond: &str) -> String {
    let cond = cond.trim();
    let rhs = ["<=", "<", "!=", ">=", ">"]
        .iter()
        .find_map(|op| cond.split_once(op).map(|(_, r)| r))
        .unwrap_or(cond);
    let mut s = rhs.trim().to_owned();
    while let Some(open) = s.find('(')
        && let Some(close) = s[open..].find(')')
        && s[open + 1..open + close].ends_with("_t")
    {
        s.replace_range(open..open + close + 1, "");
    }
    s.trim().trim_end_matches(';').trim().to_owned()
}

/// Every call in `text`, in order, each with the bound of the loop it sits in.
///
/// Blocks are followed by their braces; a `do {` learns its bound from the
/// `} while (...)` that closes it, so the calls inside are assigned after
/// the whole text is read.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
#[must_use]
pub fn calls_in_order(text: &str) -> Vec<Call> {
    /// A block still open while scanning.
    struct Open {
        /// The loop bound the header gives, or `None` for a `do` or a plain block.
        bound: Option<String>,
        /// Whether the block is a loop.
        is_loop: bool,
        /// The calls seen inside, waiting for a `do`'s bound.
        calls: Vec<Call>,
    }
    let mut stack: Vec<Open> = vec![Open {
        bound: None,
        is_loop: false,
        calls: Vec::new(),
    }];
    let push_calls = |stack: &mut Vec<Open>, calls: Vec<Call>| {
        if let Some(top) = stack.last_mut() {
            top.calls.extend(calls);
        }
    };
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
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
            let calls: Vec<Call> = done
                .calls
                .into_iter()
                .map(|mut c| {
                    if c.repeat.is_none() {
                        c.repeat.clone_from(&bound);
                    }
                    c
                })
                .collect();
            push_calls(&mut stack, calls);
        }
        let inner = stack.last().and_then(|o| {
            o.bound
                .as_deref()
                .or_else(|| stack.iter().rev().find_map(|b| b.bound.as_deref()))
        });
        let body = if closes {
            line.trim_start_matches('}').trim_start()
        } else {
            line
        };
        let opens = body.ends_with('{');
        let header = body.trim_end_matches('{').trim();
        let calls = calls_on_line(body, i + 1, inner);
        if opens {
            stack.push(Open {
                bound: header_bound(header),
                is_loop: is_loop_header(header),
                calls: Vec::new(),
            });
        }
        push_calls(&mut stack, calls);
    }
    while stack.len() > 1 {
        if let Some(done) = stack.pop() {
            push_calls(&mut stack, done.calls);
        }
    }
    let mut calls = stack.pop().map(|o| o.calls).unwrap_or_default();
    calls.sort_by_key(|c| c.line);
    calls
}

/// The identifiers assigned from a stream accessor (`rax = Core::Ptr<T>::
/// operator ->(a2)`): the stream, whatever else the calls suggest.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
fn accessor_streams(text: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        let Some((lhs, rhs)) = line.split_once(" = ") else {
            continue;
        };
        if deref_call(rhs).is_none_or(|(start, _)| start != 0) {
            continue;
        }
        let lhs = lhs.trim();
        if lhs.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            && !out.iter().any(|o| o == lhs)
        {
            out.push(lhs.to_owned());
        }
    }
    out
}

/// The accessor-assigned identifier handed first to the most calls, when
/// an accessor names one at all.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
/// * `calls` - The function's calls.
fn accessor_stream<'c>(text: &str, calls: &'c [Call]) -> Option<&'c str> {
    let streams = accessor_streams(text);
    if streams.is_empty() {
        return None;
    }
    first_max(
        stream_candidates(calls, None)
            .into_iter()
            .filter(|p| streams.iter().any(|s| s == p))
            .map(|p| {
                (
                    calls
                        .iter()
                        .filter(|c| c.args.first().is_some_and(|a| a == p))
                        .count(),
                    p,
                )
            }),
    )
}

/// Tells whether `word` occurs in `text` as a whole identifier.
///
/// # Arguments
///
/// * `text` - The text.
/// * `word` - The identifier.
pub(crate) fn has_word(text: &str, word: &str) -> bool {
    let mut from = 0;
    while let Some(at) = text[from..].find(word).map(|p| p + from) {
        let end = at + word.len();
        let before = at == 0
            || !text.as_bytes()[at - 1].is_ascii_alphanumeric() && text.as_bytes()[at - 1] != b'_';
        let after = end == text.len()
            || !text.as_bytes()[end].is_ascii_alphanumeric() && text.as_bytes()[end] != b'_';
        if before && after {
            return true;
        }
        from = end;
    }
    false
}

/// The object field a left-hand side names, spelled as a destination:
/// `a1->field_0x40` and `*(float*)(a1 + 0x40)` are `a1 + 0x40`,
/// `a1->startTick` stays.
///
/// # Arguments
///
/// * `lhs` - The left side of an assignment, trimmed.
fn field_dest(lhs: &str) -> Option<String> {
    let base_ok = |b: &str| {
        b == "this"
            || (b.starts_with('a') && b[1..].bytes().all(|c| c.is_ascii_digit()) && b.len() > 1)
    };
    if let Some((base, member)) = lhs.split_once("->")
        && base_ok(base)
        && member
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Some(match member.strip_prefix("field_0x") {
            Some(hex) => match u64::from_str_radix(hex, 16) {
                Ok(off) => format!("{base} + {off:#x}"),
                Err(_) => format!("{base}->{member}"),
            },
            None => format!("{base}->{member}"),
        });
    }
    let inner = lhs.rsplit_once(")(")?.1.trim_end_matches(')');
    let (base, off) = inner.split_once(" + ")?;
    if !base_ok(base.trim()) {
        return None;
    }
    let off = super::parse_addr(off.trim())?;
    Some(format!("{} + {off:#x}", base.trim()))
}

/// Where one part of a packed buffer goes: the object field it is unpacked
/// into, or the field a helper is handed beside it.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the packed read; the search runs forward from there.
/// * `local` - The part.
///
/// # Returns
///
/// The destination and the helper it went through, when one did.
fn sink_of(lines: &[&str], at: usize, local: &str) -> Option<(String, Option<String>)> {
    let end = lines.len().min(at + 1 + SINK_FORWARD);
    for line in &lines[at + 1..end] {
        if line.starts_with("//") || !has_word(line, local) {
            continue;
        }
        if let Some((lhs, rhs)) = line.split_once(" = ")
            && has_word(rhs, local)
            && let Some(dest) = field_dest(lhs.trim())
        {
            return Some((dest, None));
        }
        for c in calls_on_line(line, 0, None) {
            if !c.args.iter().any(|a| a == local) {
                continue;
            }
            let dest = c
                .args
                .iter()
                .filter(|a| a.as_str() != local)
                .find_map(|a| {
                    let (base, off) = a.split_once(" + ")?;
                    let off = super::parse_addr(off.trim())?;
                    object_offset(&format!("{base} + {off}"))
                        .map(|_| format!("{} + {off:#x}", base.trim()))
                })
                .unwrap_or_else(|| "?".to_owned());
            return Some((dest, Some(c.callee)));
        }
    }
    None
}

/// The parts of a buffer read off the stream whole, each with the field
/// it is unpacked into.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
/// * `call` - The read.
/// * `buffer` - The buffer variable, without its `&`.
/// * `bits` - The bit count read.
fn packed_reads(text: &str, call: &Call, buffer: &str, bits: u64) -> Vec<Field> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let parts = packed_components(&lines, buffer, bits);
    if parts.is_empty() {
        return Vec::new();
    }
    let at = call.line.saturating_sub(1);
    parts
        .into_iter()
        .map(|(local, bytes)| {
            let (dest, via) = sink_of(&lines, at, &local).unwrap_or_else(|| ("?".to_owned(), None));
            Field {
                order: String::new(),
                dest,
                kind: format!("u{}", bytes * 8),
                bytes: usize::try_from(bytes).unwrap_or(0),
                via: via.map_or_else(|| "packed".to_owned(), |h| format!("packed via {h}")),
                repeat: call.repeat.clone(),
                children: Vec::new(),
                name: String::new(),
            }
        })
        .collect()
}

/// The identifiers handed first to calls, each once, in first-seen order:
/// the parameters and locals a stream could be called in the text.
///
/// # Arguments
///
/// * `calls` - The function's calls.
/// * `exclude` - An identifier that cannot be the stream.
fn stream_candidates<'c>(calls: &'c [Call], exclude: Option<&str>) -> Vec<&'c str> {
    let mut out: Vec<&str> = Vec::new();
    for c in calls {
        let Some(first) = c.args.first() else {
            continue;
        };
        let first = first.as_str();
        if first.is_empty()
            || !first
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
            || exclude == Some(first)
            || out.contains(&first)
        {
            continue;
        }
        out.push(first);
    }
    out
}

/// The identifier most calls hand over first: the stream, when nothing
/// better is known; the earliest wins a tie.
///
/// # Arguments
///
/// * `calls` - The function's calls.
/// * `exclude` - An identifier that cannot be the stream.
fn stream_param<'c>(calls: &'c [Call], exclude: Option<&str>) -> Option<&'c str> {
    first_max(stream_candidates(calls, exclude).into_iter().map(|p| {
        (
            calls
                .iter()
                .filter(|c| c.args.first().is_some_and(|a| a == p))
                .count(),
            p,
        )
    }))
}

/// The identifier with the highest positive score; the first of equals.
///
/// # Arguments
///
/// * `scored` - `(score, identifier)` pairs in order of preference.
fn first_max<'c>(scored: impl Iterator<Item = (usize, &'c str)>) -> Option<&'c str> {
    scored
        .fold(None, |best: Option<(usize, &'c str)>, (n, p)| match best {
            Some((m, _)) if m >= n => best,
            _ if n > 0 => Some((n, p)),
            _ => best,
        })
        .map(|(_, p)| p)
}

/// Where a stream held in a local came from: `rax = Core::Ptr<T>::operator
/// ->(a2)` makes `rax` the stream `a2 (T)`.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
/// * `stream` - The identifier the stream is called by.
fn stream_origin(text: &str, stream: &str) -> String {
    let derived = text.lines().find_map(|line| {
        let (lhs, rhs) = line.trim().split_once(" = ")?;
        if lhs.trim() != stream {
            return None;
        }
        let head = rhs.split("::operator ->(").next()?;
        let class = head.rsplit_once('<')?.1.trim_end_matches('>');
        let param = rhs.rsplit_once("->(")?.1.trim_end_matches(");").trim();
        Some(format!("{param} ({class})"))
    });
    derived.unwrap_or_else(|| stream.to_owned())
}

/// The `// signature:` line of a function's pseudo-C, when it has one.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
pub(crate) fn signature_line(text: &str) -> Option<&str> {
    text.lines()
        .find_map(|l| l.trim().strip_prefix("// signature: "))
}

/// The parameter texts of a signature line, split at the top-level commas
/// of its last balanced parameter list.
///
/// # Arguments
///
/// * `sig` - The signature as the line spells it.
///
/// # Returns
///
/// The parameters, or `None` when the line has no balanced list.
pub(crate) fn signature_params(sig: &str) -> Option<Vec<String>> {
    let sig = sig.trim_end();
    let close = sig.rfind(')')?;
    let mut depth = 0i32;
    let mut open = None;
    for (i, b) in sig.bytes().enumerate().take(close + 1).rev() {
        match b {
            b')' => depth += 1,
            b'(' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    Some(split_args(&sig[open? + 1..close]))
}

/// The parameter names a function's `// signature:` line declares, in order:
/// `this` for a method's object, `a1`... otherwise, whatever the text says.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
fn param_names(text: &str) -> Vec<String> {
    let Some(sig) = signature_line(text) else {
        return PARAMS[1..].iter().map(|p| (*p).to_owned()).collect();
    };
    declared_names(sig)
}

/// The parameter names a signature declares, in order: the last word of
/// each parameter of its last balanced parameter list.
///
/// # Arguments
///
/// * `sig` - The signature as a `// signature:` line spells it after the
///   prefix: `void f(Foo *this, uint64_t a2)`.
///
/// # Returns
///
/// The names; empty when the signature has no balanced list or declares
/// none (`void f(void)`).
pub(crate) fn declared_names(sig: &str) -> Vec<String> {
    signature_params(sig)
        .unwrap_or_default()
        .iter()
        .filter_map(|p| {
            p.rsplit([' ', '*', '&'])
                .next()
                .filter(|n| !n.is_empty() && *n != "void")
                .map(str::to_owned)
        })
        .collect()
}

/// The bytes a scalar type the pseudo-C spells takes: `uint16_t` is 2.
///
/// # Arguments
///
/// * `ty` - The type, trimmed.
///
/// # Returns
///
/// The width, or `None` for a pointer, a struct or any other type.
pub(crate) fn scalar_bytes(ty: &str) -> Option<usize> {
    Some(match ty {
        "uint8_t" | "int8_t" => 1,
        "uint16_t" | "int16_t" => 2,
        "uint32_t" | "int32_t" | "float" => 4,
        "uint64_t" | "int64_t" | "double" => 8,
        "uint128_t" => 16,
        _ => return None,
    })
}

/// `(offset, width)` of a `*(uintN_t*)(param + off) = ...` or `*(T*)param = ...`
/// store on a line, when the line stores through `param`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `param` - The out parameter's name.
fn store_through(line: &str, param: &str) -> Option<(usize, usize)> {
    let (lhs, _) = line.split_once(" = ")?;
    let lhs = lhs.trim();
    let rest = lhs.strip_prefix("*(")?;
    let (ty, target) = rest.split_once("*)")?;
    let width = scalar_bytes(ty.trim())?;
    let target = target
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .trim();
    if target == param {
        return Some((0, width));
    }
    let (base, off) = target.split_once('+')?;
    (base.trim() == param)
        .then(|| super::parse_addr(off.trim()).and_then(|o| usize::try_from(o).ok()))
        .flatten()
        .map(|o| (o, width))
}

/// The class of the first parameter a function's `// signature:` line types
/// as a pointer or reference: the object a decoder fills.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
pub(crate) fn param_class(text: &str) -> Option<String> {
    let params = signature_params(signature_line(text)?)?;
    params.iter().find_map(|p| {
        let (ty, _) = p.rsplit_once(' ')?;
        let ty = ty.trim().trim_start_matches("const ").trim_end();
        let class = ty.trim_end_matches(['*', '&', ' ']);
        (class.contains("::") && class_of(class).is_some() && !class.contains('<'))
            .then(|| class.to_owned())
    })
}

/// Tells whether a stream origin names the wire rather than a file: its
/// type carries a `[types] wire` word (`Net`, `Socket`, `Packet`).
///
/// # Arguments
///
/// * `origin` - The stream as [`stream_origin`] spells it.
/// * `wire` - The words, from the packs.
fn is_wire(origin: &str, wire: &[&str]) -> bool {
    wire.iter().any(|w| origin.contains(w))
}

/// The offset a destination adds to the object it belongs to: `a1 + 32` is
/// 32, `this + 0x20` is 32, a local is nothing.
///
/// # Arguments
///
/// * `dest` - The destination text.
fn object_offset(dest: &str) -> Option<u64> {
    let (base, off) = dest.split_once('+')?;
    let base = base.trim();
    (base == "this" || (base.starts_with('a') && base[1..].bytes().all(|b| b.is_ascii_digit())))
        .then(|| super::parse_addr(off.trim()))
        .flatten()
}

/// The offset an argument adds to `param`: `param` is 0, `param + 0x10` is 16.
///
/// # Arguments
///
/// * `arg` - The argument text.
/// * `param` - The out parameter's name.
fn offset_from(arg: &str, param: &str) -> Option<usize> {
    let arg = arg.trim();
    if arg == param {
        return Some(0);
    }
    let (base, off) = arg.split_once('+')?;
    (base.trim() == param)
        .then(|| super::parse_addr(off.trim()).and_then(|o| usize::try_from(o).ok()))
        .flatten()
}

/// What one reader writes through its out parameter, followed down through
/// the readers it calls.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Written {
    /// Bytes from the out pointer to the end of the last write.
    extent: usize,
    /// The kind a type word or the primitive suggested, when one did.
    hint: Option<String>,
    /// Every read the reader itself makes off the stream, in order.
    fields: Vec<Field>,
}

/// Where the names of an object's fields come from.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ObjectNames {
    /// Nothing names them.
    None,
    /// The object's own class, by field offset.
    Own(BTreeMap<u64, String>),
    /// The class the object mirrors, in field order, each marked `~`.
    Borrowed(Vec<String>),
}

/// What a recovered schema is memoized by: the decoder's entry and the
/// class it was named for.
type SchemaKey = (u64, Option<String>);

/// One recovery's inputs, and the readers it has already followed.
struct Ctx<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Discovery results.
    analysis: &'a Analysis,
    /// Names in force.
    overlay: &'a Overlay,
    /// Readers followed so far, by callee and out index, so a primitive
    /// called from every field is decompiled once.
    memo: RefCell<FxHashMap<(String, usize), Written>>,
    /// Schemas recovered so far by entry and the class named for, so a
    /// base class's slot shared by every command is read once per class
    /// and named for each.
    schemas: RefCell<FxHashMap<SchemaKey, Option<Schema>>>,
    /// The overlay's fingerprint, keying the shared decompilation memo.
    overlay_key: u64,
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
            memo: RefCell::new(FxHashMap::default()),
            schemas: RefCell::new(FxHashMap::default()),
            overlay_key: overlay.fingerprint(),
        }
    }

    /// The record `entry` reads off its stream, once per entry.
    ///
    /// # Arguments
    ///
    /// * `entry` - The deserializer's entry.
    fn schema(&self, entry: u64, class: Option<&str>) -> Option<Schema> {
        let key = (entry, class.map(str::to_owned));
        if let Some(s) = self.schemas.borrow().get(&key) {
            return s.clone();
        }
        let s = self.recover(entry, class);
        self.schemas.borrow_mut().insert(key, s.clone());
        s
    }

    /// Reads `entry`'s text for the record it reads.
    ///
    /// # Arguments
    ///
    /// * `entry` - The deserializer's entry.
    fn recover(&self, entry: u64, class: Option<&str>) -> Option<Schema> {
        let text = plain_text_cached(
            self.program,
            self.analysis,
            self.overlay,
            self.overlay_key,
            entry,
        )?;
        let calls = calls_in_order(&text);
        let stream =
            accessor_stream(&text, &calls).or_else(|| self.stream_of(&calls, DEPTH_MAX, None))?;
        let object = class.map(str::to_owned).or_else(|| param_class(&text));
        let names = object.map_or(ObjectNames::None, |c| self.object_names(&c));
        let mut fields = self.reads_of(&text, &calls, stream, None, &names, DEPTH_MAX);
        if let ObjectNames::Own(by_offset) = &names {
            for f in fields.iter_mut().filter(|f| f.via.starts_with("packed")) {
                if let Some(off) = object_offset(&f.dest)
                    && let Some(n) = by_offset.get(&off)
                {
                    f.name.clone_from(n);
                }
            }
        }
        Some(Schema {
            entry,
            stream: stream_origin(&text, stream),
            fields,
        })
    }

    /// The field names of `class`, or, where it names none, those of the
    /// class it mirrors: one class is filled field by field from another,
    /// so the mirror's names apply in
    /// order, not by offset (the mirror may hold atoms where the command
    /// holds strings), and are marked `~`.
    ///
    /// # Arguments
    ///
    /// * `class` - The qualified class name of the object being read.
    fn object_names(&self, class: &str) -> ObjectNames {
        let own = field_names(self.program, self.analysis, self.overlay, class);
        if !own.is_empty() {
            return ObjectNames::Own(own);
        }
        let borrowed = mirror_names(self.program, self.analysis, self.overlay, class);
        if borrowed.is_empty() {
            ObjectNames::None
        } else {
            ObjectNames::Borrowed(borrowed)
        }
    }

    /// The virtual of a class that reads the most off its wire stream, with
    /// its schema; see [`schema_for_class`].
    ///
    /// # Arguments
    ///
    /// * `class` - The qualified class name.
    fn class_schema(&self, class: &str) -> Option<(u64, Schema)> {
        let info = self.analysis.classes.by_name.get(class)?;
        let wire = self.analysis.packs.list("types", "wire");
        info.slots
            .iter()
            .filter_map(|&entry| self.schema(entry, Some(class)).map(|s| (entry, s)))
            .filter(|(_, s)| weight(&s.fields).0 > 0)
            .max_by_key(|(_, s)| (is_wire(&s.stream, &wire), weight(&s.fields)))
    }
}

impl Ctx<'_> {
    /// Follows a reader to what it writes through parameter `out`, once per
    /// reader and parameter.
    ///
    /// # Arguments
    ///
    /// * `callee` - The reader as the text names it.
    /// * `out` - Index of its out parameter (0-based, as passed).
    /// * `depth` - Readers still allowed below this one.
    fn written_by(&self, callee: &str, out: usize, depth: usize) -> Written {
        let key = (callee.to_owned(), out);
        if let Some(w) = self.memo.borrow().get(&key) {
            return w.clone();
        }
        let w = self.follow(callee, out, depth);
        self.memo.borrow_mut().insert(key, w.clone());
        w
    }

    /// The identifier whose readers write: among those handed first to
    /// calls, the one most of whose callees write through the argument beside
    /// it, or, when none does, the one handed first most often.
    ///
    /// # Arguments
    ///
    /// * `calls` - The function's calls.
    /// * `depth` - Readers allowed below each call when scoring.
    /// * `exclude` - An identifier that cannot be the stream: the function's
    ///   own out pointer.
    fn stream_of<'c>(
        &self,
        calls: &'c [Call],
        depth: usize,
        exclude: Option<&str>,
    ) -> Option<&'c str> {
        let Some(below) = depth.checked_sub(1) else {
            return stream_param(calls, exclude);
        };
        first_max(stream_candidates(calls, exclude).into_iter().map(|p| {
            (
                calls
                    .iter()
                    .filter(|c| {
                        c.args.first().is_some_and(|a| a == p)
                            && c.args.len() >= 2
                            && self.written_by(&c.callee, 1, below).extent > 0
                    })
                    .count(),
                p,
            )
        }))
        .or_else(|| stream_param(calls, exclude))
    }

    /// Every read `calls` make off `stream`, in order, each with the reads its
    /// reader makes in turn; a buffer read whole and unpacked afterwards is
    /// split into its parts.
    ///
    /// # Arguments
    ///
    /// * `text` - The function's pseudo-C, for where a packed part goes.
    /// * `calls` - The function's calls.
    /// * `stream` - The identifier the stream is called by.
    /// * `out` - The function's own out parameter, so a read into it can be
    ///   placed at its offset.
    /// * `names` - Where the object's field names come from.
    /// * `depth` - Readers still allowed below each read.
    fn reads_of(
        &self,
        text: &str,
        calls: &[Call],
        stream: &str,
        out: Option<&str>,
        names: &ObjectNames,
        depth: usize,
    ) -> Vec<Field> {
        let Some(below) = depth.checked_sub(1) else {
            return Vec::new();
        };
        let mut into_object = 0usize;
        calls
            .iter()
            .filter(|c| {
                c.args.first().is_some_and(|a| a == stream)
                    && c.args.len() >= 2
                    && !c.callee.starts_with("(*")
            })
            .take(FIELDS_MAX)
            .flat_map(|c| {
                let dest = c.args.get(1).map_or("", String::as_str);
                let under = self.written_by(&c.callee, 1, below);
                if under.extent == 0
                    && under.fields.is_empty()
                    && let Some(buffer) = dest.strip_prefix("&local_")
                    && let Some(bits) = c.args.get(2).and_then(|n| super::parse_addr(n))
                    && (65..=PACKED_BITS_MAX).contains(&bits)
                {
                    let parts = packed_reads(text, c, &format!("local_{buffer}"), bits);
                    if !parts.is_empty() {
                        return parts;
                    }
                }
                let name = object_offset(dest)
                    .and_then(|off| {
                        let k = into_object;
                        into_object += 1;
                        match names {
                            ObjectNames::None => None,
                            ObjectNames::Own(by_offset) => by_offset.get(&off),
                            ObjectNames::Borrowed(in_order) => in_order.get(k),
                        }
                    })
                    .cloned()
                    .unwrap_or_default();
                vec![Field {
                    order: String::new(),
                    dest: out
                        .and_then(|p| offset_from(dest, p))
                        .map_or_else(|| dest.to_owned(), |off| format!("[+{off:#x}]")),
                    kind: kind_name(&under),
                    bytes: under.extent,
                    via: c.callee.clone(),
                    repeat: c.repeat.clone(),
                    children: under.fields,
                    name,
                }]
            })
            .collect()
    }

    /// Reads a reader's text for what it writes through parameter `out`.
    ///
    /// # Arguments
    ///
    /// * `callee` - The reader as the text names it.
    /// * `out` - Index of its out parameter.
    /// * `depth` - Readers still allowed below this one.
    fn follow(&self, callee: &str, out: usize, depth: usize) -> Written {
        let mut w = Written::default();
        let Ok(entry) = resolve(self.program, self.analysis, self.overlay, callee) else {
            return w;
        };
        let Some(text) = plain_text_cached(
            self.program,
            self.analysis,
            self.overlay,
            self.overlay_key,
            entry,
        ) else {
            return w;
        };
        let names = param_names(&text);
        let Some(param) = names.get(out).map(String::as_str) else {
            return w;
        };
        for (word, kind) in self.analysis.packs.pairs("types", "kind") {
            if text.contains(word) {
                w.hint = Some(kind.to_owned());
                break;
            }
        }
        for line in text.lines() {
            if let Some((off, width)) = store_through(line.trim(), param) {
                w.extent = w.extent.max(off + width);
            }
        }
        let calls = calls_in_order(&text);
        for c in &calls {
            if c.callee == "memcpy"
                && let Some(off) = c.args.first().and_then(|a| offset_from(a, param))
                && let Some(n) = c.args.get(2).and_then(|n| super::parse_addr(n))
            {
                w.extent = w.extent.max(off + usize::try_from(n).unwrap_or(0));
                continue;
            }
            let Some(pos) = c.args.iter().position(|a| offset_from(a, param).is_some()) else {
                continue;
            };
            let Some(below) = depth.checked_sub(1) else {
                continue;
            };
            if c.callee.starts_with("(*") || c.callee.is_empty() {
                continue;
            }
            let off = c
                .args
                .get(pos)
                .and_then(|a| offset_from(a, param))
                .unwrap_or(0);
            let under = self.written_by(&c.callee, pos, below);
            w.extent = w.extent.max(off + under.extent);
            if w.hint.is_none() {
                w.hint.clone_from(&under.hint);
            }
        }
        if let Some(stream) = self.stream_of(&calls, depth, Some(param)) {
            w.fields = self.reads_of(
                &text,
                &calls,
                stream,
                Some(param),
                &ObjectNames::None,
                depth,
            );
        }
        if let Some(bits) = bits_read(&text) {
            w.extent = w.extent.max(bits / 8);
            w.hint.get_or_insert_with(|| format!("u{bits}"));
        }
        w
    }
}

/// The bit count a primitive hands the stream's virtual read: the constant
/// closing an indirect call whose other argument is the out pointer.
///
/// # Arguments
///
/// * `text` - The reader's pseudo-C.
fn bits_read(text: &str) -> Option<usize> {
    text.lines().find_map(|line| {
        let line = line.trim();
        let at = line.find("))(")?;
        let args = split_args(line[at + 3..].trim_end_matches(';').trim_end_matches(')'));
        let last = args.last()?;
        let n = super::parse_addr(last).and_then(|v| usize::try_from(v).ok())?;
        matches!(n, 8 | 16 | 32 | 64).then_some(n)
    })
}

/// The kind a reader's writes amount to.
///
/// # Arguments
///
/// * `w` - What it writes.
fn kind_name(w: &Written) -> String {
    if w.fields.len() > 1 {
        return "struct".to_owned();
    }
    if let Some(h) = &w.hint {
        return h.clone();
    }
    match w.extent {
        1 => "u8".to_owned(),
        2 => "u16".to_owned(),
        4 => "u32".to_owned(),
        8 => "u64".to_owned(),
        0 => "?".to_owned(),
        n => format!("bytes{n}"),
    }
}

/// Recovers the record `entry` reads off its stream.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The deserializer's entry.
///
/// # Returns
///
/// The schema, or `None` when the function does not decompile or hands no
/// identifier first to any call.
#[must_use]
pub fn schema_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Schema> {
    Ctx::new(program, analysis, overlay).schema(entry, None)
}

/// Returns every read `calls` of a fragment of pseudo-C make off `stream`,
/// each reader followed as [`schema_of`] follows it: the reads of one case
/// of a dispatcher, or of the call reading its opcode.
///
/// Besides readers handed an out pointer, a fragment may read values its
/// readers return, `v = read(stream);`, each as wide as [`returned_bytes`]
/// says, with `-` for its destination when the value is not stored whole
/// (`if (read(stream) != 0)`); both kinds come out in call order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `text` - The fragment, for where a packed read's parts go.
/// * `calls` - The calls to read, as [`calls_in_order`] found them in it,
///   each with the loop bound it repeats under.
/// * `stream` - The stream's identifier in it.
pub(crate) fn reads_in(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
    calls: &[Call],
    stream: &str,
) -> Vec<Field> {
    let ctx = Ctx::new(program, analysis, overlay);
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let returned = |c: &Call| {
        let [arg] = c.args.as_slice() else {
            return None;
        };
        (arg == stream).then_some(())?;
        let bytes = returned_bytes(program, analysis, overlay, &c.callee)?;
        let dest = lines
            .get(c.line.checked_sub(1)?)
            .and_then(|l| l.split_once(" = "))
            .filter(|(_, rhs)| is_call_of(rhs, &c.callee))
            .map_or("-", |(lhs, _)| lhs.trim());
        Some(Field {
            order: String::new(),
            dest: dest.to_owned(),
            kind: format!("u{}", bytes * 8),
            bytes,
            via: c.callee.clone(),
            repeat: c.repeat.clone(),
            children: Vec::new(),
            name: String::new(),
        })
    };
    calls
        .iter()
        .flat_map(|c| {
            returned(c).map_or_else(
                || {
                    let one = std::slice::from_ref(c);
                    ctx.reads_of(text, one, stream, None, &ObjectNames::None, DEPTH_MAX)
                },
                |f| vec![f],
            )
        })
        .take(FIELDS_MAX)
        .collect()
}

/// Tells whether `expr` is one call of `callee` and nothing else: `f(a1)`,
/// not `f(a1) ^ 1`.
///
/// # Arguments
///
/// * `expr` - The expression, a trailing `;` allowed.
/// * `callee` - The callee's name.
pub(crate) fn is_call_of(expr: &str, callee: &str) -> bool {
    let Some(rest) = expr.trim().trim_end_matches(';').strip_prefix(callee) else {
        return false;
    };
    let mut depth = 0i32;
    for (i, b) in rest.bytes().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ if i == 0 => return false,
            _ => {}
        }
        if depth == 0 {
            return i + 1 == rest.len();
        }
    }
    false
}

/// Returns the bytes a reader that returns its value takes off the stream:
/// the constant it moves the stream by (`*(uint32_t*)a1 += 2;` is 2), else
/// the width of the scalar its signature returns.
///
/// Only a function that moves its stream counts: one of its lines adds to
/// something reached through its first parameter that another line reads,
/// the cursor the value is loaded through, so a predicate over the stream
/// is not a read and a counter bumped beside the cursor is not its step.
/// The step is preferred to the return type, which is as wide as the
/// register the value is returned in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `reader` - The reader as the text names it.
///
/// # Returns
///
/// The width, or `None` when the reader does not resolve, returns no
/// scalar or moves no stream.
pub(crate) fn returned_bytes(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    reader: &str,
) -> Option<usize> {
    let entry = resolve(program, analysis, overlay, reader).ok()?;
    let text = plain_text_cached(program, analysis, overlay, overlay.fingerprint(), entry)?;
    let sig = signature_line(&text)?;
    let stream = declared_names(sig).into_iter().next()?;
    if let Some(n) = literal(cursor_step(&text, &stream)?)
        && let Ok(n) = usize::try_from(n)
        && [1, 2, 4, 8].contains(&n)
    {
        return Some(n);
    }
    let head = sig.split('(').next()?;
    let (ty, _) = head.trim().rsplit_once(' ')?;
    scalar_bytes(ty.trim())
}

/// Returns what a reader adds to its cursor: the right side of the first
/// `+=` onto something reached through `stream` that another line reads.
///
/// # Arguments
///
/// * `text` - The reader's pseudo-C.
/// * `stream` - Its stream parameter.
fn cursor_step<'t>(text: &'t str, stream: &str) -> Option<&'t str> {
    text.lines()
        .filter_map(|l| l.trim().split_once(" += "))
        .find(|(lhs, _)| {
            has_word(lhs, stream)
                && text
                    .lines()
                    .any(|l| !l.contains(" += ") && l.contains(lhs.trim()))
        })
        .map(|(_, step)| step.trim_end_matches(';'))
}

/// How many reads a schema holds that came to something, nested ones
/// included, and the farthest offset a top-level read lands at.
///
/// # Arguments
///
/// * `fields` - The fields to count.
fn weight(fields: &[Field]) -> (usize, usize) {
    fields.iter().fold((0, 0), |(n, far), f| {
        let (below, _) = weight(&f.children);
        let counted = usize::from(f.bytes > 0 || f.kind != "?") + below;
        let off = f
            .dest
            .split_once('+')
            .and_then(|(_, o)| super::parse_addr(o.trim()))
            .and_then(|o| usize::try_from(o).ok())
            .unwrap_or(0);
        (n + counted, far.max(off))
    })
}

/// Picks the virtual of a class that reads the most off a stream, and its
/// schema: the deserializer, without knowing which slot it sits in.
///
/// A base class's slot, shared by every command, reads the header the
/// derived class's own decoder reads past, so among slots reading the same
/// number of fields the one landing farthest into the object wins.
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
/// The slot's entry and schema, or `None` when no slot reads anything.
#[must_use]
pub fn schema_for_class(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<(u64, Schema)> {
    Ctx::new(program, analysis, overlay).class_schema(class)
}

/// A record's top-level fields on one line: `kind@dest` each, a nested
/// record as `struct{...}` one level down, at most twelve of them.
///
/// # Arguments
///
/// * `fields` - The fields.
#[must_use]
pub fn compact_fields(fields: &[Field]) -> String {
    /// Most fields spelled out on one line.
    const COMPACT_MAX: usize = 12;
    let mut parts: Vec<String> = fields
        .iter()
        .take(COMPACT_MAX)
        .map(|f| {
            let dest = f
                .dest
                .split_once('+')
                .and_then(|(_, o)| super::parse_addr(o.trim()))
                .map_or_else(|| f.dest.clone(), |o| format!("+{o:#x}"));
            let repeat = f
                .repeat
                .as_deref()
                .map_or(String::new(), |r| format!("*{r}"));
            let dest = if f.name.is_empty() {
                dest
            } else {
                format!("{dest}={}", f.name)
            };
            if f.children.len() > 1 {
                let inner: Vec<String> = f
                    .children
                    .iter()
                    .take(COMPACT_MAX)
                    .map(|c| format!("{}{}", c.kind, c.dest))
                    .collect();
                format!("{}@{dest}{repeat}{{{}}}", f.kind, inner.join(","))
            } else {
                format!("{}@{dest}{repeat}", f.kind)
            }
        })
        .collect();
    if fields.len() > COMPACT_MAX {
        parts.push(format!("+{} more", fields.len() - COMPACT_MAX));
    }
    parts.join(" ")
}

/// Renders every class whose virtual at `slot` returns a constant, with the
/// record its reading virtual decodes: a registry's whole protocol as one
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
pub fn schemas_tsv(
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
        |ctx, c| ctx.class_schema(&c.class),
    );
    let total = rows.len();
    let read = rows.iter().filter(|r| r.found.is_some()).count();
    let shown = total.min(limit);
    let mut out = format!(
        "# {total} classes answer virtual {slot} with a constant, {read} of them decode a record, showing {shown}
"
    );
    out.push_str(
        "value	class	decoder	reads	fields
",
    );
    for row in rows.into_iter().take(limit) {
        let (value, class) = (row.value, row.class);
        match row.found {
            Some((entry, s)) => {
                let _ = writeln!(
                    out,
                    "{value:#x}	{class}	{entry:#x}	{}	{}",
                    weight(&s.fields).0,
                    compact_fields(&s.fields)
                );
            }
            None => {
                let _ = writeln!(out, "{value:#x}	{class}	-	0	");
            }
        }
    }
    out
}

/// Appends the rows of `fields` under `prefix`, numbering them and their
/// children.
///
/// # Arguments
///
/// * `out` - The table so far.
/// * `fields` - The fields to render.
/// * `prefix` - The parent's number plus a dot, or empty at the top.
fn render_fields(out: &mut String, fields: &[Field], prefix: &str) {
    for (i, f) in fields.iter().enumerate() {
        let order = format!("{prefix}{}", i + 1);
        let _ = writeln!(
            out,
            "{order}\t{}\t{}\t{}\t{}\t{}\t{}",
            f.dest,
            f.name,
            f.kind,
            f.bytes,
            f.via,
            f.repeat
                .as_deref()
                .map_or(String::new(), |r| format!("x {r}"))
        );
        render_fields(out, &f.children, &format!("{order}."));
    }
}

/// Renders a schema as a `#`-headed table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The deserializer's entry.
///
/// # Returns
///
/// The table, or `None` as for [`schema_of`].
#[must_use]
pub fn schema_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let s = schema_of(program, analysis, overlay, entry)?;
    Some(render_schema(analysis, overlay, &s, ""))
}

/// Renders the schema of the virtual of `class` that reads the most, with
/// the class's own field names on its rows.
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
/// The table, or `None` when no virtual of the class reads a stream.
#[must_use]
pub fn class_schema_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<String> {
    let (_, s) = schema_for_class(program, analysis, overlay, class)?;
    Some(render_schema(analysis, overlay, &s, class))
}

/// Renders a schema as a `#`-headed table.
///
/// # Arguments
///
/// * `analysis` - For the decoder's name.
/// * `overlay` - Names in force.
/// * `s` - The schema.
/// * `class` - The object's class when known, for the header; empty otherwise.
fn render_schema(analysis: &Analysis, overlay: &Overlay, s: &Schema, class: &str) -> String {
    let name = name_of(analysis, overlay, s.entry);
    let object = if class.is_empty() {
        String::new()
    } else {
        format!(" into a {class}")
    };
    let mut out = format!(
        "# schema read by {name} @ {:#x} from {}{object}: {} reads\n",
        s.entry,
        s.stream,
        weight(&s.fields).0
    );
    out.push_str("order\tdest\tname\tkind\tbytes\tvia\trepeat\n");
    render_fields(&mut out, &s.fields, "");
    out
}

/// The field names of the class `class` mirrors, in field order, each
/// marked `~`.
///
/// One class is filled from another, whose names apply in order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `class` - The qualified class name.
///
/// # Returns
///
/// The names, empty when the class is not a `...Command` or no class of
/// the base name names a field.
pub(crate) fn mirror_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Vec<String> {
    let Some(short) = class_of(class).map(|_| class.rsplit("::").next().unwrap_or(class)) else {
        return Vec::new();
    };
    let Some(base) = short.strip_suffix("Command") else {
        return Vec::new();
    };
    analysis
        .classes
        .by_name
        .keys()
        .filter(|k| k.rsplit("::").next() == Some(base) && k.as_str() != class)
        .map(|twin| field_names(program, analysis, overlay, twin))
        .find(|names| !names.is_empty())
        .map_or_else(Vec::new, |names| {
            names.into_values().map(|n| format!("~{n}")).collect()
        })
}

/// The offset of the field of `class` called `name`, as the class names it
/// or, when its own class names nothing, as the class it mirrors names it
/// in the decoder's field order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `class` - The qualified class name.
/// * `name` - The field name, without any `~`.
///
/// # Returns
///
/// The offset, or `None` when nothing names such a field.
#[must_use]
pub fn named_field_offset(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
    name: &str,
) -> Option<u64> {
    let ctx = Ctx::new(program, analysis, overlay);
    match ctx.object_names(class) {
        ObjectNames::None => None,
        ObjectNames::Own(by_offset) => by_offset
            .into_iter()
            .find(|(_, n)| n == name)
            .map(|(off, _)| off),
        ObjectNames::Borrowed(_) => {
            let (_, s) = ctx.class_schema(class)?;
            s.fields
                .iter()
                .find(|f| f.name.trim_start_matches('~') == name)
                .and_then(|f| object_offset(&f.dest))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The game's packed wire decoder: one 120-bit read into a local, then
    /// every part unpacked into a field or handed to a helper.
    const PACKED: &str = "// signature: uint8_t X::Decode(Commands::MoveCommand *a1, uint64_t a2)
uint16_t local_16, local_14, local_b;
uint32_t local_f;
uint64_t rax, local_18;
uint8_t local_12, local_11, local_10;

rax = X::Ready();
if (rax != 0) {
  local_18 = local_10 = local_f = local_b = 0;
  rax = Core::Ptr<Network::SafeBitReader>::operator ->(a2);
  rax = sub_140cca908(rax, &local_18, 120);
  if (rax != 0) {
    sub_1409a76c0(a1, local_18, local_16, local_14, a1 + 48);
    a1->startTick = local_f;
    a1->field_0x40 = cvtdq2ps(local_12) * 0.00390625f * 4.0f;
    a1->endTick = local_b + local_f;
    a1->field_0x44 = (cvtdq2ps(local_11) * 0.00390625f) * 3.1415927f;
    a1->field_0x48 = (cvtdq2ps(local_10) * 0.00390625f) * 3.1415927f;
    return 1;
  }
}
return 0;
";

    /// The accessor names the stream even when an intrinsic is handed a
    /// local more often, and each packed part finds the field it goes to.
    ///
    /// # Panics
    ///
    /// When a part's destination differs from the text.
    #[test]
    fn a_packed_read_is_split_into_the_fields_it_unpacks_into() {
        let calls = calls_in_order(PACKED);
        assert_eq!(accessor_stream(PACKED, &calls), Some("rax"));
        let read = calls
            .iter()
            .find(|c| c.callee == "sub_140cca908")
            .expect("the packed read");
        let fields = packed_reads(PACKED, read, "local_18", 120);
        let shape: Vec<(&str, &str, &str)> = fields
            .iter()
            .map(|f| (f.kind.as_str(), f.dest.as_str(), f.via.as_str()))
            .collect();
        assert_eq!(
            shape,
            [
                ("u16", "a1 + 0x30", "packed via sub_1409a76c0"),
                ("u16", "a1 + 0x30", "packed via sub_1409a76c0"),
                ("u16", "a1 + 0x30", "packed via sub_1409a76c0"),
                ("u8", "a1 + 0x40", "packed"),
                ("u8", "a1 + 0x44", "packed"),
                ("u8", "a1 + 0x48", "packed"),
                ("u32", "a1->startTick", "packed"),
                ("u16", "a1->endTick", "packed"),
            ],
            "{shape:?}"
        );
        assert_eq!(
            field_dest("*(float*)(a1 + 0x40)").as_deref(),
            Some("a1 + 0x40")
        );
        assert_eq!(field_dest("rax").as_deref(), None);
        let wire = crate::pack::defaults("types", "wire");
        assert!(is_wire("a2 (Network::SafeBitReader)", wire));
        assert!(!is_wire("a2 (IO::BinaryReader)", wire));
    }

    /// A reader's step is what it adds to the cursor it loads through, not
    /// to a counter beside it.
    ///
    /// # Panics
    ///
    /// When the counter's step is taken.
    #[test]
    fn a_cursor_step_is_the_one_the_load_goes_through() {
        assert!(is_call_of("f(a1);", "f"));
        assert!(is_call_of("f(g(a1), 2)", "f"));
        assert!(!is_call_of("f(a1) ^ 1", "f"));
        assert!(!is_call_of("ff(a1)", "f"));
        let text = "*(uint32_t*)(a1 + 8) += 1;\nax = *(uint16_t*)*(uint32_t*)a1;\n*(uint32_t*)a1 += 2;\nreturn ax;\n";
        assert_eq!(cursor_step(text, "a1"), Some("2"));
        assert_eq!(cursor_step("*(uint32_t*)(a1 + 8) += 1;\n", "a1"), None);
    }

    /// Calls come out in order with their arguments split at top-level
    /// commas, keywords are not calls, and a `do` loop's bound reaches the
    /// calls inside it from the `while` that closes it.
    ///
    /// # Panics
    ///
    /// When a call or bound disagrees with the sample text.
    #[test]
    fn calls_and_loop_bounds_are_read_from_the_text() {
        let text = "rax = read(a1, &home_10);\nif (rax == 0) {\n  return 0;\n}\ndo {\n  rax = sub_1(a1, &local_38);\n  Util::Array<X>::Append(a2, &local_38);\n} while ((int32_t)rdi < (int32_t)home_10);\nwhile (n < limit) {\n  read16(a1, a2 + 8);\n}\n";
        let calls = calls_in_order(text);
        let shape: Vec<(&str, usize, Option<&str>)> = calls
            .iter()
            .map(|c| (c.callee.as_str(), c.args.len(), c.repeat.as_deref()))
            .collect();
        assert_eq!(
            shape,
            vec![
                ("read", 2, None),
                ("sub_1", 2, Some("home_10")),
                ("Util::Array<X>::Append", 2, Some("home_10")),
                ("read16", 2, Some("limit")),
            ]
        );
        assert_eq!(calls[0].args, vec!["a1", "&home_10"]);
        assert_eq!(stream_param(&calls, None), Some("a1"));
        assert_eq!(stream_param(&calls, Some("a1")), Some("a2"));
        let text =
            "rax = Core::Ptr<Network::SafeBitReader>::operator ->(a2);\nsub_1(rax, a1 + 32);\n";
        let calls = calls_in_order(text);
        assert_eq!(stream_candidates(&calls, None), vec!["rax"]);
        assert_eq!(stream_origin(text, "rax"), "a2 (Network::SafeBitReader)");
        assert_eq!(stream_origin(text, "a1"), "a1");
    }

    /// Stores through the out parameter give the offset and width, an
    /// argument names its offset, and the stream's bit count is read off the
    /// virtual call.
    ///
    /// # Panics
    ///
    /// When a parse disagrees with its expectation.
    #[test]
    fn writes_offsets_and_bit_counts_are_parsed() {
        assert_eq!(
            store_through("*(uint32_t*)a2 = home_10;", "a2"),
            Some((0, 4))
        );
        assert_eq!(
            store_through("*(uint64_t*)(a2 + 0x10) = rax;", "a2"),
            Some((16, 8))
        );
        assert_eq!(store_through("*(uint32_t*)a3 = 1;", "a2"), None);
        assert_eq!(offset_from("a2 + 20", "a2"), Some(20));
        assert_eq!(offset_from("&local_38", "a2"), None);
        assert_eq!(
            bits_read("return (*(*(uint64_t*)(*(uint64_t*)rax + 0xb8)))(rax, a2, 32);"),
            Some(32)
        );
        assert_eq!(bound_of("(int32_t)rdi < (int32_t)home_10"), "home_10");
        assert_eq!(
            kind_name(&Written {
                extent: 16,
                hint: Some("guid".to_owned()),
                fields: Vec::new()
            }),
            "guid"
        );
        assert_eq!(kind_name(&Written::default()), "?");
        let field = |dest: &str, kind: &str, repeat: Option<&str>, children: Vec<Field>| Field {
            order: String::new(),
            dest: dest.to_owned(),
            kind: kind.to_owned(),
            bytes: 0,
            via: String::new(),
            repeat: repeat.map(str::to_owned),
            children,
            name: String::new(),
        };
        let record = vec![
            field("&home_10", "u32", None, Vec::new()),
            field(
                "a1 + 32",
                "struct",
                Some("home_10"),
                vec![
                    field("[+0x0]", "atom", None, Vec::new()),
                    field("[+0x8]", "u32", None, Vec::new()),
                ],
            ),
        ];
        assert_eq!(
            compact_fields(&record),
            "u32@&home_10 struct@+0x20*home_10{atom[+0x0],u32[+0x8]}"
        );
        assert_eq!(object_offset("a1 + 32"), Some(32));
        assert_eq!(object_offset("this + 0x20"), Some(32));
        assert_eq!(object_offset("&local_38"), None);
        assert_eq!(object_offset("rbx + 8"), None);
        assert_eq!(
            param_class("// signature: uint64_t class_1::vfunc_5(Cmd::Exit *a1, uint64_t a2)\n")
                .as_deref(),
            Some("Cmd::Exit")
        );
        assert_eq!(
            param_class("// signature: uint8_t sub_1(uint64_t a1, void *a2)\n"),
            None
        );
        assert_eq!(
            param_names("// signature: uint8_t sub_1(uint64_t a1, uint32_t *a2)\nrax = 1;\n"),
            vec!["a1", "a2"]
        );
        assert_eq!(
            param_names("// signature: void Widget::Send(Widget *this)\n"),
            vec!["this"]
        );
    }
}
