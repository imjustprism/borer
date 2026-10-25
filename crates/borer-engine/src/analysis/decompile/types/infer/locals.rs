//! Stack-local type refinement: `bool` for 0/1 flags and library pointers
//! (`char*`, `FILE*`, `struct group*`, `struct passwd*`) from call uses and
//! assigned results.

use super::super::super::evidence::whole_read;
use super::super::super::lexer::{Lex, Line, lex};
use super::super::*;
use super::{Slot, bit_operand, call_is_whole, cast_before, known_slot, sole_rhs};
use crate::analysis::typelib;
use crate::program::BinaryFormat;

/// Retypes stack locals whose uses prove them `bool` or a library pointer
/// (`char*`, `FILE*`, `struct group*`, `struct passwd*`).
///
/// # Arguments
///
/// * `lines` - The function's lines, rewritten in place.
///
/// # Returns
///
/// Whether any local declaration changed.
pub(in crate::analysis::decompile) fn refine_locals(lines: &mut Vec<String>) -> bool {
    let mut ptrs: Vec<(String, &'static str)> = Vec::new();
    let mut arrays: Vec<(String, u64)> = Vec::new();
    let mut bools: Vec<String> = Vec::new();
    for line in lines.iter() {
        if line.contains("//") {
            continue;
        }
        if let Some(names) = line
            .strip_prefix("uint64_t ")
            .or_else(|| line.strip_prefix("uint32_t "))
            .and_then(|r| r.strip_suffix(';'))
        {
            for name in names.split(", ").map(str::trim) {
                if name.starts_with("local_") {
                    if let Some(ty) = local_api_pointer(lines, name) {
                        ptrs.push((name.to_owned(), ty));
                    } else if let Some(span) = byte_buffer_local_span(lines, name) {
                        arrays.push((name.to_owned(), span));
                    }
                }
            }
        } else if let Some(names) = line
            .strip_prefix("uint8_t ")
            .and_then(|r| r.strip_suffix(';'))
        {
            for name in names.split(", ").map(str::trim) {
                if is_bool_local(lines, name) {
                    bools.push(name.to_owned());
                }
            }
        }
    }
    let sig_changed = propagate_char_ptr_params(lines, &ptrs);
    for line in lines.iter() {
        if line.contains("//") {
            continue;
        }
        let Some(names) = line
            .strip_prefix("uint64_t ")
            .or_else(|| line.strip_prefix("uint32_t "))
            .and_then(|r| r.strip_suffix(';'))
        else {
            continue;
        };
        for name in names.split(", ").map(str::trim) {
            if name.starts_with("local_")
                && !ptrs.iter().any(|(n, _)| n == name)
                && !arrays.iter().any(|(n, _)| n == name)
                && let Some(ty) = local_copy_pointer(lines, name, &ptrs).or_else(|| {
                    sig_changed
                        .then(|| local_api_pointer(lines, name))
                        .flatten()
                })
            {
                ptrs.push((name.to_owned(), ty));
            }
        }
    }
    if ptrs.is_empty() && arrays.is_empty() && bools.is_empty() {
        return sig_changed;
    }
    rewrite_local_declarations(lines, &ptrs, &arrays, &bools);
    true
}

/// Replaces refined local variable names in declaration lines and splices their
/// new declarations directly after the last modified declaration line.
fn rewrite_local_declarations(
    lines: &mut Vec<String>,
    ptrs: &[(String, &'static str)],
    arrays: &[(String, u64)],
    bools: &[String],
) {
    let taken: BTreeSet<&str> = ptrs
        .iter()
        .map(|(n, _)| n.as_str())
        .chain(arrays.iter().map(|(n, _)| n.as_str()))
        .chain(bools.iter().map(String::as_str))
        .collect();
    let mut at = None;
    for (i, line) in lines.iter_mut().enumerate() {
        if line.contains("//") {
            continue;
        }
        let Some((ty, rest)) = ["uint64_t", "uint32_t", "uint8_t"]
            .into_iter()
            .find_map(|t| Some((t, line.strip_prefix(&format!("{t} "))?.strip_suffix(';')?)))
        else {
            continue;
        };
        let all: Vec<&str> = rest.split(", ").map(str::trim).collect();
        let kept: Vec<&str> = all.iter().copied().filter(|n| !taken.contains(n)).collect();
        if kept.len() != all.len() {
            *line = if kept.is_empty() {
                String::from("\u{0}")
            } else {
                format!("{ty} {};", kept.join(", "))
            };
            at = Some(i);
        }
    }
    if let Some(i) = at {
        let mut added: Vec<String> = ptrs
            .iter()
            .map(|(name, ty)| format!("{ty} {name};"))
            .chain(
                arrays
                    .iter()
                    .map(|(name, span)| format!("uint8_t {name}[{span}];")),
            )
            .collect();
        if !bools.is_empty() {
            added.push(format!("bool {};", bools.join(", ")));
        }
        lines.splice(i + 1..i + 1, added);
    }
    lines.retain(|l| l != "\u{0}");
}

/// Retypes an untyped word parameter in `// signature:` to `char *` when it is
/// copied into a `char*` stack local and only used in byte-offset sums.
fn propagate_char_ptr_params(lines: &mut [String], ptrs: &[(String, &'static str)]) -> bool {
    let Some(sig_idx) = lines.iter().position(|l| l.starts_with("// signature: ")) else {
        return false;
    };
    let mut changed = false;
    for (local, ty) in ptrs {
        if *ty != "char*" {
            continue;
        }
        let prefix = format!("{local} = ");
        let Some(param) = lines.iter().find_map(|l| {
            let p = l.trim().strip_prefix(&prefix)?.strip_suffix(';')?;
            is_param_name(p).then(|| p.to_owned())
        }) else {
            continue;
        };
        if assigned_values(lines, &param) > 0 {
            continue;
        }
        let copy_stmt = format!("{local} = {param};");
        let valid_uses = lines
            .iter()
            .filter(|l| !l.starts_with("//") && !is_declaration(l))
            .all(|l| {
                if l.trim() == copy_stmt {
                    return true;
                }
                word_positions(l, &param).into_iter().all(|at| {
                    let head = l.get(..at).unwrap_or("");
                    let tail = l.get(at + param.len()..).unwrap_or("");
                    cast_before(head).is_none()
                        && (head.ends_with(" + ") || tail.starts_with(" + "))
                })
            });
        if !valid_uses {
            continue;
        }
        for word in ["uint64_t ", "uint32_t "] {
            for suf in [",", ")"] {
                let old = format!("{word}{param}{suf}");
                if lines[sig_idx].contains(&old) {
                    lines[sig_idx] = lines[sig_idx].replace(&old, &format!("char *{param}{suf}"));
                    changed = true;
                }
            }
        }
    }
    changed
}

/// Returns the stack byte span of `name` when it is an address-only stack buffer
/// passed to a call alongside a buffer length fitting its stack span.
fn byte_buffer_local_span(lines: &[String], name: &str) -> Option<u64> {
    let base = name
        .strip_prefix("local_")
        .and_then(|s| u64::from_str_radix(s, 16).ok())?;
    let top = lines
        .iter()
        .filter(|l| is_declaration(l))
        .flat_map(|l| {
            l.trim_end_matches(';')
                .split_once(' ')
                .map_or("", |(_, names)| names)
                .split(", ")
                .filter_map(|n| {
                    n.trim()
                        .trim_start_matches('*')
                        .split('[')
                        .next()?
                        .strip_prefix("local_")
                        .and_then(|s| u64::from_str_radix(s, 16).ok())
                })
        })
        .filter(|&d| d < base)
        .max()
        .unwrap_or(0);
    let span = base.saturating_sub(top);
    if span < 16 {
        return None;
    }
    let mut sized_call = false;
    let mut seen = false;
    for line in lines
        .iter()
        .filter(|l| !l.starts_with("//") && !is_declaration(l))
    {
        for at in word_positions(line, name) {
            seen = true;
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            let before_amp = head.strip_suffix('&')?;
            if !(before_amp.ends_with('(') || before_amp.ends_with(", "))
                || !(tail.starts_with(", ") || tail.starts_with(')'))
            {
                return None;
            }
            if let Some(arg) = tail
                .strip_prefix(", ")
                .and_then(|r| r.split([',', ')']).next())
                && let Some(n) = parse_const(arg.trim())
                && (16..=span).contains(&n)
            {
                sized_call = true;
            }
        }
    }
    (seen && sized_call).then_some(span)
}

/// The library pointer type (`char*`, `FILE*`, `struct group*`,
/// `struct passwd*`) a stack slot's call arguments or assigned call
/// results agree on, when every other use hands the value on whole.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The stack local's name.
fn local_api_pointer(lines: &[String], name: &str) -> Option<&'static str> {
    let mut found: Option<&'static str> = None;
    let mut byte_step = false;
    let amp = format!("&{name}");
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        if line.contains(&amp) {
            return None;
        }
    }
    for (before, line) in lines
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.starts_with("//") && !is_declaration(l))
    {
        let stmt = line.trim().strip_suffix(';').unwrap_or("");
        let parts: Vec<&str> = stmt.split(" = ").collect();
        let is_chain_write = parts.len() >= 2
            && parts[..parts.len() - 1].iter().all(|p| is_ident(p))
            && parts[..parts.len() - 1].contains(&name);
        if is_chain_write
            && !check_chain_write(
                lines,
                name,
                parts[parts.len() - 1].trim(),
                before,
                &mut found,
                &mut byte_step,
            )
        {
            return None;
        }
        for part in line
            .trim()
            .strip_prefix("for (")
            .and_then(|s| s.strip_suffix(") {"))
            .into_iter()
            .flat_map(|s| s.split("; "))
        {
            if let Some((lhs, rhs)) = part.split_once(" = ")
                && lhs.trim() == name
                && !check_chain_write(lines, name, rhs.trim(), before, &mut found, &mut byte_step)
            {
                return None;
            }
        }
        for at in word_positions(line, name) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            if is_chain_write && (tail.starts_with(" = ") || head.ends_with(" = ")) {
                continue;
            }
            if (head.trim_end().ends_with("for (") || head.ends_with("; "))
                && tail.starts_with(" = ")
            {
                continue;
            }
            if !check_pointer_read(
                lines,
                line,
                at,
                before,
                head,
                tail,
                &mut found,
                &mut byte_step,
            ) {
                return None;
            }
        }
    }
    if found.is_none()
        && byte_step
        && lines.iter().any(|l| {
            !l.starts_with("//")
                && (l.contains(&format!("*(uint8_t*){name}"))
                    || l.contains(&format!("*(int8_t*){name}")))
        })
    {
        found = Some("char*");
    }
    found.filter(|&f| !byte_step || f == "char*")
}

/// Checks that a read or step of `name` at byte `at` in `line` is compatible
/// with a library pointer type (`char*` or `FILE*`).
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `line` - The line containing the occurrence.
/// * `at` - Byte offset of `name` in `line`.
/// * `before` - Line index of `line`.
/// * `head` - Prefix of `line` before `at`.
/// * `tail` - Suffix of `line` after `name`.
/// * `found` - Pointer type agreed on so far.
/// * `byte_step` - Set when the occurrence steps by bytes or dereferences a byte.
#[expect(
    clippy::too_many_arguments,
    reason = "borrows the scan state of the enclosing line loop"
)]
fn check_pointer_read(
    lines: &[String],
    line: &str,
    at: usize,
    before: usize,
    head: &str,
    tail: &str,
    found: &mut Option<&'static str>,
    byte_step: &mut bool,
) -> bool {
    if head.ends_with(" = ") && (tail.starts_with(" + ") || tail.starts_with(" - ")) {
        *byte_step = true;
        return true;
    }
    if (head.ends_with("*(uint8_t*)(") || head.ends_with("*(int8_t*)("))
        && (tail.starts_with(" + ") || tail.starts_with(" - "))
    {
        *byte_step = true;
        return true;
    }
    if head.trim().is_empty()
        && let Some(rest) = tail.strip_prefix(" += ")
        && let Some(rhs) = rest.trim().strip_suffix(';')
        && (parse_const(rhs).is_some()
            || is_ident(rhs)
            || rhs.starts_with("*(uint8_t*)")
            || rhs.contains(" == ")
            || rhs.contains(" != "))
    {
        *byte_step = true;
        return true;
    }
    if head.ends_with("*(uint8_t*)") || head.ends_with("*(int8_t*)") {
        *byte_step = true;
        return true;
    }
    if tail
        .strip_prefix(" - ")
        .and_then(|r| r.split([';', ')', ',']).next())
        .is_some_and(|rhs| is_ident(rhs.trim()))
        || head
            .strip_suffix(" - ")
            .and_then(|h| h.rsplit(['(', ',', ' ']).next())
            .is_some_and(|lhs| is_ident(lhs.trim()))
    {
        *byte_step = true;
        return true;
    }
    if cast_before(head).is_some()
        || [" = ", " += ", " -= ", " |= ", " &= ", " ^= ", "++", "--"]
            .iter()
            .any(|op| tail.starts_with(op))
    {
        return false;
    }
    match known_slot(lines, line, at, before) {
        Some(Slot::Narrow(_)) => false,
        Some(Slot::Pointer(t)) => {
            let mapped = match t.as_str() {
                "char *" => "char*",
                "FILE *" => "FILE*",
                _ => return false,
            };
            if found.is_some_and(|f| f != mapped) {
                return false;
            }
            *found = Some(mapped);
            true
        }
        Some(Slot::Other) | None => {
            let l = Line {
                text: line,
                toks: lex(line),
            };
            let Some(k) = l.toks.iter().position(|t| t.at == at) else {
                return false;
            };
            !bit_operand(&l, k) && whole_read(&l, k)
        }
    }
}

/// Checks the right-hand side of a chain write to `name`, updating `found`
/// and `byte_step`.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The stack local's name.
/// * `rhs` - The right-hand side of the assignment.
/// * `before` - The line index of the assignment.
/// * `found` - The pointer type found so far.
/// * `byte_step` - Set when `rhs` steps from `name`.
fn check_chain_write(
    lines: &[String],
    name: &str,
    rhs: &str,
    before: usize,
    found: &mut Option<&'static str>,
    byte_step: &mut bool,
) -> bool {
    if let Some(rest) = rhs
        .strip_prefix(&format!("{name} + "))
        .or_else(|| rhs.strip_prefix(&format!("{name} - ")))
        && (parse_const(rest.trim()).is_some() || is_ident(rest.trim()))
    {
        *byte_step = true;
        return true;
    }
    match classify_rhs(lines, rhs, 0, before) {
        RhsType::Known(ty) => {
            if found.is_some_and(|f| f != ty) {
                return false;
            }
            *found = Some(ty);
            true
        }
        RhsType::Neutral => true,
        RhsType::NonPointer => false,
    }
}

/// How an assigned right-hand side relates to a library pointer type.
enum RhsType {
    /// A known library pointer (`"char*"` or `"FILE*"`).
    Known(&'static str),
    /// A null constant, unknown call, or untyped identifier compatible with a pointer.
    Neutral,
    /// A non-pointer expression (integer call result, comparison, arithmetic, etc.).
    NonPointer,
}

/// The library pointer classification of an assigned right-hand side.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `rhs` - The right-hand side of an assignment.
/// * `depth` - Assignments already followed. Stops at 4.
/// * `before` - The line index of the assignment.
fn classify_rhs(lines: &[String], rhs: &str, depth: u8, before: usize) -> RhsType {
    if depth == 4 {
        return RhsType::NonPointer;
    }
    let rhs = rhs.trim();
    if matches!(rhs, "0" | "NULL" | "nullptr") {
        return RhsType::Neutral;
    }
    let l = Line {
        text: rhs,
        toks: lex(rhs),
    };
    if l.toks.len() == 1
        && l.toks[0].lex == Lex::Literal
        && rhs.starts_with('"')
        && rhs.ends_with('"')
    {
        return RhsType::Known("char*");
    }
    if is_ident(rhs) {
        return classify_ident_rhs(lines, rhs, depth, before);
    }
    if let Some(param) = rhs
        .strip_suffix("->field_0x0")
        .or_else(|| rhs.strip_prefix('*'))
        .filter(|p| is_ident(p))
        && lines.iter().any(|l| {
            l.strip_prefix("// signature: ").is_some_and(|sig| {
                sig.split(['(', ',', ')'])
                    .map(str::trim)
                    .any(|p| p == format!("char **{param}") || p == format!("const char **{param}"))
            })
        })
    {
        return RhsType::Known("char*");
    }
    if let Some(base) = rhs
        .strip_prefix("((uint64_t*)")
        .and_then(|r| r.split_once(")["))
        .map(|(b, _)| b)
        .filter(|b| is_ident(b) && rhs.ends_with(']'))
        && matches!(
            classify_ident_rhs(lines, base, depth + 1, before),
            RhsType::Known("char**")
        )
    {
        return RhsType::Known("char*");
    }
    if l.toks.len() >= 3 && l.is(1, "(") && l.toks[0].lex == Lex::Name && call_is_whole(&l) {
        let callee = l.word(0);
        let Some(decl) = typelib::declared(callee, BinaryFormat::Elf)
            .or_else(|| typelib::declared(callee, BinaryFormat::Pe))
        else {
            return RhsType::Neutral;
        };
        return match decl.ret {
            "char *" | "const char *" => RhsType::Known("char*"),
            "FILE *" => RhsType::Known("FILE*"),
            "void *" => RhsType::Neutral,
            _ => RhsType::NonPointer,
        };
    }
    if let Some((a, b)) = ternary_arms(&l) {
        return match (
            classify_rhs(lines, a, depth + 1, before),
            classify_rhs(lines, b, depth + 1, before),
        ) {
            (RhsType::NonPointer, _) | (_, RhsType::NonPointer) => RhsType::NonPointer,
            (RhsType::Known(t1), RhsType::Known(t2)) if t1 != t2 => RhsType::NonPointer,
            (RhsType::Known(t), _) | (_, RhsType::Known(t)) => RhsType::Known(t),
            (RhsType::Neutral, RhsType::Neutral) => RhsType::Neutral,
        };
    }
    if let Some((a, b)) = rhs.split_once(" + ")
        && !a.contains('(')
        && !b.contains(')')
        && (matches!(
            classify_rhs(lines, a, depth + 1, before),
            RhsType::Known("char*")
        ) || matches!(
            classify_rhs(lines, b, depth + 1, before),
            RhsType::Known("char*")
        ))
    {
        return RhsType::Known("char*");
    }
    RhsType::NonPointer
}

/// Classifies an identifier right-hand side against signature parameters
/// and single-assignment definitions.
fn classify_ident_rhs(lines: &[String], rhs: &str, depth: u8, before: usize) -> RhsType {
    for line in lines {
        if let Some(sig) = line.strip_prefix("// signature: ") {
            for p in sig.split(['(', ',', ')']).map(str::trim) {
                if ["char *", "const char *", "uint8_t *", "int8_t *"]
                    .iter()
                    .any(|t| p == format!("{t}{rhs}"))
                {
                    return RhsType::Known("char*");
                }
                if p == format!("void **{rhs}") {
                    return RhsType::Known("void**");
                }
                if p == format!("char **{rhs}") || p == format!("const char **{rhs}") {
                    return RhsType::Known("char**");
                }
                if p == format!("FILE *{rhs}") {
                    return RhsType::Known("FILE*");
                }
                if let Some((ty, n)) = p.rsplit_once(' ')
                    && n == rhs
                    && narrow_type(ty.trim()).is_some()
                {
                    return RhsType::NonPointer;
                }
            }
        }
    }
    if let Some(src) = sole_rhs(lines, rhs, before) {
        return classify_rhs(lines, src, depth + 1, before);
    }
    RhsType::Neutral
}

/// Tells whether `param`'s layout is a contiguous run of two or more `u64`
/// fields from offset zero, read as strings or passed to calls.
pub(super) fn string_pointer_array(lines: &[String], param: &str) -> bool {
    let prefix = format!("// layout {param}: ");
    let Some(layout) = lines.iter().find_map(|l| l.strip_prefix(&prefix)) else {
        return false;
    };
    let fields: Vec<&str> = layout.split(", ").collect();
    if fields.len() < 2 {
        return false;
    }
    let mut any_str = false;
    for (i, entry) in fields.iter().enumerate() {
        let off = i * 8;
        if *entry != format!("0x{off:x} u64") {
            return false;
        }
        let field = format!("{param}->field_0x{off:x}");
        let is_str = lines.iter().any(|l| {
            !l.starts_with("//")
                && (l.contains(&format!("strcmp({field},"))
                    || l.contains(&format!("strrchr({field},"))
                    || l.contains(&format!("*(uint8_t*){field}")))
        });
        let is_call = lines.iter().any(|l| {
            !l.starts_with("//")
                && (l.contains(&format!("({field})")) || l.contains(&format!("({field},")))
        });
        if !is_str && !is_call {
            return false;
        }
        any_str |= is_str;
    }
    any_str
}

/// Tells whether `param`'s layout is a single `0x0 u32` field copied to or
/// from a stack local and never used otherwise.
pub(super) fn single_field_int_ptr(lines: &[String], param: &str) -> bool {
    if !lines
        .iter()
        .any(|l| l == &format!("// layout {param}: 0x0 u32"))
    {
        return false;
    }
    let field = format!("{param}->field_0x0");
    let mut local_copy = false;
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            if line
                .get(at + param.len()..)
                .and_then(|t| t.strip_prefix("->field_0x0"))
                .is_none_or(|r| r.starts_with(is_ident_char))
            {
                return false;
            }
        }
        if let Some((lhs, rhs)) = line
            .trim()
            .strip_suffix(';')
            .and_then(|s| s.split_once(" = "))
            && ((lhs == field && rhs.starts_with("local_"))
                || (rhs == field && lhs.starts_with("local_")))
        {
            local_copy = true;
        }
    }
    local_copy
}

/// Tells whether `param`'s layout is a single `0x0 u64` field copied into a
/// stack local that steps by bytes (`local_N += 1` or `*(uint8_t*)local_N`).
pub(super) fn single_field_char_ptr_ptr(lines: &[String], param: &str) -> bool {
    if !lines
        .iter()
        .any(|l| l == &format!("// layout {param}: 0x0 u64"))
    {
        return false;
    }
    let field = format!("{param}->field_0x0");
    let mut copied_local = None;
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            if line
                .get(at + param.len()..)
                .and_then(|t| t.strip_prefix("->field_0x0"))
                .is_none_or(|r| r.starts_with(is_ident_char))
            {
                return false;
            }
        }
        if let Some((lhs, rhs)) = line
            .trim()
            .strip_suffix(';')
            .and_then(|s| s.split_once(" = "))
            && rhs == field
            && lhs.starts_with("local_")
        {
            copied_local = Some(lhs.to_owned());
        }
    }
    let Some(local) = copied_local else {
        return false;
    };
    lines.iter().any(|l| {
        !l.starts_with("//")
            && (l.contains(&format!("*(uint8_t*){local}"))
                || l.contains(&format!("*(int8_t*){local}")))
    }) && lines.iter().any(|l| {
        !l.starts_with("//")
            && (l.trim().starts_with(&format!("{local} += "))
                || l.trim().starts_with(&format!("{local} = {local} + ")))
    })
}

/// Splits a top-level ternary expression into its two arms.
///
/// # Arguments
///
/// * `l` - The expression.
fn ternary_arms<'a>(l: &Line<'a>) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let mut q = None;
    let mut c = None;
    for (k, tok) in l.toks.iter().enumerate() {
        match l.word(k) {
            "(" | "[" => depth += 1,
            ")" | "]" => depth -= 1,
            "?" if depth == 0 && q.is_none() => q = Some(tok),
            ":" if depth == 0 && q.is_some() && c.is_none() => c = Some(tok),
            _ => {}
        }
    }
    let (q, c) = (q?, c?);
    Some((l.text.get(q.end..c.at)?.trim(), l.text.get(c.end..)?.trim()))
}

/// The library pointer type (`char*` or `FILE*`) a stack slot takes from a
/// copy of another typed stack slot.
///
/// The slot may only step by bytes or compare with the source slot.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The stack local's name.
/// * `ptrs` - Stack locals already resolved to library pointer types.
fn local_copy_pointer(
    lines: &[String],
    name: &str,
    ptrs: &[(String, &'static str)],
) -> Option<&'static str> {
    if lines
        .iter()
        .any(|l| !l.starts_with("//") && l.contains(&format!("&{name}")))
    {
        return None;
    }
    let mut found: Option<&'static str> = None;
    let mut byte_step = false;
    for (before, line) in lines
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.starts_with("//") && !is_declaration(l))
    {
        let stmt = line.trim().strip_suffix(';').unwrap_or("");
        let parts: Vec<&str> = stmt.split(" = ").collect();
        let is_chain_write = parts.len() >= 2
            && parts[..parts.len() - 1].iter().all(|p| is_ident(p))
            && parts[..parts.len() - 1].contains(&name);
        if is_chain_write {
            let rhs = parts[parts.len() - 1].trim();
            if let Some((_, ty)) = parts[..parts.len() - 1]
                .iter()
                .find_map(|&lhs| ptrs.iter().find(|(n, _)| n == lhs))
            {
                if found.is_some_and(|f| f != *ty) {
                    return None;
                }
                found = Some(*ty);
            } else {
                let (base, stepped) = match rhs.split_once(" + ") {
                    Some((b, step)) => {
                        let step = step.trim();
                        if !(parse_const(step).is_some()
                            || is_ident(step)
                            || step.starts_with("*(uint8_t*)"))
                        {
                            return None;
                        }
                        (b.trim(), true)
                    }
                    None => (rhs, false),
                };
                if let Some((_, ty)) = ptrs.iter().find(|(n, _)| n == base) {
                    if found.is_some_and(|f| f != *ty) {
                        return None;
                    }
                    found = Some(*ty);
                    byte_step |= stepped;
                } else if !matches!(rhs, "0" | "NULL" | "nullptr")
                    && !matches!(classify_rhs(lines, rhs, 0, before), RhsType::Neutral)
                {
                    return None;
                }
            }
        } else if let Some((lhs, rhs)) = stmt.split_once(" = ").or_else(|| {
            line.trim()
                .strip_prefix("for (")
                .and_then(|s| s.split_once("; "))
                .and_then(|(init, _)| init.split_once(" = "))
        }) && rhs.split(" + ").next().unwrap_or("") == name
            && let Some((_, ty)) = ptrs.iter().find(|(n, _)| n == lhs)
        {
            if found.is_some_and(|f| f != *ty) {
                return None;
            }
            found = Some(*ty);
        }
        for at in word_positions(line, name) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            if is_chain_write && (tail.starts_with(" = ") || head.ends_with(" = ")) {
                continue;
            }
            if !check_pointer_read(
                lines,
                line,
                at,
                before,
                head,
                tail,
                &mut found,
                &mut byte_step,
            ) {
                return None;
            }
        }
    }
    found.filter(|&f| !byte_step || f == "char*")
}

/// Tells whether a `uint8_t` stack local is used only as a `bool`.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The local's name.
fn is_bool_local(lines: &[String], name: &str) -> bool {
    if !name.starts_with("local_") {
        return false;
    }
    let (mut zero, mut one, mut rel_write, mut reads) = (false, false, false, 0usize);
    let mut all_reads_zero_test = true;
    for line in lines
        .iter()
        .filter(|l| !l.starts_with("//") && !is_declaration(l))
    {
        let positions = word_positions(line, name);
        if positions.is_empty() {
            continue;
        }
        let stmt = line.trim().strip_suffix(';').unwrap_or("");
        let parts: Vec<&str> = stmt.split(" = ").collect();
        let is_chain_write = parts.len() >= 2
            && parts[..parts.len() - 1].iter().all(|p| is_ident(p))
            && parts[..parts.len() - 1].contains(&name);
        if is_chain_write {
            let rhs = parts[parts.len() - 1].trim();
            if matches!(rhs, "0" | "false") {
                zero = true;
            } else if matches!(rhs, "1" | "true") {
                one = true;
            } else if is_bool_expr(rhs) {
                rel_write = true;
            } else {
                return false;
            }
        }
        for at in positions {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            if is_chain_write && tail.starts_with(" = ") {
                continue;
            }
            if head.ends_with(['&', '*'])
                || tail.starts_with(['[', '.'])
                || tail.starts_with("->")
                || [
                    " = ", " += ", " -= ", " |= ", " &= ", " ^= ", " *= ", " /= ", " %= ", " <<= ",
                    " >>= ", "++", "--",
                ]
                .iter()
                .any(|op| tail.starts_with(op))
                || head.ends_with("++")
                || head.ends_with("--")
            {
                return false;
            }
            reads += 1;
            let z = [" == 0", " != 0"].iter().any(|op| {
                tail.strip_prefix(op)
                    .is_some_and(|r| !r.starts_with(|c: char| c.is_ascii_alphanumeric()))
            });
            all_reads_zero_test &= z;
        }
    }
    (rel_write && (zero || one || reads > 0)) || (zero && one && reads > 0 && all_reads_zero_test)
}

/// Tells whether `rhs` is a relational or boolean expression at top level.
///
/// # Arguments
///
/// * `rhs` - The right-hand side of an assignment.
fn is_bool_expr(rhs: &str) -> bool {
    let l = Line {
        text: rhs.trim(),
        toks: lex(rhs.trim()),
    };
    if l.toks.is_empty() {
        return false;
    }
    let mut depth = 0i32;
    let mut rel_or_logic = false;
    let mut arith = false;
    for k in 0..l.toks.len() {
        let w = l.word(k);
        match w {
            "(" | "[" => depth += 1,
            ")" | "]" => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            "|" | "^" | "&" | "?" | ":" if depth == 0 => return false,
            "==" | "!=" | "<=" | ">=" | "<" | ">" | "&&" | "||" if depth == 0 => {
                rel_or_logic = true;
            }
            "+" | "-" | "/" | "%" | "<<" | ">>" if depth == 0 => arith = true,
            "*" if depth == 0
                && k > 0
                && (matches!(l.word(k - 1), ")" | "]") || l.toks[k - 1].lex != Lex::Punct) =>
            {
                arith = true;
            }
            _ => {}
        }
    }
    depth == 0 && (rel_or_logic || (l.is(0, "!") && !arith))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::refine_locals;

    /// Stack locals take `bool` and `char*` when their writes and reads
    /// agree, cyclic copy chains stop at a bounded depth, and integer reads,
    /// prefix parameter names, and arithmetic after `!` refuse retyping.
    #[test]
    fn stack_locals_refine_from_their_uses() {
        let mut lines: Vec<String> = [
            "// signature: uint32_t f(uint64_t a1, char *a10)",
            "uint64_t local_40, local_38, local_30, local_28, local_20, local_18, local_10;",
            "uint8_t local_a, local_9;",
            "",
            "var1 = var2;",
            "var2 = var1;",
            "local_10 = var1;",
            "local_9 = a10 != 0;",
            "local_a = !a1 + 2;",
            "local_18 = strdup(a10);",
            "local_20 = local_18 + 1;",
            "local_28 = local_18;",
            "local_30 = a1;",
            "local_38 = strchr(a10, 97);",
            "local_38 = strlen(a10);",
            "local_40 = strchr(a10, 97) == 0;",
            "if (local_9 != 0 && local_a != 0 && local_38 != 0 && local_40 != 0) {",
            "  puts(local_20);",
            "}",
            "return (local_28 & 0xff) + local_30 + local_10;",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        assert!(refine_locals(&mut lines));
        let joined = lines.join("\n");
        assert!(joined.contains("bool local_9;"), "{joined}");
        assert!(joined.contains("uint8_t local_a;"), "{joined}");
        assert!(
            joined.contains("uint64_t local_40, local_38, local_30, local_28, local_10;"),
            "{joined}"
        );
        assert!(joined.contains("char* local_18;"), "{joined}");
        assert!(joined.contains("char* local_20;"), "{joined}");
    }
}
