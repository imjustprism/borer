//! Where a written value came from: the identifiers and fields an
//! expression names, the numbers it spells, and the assignments and out
//! arguments followed back from a write to the field it was read from.

use super::*;

/// Tells whether `word` is something a value passes through on its way
/// to the stream: a register, a temporary, a local or a home slot.
///
/// # Arguments
///
/// * `word` - An identifier.
pub(super) fn is_carrier(word: &str) -> bool {
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
pub(super) fn identifiers(expr: &str) -> Vec<&str> {
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
pub(crate) fn number(s: &str) -> Option<(u64, usize)> {
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

/// Strips leading casts: `(uint8_t)local_c` is `local_c`.
///
/// # Arguments
///
/// * `s` - The expression.
pub(crate) fn strip_casts(mut s: &str) -> &str {
    while let Some(rest) = s.strip_prefix('(')
        && let Some(close) = rest.find(')')
        && let ty = rest[..close].trim()
        && (ty.ends_with("_t") || ty.ends_with('*') || ty == "char" || ty == "int")
    {
        s = rest[close + 1..].trim_start();
    }
    s.trim()
}

/// Returns the value of `s` when the whole of it, casts stripped, is a
/// decimal or `0x` hexadecimal number: `33` and `(uint8_t)0x21` are, `a2`
/// and `12 + a2` are not.
///
/// # Arguments
///
/// * `s` - The text.
pub(crate) fn literal(s: &str) -> Option<u64> {
    let s = strip_casts(s);
    number(s).and_then(|(v, len)| (len == s.len()).then_some(v))
}

/// Spells an offset as the tables do.
///
/// # Arguments
///
/// * `off` - The offset.
pub(super) fn offset_text(off: u64) -> String {
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
pub(super) fn field_tokens(expr: &str) -> Vec<String> {
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

/// Returns a helper's argument as the source of its write: a number or a
/// bare parameter as written, else the field [`field_of`] reads in it.
///
/// # Arguments
///
/// * `arg` - The argument.
pub(super) fn constant_or_field(arg: &str) -> Option<String> {
    let bare = literal(arg).is_some() || BASES.contains(&arg.trim());
    bare.then(|| arg.trim().to_owned())
        .or_else(|| field_of(arg))
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
pub(super) fn field_of(expr: &str) -> Option<String> {
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
pub(super) fn compact_expr(expr: &str) -> String {
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
pub(super) fn element_of(expr: &str) -> Option<String> {
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
pub(super) fn source_chain_end(lines: &[&str], at: usize, var: &str) -> Option<(String, usize)> {
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
pub(super) fn carrier_plus(expr: &str) -> Option<(&str, u64)> {
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
pub(super) fn assigned_to<'l>(line: &'l str, var: &str) -> Option<&'l str> {
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
pub(super) fn source_of(lines: &[&str], at: usize, var: &str) -> Option<String> {
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
pub(super) fn out_arg_source(lines: &[&str], at: usize, var: &str) -> Option<(String, String)> {
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
pub(super) fn out_arg_source_below(
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
