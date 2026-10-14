//! Final text passes: `x ?: y`, temporary names, float returns, and the source
//! file a function cites.

use super::*;
use crate::num::from_usize;

/// The text passes every decompile ends with.
///
/// The header lines the text's own calls give, one variable per register
/// web ([`vars::split_webs`]), layouts, then parameter types, then the
/// byte arithmetic those types would otherwise scale, and last the names
/// and types the evidence gives the variables and the constants they
/// take ([`evidence::name_vars`]).
///
/// For callers that assemble the text themselves; [`decompile`] and
/// [`decompile_named`] already apply it.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `bitness` - Decoder bitness of the program (32 or 64), which is the
///   width of a parameter nothing narrowed.
/// * `packs` - The packs in force, for the stream classes a `// wire:`
///   line is read through.
///
/// # Returns
///
/// The text with the names its own assertions give, layouts, parameter
/// types and byte offsets through typed pointers applied.
#[must_use]
pub fn polish(text: &str, bitness: u32, packs: &crate::pack::Packs) -> String {
    let streams = packs.list("types", "stream");
    let word = word_type(bitness);
    let text = normalize_temps(&evidence::name_vars(
        &byte_arithmetic(
            &type_locals(&type_parameters(
                &apply_layouts(&vars::split_webs(&wire_format(
                    &source_file(&name_own_fields(text)),
                    &streams,
                ))),
                word,
            )),
            word,
        ),
        u8::try_from(bitness).unwrap_or(64),
    ));
    let mut out: String = text.lines().map(elvis).collect::<Vec<_>>().join("\n");
    out.push('\n');
    out
}

/// Writes `(x != 0 ? x : y)` as `(x ?: y)` on one line.
///
/// A value used when it is set and a fallback otherwise, `heapBuffer ?
/// heapBuffer : localBuffer`, is one load and one test in the code, and
/// spelling it twice doubles what a reader has to compare. Only a value
/// that calls nothing is shortened, so reading it once is reading it twice.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C.
pub(super) fn elvis(line: &str) -> String {
    /// What joins the tested value to the value used when it is set.
    const TEST: &str = " != 0 ? ";
    let mut out = line.to_owned();
    let mut from = 0;
    while let Some(i) = out.get(from..).and_then(|t| t.find(TEST)).map(|i| from + i) {
        from = i + TEST.len();
        let head = out.get(..i).unwrap_or("");
        let mut depth = 0i32;
        let open = head.char_indices().rev().find_map(|(k, c)| {
            match c {
                ')' => depth += 1,
                '(' if depth == 0 => return Some(k),
                '(' => depth -= 1,
                _ => {}
            }
            None
        });
        let Some(open) = open else {
            continue;
        };
        let value = head.get(open + 1..).unwrap_or("");
        let calls = value
            .char_indices()
            .any(|(k, c)| c == '(' && value.get(..k).is_some_and(|h| h.ends_with(is_ident_char)));
        let tail = out.get(from..).unwrap_or("");
        let Some(rest) = tail.strip_prefix(value).and_then(|r| r.strip_prefix(" : ")) else {
            continue;
        };
        if value.is_empty() || calls {
            continue;
        }
        let replacement = format!("({value} ?: ");
        let end = out.len() - rest.len();
        out.replace_range(open..end, &replacement);
        from = open + replacement.len();
    }
    out
}

/// Threshold above which a `tmp_N` is a lift-pass materialization temporary.
///
/// The emission pass numbers readable temporaries from 1; the lift pass parks
/// values from `1 << 30` to keep the two spaces apart.
pub(super) const LIFT_TMP_BASE: u64 = 1 << 30;

/// Parses a `tmp_<digits>` token starting at byte `pos`, if one does.
///
/// Requires a word boundary before `tmp_` so `xtmp_5` does not match, and
/// consumes the whole digit run.
///
/// # Arguments
///
/// * `bytes` - The text as bytes.
/// * `pos` - The candidate start.
///
/// # Returns
///
/// `(id, length)` of the token, or `None`.
pub(super) fn temp_token(bytes: &[u8], pos: usize) -> Option<(u64, usize)> {
    if pos > 0 {
        let p = bytes[pos - 1];
        if p.is_ascii_alphanumeric() || p == b'_' {
            return None;
        }
    }
    let rest = bytes.get(pos..)?;
    let digits = rest.strip_prefix(b"tmp_")?;
    let n = digits.iter().take_while(|b| b.is_ascii_digit()).count();
    if n == 0 {
        return None;
    }
    let id: u64 = std::str::from_utf8(&digits[..n]).ok()?.parse().ok()?;
    Some((id, 4 + n))
}

/// Renumbers any lift-pass temporary that leaked into the emitted text.
///
/// Almost every value parked in a `1 << 30`-based temporary is inlined before
/// it is emitted, but a value compared straight off a join can escape as
/// `tmp_1073741825`. This maps every such leaked id to a small name just past
/// the readable temporaries, consistently — each distinct id to one distinct
/// name — so the output never shows a raw internal id. Readable temporaries and
/// every other token are left untouched; the rewrite is deterministic.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The text with leaked temporaries renumbered, or unchanged when there are
/// none.
pub(super) fn normalize_temps(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut small_max = 0u64;
    let mut leaked: BTreeSet<u64> = BTreeSet::new();
    let mut i = 0;
    while i < bytes.len() {
        if let Some((id, len)) = temp_token(bytes, i) {
            if id >= LIFT_TMP_BASE {
                leaked.insert(id);
            } else {
                small_max = small_max.max(id);
            }
            i += len;
        } else {
            i += 1;
        }
    }
    if leaked.is_empty() {
        return text.to_owned();
    }
    let remap: BTreeMap<u64, u64> = leaked
        .iter()
        .enumerate()
        .map(|(k, id)| (*id, small_max + 1 + from_usize(k)))
        .collect();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < bytes.len() {
        if let Some((id, len)) = temp_token(bytes, i) {
            match remap.get(&id) {
                Some(new) => out.push_str(&format!("tmp_{new}")),
                None => out.push_str(&text[i..i + len]),
            }
            i += len;
        } else {
            // Copy one UTF-8 character so we never split a codepoint.
            let ch_len = text[i..].chars().next().map_or(1, char::len_utf8);
            out.push_str(&text[i..i + ch_len]);
            i += ch_len;
        }
    }
    out
}

/// Tells whether a declared return type comes back in `xmm0`.
///
/// # Arguments
///
/// * `ret` - The declared return type.
pub(super) fn float_return(ret: &str) -> bool {
    matches!(
        ret.trim_start_matches("const ").trim(),
        "float" | "double" | "long double"
    )
}

/// Heads a function with the source file it came from.
///
/// Every assertion cites the file it was written in, so a function that
/// asserts anything says where it lives. That is the subsystem it belongs
/// to, and the question "what is this part of" is otherwise answered only
/// by reading its callers. A body citing several files inlined a callee
/// that asserts too, so the file is taken when it is the only one, when the
/// function's class names it (`Skills::GameSkill` names `gameskill.cc`), or
/// when one is cited more often than any other; nothing is written when the
/// evidence ties, since a guessed location is worse than none.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
///
/// # Returns
///
/// The text with a `// source:` line, or unchanged.
pub(super) fn source_file(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    // A source the debug information stated is a fact and stands: the
    // citations guess at a file, so they do not get a second word in.
    if lines[..header_len(&lines)]
        .iter()
        .any(|l| l.starts_with("// source:"))
    {
        return text.to_owned();
    }
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut order: Vec<&str> = Vec::new();
    for line in &lines {
        for p in cited_paths(line) {
            if counts
                .insert(p, counts.get(p).copied().unwrap_or(0) + 1)
                .is_none()
            {
                order.push(p);
            }
        }
    }
    let Some(pick) = pick_path(&counts, &order, lines.first().copied().unwrap_or("")) else {
        return text.to_owned();
    };
    let mut out: Vec<String> = lines.iter().map(|l| (*l).to_owned()).collect();
    out.insert(header_len(&lines), format!("// source: {pick}"));
    let mut joined = out.join("\n");
    joined.push('\n');
    joined
}

/// Lists the source paths a line quotes, and the crate file a Rust
/// panic's location beside it names (`// at rhai-1.26.1/src/parser.rs:12:5`).
///
/// # Arguments
///
/// * `line` - One emitted line.
///
/// # Returns
///
/// Each quoted token that names a source file, then the location's file.
pub(super) fn cited_paths(line: &str) -> Vec<&str> {
    /// Extensions a cited source file ends in.
    const EXTENSIONS: [&str; 6] = [".h", ".hpp", ".inl", ".c", ".cc", ".cpp"];
    let mut out = Vec::new();
    let mut rest = line;
    while let Some((_, tail)) = rest.split_once('"') {
        let Some((text, after)) = tail.split_once('"') else {
            break;
        };
        rest = after;
        if !text.contains(' ') && EXTENSIONS.iter().any(|e| text.ends_with(e)) {
            out.push(text);
        }
    }
    // INVARIANT: a Rust panic's location, written beside its call, cites
    // the crate file it was raised in; the standard library's own files
    // are where every crate's panics go, no file of this function's.
    if let Some((_, at)) = line.rsplit_once("  // at ")
        && let Some(path) = at.rsplitn(3, ':').nth(2)
        && path.ends_with(".rs")
        && !["core/", "alloc/", "std/"]
            .iter()
            .any(|s| path.starts_with(s))
    {
        out.push(path);
    }
    out
}

/// Chooses the function's own file from the ones its body cites.
///
/// # Arguments
///
/// * `counts` - How often each path appears.
/// * `order` - The paths in first-appearance order.
/// * `head` - The function's first header line, which names it.
///
/// # Returns
///
/// The path, or `None` when the evidence does not settle on one.
pub(super) fn pick_path<'a>(
    counts: &BTreeMap<&'a str, usize>,
    order: &[&'a str],
    head: &str,
) -> Option<&'a str> {
    if let [only] = order {
        return Some(only);
    }
    let name = head.strip_prefix("// ")?.split(" @ ").next()?;
    let stem = classes::class_of(name)
        .unwrap_or("")
        .rsplit("::")
        .next()
        .unwrap_or("")
        .split('<')
        .next()
        .unwrap_or("")
        .to_lowercase();
    if !stem.is_empty()
        && let Some(p) = order.iter().find(|p| {
            p.rsplit('/')
                .next()
                .and_then(|f| f.rsplit_once('.'))
                .is_some_and(|(s, _)| s == stem)
        })
    {
        return Some(p);
    }
    let best = counts.values().max().copied()?;
    let mut top = counts.iter().filter(|(_, n)| **n == best);
    let (only, None) = (top.next()?, top.next()) else {
        return None;
    };
    Some(only.0)
}
