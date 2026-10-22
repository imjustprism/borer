//! Final text passes: `x ?: y`, temporary names, float returns, and the source
//! file a function cites.

use std::collections::{BTreeMap, BTreeSet};

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
    polish_skipping(text, bitness, packs, Passes::NONE)
}

/// [`polish`] with some of its passes left out.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `bitness` - Decoder bitness of the program (32 or 64).
/// * `packs` - The packs in force.
/// * `skip` - The passes left out ([`Passes`]).
///
/// # Returns
///
/// The polished text.
pub(super) fn polish_skipping(
    text: &str,
    bitness: u32,
    packs: &crate::pack::Packs,
    skip: Passes,
) -> String {
    let streams = packs.list("types", "stream");
    let word = word_type(bitness);
    let text = skip.apply(Pass::NameOwnFields, text.to_owned(), name_own_fields);
    let text = skip.apply(Pass::SourceFile, text, source_file);
    let text = skip.apply(Pass::WireFormat, text, |t| wire_format(t, &streams));
    let text = skip.apply(Pass::SplitWebs, text, vars::split_webs);
    let text = skip.apply(Pass::ApplyLayouts, text, apply_layouts);
    let text = skip.apply(Pass::FloatLanes, text, float_lanes);
    let text = skip.apply(Pass::LaneLocals, text, lane_locals);
    let text = skip.apply(Pass::TypeParameters, text, |t| type_parameters(t, word));
    let text = skip.apply(Pass::TypeLocals, text, type_locals);
    let text = skip.apply(Pass::ByteArithmetic, text, |t| byte_arithmetic(t, word));
    let text = skip.apply(Pass::NameVars, text, |t| {
        evidence::name_vars(t, u8::try_from(bitness).unwrap_or(64))
    });
    let text = skip.apply(Pass::NormalizeTemps, text, normalize_temps);
    let text = skip.apply(Pass::QuietZeroTests, text, quiet_zero_tests);
    let text = skip.apply(
        Pass::DropRepeatedAssignments,
        text,
        drop_repeated_assignments,
    );
    let mut out = String::with_capacity(text.len() + 1);
    for (i, line) in text.lines().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let line = skip.apply(Pass::CompoundAssign, line.to_owned(), compound_assign);
        out.push_str(&skip.apply(Pass::Elvis, line, elvis));
    }
    out.push('\n');
    let text = skip.apply(Pass::SpellIndex, out, spell_index);
    let text = skip.apply(Pass::SpellOwnEnum, text, spell_own_enum);
    let text = skip.apply(Pass::SpellNullptr, text, spell_nullptr);
    let text = skip.apply(Pass::StoreStrings, text, store_strings);
    let text = skip.apply(Pass::CopyRuns, text, copy_runs);
    let text = skip.apply(Pass::StackArrays, text, stack_arrays);
    let text = skip.apply(Pass::CallablePointers, text, callable_pointers);
    let text = skip.apply(Pass::FloatBitReads, text, float_bit_reads);
    let text = skip.apply(Pass::FloatBitCopies, text, float_bit_copies);
    let text = skip.apply(Pass::RefoldJumps, text, refold_jumps);
    skip.apply(Pass::SpellFloatRelations, text, spell_float_relations)
}

/// Drops an assignment an `if` block opens with when the line before the
/// `if` made the very same one.
///
/// `var1 = 0; if (a1 != 0) { var1 = 0; ... }` sets nothing new: the value
/// is a constant, an address or a plain name, and the condition between
/// the two neither names the variable nor assigns anything, so the second
/// write stores what the first left. A loop's head runs again after its
/// body, so only an `if` qualifies.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The text without those repeats.
fn drop_repeated_assignments(text: &str) -> String {
    let mut lines: Vec<&str> = text.lines().collect();
    let mut i = 0;
    while i + 2 < lines.len() {
        let first = lines[i].trim();
        let cond = lines[i + 1]
            .trim()
            .strip_prefix("if (")
            .and_then(|c| c.strip_suffix(") {"));
        let repeated = first
            .strip_suffix(';')
            .and_then(|b| b.split_once(" = "))
            .is_some_and(|(name, value)| {
                let simple = parse_const(value).is_some()
                    || is_ident(value)
                    || value.strip_prefix('&').is_some_and(is_ident);
                simple
                    && is_ident(name)
                    && name != value
                    && cond.is_some_and(|c| {
                        word_positions(c, name).is_empty()
                            && !c.contains(" = ")
                            && !c.contains("++")
                            && !c.contains("--")
                    })
                    && lines[i + 2].trim() == first
            });
        if repeated {
            lines.remove(i + 2);
        }
        i += 1;
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Writes `(x != 0 ? x : y)` as `(x ?: y)` on one line.
///
/// `name = name op value` as `name op= value`, when both reads of `name`
/// are that plain name and `value` is one name or one number.
///
/// `x += y + z` is not `x = (x + y) + z` for every operator, and
/// `*p = *p + 1` is two loads. A call on either side stays `=`. `++` is
/// not the spelling of an add.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C.
pub(super) fn compound_assign(line: &str) -> String {
    let trimmed = line.trim_start();
    let Some(stmt) = trimmed.strip_suffix(';') else {
        return line.to_owned();
    };
    let Some((lhs, rhs)) = stmt.split_once(" = ") else {
        return line.to_owned();
    };
    if !is_ident(lhs) || stmt.contains('(') {
        return line.to_owned();
    }
    const OPS: [&str; 7] = [" + ", " - ", " << ", " >> ", " & ", " | ", " ^ "];
    for op in OPS {
        let Some(rest) = rhs.strip_prefix(lhs).and_then(|r| r.strip_prefix(op)) else {
            continue;
        };
        if !primary(rest) {
            return line.to_owned();
        }
        let pad = line.len() - trimmed.len();
        let sym = op.trim();
        return format!("{}{lhs} {sym}= {rest};", " ".repeat(pad));
    }
    line.to_owned()
}

/// A name or an integer literal, the only right-hand side a compound
/// assignment may take without changing the order of operations.
///
/// # Arguments
///
/// * `text` - The text after `name op`.
fn primary(text: &str) -> bool {
    if is_ident(text) {
        return true;
    }
    if let Some(hex) = text.strip_prefix("0x") {
        return !hex.is_empty() && hex.chars().all(|c| c.is_ascii_hexdigit());
    }
    !text.is_empty() && text.chars().all(|c| c.is_ascii_digit())
}

/// Shortens a value used when set and a fallback otherwise to `x ?: y`.
///
/// `heapBuffer ? heapBuffer : localBuffer` is one load and one test in the
/// code, and spelling it twice doubles what a reader has to compare. Only a
/// value that calls nothing is shortened, so reading it once is reading it
/// twice.
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

/// The bits type of a scalar float type the text names, `float` or
/// `double`, with its width.
///
/// # Arguments
///
/// * `ty` - A type as the text spells it.
fn float_bits_type(ty: &str) -> Option<(&'static str, u8)> {
    match ty.trim() {
        "float" => Some(("uint32_t", 32)),
        "double" => Some(("uint64_t", 64)),
        _ => None,
    }
}

/// Writes the copies between a float the signature declares and a local
/// the text declares as an integer as the bits the machine copies.
///
/// A vector register the lifter declares as an integer, the bits a sign
/// mask leaves, is still the register a plain `movaps` copies a float
/// argument into and the register whose bits a float function hands back
/// in `xmm0`. C converts on `var1 = a1` and on `return var1`: a number
/// where the machine moved bits. A whole copy of a `float` parameter into
/// a `uint32_t` or `uint64_t` local reads its bits, `*(uint32_t*)&a1`, a
/// `double` one into a `uint64_t` local `*(uint64_t*)&a1`, and a `return`
/// of a local at least as wide as the function's `float` or `double`
/// result reads the local's low bytes as that result, `*(float*)&var1`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those copies spelled as bit copies.
pub(super) fn float_bit_copies(text: &str) -> String {
    let Some(sig) = text.lines().find_map(|l| l.strip_prefix("// signature: ")) else {
        return text.to_owned();
    };
    let Some((head, params)) = sig.split_once('(') else {
        return text.to_owned();
    };
    let result = head
        .trim()
        .rsplit_once(' ')
        .and_then(|(ty, _)| float_bits_type(ty))
        .map(|(_, bits)| (if bits == 32 { "float" } else { "double" }, bits));
    let floats: BTreeMap<&str, (&str, u8)> = params
        .split([',', ')'])
        .filter_map(|p| {
            let (ty, name) = p.trim().rsplit_once(' ')?;
            let bits = float_bits_type(ty)?;
            is_param_name(name).then_some((name, bits))
        })
        .collect();
    if floats.is_empty() && result.is_none() {
        return text.to_owned();
    }
    let mut locals: BTreeMap<String, u8> = BTreeMap::new();
    for line in text.lines() {
        for (ty, bits) in [("uint32_t ", 32), ("uint64_t ", 64)] {
            let Some(rest) = line.strip_prefix(ty).and_then(|r| r.strip_suffix(';')) else {
                continue;
            };
            for name in rest.split(", ").map(str::trim) {
                if is_ident(name) && !is_param_name(name) {
                    locals.insert(name.to_owned(), bits);
                }
            }
        }
    }
    if locals.is_empty() {
        return text.to_owned();
    }
    let mut changed = false;
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    for line in lines.iter_mut().filter(|l| !l.starts_with("//")) {
        let indent = " ".repeat(line.len() - line.trim_start().len());
        let Some(body) = line.trim().strip_suffix(';') else {
            continue;
        };
        let rewritten = if let Some(local) = body.strip_prefix("return ") {
            result
                .filter(|(_, bits)| locals.get(local).is_some_and(|w| w >= bits))
                .map(|(ty, _)| format!("{indent}return *({ty}*)&{local};"))
        } else if let Some((lhs, rhs)) = body.split_once(" = ") {
            floats
                .get(rhs)
                .filter(|(_, bits)| locals.get(lhs).is_some_and(|w| w >= bits))
                .map(|(ty, _)| format!("{indent}{lhs} = *({ty}*)&{rhs};"))
        } else {
            None
        };
        if let Some(new) = rewritten {
            *line = new;
            changed = true;
        }
    }
    if !changed {
        return text.to_owned();
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
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

/// Writes a pointer compared with zero as `nullptr`.
///
/// An integer compared with zero stays `0`, and so does `return 0`, a
/// cast to an integer, and a load of an integer. A name declared as a
/// pointer, `this`, or a load whose cast type is itself a pointer
/// (`*(uint8_t**)p`) takes `nullptr`. `NULL` is a call argument, not
/// this spelling. An enumerator the header already named stays that
/// name: this runs after [`spell_own_enum`].
///
/// # Arguments
///
/// * `text` - A decompilation, types and enumerator names already applied.
pub(super) fn spell_nullptr(text: &str) -> String {
    let names = pointer_names(text);
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        if line.trim_start().starts_with("//") {
            out.push_str(line);
        } else {
            out.push_str(&rewrite_nullptr(line, &names));
        }
        out.push('\n');
    }
    out
}

/// Names the text declares as pointers: a signature parameter whose type
/// has a `*`, including `this`, and a local declaration with a star.
///
/// # Arguments
///
/// * `text` - The function.
fn pointer_names(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if let Some(sig) = trimmed.strip_prefix("// signature: ") {
            out.extend(signature_pointers(sig));
            continue;
        }
        let Some((ty, items)) = vars::declaration(line) else {
            continue;
        };
        let typed = ty.trim_end().ends_with('*');
        for (stars, name) in items {
            if typed || !stars.is_empty() {
                out.insert(name.to_owned());
            }
        }
    }
    out
}

/// The pointer parameters of one signature.
///
/// `uint32_t*a1` has no space between the type and the name. A parameter
/// whose type contains `(` is left out: a function-pointer type is not
/// one name this pass can see.
///
/// # Arguments
///
/// * `sig` - The text after `// signature: `.
fn signature_pointers(sig: &str) -> Vec<String> {
    let Some(open) = sig.find('(') else {
        return Vec::new();
    };
    let mut depth = 0i32;
    let mut end = None;
    for (i, c) in sig[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(open + i);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(end) = end else {
        return Vec::new();
    };
    split_params(&sig[open + 1..end])
        .into_iter()
        .filter_map(|param| {
            let param = param.trim();
            if param.is_empty() || param.contains('(') {
                return None;
            }
            let name = trailing_ident(param)?;
            let ty = param[..param.len() - name.len()].trim();
            (ty.contains('*') || name == "this").then(|| name.to_owned())
        })
        .collect()
}

/// Splits a parameter list on commas that are not inside `<` or `(`.
///
/// # Arguments
///
/// * `params` - The text between the signature's parentheses.
fn split_params(params: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in params.char_indices() {
        match c {
            '<' | '(' => depth += 1,
            '>' | ')' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&params[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&params[start..]);
    out
}

/// The identifier a text ends with, when it ends with one.
///
/// # Arguments
///
/// * `text` - A parameter or the text before a compare.
fn trailing_ident(text: &str) -> Option<&str> {
    let bytes = text.as_bytes();
    let mut i = bytes.len();
    while i > 0 && is_ident_char(bytes[i - 1] as char) {
        i -= 1;
    }
    let word = text.get(i..)?;
    word.as_bytes()
        .first()
        .is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_')
        .then_some(word)
}

/// Replaces pointer zero tests on one line, leaving strings and comments.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C.
/// * `names` - Pointer names declared in the function.
fn rewrite_nullptr(line: &str, names: &BTreeSet<String>) -> String {
    let bytes = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut i = 0;
    let mut quote = false;
    let mut escaped = false;
    while i < bytes.len() {
        let c = bytes[i];
        if quote {
            out.push(c as char);
            if escaped {
                escaped = false;
            } else if c == b'\\' {
                escaped = true;
            } else if c == b'"' {
                quote = false;
            }
            i += 1;
            continue;
        }
        if c == b'"' {
            quote = true;
            out.push('"');
            i += 1;
            continue;
        }
        if c == b'/' && bytes.get(i + 1) == Some(&b'/') {
            out.push_str(line.get(i..).unwrap_or(""));
            break;
        }
        if c == b'/' && bytes.get(i + 1) == Some(&b'*') {
            let rest = line.get(i + 2..).unwrap_or("");
            let Some(end) = rest.find("*/") else {
                out.push_str(line.get(i..).unwrap_or(""));
                break;
            };
            let stop = i + 2 + end + 2;
            out.push_str(line.get(i..stop).unwrap_or(""));
            i = stop;
            continue;
        }
        if let Some(span) = null_compare(line, i, names) {
            out.push_str("nullptr");
            i = span;
            continue;
        }
        out.push(c as char);
        i += 1;
    }
    out
}

/// When `at` is the `0` of a pointer's `== 0` or `!= 0`, the index just
/// past that `0`.
///
/// The `0` is replaced. The operator stays where it is, on either side.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Index of a candidate `0`.
/// * `names` - Pointer names.
fn null_compare(line: &str, at: usize, names: &BTreeSet<String>) -> Option<usize> {
    let bytes = line.as_bytes();
    if bytes.get(at) != Some(&b'0') {
        return None;
    }
    if at > 0 && is_ident_char(bytes[at - 1] as char) {
        return None;
    }
    if bytes.get(at + 1).is_some_and(|c| is_ident_char(*c as char)) {
        return None;
    }
    let before = line.get(..at)?;
    let after = line.get(at + 1..)?;
    if zero_on_the_right(before, names) || zero_on_the_left(before, after, names) {
        return Some(at + 1);
    }
    None
}

/// Tells whether `before` ends with `operand ==` or `operand !=` and that
/// operand is a pointer.
///
/// # Arguments
///
/// * `before` - The line up to the `0`.
/// * `names` - Pointer names.
fn zero_on_the_right(before: &str, names: &BTreeSet<String>) -> bool {
    let trimmed = before.trim_end();
    let Some(head) = trimmed
        .strip_suffix("==")
        .or_else(|| trimmed.strip_suffix("!="))
    else {
        return false;
    };
    trailing_operand(head).is_some_and(|operand| operand_is_pointer(operand, names))
}

/// Tells whether `after` begins with `== operand` or `!= operand` and that
/// operand is a pointer, and the `0` itself is the whole left side.
///
/// # Arguments
///
/// * `before` - The line up to the `0`.
/// * `after` - The line after the `0`.
/// * `names` - Pointer names.
fn zero_on_the_left(before: &str, after: &str, names: &BTreeSet<String>) -> bool {
    if !operand_is_whole(before) {
        return false;
    }
    let rest = after.trim_start();
    let Some(rel) = rest.strip_prefix("==").or_else(|| rest.strip_prefix("!=")) else {
        return false;
    };
    let right = rel.trim_start();
    leading_operand(right).is_some_and(|operand| operand_is_pointer(operand, names))
}

/// The operand that `text` ends with, when a boundary stands before it.
///
/// # Arguments
///
/// * `text` - The line up to `==` or `!=`.
fn trailing_operand(text: &str) -> Option<&str> {
    let t = text.trim_end();
    if let Some(name) = trailing_ident(t) {
        let start = t.len() - name.len();
        if operand_is_whole(t.get(..start).unwrap_or("")) {
            return Some(name);
        }
    }
    let mut from = 0;
    while let Some(rel) = t.get(from..).and_then(|s| s.find("*(")) {
        let at = from + rel;
        if operand_is_whole(t.get(..at).unwrap_or(""))
            && let Some(load) = leading_load(t.get(at..).unwrap_or(""))
            && load.len() == t.len() - at
        {
            return t.get(at..);
        }
        from = at + 2;
    }
    None
}

/// Tells whether `left` is exactly one pointer operand.
///
/// A sum, a cast to an integer, and a field stay what they are: the
/// operand has to be a declared pointer name or a load of a pointer.
///
/// # Arguments
///
/// * `left` - The text before the operator, operator excluded.
/// * `names` - Pointer names.
fn operand_is_pointer(left: &str, names: &BTreeSet<String>) -> bool {
    let left = left.trim();
    if is_ident(left) {
        return names.contains(left);
    }
    leading_load(left).is_some_and(|load| load.len() == left.len())
}

/// Tells whether the `(` at the start closes on the last character.
///
/// # Arguments
///
/// * `text` - A candidate address.
fn paren_spans(text: &str) -> bool {
    let mut depth = 0i32;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return i + 1 == text.len();
                }
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    false
}

/// The operand at the start of `text`: a name, or a load of a pointer.
///
/// # Arguments
///
/// * `text` - The text after `==` or `!=`.
fn leading_operand(text: &str) -> Option<&str> {
    if let Some(load) = leading_load(text) {
        return Some(load);
    }
    let n = ident_len(text);
    let name = text.get(..n)?;
    (is_ident(name) && boundary_after(text.get(n..).unwrap_or(""))).then_some(name)
}

/// A `*(type*)address` at the start of `text` whose type is a pointer.
///
/// # Arguments
///
/// * `text` - A candidate load.
fn leading_load(text: &str) -> Option<&str> {
    if !text.starts_with("*(") {
        return None;
    }
    let rest = text.get(2..)?;
    let close = rest.find("*)")?;
    let ty = rest.get(..close)?.trim();
    if !ty.ends_with('*') || ty.contains('(') {
        return None;
    }
    let after = rest.get(close + 2..)?;
    let addr_len = if after.starts_with('(') {
        take_paren(after)?.len()
    } else {
        let n = ident_len(after);
        let name = after.get(..n)?;
        if !is_ident(name) {
            return None;
        }
        n
    };
    text.get(..2 + close + 2 + addr_len)
}

/// How many bytes of identifier `text` starts with.
///
/// # Arguments
///
/// * `text` - The text after an operator.
fn ident_len(text: &str) -> usize {
    text.chars()
        .take_while(|c| is_ident_char(*c))
        .map(char::len_utf8)
        .sum()
}

/// A parenthesized span at the start of `text`.
///
/// # Arguments
///
/// * `text` - Text starting with `(`.
fn take_paren(text: &str) -> Option<&str> {
    if !paren_spans(text) {
        let mut depth = 0i32;
        for (i, c) in text.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return text.get(..=i);
                    }
                }
                _ => {}
            }
        }
        return None;
    }
    Some(text)
}

/// Tells whether what follows an operand does not continue it.
///
/// `->`, `.` and `::` are the same value's field or scope, not a new
/// operand, so `0 == a1->head` is the field.
///
/// # Arguments
///
/// * `after` - The text after a candidate operand.
fn boundary_after(after: &str) -> bool {
    let after = after.trim_start();
    !(after.starts_with("->")
        || after.starts_with('.')
        || after.starts_with("::")
        || after.starts_with(|c: char| is_ident_char(c)))
}

/// Tells whether `text` ends at an operand boundary.
///
/// # Arguments
///
/// * `text` - The line up to a candidate operand.
fn operand_is_whole(text: &str) -> bool {
    let t = text.trim_end();
    if t.is_empty() {
        return true;
    }
    if t.ends_with(['(', ',', ';', '{', '?', ':']) {
        return true;
    }
    if t.ends_with("&&") || t.ends_with("||") {
        return true;
    }
    if t.ends_with('=') && !t.ends_with("==") && !t.ends_with("<=") && !t.ends_with(">=") {
        let compound = ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="];
        return !compound.iter().any(|op| t.ends_with(op));
    }
    trailing_ident(t).is_some_and(|w| matches!(w, "return" | "if" | "while" | "for" | "case"))
}
