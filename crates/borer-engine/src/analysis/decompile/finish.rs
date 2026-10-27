//! Final text passes: `x ?: y`, temporary names, float returns, and the source
//! file a function cites.

use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::analysis::Analysis;
use crate::num::from_usize;
use crate::program::Program;

mod callee;
mod callfmt;
mod selects;

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
    polish_skipping(text, bitness, packs, Passes::NONE, None)
}

/// [`polish_skipping`] with the caller literals and the callees of `entry`
/// in scope.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `skip` - The passes left out ([`Passes`]).
/// * `program` - The loaded image, for its bitness.
/// * `analysis` - Discovery results, holding the packs in force.
/// * `overlay` - The names in force, which the callees' texts are built
///   under.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The polished text.
pub(super) fn polish_at(
    text: &str,
    skip: Passes,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> String {
    polish_skipping(
        text,
        program.arch.bitness().unwrap_or(64),
        &analysis.packs,
        skip,
        Some((program, analysis, overlay, entry)),
    )
}

/// [`polish`] with some of its passes left out.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `bitness` - Decoder bitness of the program (32 or 64).
/// * `packs` - The packs in force.
/// * `skip` - The passes left out ([`Passes`]).
/// * `callers` - The image, the analysis, the names in force and the
///   function, so a `gettext` of a parameter can take its type from the
///   literals the callers pass, and a parameter passed whole to another
///   function the type that function's text gives it ([`callee::noted`]).
///   `None` leaves that evidence out.
///
/// # Returns
///
/// The polished text.
pub(super) fn polish_skipping(
    text: &str,
    bitness: u32,
    packs: &crate::pack::Packs,
    skip: Passes,
    callers: Option<callee::Scope<'_>>,
) -> String {
    let streams = packs.list("types", "stream");
    let word = word_type(bitness);
    let text = skip.apply(Pass::SplitReturns, text.to_owned(), split_returns);
    let text = skip.apply(Pass::NameOwnFields, text, name_own_fields);
    let text = skip.apply(Pass::SourceFile, text, source_file);
    let text = skip.apply(Pass::WireFormat, text, |t| wire_format(t, &streams));
    let text = skip.apply(Pass::SplitWebs, text, vars::split_webs);
    let text = skip.apply(Pass::ApplyLayouts, text, apply_layouts);
    let text = skip.apply(Pass::FloatLanes, text, float_lanes);
    let text = skip.apply(Pass::LaneLocals, text, lane_locals);
    let text = skip.apply(Pass::CalleeTypes, text, |t| callee::noted(t, word, callers));
    let text = skip.apply(Pass::TypeParameters, text, |t| {
        let callers = callers.map(|(program, analysis, _, entry)| (program, analysis, entry));
        type_parameters(&callfmt::noted(t, callers), word)
    });
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
    let text = skip.apply(Pass::SelectStatements, text, selects::select_statements);
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

/// Finishes a body for the tools.
///
/// The steps are [`polish`], then the tables it reads inline ([`super::tables::inline_tables`]),
/// then the translation-unit closure ([`super::unit::close`]), then its
/// vector declarations ([`super::vector::declare`]) and its helper
/// definitions ([`super::helper::declare`]), each step timed
/// ([`crate::timing::Step`]), and last the structs and tables it names
/// ([`super::defs::declare`]), each left out when the overlay's [`Passes`]
/// say so.
///
/// # Arguments
///
/// * `text` - The plain or named decompilation.
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, for the packs and the callees.
/// * `overlay` - User names, and the passes left out.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The text the tools show.
pub(super) fn finished(
    text: &str,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> String {
    use crate::timing::{Step, timed};
    let skip = overlay.passes;
    let text = timed(Step::Polish, || {
        polish_at(text, skip, program, analysis, overlay, entry)
    });
    let text = timed(Step::InlineTables, || {
        skip.apply(Pass::InlineTables, text, |t| {
            tables::inline_tables(t, program)
        })
    });
    let text = timed(Step::UnitClosure, || {
        skip.apply(Pass::UnitClosure, text, |t| {
            unit::close(t, program, analysis, overlay, entry)
        })
    });
    let text = timed(Step::Vectors, || {
        skip.apply(Pass::VectorDeclare, text, |t| vector::declare(t, program))
    });
    let text = timed(Step::Helpers, || {
        skip.apply(Pass::HelperDeclare, text, |t| helper::declare(t, program))
    });
    skip.apply(Pass::TypeDeclare, text, |t| defs::declare(t, program))
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

/// Longest run of plain statements between an `if` chain and the `return`
/// [`split_returns`] copies into its arms.
const SPLIT_TAIL_MAX: usize = 3;

/// Gives each arm of an `if` chain that ends by setting the value a
/// `return v;` after the chain hands back its own copy of that `return`.
///
/// A compiler merges the `return` statements of a function into one exit
/// block, each site setting the result register and jumping there, so
/// `if (c) { ...; v = 1; } else { ...; v = 0; } return v;` is the text of
/// `if (c) { ...; return 1; } ...; return 0;`. Every arm that falls out
/// of the chain must end in an assignment to `v`, a register's or
/// temporary's name (a frame slot or a global is a source variable the
/// `return` reads, which stays shared); an arm that leaves (a `return`,
/// `goto`, `break` or `continue`) keeps its text. The copy is the
/// `return` and the at most [`SPLIT_TAIL_MAX`] plain statements, none of
/// them a call, between the chain and it, so the text runs exactly as
/// before. A final `else` that falls out loses its braces instead: its
/// statements follow the chain and run on into the tail, as the source's
/// last `return` did.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The text with the merged returns split.
pub(super) fn split_returns(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut changed = false;
    let mut r = lines.len();
    while r > 0 {
        r -= 1;
        if let Some(at) = split_return_at(&mut lines, r) {
            changed = true;
            r = at.min(lines.len());
        }
    }
    if !changed {
        return text.to_owned();
    }
    merge_return_assignments(&mut lines);
    rejoin(&lines, text)
}

/// Splits the merged `return` on line `r` into the arms of the `if` chain
/// before it ([`split_returns`]).
///
/// # Arguments
///
/// * `lines` - The function's lines, rewritten in place.
/// * `r` - The line of a `return v;`.
///
/// # Returns
///
/// The chain's first line when the `return` was split, else `None`.
fn split_return_at(lines: &mut Vec<String>, r: usize) -> Option<usize> {
    let ret = lines.get(r)?;
    let v = ret.trim().strip_prefix("return ")?.strip_suffix(';')?;
    if !is_plain_var(v) || v.starts_with("local_") || is_global_name(v) {
        return None;
    }
    let ind = indent_of(ret);
    let mut close = r.checked_sub(1)?;
    while lines[close].trim() != "}" {
        let t = lines[close].trim();
        if indent_of(&lines[close]) != ind
            || r - close > SPLIT_TAIL_MAX
            || !t.ends_with(';')
            || transfers(t)
            || impure(t)
            || t.contains('{')
            || t.contains('}')
            || is_case(t)
        {
            return None;
        }
        close = close.checked_sub(1)?;
    }
    if indent_of(&lines[close]) != ind {
        return None;
    }
    let mut arms: Vec<usize> = vec![close];
    let mut open = close;
    let final_else = loop {
        open = open.checked_sub(1)?;
        let l = &lines[open];
        if l.trim().is_empty() || indent_of(l) > ind {
            continue;
        }
        let t = l.trim();
        if indent_of(l) < ind {
            return None;
        }
        if t.starts_with("if (") && t.ends_with(") {") {
            break arms.len() > 1 && lines[arms[1]].trim() == "} else {";
        }
        if t != "} else {" && !(t.starts_with("} else if (") && t.ends_with(") {")) {
            return None;
        }
        arms.push(open);
    };
    let ends: Vec<Option<usize>> = arms
        .iter()
        .map(|&end| {
            (open + 1..end)
                .rev()
                .find(|&k| !lines[k].trim().is_empty())
                .filter(|&k| indent_of(&lines[k]) == ind + 2)
        })
        .collect();
    let mut into: Vec<usize> = Vec::new();
    for (&end, last) in arms.iter().zip(&ends) {
        let last = (*last).filter(|&k| k > open)?;
        let t = lines[last].trim();
        if transfers(t) {
            continue;
        }
        if plain_assignment(t).is_none_or(|(lhs, _)| lhs != v) {
            return None;
        }
        into.push(end);
    }
    if into.is_empty() {
        return None;
    }
    let tail: Vec<String> = lines[close + 1..=r]
        .iter()
        .map(|l| format!("  {l}"))
        .collect();
    if final_else && into.first() == Some(&close) {
        let other = arms[1];
        for l in &mut lines[other + 1..close] {
            if let Some(rest) = l.strip_prefix("  ") {
                *l = rest.to_owned();
            }
        }
        lines.remove(close);
        lines[other] = format!("{}}}", " ".repeat(ind));
        into.remove(0);
    }
    for end in into {
        lines.splice(end..end, tail.iter().cloned());
    }
    Some(open)
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
