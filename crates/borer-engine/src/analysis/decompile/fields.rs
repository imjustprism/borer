//! Field names and layouts: members named by asserts and setters, by types
//! the user applied to globals, and `this` rendered through them.

use super::*;

/// Names the fields a function's own assertions name.
///
/// A guarded assertion carries both halves of a field name inside one
/// function: `if (*(uint32_t*)(this + 8) == 0) { n_assert("0 != this->elements",
/// "util/array.h", ...); }` says the field at 8 is called `elements`.
/// [`decompile_named`] needs the object's class to look a name up, and most
/// functions have no name to take a class from; a function that asserts
/// about itself needs none, so those offsets are named anyway. Runs before
/// the layout pass, so a named offset leaves the `// layout` line the way a
/// class-named one does. An assertion naming a method rather than a member
/// says what reads the field, not what it is called, and is ignored; so is
/// an offset two assertions disagree about.
///
/// # Arguments
///
/// * `text` - A decompiled function, before layouts.
///
/// # Returns
///
/// The text with those offsets renamed.
pub(super) fn name_own_fields(text: &str) -> String {
    let names = own_field_names(text);
    if names.is_empty() {
        return text.to_owned();
    }
    let mut out: Vec<String> = text.lines().map(str::to_owned).collect();
    for (var, fields) in &names {
        for line in &mut out {
            if line.starts_with("//") {
                continue;
            }
            if let Some(zero) = fields.get(&0) {
                *line = rename_zero_field(line, var, zero);
            }
            *line = rename_fields(line, var, fields);
        }
    }
    let mut joined = out.join("\n");
    joined.push('\n');
    joined
}

/// Reads the field names a function's guarded assertions give, by object.
///
/// # Arguments
///
/// * `text` - A decompiled function, before layouts.
///
/// # Returns
///
/// Object name to offset to member name, holding only the offsets exactly
/// one member name was seen for.
pub(super) fn own_field_names(text: &str) -> BTreeMap<String, BTreeMap<u64, String>> {
    let lines: Vec<&str> = text.lines().collect();
    let mut seen: BTreeMap<(String, u64), Option<String>> = BTreeMap::new();
    for (i, line) in lines.iter().enumerate() {
        let Some(member) = asserted_member(line) else {
            continue;
        };
        let Some((base, off)) = guarding_field(&lines, i) else {
            continue;
        };
        seen.entry((base.to_owned(), off))
            .and_modify(|e| {
                if e.as_deref() != Some(member) {
                    *e = None;
                }
            })
            .or_insert_with(|| Some(member.to_owned()));
    }
    let mut out: BTreeMap<String, BTreeMap<u64, String>> = BTreeMap::new();
    for ((base, off), name) in seen {
        if let Some(n) = name {
            out.entry(base).or_default().insert(off, n);
        }
    }
    out
}

/// Reads the field the guard around an assertion tests.
///
/// The assertion is not always the line after its guard: a caller that
/// spells the signature out first puts `local_8 = __FUNCSIG__(...)` between
/// them. The guard is the nearest line above that opens a block at a
/// smaller indent, with nothing but plain statements in between, and it is
/// only a guard when it dereferences exactly one field.
///
/// # Arguments
///
/// * `lines` - The function's lines.
/// * `at` - Index of the line making the assertion.
///
/// # Returns
///
/// The object and the offset the guard tests, or `None`.
pub(super) fn guarding_field<'a>(lines: &[&'a str], at: usize) -> Option<(&'a str, u64)> {
    /// Longest run of plain statements between a guard and its assertion.
    const GUARD_GAP_MAX: usize = 3;
    let ind = lines.get(at).map_or(0, |l| indent_of(l));
    for j in (at.saturating_sub(GUARD_GAP_MAX)..at).rev() {
        let line = lines.get(j)?;
        let t = line.trim();
        if if_opener(t).is_some() && indent_of(line) < ind {
            let mut fields = field_accesses(t);
            fields.dedup();
            let [(base, off, _)] = fields[..] else {
                return None;
            };
            return u64::try_from(off).ok().map(|off| (base, off));
        }
        if t.contains('{') || t.contains('}') || t.is_empty() || t.ends_with(':') {
            return None;
        }
    }
    None
}

/// Reads the one member of `this` an assertion on this line names.
///
/// # Arguments
///
/// * `line` - One emitted line.
///
/// # Returns
///
/// The member name, or `None` when the line asserts nothing, names a method
/// rather than a member, or names more than one member.
pub(super) fn asserted_member(line: &str) -> Option<&str> {
    let (_, rest) = line.split_once('"')?;
    let (cond, _) = rest.split_once('"')?;
    let mut found = None;
    for (at, _) in cond.match_indices("this->") {
        let tail = cond.get(at + 6..)?;
        let end = tail.find(|c: char| !is_ident_char(c)).unwrap_or(tail.len());
        let name = tail.get(..end)?;
        if name.is_empty() || tail.get(end..).is_some_and(|t| t.starts_with('(')) {
            return None;
        }
        if found.is_some_and(|f| f != name) {
            return None;
        }
        found = Some(name);
    }
    found
}

/// Fewest field-style accesses through one pointer that earn it a layout.
pub(super) const LAYOUT_MIN: usize = 3;

/// Consecutive same-width offsets from this many on are an array, not
/// fields, and stay as they were.
pub(super) const LAYOUT_RUN: usize = 8;

/// Longest layout header line; longer layouts continue on `//  ` lines.
pub(super) const LAYOUT_WIDTH: usize = 100;

/// Drops the runs of [`LAYOUT_RUN`] or more consecutive same-width offsets
/// from a layout.
///
/// # Arguments
///
/// * `fields` - Offset to type letter, edited in place.
pub(super) fn drop_array_runs(fields: &mut BTreeMap<i64, &'static str>) {
    let entries: Vec<(i64, &'static str)> = fields.iter().map(|(o, l)| (*o, *l)).collect();
    let width = |letter: &str| {
        letter
            .get(1..)
            .and_then(|w| w.parse::<i64>().ok())
            .unwrap_or(0)
            / 8
    };
    let mut run: Vec<i64> = Vec::new();
    let mut drop: Vec<i64> = Vec::new();
    for (k, (off, letter)) in entries.iter().enumerate() {
        let continues = k > 0
            && entries[k - 1].1 == *letter
            && width(letter) > 0
            && entries[k - 1].0 + width(letter) == *off;
        if !continues {
            if run.len() >= LAYOUT_RUN {
                drop.extend(&run);
            }
            run.clear();
        }
        run.push(*off);
    }
    if run.len() >= LAYOUT_RUN {
        drop.extend(&run);
    }
    for off in drop {
        fields.remove(&off);
    }
}

/// The type letter of a load or store cast, for a layout header.
///
/// # Arguments
///
/// * `ty` - The C type name inside `*(T*)`.
pub(super) fn layout_type(ty: &str) -> Option<&'static str> {
    Some(match ty {
        "uint8_t" => "u8",
        "uint16_t" => "u16",
        "uint32_t" => "u32",
        "uint64_t" => "u64",
        "uint128_t" => "u128",
        "int8_t" => "i8",
        "int16_t" => "i16",
        "int32_t" => "i32",
        "int64_t" => "i64",
        "float" => "f32",
        "double" => "f64",
        _ => return None,
    })
}

/// The field-style accesses in one line: `(base, offset, type letter)` for
/// every `*(T*)(base + off)`, `*(T*)(off + base)`, `*(T*)(base - off)` and
/// `*(T*)base`.
///
/// A pointer into the middle of a struct reads the members before it at
/// `base - off`, and those keep their negative offset.
///
/// # Arguments
///
/// * `line` - The line.
pub(super) fn field_accesses(line: &str) -> Vec<(&str, i64, &'static str)> {
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(i) = line.get(from..).and_then(|t| t.find("*(")) {
        let at = from + i;
        from = at + 2;
        let Some(rest) = line.get(at + 2..) else {
            break;
        };
        let Some(close) = rest.find("*)") else {
            continue;
        };
        let Some(letter) = rest.get(..close).and_then(layout_type) else {
            continue;
        };
        let Some(operand) = rest.get(close + 2..) else {
            continue;
        };
        if let Some(inner) = operand.strip_prefix('(') {
            let Some(end) = inner.find(')') else {
                continue;
            };
            let Some(operand) = inner.get(..end) else {
                continue;
            };
            let below = operand.split_once(" - ").and_then(|(l, r)| {
                let off = i64::try_from(parse_const(r)?).ok()?;
                Some((l, off.checked_neg()?))
            });
            let above = || {
                let (l, r) = operand.split_once(" + ")?;
                let (base, off) = match (number(l), number(r)) {
                    (None, Some((off, _))) => (l, off),
                    (Some((off, _)), None) => (r, off),
                    _ => return None,
                };
                Some((base, i64::try_from(off).ok()?))
            };
            let Some((base, off)) = below.or_else(above) else {
                continue;
            };
            if is_ident(base) {
                out.push((base, off, letter));
            }
        } else {
            let end = operand
                .find(|c: char| !is_ident_char(c))
                .unwrap_or(operand.len());
            let base = operand.get(..end).unwrap_or("");
            let after = operand.get(end..).unwrap_or("");
            if !base.is_empty()
                && !base.starts_with(|c: char| c.is_ascii_digit())
                && !after.starts_with("->")
            {
                out.push((base, 0, letter));
            }
        }
    }
    out
}

/// Lists the bases a line reads a named member through.
///
/// `this->size` counts toward `this`'s layout the way `*(uint32_t*)(this +
/// 8)` does; `this->Update()` is a call, not a field, and does not.
///
/// # Arguments
///
/// * `line` - One emitted line.
///
/// # Returns
///
/// Each base, once per member access on the line.
pub(super) fn named_members(line: &str) -> Vec<&str> {
    let mut out = Vec::new();
    for (at, _) in line.match_indices("->") {
        let Some(tail) = line.get(at + 2..) else {
            break;
        };
        let end = tail.find(|c: char| !is_ident_char(c)).unwrap_or(tail.len());
        if end == 0 || tail.get(end..).is_some_and(|t| t.starts_with('(')) {
            continue;
        }
        let head = line.get(..at).unwrap_or("");
        let start = head.rfind(|c: char| !is_ident_char(c)).map_or(0, |i| {
            i + head[i..].chars().next().map_or(0, char::len_utf8)
        });
        let base = head.get(start..).unwrap_or("");
        if !base.is_empty() && !base.starts_with(|c: char| c.is_ascii_digit()) {
            out.push(base);
        }
    }
    out
}

/// Fewest call sites before a parameter's constants are worth listing.
///
/// One caller says what one caller does; several agreeing on a small set of
/// values is the parameter's domain.
pub(super) const PARAM_VALUE_SITES: usize = 2;

/// Renders the constants callers pass, as `a2 = 0, 1, 2` per parameter.
///
/// "What is this parameter ever called with" otherwise takes a script over
/// every call site; the walk already passes every call, so the values come
/// out of it for nothing. A parameter with one
/// value is as useful as one with six: it says every caller agrees, which
/// is why a parameter one site leaves unknown, and a function some caller
/// reaches through a pointer, has none ([`Analysis::param_values`]).
///
/// # Arguments
///
/// * `analysis` - Holds the values the walk collected.
/// * `entry` - The function's entry address.
/// * `count` - How many parameters the signature declares.
///
/// # Returns
///
/// The header text, or `None` when nothing was collected for a declared
/// parameter.
pub(super) fn passed_values(analysis: &Analysis, entry: u64, count: usize) -> Option<String> {
    let slots = analysis.param_values.get(&entry)?;
    let mut parts: Vec<String> = Vec::new();
    for (slot, values) in slots {
        if usize::from(*slot) >= count || values.is_empty() {
            continue;
        }
        let shown: Vec<String> = values.iter().map(|v| const_text(*v)).collect();
        parts.push(format!("a{} = {}", u32::from(*slot) + 1, shown.join(", ")));
    }
    (!parts.is_empty()).then(|| parts.join("; "))
}

/// The spelling of a constant in a header: decimal under ten, else hex.
///
/// # Arguments
///
/// * `v` - The value.
pub(super) fn const_text(v: u64) -> String {
    if v < 10 {
        v.to_string()
    } else if v > u64::from(u32::MAX) {
        format!("{:#x}", v.cast_signed())
    } else {
        format!("{v:#x}")
    }
}

/// The spelling of an offset in emitted text: decimal under ten, else hex.
///
/// # Arguments
///
/// * `off` - The offset.
pub(super) fn offset_text(off: u64) -> String {
    if off >= 10 {
        format!("{off:#x}")
    } else {
        off.to_string()
    }
}

/// Names the fields of every pointer a function reads through often enough,
/// and heads the body with each pointer's layout.
///
/// A base (a parameter, `this`, a local or a register) that is assigned at
/// most once and accessed at [`LAYOUT_MIN`] constant offsets or more gets a
/// `// layout base: 0x18 u32, 0x20 u64` line (wrapped at [`LAYOUT_WIDTH`]
/// columns onto `//  ` lines), and each of those accesses
/// renders as `base->field_0x18`; a bare `base + 0x18` becomes
/// `&base->field_0x18`. A pointer into the middle of a struct reads the
/// members before it at `base - 0x40`: those list at `-0x40` and render as
/// `base->field_neg0x40`. A field an earlier pass already named counts
/// toward that total, so naming two of a base's three fields does not cost
/// the third the offset it would otherwise have had. An offset accessed at two widths stays as it was
/// (a signed and an unsigned read of one width count as the signed one),
/// and so does one read both as an integer and as a float: a `double`
/// copied out of a `uint64_t` field would convert the value where the
/// machine moves the bits,
/// as do the segment bases and runs of consecutive same-width offsets long
/// enough to be an array ([`drop_array_runs`]).
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
///
/// # Returns
///
/// The text with layouts applied.
pub(super) fn apply_layouts(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut seen: BTreeMap<&str, BTreeMap<i64, BTreeSet<&str>>> = BTreeMap::new();
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut assigned: BTreeMap<&str, usize> = BTreeMap::new();
    for line in &lines {
        if !line.starts_with("//") {
            for base in named_members(line) {
                *counts.entry(base).or_default() += 1;
            }
        }
        for (base, off, letter) in field_accesses(line) {
            seen.entry(base)
                .or_default()
                .entry(off)
                .or_default()
                .insert(letter);
            *counts.entry(base).or_default() += 1;
        }
        note_assigned_line(line.trim_start(), &mut assigned);
    }
    let mut headers: Vec<String> = Vec::new();
    let mut renames = Vec::new();
    for (base, offsets) in &seen {
        if counts.get(base).copied().unwrap_or(0) < LAYOUT_MIN
            || assigned.get(base).copied().unwrap_or(0) > 1
            || matches!(*base, "gs" | "fs")
        {
            continue;
        }
        let mut fields: BTreeMap<i64, &str> = BTreeMap::new();
        for (off, letters) in offsets {
            let letter = match letters.iter().copied().collect::<Vec<_>>().as_slice() {
                [one] => *one,
                [a, b]
                    if a.get(1..) == b.get(1..)
                        && [a, b].iter().all(|l| l.starts_with(['i', 'u'])) =>
                {
                    if a.starts_with('i') { *a } else { *b }
                }
                _ => continue,
            };
            fields.insert(*off, letter);
        }
        drop_array_runs(&mut fields);
        if fields.is_empty() {
            continue;
        }
        let mut header = format!("// layout {base}:");
        for (k, (o, l)) in fields.iter().enumerate() {
            let item = format!(
                "{}{}{:#x} {l}",
                if k == 0 { " " } else { ", " },
                if *o < 0 { "-" } else { "" },
                o.unsigned_abs()
            );
            if header.len() + item.len() > LAYOUT_WIDTH {
                headers.push(std::mem::replace(&mut header, "//  ".to_owned()));
                header.push_str(item.trim_start_matches(','));
            } else {
                header.push_str(&item);
            }
        }
        headers.push(header);
        let above: BTreeMap<u64, String> = fields
            .keys()
            .filter_map(|o| u64::try_from(*o).ok())
            .map(|o| (o, format!("field_{o:#x}")))
            .collect();
        let below: BTreeMap<u64, String> = fields
            .keys()
            .filter(|o| **o < 0)
            .map(|o| {
                (
                    o.unsigned_abs(),
                    format!("field_neg{:#x}", o.unsigned_abs()),
                )
            })
            .collect();
        renames.push(((*base).to_owned(), above, below));
    }
    if renames.is_empty() {
        return text.to_owned();
    }
    for line in &mut lines {
        for (base, names, below) in &renames {
            if !line.contains(base.as_str()) {
                continue;
            }
            for (off, name) in names {
                let swapped = format!("({} + {base})", offset_text(*off));
                if line.contains(&swapped) {
                    *line = line.replace(&swapped, &format!("({base} + {})", offset_text(*off)));
                }
                if *off == 0 {
                    *line = rename_zero_field(line, base, name);
                }
            }
            *line = rename_fields(line, base, names);
            *line = rename_fields_at(line, base, below, " - ");
        }
    }
    let at = header_len(&lines);
    for (k, h) in headers.into_iter().enumerate() {
        lines.insert(at + k, h);
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Counts assignments to identifiers in one trimmed line, including `for (` headers.
fn note_assigned_line<'a>(t: &'a str, assigned: &mut BTreeMap<&'a str, usize>) {
    if let Some(inner) = t.strip_prefix("for (").and_then(|s| s.strip_suffix(") {")) {
        for part in inner.split("; ") {
            if let Some((lhs, _)) = part.split_once(" = ")
                && is_ident(lhs)
            {
                *assigned.entry(lhs).or_default() += 1;
            }
        }
    }
    if let Some((lhs, _)) = t.split_once(" = ")
        && is_ident(lhs)
    {
        *assigned.entry(lhs).or_default() += 1;
    }
    for op in [
        " += ", " -= ", " |= ", " &= ", " ^= ", " <<= ", " >>= ", " *= ",
    ] {
        if let Some((lhs, _)) = t.split_once(op)
            && is_ident(lhs)
        {
            *assigned.entry(lhs).or_default() += 1;
        }
    }
}

/// Rewrites `*(T*)base` (no offset) in one line as `base->name`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `base` - The pointer.
/// * `name` - The field name at offset zero.
pub(super) fn rename_zero_field(line: &str, base: &str, name: &str) -> String {
    let mut s = line.to_owned();
    let mut from = 0;
    while let Some(i) = s.get(from..).and_then(|t| t.find(base)) {
        let at = from + i;
        from = at + base.len();
        let after = s.get(at + base.len()..).unwrap_or("");
        let before_ok = s.get(..at).is_some_and(|h| h.ends_with("*)"))
            && s.get(..at).and_then(deref_cast_start).is_some();
        if !before_ok || after.starts_with(is_ident_char) || after.starts_with("->") {
            continue;
        }
        let Some(cast) = s.get(..at).and_then(deref_cast_start) else {
            continue;
        };
        let replacement = format!("{base}->{name}");
        s.replace_range(cast..at + base.len(), &replacement);
        from = cast + replacement.len();
    }
    s
}

/// Most class-typed objects whose fields [`decompile_named`] renders by name.
pub(super) const NAMED_OBJECTS_MAX: usize = 4;

/// Rewrites the field accesses of `var` in one line by name.
///
/// `*(T*)(var + off)` becomes `var->name` and a bare `(var + off)` or
/// `var + off,` argument becomes `&var->name`, as does the address a
/// `lea` computes, `x = var + off;`; offsets without a name stay.
/// The offset must be the whole operand: `*(float*)(this + 0x948 +
/// (int32_t)a2 * 0x50)` indexes an array that begins at 0x948, and reading
/// its first term as the field would cut the expression apart.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The object variable (`this` or `a1`).
/// * `names` - Field names by offset.
pub(super) fn rename_fields(line: &str, var: &str, names: &BTreeMap<u64, String>) -> String {
    rename_fields_at(line, var, names, " + ")
}

/// Rewrites the field accesses of `var` on one side of it in one line by
/// name, as [`rename_fields`] does for `var + off`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The object variable.
/// * `names` - Field names by distance from `var`.
/// * `op` - ` + ` for the fields above `var`, ` - ` for those below it.
///
/// # Returns
///
/// The line with those accesses named.
pub(super) fn rename_fields_at(
    line: &str,
    var: &str,
    names: &BTreeMap<u64, String>,
    op: &str,
) -> String {
    if names.is_empty() {
        return line.to_owned();
    }
    let lea = line
        .strip_suffix(';')
        .and_then(|t| t.split_once(" = "))
        .and_then(|(lhs, rhs)| {
            let operand = rhs.strip_prefix(var)?.strip_prefix(op)?;
            let off = parse_const(operand)?;
            Some(format!("{lhs} = &{var}->{};", names.get(&off)?))
        });
    if let Some(named) = lea {
        return named;
    }
    let needle = format!("({var}{op}");
    let mut s = line.to_owned();
    let mut from = 0;
    while let Some(i) = s.get(from..).and_then(|t| t.find(&needle)) {
        let at = from + i;
        let inner = at + needle.len();
        let Some(rest) = s.get(inner..) else {
            break;
        };
        let Some(end) = rest.find([')', ',']) else {
            break;
        };
        let closer = rest.as_bytes().get(end).copied();
        let Some(off) = rest.get(..end).and_then(parse_const) else {
            from = inner;
            continue;
        };
        let Some(name) = names.get(&off) else {
            from = inner;
            continue;
        };
        if closer == Some(b')')
            && let Some(cast) = s.get(..at).and_then(deref_cast_start)
        {
            let replacement = format!("{var}->{name}");
            s.replace_range(cast..inner + end + 1, &replacement);
            from = cast + replacement.len();
        } else {
            let replacement = format!("&{var}->{name}");
            s.replace_range(at + 1..inner + end, &replacement);
            from = at + 1 + replacement.len();
        }
    }
    s
}

/// Returns where the `*(T*)` cast starts when `head` ends with one.
///
/// # Arguments
///
/// * `head` - The text before a `(var + off)` operand.
pub(super) fn deref_cast_start(head: &str) -> Option<usize> {
    let h = head.strip_suffix("*)")?;
    let start = h.rfind("*(")?;
    is_ident(h.get(start + 2..)?).then_some(start)
}

/// The fields a user-typed pointer names.
///
/// Offset to the field's name and the letter of its stated width, the
/// width a load must read for the name to be true. A field of an enum
/// type states the enum's width (4 or 8), since its members are that
/// wide.
pub(super) type TypedFields = BTreeMap<u64, (String, &'static str)>;

/// The user-typed globals of a function: the variable each renders as, with
/// the fields its applied type states and the letter of each field's width.
///
/// A global is user-typed when [`Overlay::applied`] states a type at its
/// address and that type points (through pointers and aliases) at a user
/// struct; the fields that could not render as one access, an embedded
/// struct among them, are left out rather than named at a width they do not
/// have. A field naming an enum is no wider a guess than a scalar: the
/// enum's width is the field's width, so the field names the loads that
/// read it at that width and [`super::enums::apply_user_enums`] names the
/// constants they are compared with. The same global read at two widths
/// renders as two names, each getting the fields.
///
/// # Arguments
///
/// * `overlay` - The user types and applications.
/// * `globals` - The absolute accesses the function hoisted to globals.
/// * `names` - The name resolver, for each global's rendered variable.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// `(variable, fields)` per typed global, by variable name.
pub(super) fn typed_globals(
    overlay: &Overlay,
    globals: &BTreeSet<(u64, Ty)>,
    names: &Names<'_>,
    word: u64,
) -> Vec<(String, TypedFields)> {
    let mut out: BTreeMap<String, TypedFields> = BTreeMap::new();
    for &(addr, ty) in globals {
        let Some(expr) = overlay.applied.get(&addr) else {
            continue;
        };
        let Some(s) = crate::analysis::utypes::pointee_struct(&overlay.types, expr) else {
            continue;
        };
        let fields = struct_fields(&overlay.types, s, word);
        if fields.is_empty() {
            continue;
        }
        out.entry(names.key(Key::Global(addr, ty.bits())))
            .or_insert(fields);
    }
    out.into_iter().collect()
}

/// The fields of a user struct a typed pointer names, by offset, each with
/// the letter of its width; a field that renders as no one access (an
/// embedded struct) is left out.
///
/// # Arguments
///
/// * `types` - The types a field may name, for an enum field's width.
/// * `s` - The struct.
/// * `word` - The image's pointer width in bytes (4 or 8).
pub(super) fn struct_fields(
    types: &BTreeMap<String, crate::analysis::utypes::UserType>,
    s: &crate::analysis::utypes::UserStruct,
    word: u64,
) -> TypedFields {
    let mut fields: TypedFields = BTreeMap::new();
    for (off, f) in &s.fields {
        let letter =
            f.ty.c_name(word)
                .as_deref()
                .and_then(layout_type)
                .or_else(|| {
                    let e = crate::analysis::utypes::named_enum(types, &f.ty)?;
                    match e.size {
                        4 => Some("u32"),
                        8 => Some("u64"),
                        _ => None,
                    }
                });
        let Some(letter) = letter else {
            continue;
        };
        fields.insert(*off, (f.name.clone(), letter));
    }
    fields
}

/// Names the fields of user-typed globals through a whole text
/// ([`typed_globals`]).
///
/// Runs before the layout pass of [`apply_layouts`], so a field the user
/// named suppresses that pointer's `// layout` line the way a class-named
/// one does.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `typed` - The typed globals of [`typed_globals`].
///
/// # Returns
/// The text with the user-typed globals' fields named.
pub(super) fn rename_typed(text: &str, typed: &[(String, TypedFields)]) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    for line in &mut lines {
        if line.starts_with("//") {
            continue;
        }
        for (var, fields) in typed {
            *line = rename_typed_fields(line, var, fields);
        }
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Rewrites the field accesses of one user-typed pointer in one line by
/// name, at the width the field states.
///
/// The same shapes [`rename_fields`] renames, with the load's cast checked
/// against the field's stated width first: `*(uint32_t*)(v + 0x18)` names
/// `v->hp` only when `hp` is a `u32`, and a load the field cannot explain
/// stays as it was, since reading it as the field would state a width the
/// type does not. The address forms have no cast to check.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The typed pointer.
/// * `fields` - The field names by offset, with each field's width letter.
pub(super) fn rename_typed_fields(line: &str, var: &str, fields: &TypedFields) -> String {
    let lea = line
        .strip_suffix(';')
        .and_then(|t| t.split_once(" = "))
        .and_then(|(lhs, rhs)| {
            let operand = rhs.strip_prefix(var)?.strip_prefix(" + ")?;
            let off = parse_const(operand)?;
            Some(format!("{lhs} = &{var}->{};", fields.get(&off)?.0))
        });
    if let Some(named) = lea {
        return named;
    }
    let needle = format!("({var} + ");
    let mut s = line.to_owned();
    let mut from = 0;
    while let Some(i) = s.get(from..).and_then(|t| t.find(&needle)) {
        let at = from + i;
        let inner = at + needle.len();
        let Some(rest) = s.get(inner..) else {
            break;
        };
        let Some(end) = rest.find([')', ',']) else {
            break;
        };
        let closer = rest.as_bytes().get(end).copied();
        let Some(off) = rest.get(..end).and_then(parse_const) else {
            from = inner;
            continue;
        };
        let Some((name, letter)) = fields.get(&off) else {
            from = inner;
            continue;
        };
        if closer == Some(b')')
            && let Some(cast) = s.get(..at).and_then(deref_cast_start)
        {
            let head = s.get(..at).unwrap_or("");
            let stated = head
                .get(cast + 2..)
                .and_then(|t| t.get(..t.len().saturating_sub(2)));
            if stated.and_then(layout_type) != Some(*letter) {
                from = inner;
                continue;
            }
            let replacement = format!("{var}->{name}");
            s.replace_range(cast..inner + end + 1, &replacement);
            from = cast + replacement.len();
        } else {
            let replacement = format!("&{var}->{name}");
            s.replace_range(at + 1..inner + end, &replacement);
            from = at + 1 + replacement.len();
        }
    }
    s
}

/// Advances multiline `/* ... */` block-comment state across `line`, returning
/// the byte offset of the first code token on `line` (`None` when the line holds
/// no code tokens).
///
/// # Arguments
///
/// * `line` - Source line.
/// * `in_comment` - Whether `line` begins inside an unclosed `/*` block comment;
///   updated if `line` closes that comment or opens a new unclosed `/*`.
pub(super) fn step_block_comment(line: &str, in_comment: &mut bool) -> Option<usize> {
    let from = if *in_comment {
        let close = line.find("*/")?;
        *in_comment = false;
        close + 2
    } else {
        0
    };
    let mut first_code = None;
    for (piece, span) in lexer::scan(line, from) {
        match piece {
            lexer::Piece::Space => {}
            lexer::Piece::Comment => {
                let seg = line.get(span).unwrap_or("");
                if seg.starts_with("/*") && !(seg.len() >= 4 && seg.ends_with("*/")) {
                    *in_comment = true;
                }
            }
            lexer::Piece::Token(_) => {
                first_code.get_or_insert(span.start);
            }
        }
    }
    first_code
}

/// Counts direct variable writes (`=`, compound assignments, `++`, `--`) on `line`.
///
/// # Arguments
///
/// * `line` - Code slice of one source line.
/// * `assigned` - Per-identifier write counter.
pub(super) fn note_line_writes<'a>(line: &'a str, assigned: &mut BTreeMap<&'a str, usize>) {
    let ln = lexer::Line {
        text: line,
        toks: lexer::lex(line),
    };
    let mut ctrl_parens: Vec<bool> = Vec::new();
    let mut close_ctrl = false;
    let mut decl_stars = false;
    for (i, tok) in ln.toks.iter().enumerate() {
        if tok.lex != lexer::Lex::Name {
            let w = ln.word(i);
            if tok.lex == lexer::Lex::Punct {
                match w {
                    "(" => ctrl_parens
                        .push(i > 0 && matches!(ln.word(i - 1), "if" | "while" | "for" | "switch")),
                    ")" => close_ctrl = ctrl_parens.pop().unwrap_or(false),
                    _ => {}
                }
            }
            if !(tok.lex == lexer::Lex::Punct && w == "*") {
                decl_stars = false;
            }
            continue;
        }
        let Some(name) = line.get(tok.at..tok.end) else {
            decl_stars = false;
            continue;
        };
        let star_decl = decl_stars;
        decl_stars = !matches!(name, "return" | "else" | "do" | "case" | "sizeof");
        let prev = i.checked_sub(1).map(|j| ln.word(j));
        let next = (i + 1 < ln.toks.len()).then(|| ln.word(i + 1));
        if matches!(prev, Some("." | "->")) {
            decl_stars = false;
            continue;
        }
        let assign_op = matches!(
            next,
            Some("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=")
        );
        let direct_lhs = assign_op
            && match prev {
                None
                | Some(
                    ";" | "{" | "}" | "(" | "," | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&="
                    | "|=" | "^=" | "<<=" | ">>=" | "?" | ":" | "else" | "do",
                ) => true,
                Some(")") => close_ctrl,
                Some("*") => star_decl,
                Some(w) => is_ident(w) && !matches!(w, "case" | "sizeof"),
            };
        let post_step = matches!(next, Some("++" | "--"));
        let pre_step =
            matches!(prev, Some("++" | "--")) && !matches!(next, Some("." | "->" | "[" | "("));
        if direct_lhs || post_step || pre_step {
            let entry = assigned.entry(name).or_default();
            *entry = entry.saturating_add(1);
        }
    }
}

/// Infers single-assigned SDK structure tags `(variable, tag)` from declared
/// API calls across `text`.
///
/// # Arguments
///
/// * `text` - The function's text.
/// * `format` - Binary format selecting platform declarations.
pub(super) fn api_pointee_tags<'a>(
    text: &'a str,
    format: crate::program::BinaryFormat,
) -> BTreeMap<&'a str, &'static str> {
    let mut found: BTreeMap<&'a str, Option<&'static str>> = BTreeMap::new();
    let mut assigned: BTreeMap<&'a str, usize> = BTreeMap::new();
    let mut in_comment = false;
    for line in text.lines() {
        let Some(code_at) = step_block_comment(line, &mut in_comment) else {
            continue;
        };
        let t = line.get(code_at..).unwrap_or("");
        note_line_writes(t, &mut assigned);
        let bytes = t.as_bytes();
        for open in code_open_parens(t) {
            let Some(callee) = callee_before_paren(t, open) else {
                continue;
            };
            let Some(decl) = crate::analysis::typelib::declared(callee, format) else {
                continue;
            };
            let limit = bytes.len().min(open.saturating_add(4097));
            let Some(args) = call_args_at(t, open, limit) else {
                continue;
            };
            for (arg, param) in args.into_iter().zip(&decl.params) {
                if !is_ident(arg) || arg.starts_with(|c: char| c.is_ascii_digit()) {
                    continue;
                }
                let Some(s) = crate::analysis::sdk::pointee(param.ty) else {
                    continue;
                };
                found
                    .entry(arg)
                    .and_modify(|prev| {
                        if *prev != Some(s.tag) {
                            *prev = None;
                        }
                    })
                    .or_insert(Some(s.tag));
            }
        }
    }
    found
        .into_iter()
        .filter_map(|(name, tag)| {
            let tag = tag?;
            crate::analysis::sdk::structure(tag)?;
            (assigned.get(name).copied().unwrap_or(0) <= 1).then_some((name, tag))
        })
        .collect()
}

/// Returns the pointers a function hands to an API as SDK structures, with
/// their fields.
///
/// A name passed whole to a declared API whose parameter points at an SDK
/// structure ([`crate::analysis::sdk::pointee`]) takes that structure:
/// `EnterCriticalSection(a1)` makes `a1` an `LPCRITICAL_SECTION`, so
/// `*(uint32_t*)(a1 + 0xc)` is `a1->RecursionCount`.
///
/// Only a name the text assigns at most once is typed, so a variable that
/// holds two different objects in turn is never read as one; a name two
/// calls type as different structures is left alone.
///
/// # Arguments
///
/// * `text` - The function's body.
/// * `format` - The binary's format, which picks the platform's
///   declarations.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// `(name, fields)` per typed pointer, by name.
pub(super) fn api_typed(
    text: &str,
    format: crate::program::BinaryFormat,
    word: u64,
) -> Vec<(String, TypedFields)> {
    let bits = u8::try_from(word * 8).unwrap_or(64);
    api_pointee_tags(text, format)
        .into_iter()
        .filter_map(|(name, tag)| {
            let s = crate::analysis::sdk::structure(tag)?;
            let fields: TypedFields = s
                .at(word)
                .into_iter()
                .filter_map(|(off, f)| {
                    let pass = crate::analysis::typelib::pass_of(f.ty, bits, format)?;
                    Some((off, (f.name.to_owned(), pass_letter(pass, bits)?)))
                })
                .collect();
            (!fields.is_empty()).then(|| (name.to_owned(), fields))
        })
        .collect()
}

/// The width letter a load of a value passed as `pass` is cast to.
///
/// An integer takes the unsigned letter of its width, as the lifting casts
/// a load whose sign nothing states.
///
/// # Arguments
///
/// * `pass` - What the machine passes the value as.
/// * `word` - The pointer width in bits.
///
/// # Returns
///
/// The letter, or `None` for `void`.
fn pass_letter(pass: crate::analysis::typelib::Pass, word: u8) -> Option<&'static str> {
    use crate::analysis::typelib::Pass;
    let bits = match pass {
        Pass::Void => return None,
        Pass::Float(32) => return Some("f32"),
        Pass::Float(_) => return Some("f64"),
        Pass::Int { bits, .. } => bits,
        Pass::Pointer => word,
    };
    Some(match bits {
        8 => "u8",
        16 => "u16",
        32 => "u32",
        _ => "u64",
    })
}

/// Byte offsets of every opening `(` in `line` that is a code punctuation token.
///
/// # Arguments
///
/// * `line` - Source line.
fn code_open_parens(line: &str) -> impl Iterator<Item = usize> + '_ {
    lexer::scan(line, 0).filter_map(move |(piece, span)| {
        (piece == lexer::Piece::Token(lexer::Lex::Punct) && line.get(span.clone()) == Some("("))
            .then_some(span.start)
    })
}

/// Extracts the bare ASCII identifier immediately preceding `(` at `open`.
///
/// # Arguments
///
/// * `line` - Source line.
/// * `open` - Byte index of `(`.
fn callee_before_paren(line: &str, open: usize) -> Option<&str> {
    let prefix = line.get(..open)?;
    let start = prefix
        .char_indices()
        .rev()
        .find_map(|(i, ch)| {
            let cont = ch.is_ascii_alphanumeric()
                || ch == '_'
                || ch == '$'
                || (!ch.is_ascii() && !ch.is_whitespace());
            (!cont).then_some(i + ch.len_utf8())
        })
        .unwrap_or(0);
    line.get(start..open)
        .filter(|c| is_ident(c) && !c.starts_with(|ch: char| ch.is_ascii_digit()))
}

/// Splits arguments inside `(` at `open` up to byte offset `limit`.
///
/// # Arguments
///
/// * `line` - Source line.
/// * `open` - Byte index of `(`.
/// * `limit` - Exclusive upper byte bound to scan.
fn call_args_at(line: &str, open: usize, limit: usize) -> Option<Vec<&str>> {
    let slice = line.as_bytes().get(open + 1..limit)?;
    let (mut depth, mut from, mut args) = (0usize, open + 1, Vec::new());
    for (rel, &b) in slice.iter().enumerate() {
        let i = open + 1 + rel;
        match b {
            b'(' | b'[' => depth += 1,
            b')' | b']' if depth > 0 => depth -= 1,
            b')' => {
                args.extend(line.get(from..i).map(str::trim).filter(|a| !a.is_empty()));
                return Some(args);
            }
            b',' if depth == 0 => {
                args.extend(line.get(from..i).map(str::trim));
                from = i + 1;
            }
            b'"' => return None,
            _ => {}
        }
    }
    None
}

/// The calls by plain name in one line, each with its whole arguments.
///
/// # Arguments
///
/// * `line` - The line.
///
/// # Returns
///
/// `(callee, arguments)` per call, outermost first; an argument is its
/// trimmed text between the commas at the call's own depth.
#[cfg(test)]
fn calls_in(line: &str) -> Vec<(&str, Vec<&str>)> {
    let mut out = Vec::new();
    let limit = line.len();
    for open in code_open_parens(line) {
        let Some(callee) = callee_before_paren(line, open) else {
            continue;
        };
        if let Some(args) = call_args_at(line, open, limit) {
            out.push((callee, args));
        }
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{api_typed, calls_in, rename_typed};
    use crate::program::BinaryFormat;

    /// Multibyte UTF-8 before `(` never slices mid-character or splits off an
    /// ASCII API suffix from a Unicode identifier.
    #[test]
    fn calls_in_handles_multibyte_utf8_before_paren() {
        assert_eq!(calls_in("café(a); f(x);"), vec![("f", vec!["x"])]);
        assert_eq!(
            calls_in("caféEnterCriticalSection(a1); f(x);"),
            vec![("f", vec!["x"])]
        );
        assert_eq!(
            calls_in("cafe\u{301}EnterCriticalSection(a1); f(x);"),
            vec![("f", vec!["x"])]
        );
        let unicode_prefixed = concat!(
            "caféEnterCriticalSection(a1);\n",
            "cafe\u{301}EnterCriticalSection(a1);\n",
            "puts(\"EnterCriticalSection(a1)\"); /* EnterCriticalSection(a1); */\n",
            "/*\nEnterCriticalSection(a1);\n*/\n",
            "v = *(uint32_t*)(a1 + 0x8);\n",
        );
        assert!(api_typed(unicode_prefixed, BinaryFormat::Pe, 8).is_empty());
    }

    /// A call's whole arguments split at its own depth.
    #[test]
    fn calls_split_their_arguments() {
        assert_eq!(
            calls_in("x = f(a1, g(b, c), *(uint32_t*)(a2 + 8));"),
            vec![
                ("f", vec!["a1", "g(b, c)", "*(uint32_t*)(a2 + 8)"]),
                ("g", vec!["b", "c"]),
            ]
        );
    }

    /// A pointer passed whole to an API declaring a structure pointer reads
    /// its fields by the structure's names, at the image's word; one the
    /// text assigns twice stays untyped.
    #[test]
    fn a_pointer_handed_to_an_api_takes_its_structure() {
        let text =
            "EnterCriticalSection(a1);\nv = *(uint32_t*)(a1 + 0x8);\nLeaveCriticalSection(a1);\n";
        let typed = api_typed(text, BinaryFormat::Pe, 8);
        assert_eq!(typed.len(), 1);
        let renamed = rename_typed(text, &typed);
        assert!(renamed.contains("v = a1->LockCount;"), "{renamed}");
        let typed32 = api_typed(text.replace("0x8", "0x4").as_str(), BinaryFormat::Pe, 4);
        let renamed32 = rename_typed(&text.replace("0x8", "0x4"), &typed32);
        assert!(renamed32.contains("v = a1->LockCount;"), "{renamed32}");
        let twice = "var1 = f();\nEnterCriticalSection(var1);\nvar1 = g();\n";
        assert!(api_typed(twice, BinaryFormat::Pe, 8).is_empty());
        assert!(api_typed(text, BinaryFormat::Elf, 8).is_empty());
    }

    /// Braceless conditional writes, compound assignments and steps count as
    /// reassignments, while dereference and member stores keep single-assigned
    /// API pointers typed.
    #[test]
    fn inline_reassignments_keep_api_pointers_untyped_while_pointee_stores_do_not() {
        for reassigned in [
            "var1 = f();\nif (ready) var1 = g();\nEnterCriticalSection(var1);\n",
            "var1 = f();\n*var1++;\nEnterCriticalSection(var1);\n",
            "var1 = f();\nx = var1 = g();\nEnterCriticalSection(var1);\n",
            "var1 = f();\nx += var1 = g();\nEnterCriticalSection(var1);\n",
            "var1 = f();\nEnterCriticalSection(var1);\nreturn var1 = g();\n",
        ] {
            assert!(
                api_typed(reassigned, BinaryFormat::Pe, 8).is_empty(),
                "{reassigned}"
            );
        }
        let pointee_store = concat!(
            "var1 = f();\n",
            "*(uint32_t *)var1 = 0;\n",
            "var1->LockCount = 1;\n",
            "EnterCriticalSection(var1);\n",
        );
        assert_eq!(api_typed(pointee_store, BinaryFormat::Pe, 8).len(), 1);
        let hostile = format!(
            "var1 = f();\n{}{}EnterCriticalSection(var1);\n",
            "(".repeat(20_000),
            ")x ".repeat(20_000),
        );
        assert_eq!(api_typed(&hostile, BinaryFormat::Pe, 8).len(), 1);
    }
}
