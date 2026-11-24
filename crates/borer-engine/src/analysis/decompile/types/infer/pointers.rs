//! What the loads and stores through a parameter, or a copy of it, show it
//! points at.

use super::*;

/// Largest offset from a parameter that reads as a field of what it points
/// at; a load at a larger one indexes an absolute address by the parameter.
const FIELD_OFFSET_MAX: u64 = 0x1_0000;

/// The value types a load through an address is cast to, with their widths
/// in bytes.
const LOAD_TYPES: [(&str, usize); 11] = [
    ("uint8_t", 1),
    ("uint16_t", 2),
    ("uint32_t", 4),
    ("uint64_t", 8),
    ("uint128_t", 16),
    ("int8_t", 1),
    ("int16_t", 2),
    ("int32_t", 4),
    ("int64_t", 8),
    ("float", 4),
    ("double", 8),
];

/// The pointer type the body shows a parameter to be, when it loads or
/// stores through it and never assigns it.
///
/// A load or store through the parameter, `*(T*)a2` or `*(T*)(a2 + 0x10)`,
/// an element read `((T*)a2)[i]`, or a field the layout pass named on it,
/// `a2->field_0x10`, uses its value as an address, which only a pointer
/// is. The pointee follows the register scan's rule ([`pointee_type`]):
/// one width at offset zero is a pointer to that width, anything else
/// `void *`. Reading it off the text sees what the register scan cannot: an
/// argument that arrives on the stack, as every 32-bit `cdecl` and
/// `stdcall` one does. An offset past [`FIELD_OFFSET_MAX`] makes the
/// parameter the index of an absolute address, not a pointer, and a
/// parameter the body assigns, or casts to a narrow integer, is left as
/// it is; a cast in front of `a2->field_0x10` casts the field, not `a2`.
/// A load at the parameter plus a narrow integer, `*(T*)(a2 + local_10)`
/// ([`indexed_by_int`]), indexes from it.
/// The loads through a variable the parameter is copied into ([`copies`])
/// count too: at their own offsets when the copy only holds the
/// parameter, and as a walk ([`Witness::SteppedCopy`]) when the copy is
/// indexed, or stepped ([`steps`]) by the width it reads (any step, for
/// bytes) and read where it points or where a step lands (`c = p[1];
/// p += 1;`), so bytes read through it make a byte pointer. A wider copy
/// stepped by another amount, or one read only elsewhere, walks something
/// whose element the text does not show: `void *`.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
///
/// # Returns
///
/// The pointer type, or `None` when nothing in the body shows one.
pub(super) fn pointed_at(lines: &[String], param: &str) -> Option<&'static str> {
    if assigned_values(lines, param) > 0 {
        return None;
    }
    let mut widths: BTreeSet<usize> = BTreeSet::new();
    let mut offsets: BTreeSet<i64> = BTreeSet::new();
    let mut types: BTreeSet<&'static str> = BTreeSet::new();
    let mut walk =
        accesses(lines, param, &mut widths, &mut offsets, &mut types)?.then_some(Witness::Walk);
    let mut unshown = false;
    for copy in copies(lines, param) {
        let (mut own, mut moved) = (BTreeSet::new(), BTreeSet::new());
        let indexed = accesses(lines, &copy, &mut own, &mut moved, &mut types)?;
        widths.extend(own.iter().copied());
        if moved.is_empty() {
            continue;
        }
        let steps = steps(lines, &copy);
        let width = own.iter().copied().next().filter(|_| own.len() == 1);
        let by_width = width == Some(1)
            || steps.iter().all(|s| {
                s.zip(width)
                    .is_some_and(|(k, w)| u64::try_from(w).is_ok_and(|w| w == k))
            });
        let lands = moved.contains(&0)
            || steps
                .iter()
                .flatten()
                .any(|&k| i64::try_from(k).is_ok_and(|k| moved.contains(&k)));
        if indexed || (!steps.is_empty() && by_width && lands) {
            walk = walk.or(Some(Witness::SteppedCopy));
            offsets.insert(0);
        } else if !steps.is_empty() {
            unshown = true;
        }
        offsets.extend(moved);
    }
    if offsets.is_empty() {
        return None;
    }
    if unshown {
        return Some("void *");
    }
    let has_copy = !copies(lines, param).is_empty();
    let ty = if has_copy
        && widths == BTreeSet::from([4])
        && types.contains("float")
        && types.iter().all(|&t| matches!(t, "float" | "uint32_t"))
    {
        "float *"
    } else if has_copy
        && widths == BTreeSet::from([8])
        && types.contains("double")
        && types.iter().all(|&t| matches!(t, "double" | "uint64_t"))
    {
        "double *"
    } else {
        pointee_type(&widths, &offsets, walk)
    };
    Some(ty)
}

/// Collects the widths and offsets of the loads and stores through one
/// name, for [`pointed_at`].
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The name.
/// * `widths` - Access widths in bytes, added to.
/// * `offsets` - Offsets from the name, added to.
/// * `types` - Load cast types, added to.
///
/// # Returns
///
/// Whether some access indexes from the name rather than reading at a
/// constant offset ([`pointee_type`]), or `None` when a use casts the
/// name to a narrow signed integer, which no pointer is.
fn accesses(
    lines: &[String],
    name: &str,
    widths: &mut BTreeSet<usize>,
    offsets: &mut BTreeSet<i64>,
    types: &mut BTreeSet<&'static str>,
) -> Option<bool> {
    let mut walked = false;
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, name) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            if tail.starts_with("->") {
                offsets.extend([0, 1]);
                continue;
            }
            if ["(int8_t)", "(int16_t)", "(int32_t)"]
                .iter()
                .any(|c| head.ends_with(c))
            {
                return None;
            }
            for (ty, width) in LOAD_TYPES {
                let field = head.strip_suffix(&format!("*({ty}*)(")).and_then(|_| {
                    let (sign, rest) = if let Some(r) = tail.strip_prefix(" + ") {
                        (1, r)
                    } else {
                        (-1, tail.strip_prefix(" - ")?)
                    };
                    let k = parse_const(rest.get(..rest.find(')')?)?)?;
                    (k < FIELD_OFFSET_MAX).then(|| sign * i64::try_from(k).unwrap_or(i64::MAX))
                });
                if head.ends_with(&format!("*({ty}*)")) {
                    widths.insert(width);
                    types.insert(ty);
                    offsets.insert(0);
                } else if let Some(k) = field {
                    widths.insert(width);
                    types.insert(ty);
                    offsets.insert(k);
                } else if (head.ends_with(&format!("(({ty}*)")) && tail.starts_with(")["))
                    || (head.ends_with(&format!("*({ty}*)(")) && indexed_by_int(lines, tail))
                    || (head.ends_with(&format!("(({ty}*)(")) && indexed_cast(tail))
                    || commuted_index(lines, head, tail, ty)
                {
                    widths.insert(width);
                    types.insert(ty);
                    offsets.extend([0, 1]);
                    walked = true;
                }
            }
        }
    }
    Some(walked)
}

/// Tells whether `tail` closes a pointer cast over a sum that is then
/// indexed: ` + expr))[i]`.
///
/// # Arguments
///
/// * `tail` - The text after the base name inside `(({ty}*)(`.
fn indexed_cast(tail: &str) -> bool {
    let Some(rest) = tail.strip_prefix(" + ") else {
        return false;
    };
    let mut depth = 1i32;
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return rest.get(i..).is_some_and(|r| r.starts_with("))["));
                }
            }
            _ => {}
        }
    }
    false
}

/// Tells whether a load adds a zero-initialized loop index on the left of
/// the base pointer: `*(T*)(index + base)`.
///
/// # Arguments
///
/// * `lines` - The function, declarations included.
/// * `head` - The text before `base`.
/// * `tail` - The text after `base`.
/// * `ty` - The load's type name.
fn commuted_index(lines: &[String], head: &str, tail: &str, ty: &str) -> bool {
    if !tail.starts_with(')') {
        return false;
    }
    let Some(before) = head.strip_suffix(" + ") else {
        return false;
    };
    let prefix = format!("*({ty}*)(");
    let Some(index) = before
        .rfind(&prefix)
        .and_then(|i| before.get(i + prefix.len()..))
    else {
        return false;
    };
    let index = index.strip_prefix("(int64_t)(int32_t)").unwrap_or(index);
    is_ident(index)
        && !is_param_name(index)
        && declared_scalar(lines, index).is_some()
        && lines.iter().any(|l| {
            let t = l.trim();
            (t.ends_with(" = 0;") && t.split(" = ").any(|lhs| lhs == index))
                || t.starts_with(&format!("for ({index} = 0;"))
        })
}

/// Tells whether the text after a name adds a narrow integer to it.
///
/// ` + local_10)` with `local_10` declared an `int32_t`, or ` +
/// (int64_t)(int32_t)i)`, adds an index no pointer is, so the name is the
/// base of the address.
///
/// # Arguments
///
/// * `lines` - The function, declarations included.
/// * `tail` - The text after the name.
fn indexed_by_int(lines: &[String], tail: &str) -> bool {
    let Some(rest) = tail.strip_prefix(" + ") else {
        return false;
    };
    let index = rest.split(')').next().unwrap_or("");
    rest.starts_with("(int64_t)")
        || (is_ident(index)
            && rest.get(index.len()..).is_some_and(|r| r.starts_with(')'))
            && declared_scalar(lines, index).is_some())
}

/// The variables a parameter is copied into whole and that only step
/// from there: `local_10 = a1;` then `local_10 += 2;`, the home an
/// unoptimized build keeps a parameter in.
///
/// A copy assigned anything else as well holds more than the parameter,
/// so it is left out.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
pub(super) fn copies(lines: &[String], param: &str) -> Vec<String> {
    let whole = format!(" = {param};");
    let mut out: Vec<String> = Vec::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        let Some(lhs) = line.trim().strip_suffix(whole.as_str()) else {
            continue;
        };
        for dest in lhs.split(" = ") {
            if !is_ident(dest) || dest == param || out.iter().any(|c| c == dest) {
                continue;
            }
            let writes = lines
                .iter()
                .filter(|l| {
                    let t = l.trim();
                    t.strip_prefix(dest).is_some_and(|r| r.starts_with(" = "))
                        || t.contains(&format!(" = {dest} = "))
                })
                .count();
            if writes == 1 {
                out.push(dest.to_owned());
            }
        }
    }
    out
}

/// The loop variables a `for` header initializes whole from `param` and
/// that are never assigned outside that `for` header.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
pub(super) fn for_init_copies(lines: &[String], param: &str) -> Vec<String> {
    let suffix = format!(" = {param};");
    let mut out: Vec<String> = Vec::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        let Some(rest) = line.trim().strip_prefix("for (") else {
            continue;
        };
        let Some((dest, _)) = rest.split_once(&suffix) else {
            continue;
        };
        if !is_ident(dest) || dest == param || out.iter().any(|c| c == dest) {
            continue;
        }
        let other_writes = lines
            .iter()
            .filter(|l| {
                let t = l.trim();
                !t.starts_with("for (")
                    && (t.strip_prefix(dest).is_some_and(|r| r.starts_with(" = "))
                        || t.contains(&format!(" = {dest} = ")))
            })
            .count();
        if other_writes == 0 {
            out.push(dest.to_owned());
        }
    }
    out
}

/// Returns the amounts each line steps a copy of a pointer by.
///
/// `p += 4` and `p -= 4` step it by 4, `p++` and `--p` by 1; a step by a
/// value the text does not spell as a constant (`p += n`) is `None`.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `copy` - The copy's name.
///
/// # Returns
///
/// One entry per stepping line, empty when nothing steps the copy.
fn steps(lines: &[String], copy: &str) -> Vec<Option<u64>> {
    let mut out = Vec::new();
    for t in lines
        .iter()
        .filter(|l| !l.starts_with("//"))
        .map(|l| l.trim())
    {
        let after = t.strip_prefix(copy).unwrap_or("");
        if let Some(k) = after
            .strip_prefix(" += ")
            .or_else(|| after.strip_prefix(" -= "))
        {
            out.push(k.strip_suffix(';').and_then(parse_const));
        } else if matches!(after, "++;" | "--;")
            || ["++", "--"]
                .iter()
                .any(|op| t.strip_prefix(op).and_then(|r| r.strip_prefix(copy)) == Some(";"))
        {
            out.push(Some(1));
        }
    }
    out
}
