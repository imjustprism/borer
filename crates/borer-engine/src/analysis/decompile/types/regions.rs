//! Frame regions a fill or a copy runs past the slot it starts at, declared
//! as one byte array ([`filled_regions`]).

use super::super::fields::offset_text;
use super::super::line::parse_const;
use super::*;
use crate::analysis::attributes::call_args;

/// A frame slot a declaration names.
struct Slot {
    /// The name, `local_N`.
    name: String,
    /// The type a pointer to it has, `uint16_t*`.
    pointer: String,
    /// The bytes it takes; `None` for a type whose size the text does not say.
    size: Option<i64>,
}

/// A frame region declared as one byte array.
struct Region<'s> {
    /// The array's name, its first slot's.
    name: String,
    /// Its bytes.
    len: i64,
    /// The slots inside it, each with its offset in bytes, the first slot
    /// first.
    parts: Vec<(&'s Slot, u64)>,
}

/// Declares a frame region that a fill or a copy of a constant size runs
/// over as one byte array.
///
/// `memset(&local_70, 0, 104)` writes 104 bytes up from `local_70`, which C
/// allows only inside one object. The slots the text names among those
/// bytes are parts of it, so a read of one (`local_34`) sees what the fill,
/// or a call the region is handed to after it, wrote there. The slot
/// becomes `uint8_t local_70[104]`, its address `local_70`, and each part
/// a typed place at its offset: `local_34`, a `uint8_t`, is
/// `local_70[0x3c]`, and `local_30`, a `uint16_t`, is
/// `*(uint16_t*)&local_70[0x40]`. The size passed to `memset`, `memcpy` or
/// `memmove` gives a region, and regions that overlap are one. A region is
/// left alone when it would reach the frame base, when a slot the text
/// names lies only partly inside it or has a type whose size the text does
/// not say, or when the text reads through a slot inside it at an offset
/// it computes, which may reach past the fill: [`stack_arrays`] sizes that
/// one.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
/// * `word` - The machine word's type, which a pointer is as wide as.
///
/// # Returns
///
/// The text with those regions declared.
pub(in crate::analysis::decompile) fn filled_regions(text: &str, word: &str) -> String {
    if !text.contains("&local_") {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let slots = slots(&lines, word);
    let indexed = indexed_through(&lines);
    let named: BTreeSet<i64> = lines
        .iter()
        .filter(|l| !l.starts_with("//"))
        .flat_map(|l| {
            l.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .filter_map(local_depth)
                .collect::<Vec<_>>()
        })
        .collect();
    let mut arrays = Vec::new();
    for (start, end) in regions(&lines) {
        let Some(base) = slots.get(&start).filter(|_| end >= 0) else {
            continue;
        };
        if base.size.is_none_or(|n| n >= start - end) {
            continue;
        }
        let mut parts = Vec::new();
        let mut whole = true;
        for &depth in named.range(end + 1..).rev() {
            let slot = slots.get(&depth);
            match (slot, slot.and_then(|s| s.size)) {
                (Some(slot), Some(size))
                    if depth <= start
                        && depth - size >= end
                        && !indexed.contains(slot.name.as_str()) =>
                {
                    parts.push((slot, start.abs_diff(depth)));
                }
                (_, Some(size)) if depth - size >= start => {}
                (_, None) if depth > start => {}
                _ => whole = false,
            }
        }
        if whole {
            arrays.push(Region {
                name: base.name.clone(),
                len: start - end,
                parts,
            });
        }
    }
    if arrays.is_empty() {
        return text.to_owned();
    }
    let gone: BTreeSet<&str> = arrays
        .iter()
        .flat_map(|r| r.parts.iter().map(|(slot, _)| slot.name.as_str()))
        .collect();
    let decls = arrays
        .iter()
        .map(|r| format!("uint8_t {}[{}];", r.name, r.len))
        .collect();
    declare_arrays(&mut lines, &gone, decls);
    for line in lines
        .iter_mut()
        .filter(|l| !l.starts_with("//") && !is_declaration(l))
    {
        for r in &arrays {
            for (slot, off) in &r.parts {
                *line = respell(line, slot, &r.name, *off);
            }
        }
    }
    lines.join("\n") + "\n"
}

/// The frame slots the declarations name, by depth below the frame base.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `word` - The machine word's type.
fn slots(lines: &[String], word: &str) -> BTreeMap<i64, Slot> {
    let mut out = BTreeMap::new();
    for line in lines.iter().filter(|l| is_declaration(l)) {
        let Some((ty, names)) = line.trim().trim_end_matches(';').split_once(' ') else {
            continue;
        };
        for name in names.split(", ").map(str::trim) {
            let bare = name.trim_start_matches('*');
            let stars = name.len() - bare.len();
            let (bare, array) = bare
                .split_once('[')
                .map_or((bare, false), |(n, _)| (n, true));
            let Some(depth) = local_depth(bare) else {
                continue;
            };
            let size = match (stars, ty) {
                _ if array => None,
                (0, "float") => Some(4),
                (0, "double") => Some(8),
                (0, _) => slot_type(ty).map(slot_size),
                _ => Some(slot_size(word)),
            };
            let slot = Slot {
                name: bare.to_owned(),
                pointer: format!("{ty}{}*", "*".repeat(stars)),
                size: size.and_then(|n| i64::try_from(n).ok()),
            };
            out.insert(depth, slot);
        }
    }
    out
}

/// The regions the fills and copies of a constant size run over, each as
/// the depth it starts at and the depth past its end, overlapping ones
/// merged.
///
/// # Arguments
///
/// * `lines` - The function.
fn regions(lines: &[String]) -> Vec<(i64, i64)> {
    let mut spans = Vec::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for (callee, ends) in [("memset", 1), ("memcpy", 2), ("memmove", 2)] {
            let Some(args) = call_args(line, callee) else {
                continue;
            };
            let Some(len) = args
                .get(2)
                .and_then(|a| parse_const(a))
                .and_then(|n| i64::try_from(n).ok())
            else {
                continue;
            };
            for arg in args.iter().take(ends) {
                if let Some(start) = arg.strip_prefix('&').and_then(local_depth)
                    && let Some(end) = start.checked_sub(len)
                {
                    spans.push((start, end));
                }
            }
        }
    }
    spans.sort_by_key(|&(start, _)| std::cmp::Reverse(start));
    let mut out: Vec<(i64, i64)> = Vec::new();
    for (start, end) in spans {
        match out.last_mut() {
            Some(last) if start > last.1 => last.1 = last.1.min(end),
            _ => out.push((start, end)),
        }
    }
    out
}

/// Spells each use of a slot in one line as the place it is in its region.
///
/// Its address is the region's name at offset 0, else `&region[off]`; with
/// arithmetic after it, it keeps its own type (`(uint32_t*)&region[8] + 1`).
/// Its value is `region[off]` for a byte, else `*(T*)&region[off]`, in
/// parentheses before an operator that binds tighter. The region's own
/// slot is spelled first, before the parts' spellings name the region. A
/// name in a string literal or in the line's comment is no use.
///
/// # Arguments
///
/// * `line` - One line.
/// * `slot` - The slot.
/// * `region` - The region's name.
/// * `off` - The slot's offset in the region, in bytes.
fn respell(line: &str, slot: &Slot, region: &str, off: u64) -> String {
    let mut out = line.to_owned();
    let at = if off == 0 {
        region.to_owned()
    } else {
        format!("&{region}[{}]", offset_text(off))
    };
    let code = line
        .match_indices("//")
        .map(|(at, _)| at)
        .find(|&at| !in_literal(line.get(..at).unwrap_or("")))
        .unwrap_or(line.len());
    for pos in word_positions(line, &slot.name).into_iter().rev() {
        let end = pos + slot.name.len();
        let head = line.get(..pos).unwrap_or("");
        if pos >= code || in_literal(head) {
            continue;
        }
        let tail = line.get(end..).unwrap_or("").trim_start();
        let arithmetic = tail.starts_with(['+', '-']) && !tail.starts_with("->");
        if head.ends_with('&') && !head.ends_with("&&") {
            let place = if arithmetic {
                format!("({}){at}", slot.pointer)
            } else {
                at.clone()
            };
            out.replace_range(pos - 1..end, &place);
            continue;
        }
        let tight = ["[", ".", "->", "++", "--", "("]
            .iter()
            .any(|op| tail.starts_with(op));
        let value = if slot.pointer == "uint8_t*" {
            format!("{region}[{}]", offset_text(off))
        } else if tight {
            format!("(*({}){at})", slot.pointer)
        } else {
            format!("*({}){at}", slot.pointer)
        };
        out.replace_range(pos..end, &value);
    }
    out
}

/// Takes the names of `gone` out of the declarations and declares `decls`
/// after the last declaration line that named one.
///
/// # Arguments
///
/// * `lines` - The function, rewritten in place.
/// * `gone` - The names, without a pointer's `*`.
/// * `decls` - The declaration lines to add.
pub(super) fn declare_arrays(lines: &mut Vec<String>, gone: &BTreeSet<&str>, decls: Vec<String>) {
    let mut at = None;
    for (k, line) in lines.iter_mut().enumerate() {
        if !is_declaration(line) {
            continue;
        }
        let Some((ty, names)) = line.trim_end_matches(';').split_once(' ') else {
            continue;
        };
        let kept: Vec<&str> = names
            .split(", ")
            .filter(|n| !gone.contains(n.trim().trim_start_matches('*')))
            .collect();
        if kept.len() != names.split(", ").count() {
            *line = if kept.is_empty() {
                String::from("\u{0}")
            } else {
                format!("{ty} {};", kept.join(", "))
            };
            at = Some(k);
        }
    }
    if let Some(k) = at {
        lines.splice(k + 1..k + 1, decls);
    }
    lines.retain(|l| l != "\u{0}");
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::filled_regions;

    /// A fill past its slot makes the slots among its bytes parts of one
    /// array, each read at its offset with its own type; a slot's name in a
    /// string or a comment stays as it is.
    #[test]
    fn a_fill_past_its_slot_is_one_array_of_the_slots_it_covers() {
        let text = [
            "// signature: uint16_t f()",
            "extern void *memset(void *s, int c, size_t n);",
            "uint16_t local_30;",
            "uint64_t local_70;",
            "uint8_t local_34;",
            "",
            "memset(&local_70, 0, 104);",
            "GetStartupInfoW(&local_70);",
            "log(\"local_30 // local_34\", local_30); // local_34",
            "return ((local_34 & 1) != 0 ? local_30 : 10);",
        ]
        .join("\n");
        let want = [
            "// signature: uint16_t f()",
            "extern void *memset(void *s, int c, size_t n);",
            "uint8_t local_70[104];",
            "",
            "memset(local_70, 0, 104);",
            "GetStartupInfoW(local_70);",
            "log(\"local_30 // local_34\", *(uint16_t*)&local_70[0x40]); // local_34",
            "return ((local_70[0x3c] & 1) != 0 ? *(uint16_t*)&local_70[0x40] : 10);",
            "",
        ]
        .join("\n");
        assert_eq!(filled_regions(&text, "uint64_t"), want);
    }

    /// A copy's region keeps each part's type: a pointer slot read through,
    /// an address with arithmetic after it, and a value stored; fills that
    /// overlap are one region.
    #[test]
    fn overlapping_fills_are_one_region_whose_parts_keep_their_types() {
        let text = [
            "uint32_t local_40, local_38;",
            "uint64_t *local_30;",
            "",
            "memcpy(&local_40, a1, 16);",
            "memset(&local_38, 0, 16);",
            "local_30 = &local_38 + 1;",
            "local_40 = 7;",
            "return local_30[1];",
        ]
        .join("\n");
        let out = filled_regions(&text, "uint64_t");
        assert!(out.starts_with("uint8_t local_40[24];\n"), "{out}");
        assert!(out.contains("memcpy(local_40, a1, 16);"), "{out}");
        assert!(out.contains("memset(&local_40[8], 0, 16);"), "{out}");
        assert!(
            out.contains("*(uint64_t**)&local_40[0x10] = (uint32_t*)&local_40[8] + 1;"),
            "{out}"
        );
        assert!(out.contains("*(uint32_t*)local_40 = 7;"), "{out}");
        assert!(
            out.contains("return (*(uint64_t**)&local_40[0x10])[1];"),
            "{out}"
        );
    }

    /// A region that cannot be one array stays apart.
    ///
    /// That is one a slot lies only partly inside, one that would reach the
    /// frame base, one holding a slot with no size the text says, a fill
    /// inside its own slot, and one holding a slot the text indexes, which
    /// may reach past the fill.
    #[test]
    fn a_region_that_cannot_be_one_array_is_left_alone() {
        for text in [
            "uint64_t local_70, local_c;\n\nmemset(&local_70, 0, 104);\nreturn local_c;\n",
            "uint64_t local_10;\n\nmemset(&local_10, 0, 32);\nreturn local_10;\n",
            "uint64_t local_70;\n\nmemset(&local_70, 0, 104);\nreturn local_30.x;\n",
            "uint128_t local_20;\n\nmemset(&local_20, 0, 16);\nreturn local_20;\n",
            "uint64_t local_40;\n\nmemset(&local_40, 0, 16);\n((uint8_t*)&local_40)[a1 & 31] = 7;\n",
        ] {
            assert_eq!(filled_regions(text, "uint64_t"), text);
        }
    }
}
