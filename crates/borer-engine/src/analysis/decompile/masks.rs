//! Locals a 32-bit write zero-extends: the masks the lifter prints for
//! them, read back as `uint32_t` declarations and compound assignments.

use super::*;

/// Declares a local a 32-bit write zero-extended, and spells the sum back
/// as a compound assignment.
///
/// A 32-bit register write keeps the low half and clears the rest. The
/// lifter prints that as `v = (v + x) & 0xffffffff` so the text wraps where
/// the machine does. Where every use of `v` is one of those writes, a
/// constant update, a 32-bit load, a cast to that width, a `return` of it,
/// an index in an address, or its value handed on whole (a call's
/// argument, the value an assignment stores), `v` is a `uint32_t` (or an
/// `int32_t` when the only casts are signed, it is not returned, handed
/// on or an index). An index or a value handed on is the zero-extended
/// value, so a signed compare of that local keeps its cast.
/// The mask then says nothing the declaration does not, so the
/// write is `v += x` again and a counted `while` of it is a `for`. A use
/// the mask does not cover stays as it was: narrowing it would sign-extend
/// or wrap a value the machine kept. A local no read needs more than the
/// low 32 bits of ([`low_demand`]) is a `uint32_t` too, and a value
/// written to it is a 32-bit read of its own. A local every read of which
/// says a byte or a word is left to [`type_locals`], which declares it at
/// that width.
///
/// # Arguments
///
/// * `text` - A decompiled function, webs already split.
///
/// # Returns
///
/// The text with those locals declared at the width their writes used.
pub(super) fn lane_locals(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let declared = uint64_names(&lines);
    let uses = word_lines(&lines);
    let narrow = narrow_declarations(&lines);
    let low = low_demand(&lines, &uses, &declared, &narrow);
    let mut sinks: BTreeSet<&str> = low.iter().map(String::as_str).collect();
    sinks.extend(
        narrow
            .iter()
            .filter(|(_, ty)| integer_bits(ty).is_some())
            .map(|(n, _)| n.as_str()),
    );
    let mut held: BTreeSet<&str> = low.iter().map(String::as_str).collect();
    held.extend(
        narrow
            .iter()
            .filter(|(_, ty)| narrow_type(ty).is_some_and(|(_, mask)| mask.is_some()))
            .map(|(n, _)| n.as_str()),
    );
    let casts = Casts::of(&lines);
    let typed: Vec<(String, &'static str)> = declared
        .into_iter()
        .filter_map(|name| {
            let at = uses.get(name.as_str()).map_or(&[][..], Vec::as_slice);
            let reads = at
                .iter()
                .filter_map(|&k| lines.get(k))
                .filter(|l| !is_declaration(l));
            if inferred_type_on(&lines, &casts, reads, &name)
                .and_then(integer_bits)
                .is_some_and(|bits| bits < 32)
            {
                return None;
            }
            lane_type(&lines, at, &name, &sinks, &held)
                .or_else(|| low.contains(&name).then_some("uint32_t"))
                .map(|ty| (name, ty))
        })
        .collect();
    drop(casts);
    drop(held);
    drop(sinks);
    drop(uses);
    if typed.is_empty() {
        return text.to_owned();
    }
    let lanes: BTreeSet<&str> = typed.iter().map(|(n, _)| n.as_str()).collect();
    for line in &mut lines {
        if let Some(next) = unwrap_lane(line, &lanes).or_else(|| unwrap_for_step(line, &lanes)) {
            *line = next;
        }
    }
    let mut i = 0;
    while i < lines.len() {
        if let Some(split) = split_const_chain(&lines[i], &lanes) {
            let n = split.len();
            lines.splice(i..=i, split);
            i += n;
        } else {
            i += 1;
        }
    }
    redeclare(&mut lines, &typed);
    strip_widths(&mut lines, &typed, |l| {
        !l.starts_with("//") && !is_declaration(l)
    });
    loops::recover_loops(&mut lines);
    sugar_gap(&mut lines);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Each word of `lines` ([`tokens`]), with the lines it is on, in order.
///
/// A whole-word search for an identifier ([`word_positions`]) finds it
/// only on these lines, so a scan over them reads what one over every
/// line reads.
///
/// # Arguments
///
/// * `lines` - The text's lines.
///
/// # Returns
///
/// Per word, the indices of its lines, ascending and without repeats.
pub(super) fn word_lines(lines: &[String]) -> BTreeMap<&str, Vec<usize>> {
    let mut uses: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (k, l) in lines.iter().enumerate() {
        for tok in tokens(l) {
            let at = uses.entry(tok).or_default();
            if at.last() != Some(&k) {
                at.push(k);
            }
        }
    }
    uses
}

/// Strips each typed variable's redundant casts and masks
/// ([`strip_width`]) from every line `keep` accepts, the variables taken
/// in order.
///
/// A line changes only where an identifier is a whole word of it, so each
/// line is read for the variables it names, in their order, rather than
/// every variable being looked for in every line: a function of thousands
/// of lines declares hundreds of narrow locals. A name that is no
/// identifier is looked for as text, as before.
///
/// # Arguments
///
/// * `lines` - The lines, rewritten in place.
/// * `typed` - The variables with their declared types.
/// * `keep` - Whether a line, as it stands, may change.
pub(super) fn strip_widths(
    lines: &mut [String],
    typed: &[(String, &'static str)],
    keep: impl Fn(&str) -> bool,
) {
    let mut at: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    let mut loose: Vec<usize> = Vec::new();
    for (k, (name, _)) in typed.iter().enumerate() {
        if is_ident(name) {
            at.entry(name.as_str()).or_default().push(k);
        } else {
            loose.push(k);
        }
    }
    for line in lines {
        let mut from = 0;
        while let Some(k) = tokens(line)
            .filter_map(|w| at.get(w))
            .flatten()
            .copied()
            .chain(
                loose
                    .iter()
                    .copied()
                    .filter(|&k| typed.get(k).is_some_and(|(n, _)| line.contains(n.as_str()))),
            )
            .filter(|&k| k >= from)
            .min()
        {
            from = k + 1;
            let Some((name, ty)) = typed.get(k) else {
                break;
            };
            if let Some((casts, mask)) = narrow_type(ty)
                && keep(line)
            {
                *line = strip_width(line, name, casts, mask);
            }
        }
    }
}

/// The names a `uint64_t` declaration lists.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
pub(super) fn uint64_names(lines: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for line in lines {
        let Some(rest) = line
            .strip_prefix("uint64_t ")
            .and_then(|r| r.strip_suffix(';'))
        else {
            continue;
        };
        for name in rest.split(", ") {
            let name = name.trim();
            if is_register_name(name) || vars::is_var_name(name) {
                out.push(name.to_owned());
            }
        }
    }
    out
}

/// The 32-bit type `name` has when its uses all agree, if they do.
///
/// A constant assigned through one or several names truncates each of
/// them to the same bits, so such a line says nothing against the type.
/// A test `name == k` or `name != k` of a constant below `2^31` reads the
/// same at either width while every write leaves the high half clear: a
/// masked write or a constant does, a `+=` can carry into it. Only a
/// `varN` local qualifies, as a register name can hold an entry value.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `at` - The lines that name `name`, in order.
/// * `name` - A `uint64_t` local.
/// * `sinks` - The locals only the low 32 bits of a value reach
///   ([`masked_read`]).
/// * `held` - The locals that hold an unsigned value of at most 32 bits,
///   which a plain write may copy.
fn lane_type(
    lines: &[String],
    at: &[usize],
    name: &str,
    sinks: &BTreeSet<&str>,
    held: &BTreeSet<&str>,
) -> Option<&'static str> {
    let mut masked = false;
    let mut signed = false;
    let mut unsigned = false;
    let mut returned = false;
    let mut indexed = false;
    let mut compared = false;
    let mut compound = false;
    let mut whole = false;
    for line in at.iter().filter_map(|&k| lines.get(k)) {
        if line.starts_with("//") || is_declaration(line) {
            continue;
        }
        let trimmed = line.trim();
        if trimmed == format!("return {name};") {
            returned = true;
        }
        if for_step_masked(trimmed, name) {
            masked = true;
        }
        let chained = const_chain(trimmed).is_some_and(|chain| chain.contains(&name));
        if !chained {
            if let Some(rhs) = masked_rhs(trimmed, name) {
                masked = true;
                if rhs.contains('=') {
                    return None;
                }
            } else if let Some(rhs) = plain_rhs(trimmed, name) {
                if !fits_u32(rhs) && !narrow_load(rhs) && !held.contains(rhs) {
                    return None;
                }
            } else if let Some(rhs) = compound_rhs(trimmed, name) {
                compound = true;
                if !fits_u32(rhs) {
                    return None;
                }
            }
        }
        for at in word_positions(line, name) {
            if address_index(line, at, name) {
                indexed = true;
                continue;
            }
            if small_equality(line, at, name) {
                compared = true;
                continue;
            }
            if whole_value(line, at, name) {
                whole = true;
                continue;
            }
            if lane_use(line, at, name, sinks) {
                let head = line.get(..at).unwrap_or("");
                if head.ends_with("(int32_t)") || head.ends_with("(int64_t)(int32_t)") {
                    signed = true;
                } else if head.ends_with("(uint32_t)") {
                    unsigned = true;
                }
                continue;
            }
            return None;
        }
    }
    if !masked || (compared && (compound || !vars::is_var_name(name))) {
        return None;
    }
    if indexed || returned || unsigned || whole || !signed {
        Some("uint32_t")
    } else {
        Some("int32_t")
    }
}

/// Tells whether `name` at `at` is an index in a load or a store.
///
/// `*(uint8_t*)(a2 + name)` and `((uint8_t*)a2)[name]` add the
/// zero-extended register. A sum that is not an address is a full-width
/// add and is not one.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
fn address_index(line: &str, at: usize, name: &str) -> bool {
    let head = line.get(..at).unwrap_or("");
    let tail = line.get(at + name.len()..).unwrap_or("");
    let left = head.ends_with(" + ") || head.ends_with(" - ") || head.ends_with(['(', '[']);
    let right = tail.starts_with(" + ") || tail.starts_with(" - ") || tail.starts_with([')', ']']);
    if !left || !right {
        return false;
    }
    let from = head.rfind([';', '\n']).map_or(0, |i| i + 1);
    let region = line.get(from..).unwrap_or(line);
    region.contains("*(") || region.contains(")[")
}

/// Tells whether `name` at `at` hands its value on whole: the entire
/// argument of a call by name, or the entire value an assignment, a store
/// or a `+=`, `-=`, `&=`, `|=` or `^=` writes.
///
/// Every write of a lane local leaves a value below `2^32`, so a
/// `uint32_t` holding it hands on the very number the `uint64_t` did: a
/// parameter or a destination converts the same value either way, and
/// those compound operators keep the low bits of a narrower destination
/// and all of a wider one. A `sizeof` reads the type, not the value, and
/// is not one.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
fn whole_value(line: &str, at: usize, name: &str) -> bool {
    let head = line.get(..at).unwrap_or("");
    let tail = line.get(at + name.len()..).unwrap_or("");
    if tail == ";" {
        return [" = ", " += ", " -= ", " &= ", " |= ", " ^= "]
            .iter()
            .any(|op| {
                head.strip_suffix(op)
                    .map(str::trim)
                    .is_some_and(|lhs| !lhs.is_empty() && lhs != name)
            });
    }
    if !(head.ends_with('(') || head.ends_with(", ")) || !tail.starts_with([')', ',']) {
        return false;
    }
    let Some(open) = level_open(line, at) else {
        return false;
    };
    let callee = line.get(..open).unwrap_or("");
    let word = callee
        .rfind(|c: char| !is_ident_char(c))
        .map_or(callee, |k| callee.get(k + 1..).unwrap_or(""));
    line.get(open..=open) == Some("(") && is_ident(word) && word != "sizeof"
}

/// Tells whether `rhs` is one load of an unsigned integer of at most 32
/// bits: `*(uint32_t*)p`, `*(uint16_t*)(p + 8)` or `((uint8_t*)p)[i]`.
///
/// # Arguments
///
/// * `rhs` - The right-hand side of a plain write.
fn narrow_load(rhs: &str) -> bool {
    ["uint32_t", "uint16_t", "uint8_t"].iter().any(|ty| {
        let deref = rhs.strip_prefix(&format!("*({ty}*)")).is_some_and(|p| {
            is_ident(p) || (p.starts_with('(') && p.ends_with(')') && peel(p) != p)
        });
        let index = rhs
            .strip_prefix(&format!("(({ty}*)"))
            .and_then(|r| r.strip_suffix(']'))
            .and_then(|r| r.split_once(")["))
            .is_some_and(|(base, i)| is_ident(base) && is_ident(i));
        deref || index
    })
}

/// Tells whether `name` at `at` is a whole `name == k` or `name != k` test
/// of a constant below `2^31`.
///
/// The test opens a parenthesis or follows `&&` or `||`, and the constant
/// closes it or comes before `&&`, `||` or `?`, so no operator binds
/// either side tighter than the compare.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
fn small_equality(line: &str, at: usize, name: &str) -> bool {
    let head = line.get(..at).unwrap_or("");
    let tail = line.get(at + name.len()..).unwrap_or("");
    if !(head.ends_with('(') || head.ends_with("&& ") || head.ends_with("|| ")) {
        return false;
    }
    let Some(rest) = tail
        .strip_prefix(" == ")
        .or_else(|| tail.strip_prefix(" != "))
    else {
        return false;
    };
    let end = rest
        .find(|c: char| !c.is_ascii_alphanumeric())
        .unwrap_or(rest.len());
    let (constant, after) = rest.split_at(end);
    let closes = after.starts_with(')')
        || after.starts_with(" && ")
        || after.starts_with(" || ")
        || after.starts_with(" ? ");
    let value = match constant.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => constant.parse().ok(),
    };
    closes && value.is_some_and(|v| v <= 0x7fff_ffff)
}

/// Tells whether the use of `name` at `at` is a 32-bit one: its own write,
/// a width cast, or a read under a truncating mask.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
/// * `sinks` - The locals only the low 32 bits of a value reach.
fn lane_use(line: &str, at: usize, name: &str, sinks: &BTreeSet<&str>) -> bool {
    if for_part_use(line, at, name) {
        return true;
    }
    let head = line.get(..at).unwrap_or("");
    let tail = line.get(at + name.len()..).unwrap_or("");
    if head.ends_with("(int32_t)")
        || head.ends_with("(uint32_t)")
        || head.ends_with("(int64_t)(int32_t)")
    {
        return true;
    }
    if const_chain(line.trim()).is_some_and(|names| names.contains(&name)) {
        return true;
    }
    let trimmed = line.trim();
    if trimmed == format!("return {name};") {
        return true;
    }
    if masked_rhs(trimmed, name).is_some() && head.trim().is_empty() {
        return true;
    }
    if plain_rhs(trimmed, name).is_some() && head.trim().is_empty() {
        return true;
    }
    if compound_rhs(trimmed, name).is_some() && head.trim().is_empty() {
        return true;
    }
    if let Some((_, _)) = masked_assign(trimmed) {
        let eq = trimmed.find(" = ").unwrap_or(0);
        return at > eq;
    }
    let _ = tail;
    masked_read(line, at, at + name.len(), sinks)
}

/// Most parenthesis levels [`masked_read`] climbs.
const READ_LEVELS: u8 = 16;

/// Tells whether only the low 32 bits of the operand at `from..to` reach
/// the line's result.
///
/// The walk climbs the parentheses around the operand. At each level the
/// operators outside every inner parenthesis must all keep low bits low
/// (`+`, `-`, `*`, `<<`, `&`, `|`, `^`): a carry runs up, never down, so the
/// operand's high bits reach only high bits. The read is a 32-bit one where
/// a level ends in a 32-bit mask ([`depth0_mask`]) with no `|` or `^` beside it to take the
/// operand out from under the mask, or where the group is masked or cast
/// to a 32-bit integer as a whole. A shift right, a division, a
/// comparison, a call's argument list, an index or any other cast stops
/// it, as does a dereference, an address taken, a member read or an index
/// of the operand itself: those read the high bits too. A statement that
/// writes the whole
/// line to a sink keeps only the low bits as well ([`sink_rhs`]).
///
/// # Arguments
///
/// * `line` - The line.
/// * `from` - Byte index where the operand starts.
/// * `to` - Byte index just past it.
/// * `sinks` - The locals only the low 32 bits of a value reach.
fn masked_read(line: &str, mut from: usize, mut to: usize, sinks: &BTreeSet<&str>) -> bool {
    for _ in 0..READ_LEVELS {
        let before = line.get(..from).unwrap_or("");
        let after = line.get(to..).unwrap_or("");
        if before.ends_with([')', '*', '&', '!', '.'])
            || before.ends_with("->")
            || after.starts_with(['[', '(', '.'])
            || after.starts_with("->")
        {
            return false;
        }
        let (open, close) = (level_open(line, from), level_close(line, to));
        let start = open.map_or_else(
            || {
                line.get(..from)
                    .and_then(|h| h.rfind(';'))
                    .map_or(0, |k| k + 1)
            },
            |o| o + 1,
        );
        let end = close.unwrap_or_else(|| {
            line.get(to..)
                .and_then(|t| t.find(';'))
                .map_or(line.len(), |k| to + k)
        });
        let Some(raw) = line.get(start..end) else {
            return false;
        };
        if open.is_none()
            && let Some(rhs) = sink_rhs(raw, sinks)
        {
            let rhs_at = end - rhs.len();
            return from >= rhs_at && level_operators(rhs).is_some();
        }
        let level = assigned_value(raw);
        let ops = level_operators(level);
        let Some(ops) = ops else {
            return false;
        };
        let wide = ops.iter().any(|op| matches!(*op, "|" | "^"));
        if ops.contains(&"&") && !wide && depth0_mask(level) {
            return true;
        }
        let (Some(o), Some(c)) = (open, close) else {
            return false;
        };
        if line.get(o..=o) != Some("(") || line.get(c..=c) != Some(")") {
            return false;
        }
        let head = line.get(..o).unwrap_or("");
        if head.ends_with(is_ident_char) {
            return false;
        }
        if head.ends_with("(int32_t)") || head.ends_with("(uint32_t)") {
            return true;
        }
        if head.ends_with(')') {
            return false;
        }
        from = o;
        to = c + 1;
    }
    false
}

/// The value a statement writes where only its low 32 bits land: a sink
/// local assigned or updated by an operator that keeps low bits low, or a
/// store of at most 32 bits.
///
/// `low = v * 31;`, `low += v;` and `*(uint16_t*)(a1 + 4) = v;` keep only
/// the low bits of what they write, whatever `v` holds above them.
///
/// # Arguments
///
/// * `raw` - One statement, without its semicolon.
/// * `sinks` - The locals only the low 32 bits of a value reach.
///
/// # Returns
///
/// The written value's text, a suffix of `raw`, or `None` for any other
/// statement.
fn sink_rhs<'a>(raw: &'a str, sinks: &BTreeSet<&str>) -> Option<&'a str> {
    const OPS: [&str; 8] = [
        " = ", " += ", " -= ", " *= ", " <<= ", " &= ", " |= ", " ^= ",
    ];
    let t = raw.trim_start();
    let lhs_end = t.find(' ')?;
    let lhs = t.get(..lhs_end)?;
    let rest = t.get(lhs_end..)?;
    if is_ident(lhs) && sinks.contains(lhs) {
        let op = OPS.iter().find(|op| rest.starts_with(**op))?;
        return rest.get(op.len()..);
    }
    let store = [
        "uint32_t", "int32_t", "uint16_t", "int16_t", "uint8_t", "int8_t",
    ]
    .iter()
    .any(|ty| t.starts_with(&format!("*({ty}*)")));
    if !store {
        return None;
    }
    let mut depth = 0i32;
    for (i, c) in t.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                return t
                    .get(i..)
                    .and_then(|r| r.strip_prefix(" = "))
                    .filter(|_| balanced(t.get(..i).unwrap_or("")));
            }
            _ => {}
        }
    }
    None
}

/// Returns the `uint64_t` locals no read needs more than the low 32 bits of.
///
/// Every read is under a 32-bit mask, a cast to 32 bits or narrower, or in
/// what a statement writes to a sink ([`sink_rhs`]) through operators that
/// keep low bits low.
///
/// Such a local is a `uint32_t` whatever its writes compute, since what is
/// truncated is what no reader looks at. A local's own updates
/// (`v = v * 31 + x`) read it into itself, so the set is the largest one
/// that holds up: every local starts in it and leaves when a read it does
/// not cover turns up, until none does. Only `varN` locals qualify, as a
/// register name can hold an entry value.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `uses` - Each word's lines ([`word_lines`]).
/// * `declared` - The `uint64_t` locals.
/// * `narrow` - The locals declared at a narrow integer type, sinks
///   already.
///
/// # Returns
///
/// The locals whose reads need only their low 32 bits.
fn low_demand(
    lines: &[String],
    uses: &BTreeMap<&str, Vec<usize>>,
    declared: &[String],
    narrow: &[(String, &'static str)],
) -> BTreeSet<String> {
    let mut low: BTreeSet<&str> = declared
        .iter()
        .map(String::as_str)
        .filter(|n| vars::is_var_name(n))
        .collect();
    loop {
        let mut sinks = low.clone();
        sinks.extend(
            narrow
                .iter()
                .filter(|(_, ty)| integer_bits(ty).is_some())
                .map(|(n, _)| n.as_str()),
        );
        let gone: Vec<&str> = low
            .iter()
            .copied()
            .filter(|name| {
                let at = uses.get(name).map_or(&[][..], Vec::as_slice);
                !at.iter().filter_map(|&k| lines.get(k)).all(|line| {
                    line.starts_with("//")
                        || is_declaration(line)
                        || word_positions(line, name)
                            .into_iter()
                            .all(|p| low_read(line, p, name, &sinks))
                })
            })
            .collect();
        if gone.is_empty() {
            return low.into_iter().map(str::to_owned).collect();
        }
        for name in gone {
            low.remove(name);
        }
    }
}

/// Tells whether the occurrence of `name` at `at` needs only its low 32 bits.
///
/// It does as a plain write of it, an update by an operator that keeps low
/// bits low, a cast to 32 bits or narrower, or a read [`masked_read`]
/// accepts.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
/// * `sinks` - The locals only the low 32 bits of a value reach.
fn low_read(line: &str, at: usize, name: &str, sinks: &BTreeSet<&str>) -> bool {
    const KEEP: [&str; 8] = [
        " = ", " += ", " -= ", " *= ", " <<= ", " &= ", " |= ", " ^= ",
    ];
    let head = line.get(..at).unwrap_or("");
    let tail = line.get(at + name.len()..).unwrap_or("");
    if head.trim().is_empty() && KEEP.iter().any(|op| tail.starts_with(op)) {
        return sinks.contains(name);
    }
    let narrow_cast = [
        "(int32_t)",
        "(uint32_t)",
        "(int16_t)",
        "(uint16_t)",
        "(int8_t)",
        "(uint8_t)",
    ]
    .iter()
    .any(|c| head.ends_with(c));
    narrow_cast || masked_read(line, at, at + name.len(), sinks)
}

/// The value side of `name = value`, or the whole text when it assigns
/// nothing.
///
/// # Arguments
///
/// * `level` - One level's text.
fn assigned_value(level: &str) -> &str {
    let t = level.trim();
    match t.split_once(" = ") {
        Some((lhs, rhs)) if is_ident(lhs) || lhs.starts_with("for (") => rhs,
        _ => t,
    }
}

/// The `(` or `[` that opens the level holding byte `at`, if any.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - A byte index.
fn level_open(line: &str, at: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in line.get(..at)?.char_indices().rev() {
        match c {
            ')' | ']' => depth += 1,
            '(' | '[' if depth == 0 => return Some(i),
            '(' | '[' => depth -= 1,
            ';' if depth == 0 => return None,
            _ => {}
        }
    }
    None
}

/// The `)` or `]` that closes the level holding byte `at`, if any.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - A byte index.
fn level_close(line: &str, at: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in line.get(at..)?.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' if depth == 0 => return Some(at + i),
            ')' | ']' => depth -= 1,
            ';' if depth == 0 => return None,
            _ => {}
        }
    }
    None
}

/// The binary operators of one level, outside its inner parentheses, when
/// every one keeps low bits low; `None` when one does not.
///
/// # Arguments
///
/// * `level` - The text between a level's parentheses.
fn level_operators(level: &str) -> Option<Vec<&'static str>> {
    const KEEP: [&str; 7] = [" + ", " - ", " * ", " << ", " & ", " | ", " ^ "];
    let mut ops = Vec::new();
    let mut depth = 0i32;
    let mut i = 0;
    while let Some(c) = level.get(i..).and_then(|r| r.chars().next()) {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                let rest = level.get(i..).unwrap_or("");
                if let Some(op) = KEEP.iter().find(|op| rest.starts_with(**op)) {
                    ops.push(op.trim());
                    i += op.len();
                    continue;
                }
                if rest.trim_start().starts_with(|c: char| {
                    !c.is_alphanumeric() && c != '(' && c != '*' && c != '-' && c != '~'
                }) {
                    return None;
                }
            }
            _ => {}
        }
        i += c.len_utf8();
    }
    Some(ops)
}

/// Tells whether a level's value depends on no bit above the low 32.
///
/// It has a ` & k` outside its inner parentheses whose constant `k` fits in
/// 32 bits: ` & 0xffffffff`, ` & 0xff` or the ` & 0x1f` of a shift count.
/// The constant ends the level or another ` & ` follows it, so no operator
/// binding tighter takes it as an operand.
///
/// # Arguments
///
/// * `level` - The text between a level's parentheses.
fn depth0_mask(level: &str) -> bool {
    let mut depth = 0i32;
    for (i, c) in level.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                let Some(rest) = level.get(i..).and_then(|r| r.strip_prefix(" & ")) else {
                    continue;
                };
                let end = rest
                    .find(|c: char| !c.is_ascii_alphanumeric())
                    .unwrap_or(rest.len());
                let last = rest
                    .get(end..)
                    .is_none_or(|t| t.is_empty() || t.starts_with(" & "));
                if last
                    && parse_const(rest.get(..end).unwrap_or("")).is_some_and(|k| k <= 0xffff_ffff)
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// The right-hand side of `name = rhs & 0xffffffff`, when the mask covers it.
///
/// # Arguments
///
/// * `trimmed` - The line, trimmed, semicolon included.
/// * `name` - The variable written.
fn masked_rhs<'a>(trimmed: &'a str, name: &str) -> Option<&'a str> {
    let (lhs, rhs) = masked_assign(trimmed)?;
    (lhs == name).then_some(rhs)
}

/// `name = <expr> & 0xffffffff` split into the name and the masked expression.
///
/// # Arguments
///
/// * `trimmed` - One trimmed line.
fn masked_assign(trimmed: &str) -> Option<(&str, &str)> {
    let body = trimmed.strip_suffix(';')?;
    let (lhs, rhs) = body.split_once(" = ")?;
    if !is_ident(lhs) {
        return None;
    }
    let expr = rhs.strip_suffix(" & 0xffffffff")?.trim();
    balanced(expr).then_some((lhs, expr))
}

/// The names a `a = b = 0` chain writes, when the value fits in 32 bits.
///
/// # Arguments
///
/// * `trimmed` - One trimmed line.
pub(super) fn const_chain(trimmed: &str) -> Option<Vec<&str>> {
    let body = trimmed.strip_suffix(';')?;
    let mut parts: Vec<&str> = body.split(" = ").collect();
    let value = parts.pop()?.trim();
    if parts.is_empty() || !fits_u32(value) {
        return None;
    }
    if parts.iter().any(|p| !is_ident(p.trim())) {
        return None;
    }
    Some(parts.iter().map(|p| p.trim()).collect())
}

/// A plain `name = rhs` that is not a masked write.
///
/// # Arguments
///
/// * `trimmed` - One trimmed line.
/// * `name` - The variable.
fn plain_rhs<'a>(trimmed: &'a str, name: &str) -> Option<&'a str> {
    if masked_assign(trimmed).is_some() {
        return None;
    }
    let body = trimmed.strip_suffix(';')?;
    let (lhs, rhs) = body.split_once(" = ")?;
    (lhs == name && is_ident(lhs)).then_some(rhs.trim())
}

/// A compound `name += rhs` (and the other compound operators).
///
/// # Arguments
///
/// * `trimmed` - One trimmed line.
/// * `name` - The variable.
fn compound_rhs<'a>(trimmed: &'a str, name: &str) -> Option<&'a str> {
    let body = trimmed.strip_suffix(';')?;
    let (lhs, rest) = body.split_once(' ')?;
    if lhs != name {
        return None;
    }
    let (op, rhs) = rest.split_once(' ')?;
    matches!(op, "+=" | "-=").then_some(rhs.trim())
}

/// Tells whether parentheses in `text` balance and never go negative.
///
/// # Arguments
///
/// * `text` - An expression.
pub(super) fn balanced(text: &str) -> bool {
    let mut depth = 0i32;
    for c in text.chars() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

/// Tells whether `text` is a constant that fits in 32 bits.
///
/// # Arguments
///
/// * `text` - The right-hand side.
fn fits_u32(text: &str) -> bool {
    let token = text.trim();
    let token = token.strip_suffix("u").unwrap_or(token);
    let value = match token.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => token.parse().ok(),
    };
    value.is_some_and(|v| v <= 0xffff_ffff)
}

/// Rewrites one lane's masked assignment as a compound update when it is
/// `name = name op rhs`, otherwise as a plain assignment of the low half.
///
/// # Arguments
///
/// * `line` - One line.
/// * `lanes` - The locals declared at 32 bits.
fn unwrap_lane(line: &str, lanes: &BTreeSet<&str>) -> Option<String> {
    let indent_len = line.len() - line.trim_start().len();
    let (indent, trimmed) = line.split_at(indent_len);
    let (lhs, expr) = masked_assign(trimmed)?;
    if !lanes.contains(lhs) {
        return None;
    }
    let inner = peel(expr);
    let rewritten = compound_of(lhs, inner).unwrap_or_else(|| format!("{lhs} = {inner}"));
    Some(format!("{indent}{rewritten};"))
}

/// The three clauses of a `for` header, when `line` is one.
///
/// # Arguments
///
/// * `line` - One line.
fn for_clauses(line: &str) -> Option<(&str, &str, &str)> {
    let rest = line.trim().strip_prefix("for (")?;
    let header = rest.strip_suffix(") {")?;
    let mut parts: Vec<&str> = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, c) in header.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ';' if depth == 0 => {
                parts.push(header.get(start..i)?.trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(header.get(start..)?.trim());
    (parts.len() == 3).then_some((parts[0], parts[1], parts[2]))
}

/// Tells whether `name` at `at` is the initializer, the compare, or the
/// step of a `for` whose step is a 32-bit wrapping update.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - Byte index of the name.
/// * `name` - The variable.
fn for_part_use(line: &str, at: usize, name: &str) -> bool {
    let Some((init, _cond, step)) = for_clauses(line) else {
        return false;
    };
    let step_stmt = format!("{step};");
    let Some((lhs, _)) = masked_assign(&step_stmt) else {
        return false;
    };
    if lhs != name {
        return false;
    }
    let Some(header_at) = line.find("for (").map(|i| i + "for (".len()) else {
        return false;
    };
    let Some(header) = line.get(header_at..).and_then(|h| h.strip_suffix(") {")) else {
        return false;
    };
    let Some(local) = at.checked_sub(header_at) else {
        return false;
    };
    if local >= header.len() {
        return false;
    }
    let mut ranges: Vec<std::ops::Range<usize>> = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, c) in header.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ';' if depth == 0 => {
                ranges.push(start..i);
                start = i + 1;
            }
            _ => {}
        }
    }
    ranges.push(start..header.len());
    let Some(clause) = ranges
        .iter()
        .position(|r| r.start <= local && local < r.end)
    else {
        return false;
    };
    match clause {
        0 => {
            let Some(value) = init
                .strip_prefix(name)
                .and_then(|r| r.trim_start().strip_prefix('='))
                .map(str::trim)
            else {
                return false;
            };
            header
                .get(ranges[0].clone())
                .is_some_and(|c| c.trim().starts_with(name))
                && fits_u32(value)
        }
        1 => {
            let head = line.get(..at).unwrap_or("");
            head.ends_with("(int32_t)")
                || head.ends_with("(uint32_t)")
                || head.ends_with("(int64_t)(int32_t)")
        }
        _ => true,
    }
}

/// Tells whether a `for` step writes `name` through a 32-bit mask.
///
/// # Arguments
///
/// * `trimmed` - The line, trimmed.
/// * `name` - The variable.
fn for_step_masked(trimmed: &str, name: &str) -> bool {
    let Some((_, _, step)) = for_clauses(trimmed) else {
        return false;
    };
    let stmt = format!("{step};");
    masked_assign(&stmt).is_some_and(|(lhs, _)| lhs == name)
}

/// Rewrites a `for` step `name = (name + n) & 0xffffffff` as `name += n`.
///
/// The declaration is already the lane, so the add wraps where the mask did.
///
/// # Arguments
///
/// * `line` - One line.
/// * `lanes` - The locals declared at 32 bits.
fn unwrap_for_step(line: &str, lanes: &BTreeSet<&str>) -> Option<String> {
    let (init, cond, step) = for_clauses(line)?;
    let stmt = format!("{step};");
    let (lhs, expr) = masked_assign(&stmt)?;
    let lhs = lhs.to_owned();
    let expr = expr.to_owned();
    if !lanes.contains(lhs.as_str()) {
        return None;
    }
    let rewritten = compound_of(&lhs, peel(&expr))?;
    let indent_len = line.len() - line.trim_start().len();
    let indent = line.get(..indent_len).unwrap_or("");
    Some(format!("{indent}for ({init}; {cond}; {rewritten}) {{"))
}

/// Splits `a = b = 0` into one assignment a name when any of them is a lane.
///
/// The rightmost name is written first, which is the order the chain
/// itself writes them.
///
/// # Arguments
///
/// * `line` - One line.
/// * `lanes` - The locals declared at 32 bits.
fn split_const_chain(line: &str, lanes: &BTreeSet<&str>) -> Option<Vec<String>> {
    let indent_len = line.len() - line.trim_start().len();
    let (indent, trimmed) = line.split_at(indent_len);
    let names = const_chain(trimmed)?;
    if !names.iter().any(|n| lanes.contains(n)) || names.len() < 2 {
        return None;
    }
    let value = trimmed
        .strip_suffix(';')
        .and_then(|b| b.rsplit(" = ").next())?
        .trim();
    Some(
        names
            .into_iter()
            .rev()
            .map(|n| format!("{indent}{n} = {value};"))
            .collect(),
    )
}

/// Drops one pair of parentheses that wraps the whole expression.
///
/// # Arguments
///
/// * `expr` - The masked expression.
pub(super) fn peel(expr: &str) -> &str {
    let expr = expr.trim();
    if expr.len() >= 2 && expr.starts_with('(') && expr.ends_with(')') {
        let inner = expr.get(1..expr.len() - 1).unwrap_or(expr);
        let mut depth = 0i32;
        let mut wraps = true;
        for (i, c) in expr.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && i + 1 != expr.len() {
                        wraps = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if wraps && balanced(inner) {
            return inner.trim();
        }
    }
    expr
}

/// `name + rhs` as `name += rhs`, and the same for `-`.
///
/// # Arguments
///
/// * `name` - The variable written.
/// * `expr` - The unmasked expression.
fn compound_of(name: &str, expr: &str) -> Option<String> {
    let (left, op, right) = top_op(expr)?;
    if left == name && (op == "+" || op == "-") {
        let sym = if op == "+" { "+=" } else { "-=" };
        return Some(format!("{name} {sym} {right}"));
    }
    if right == name && op == "+" {
        return Some(format!("{name} += {left}"));
    }
    None
}

/// The top-level `+` or `-` of an expression, when it has one.
///
/// # Arguments
///
/// * `expr` - An expression with balanced parentheses.
fn top_op(expr: &str) -> Option<(&str, &str, &str)> {
    let bytes = expr.as_bytes();
    let mut depth = 0i32;
    let mut found = None;
    for (i, b) in bytes.iter().copied().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b'+' | b'-'
                if depth == 0
                    && i > 0
                    && bytes[i - 1] == b' '
                    && bytes.get(i + 1) == Some(&b' ') =>
            {
                if found.is_some() {
                    return None;
                }
                found = Some(i);
            }
            _ => {}
        }
    }
    let at = found?;
    let op = expr.get(at..at + 1)?;
    let left = expr.get(..at)?.trim();
    let right = expr.get(at + 1..)?.trim();
    if left.is_empty() || right.is_empty() {
        return None;
    }
    Some((left, op, right))
}

#[cfg(test)]
mod lane_tests {
    use super::lane_locals;

    /// Reads under a 32-bit mask inside a condition, an index or a `for`
    /// header are 32-bit reads, so the bounds of a binary search are
    /// `uint32_t` and their masks go.
    ///
    /// Each read of `var1` and `var2` reaches its line's result only through
    /// `-`, `+` and a ` & 0xffffffff`, which keep low bits low. A shift
    /// right of the unmasked value reads the high bits, so `var4`, read
    /// that way, stays as it was, and so does `var3`, which a 64-bit sum
    /// writes.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn reads_under_a_mask_anywhere_on_the_line_are_32_bit_reads() {
        let text = concat!(
            "uint64_t var1, var2, var3, var4;\n",
            "\n",
            "var1 = 0;\n",
            "var2 = (a2 - 1) & 0xffffffff;\n",
            "var4 = a2 & 0xffffffff;\n",
            "for (var3 = ((((var2 - var1) & 0xffffffff) >> 1) + var1) & 0xffffffff; a1[var3 & 0xffffffff] != (uint32_t)a3; var3 = ((((var2 - var1) & 0xffffffff) >> 1) + var1) & 0xffffffff) {\n",
            "  if ((int32_t)a1[((((var2 - var1) & 0xffffffff) >> 1) + var1) & 0xffffffff] >= (int32_t)a3) {\n",
            "    var2 = (var3 - 1) & 0xffffffff;\n",
            "  } else {\n",
            "    var1 = (var3 + 1) & 0xffffffff;\n",
            "  }\n",
            "}\n",
            "var3 = var3 + (var4 >> 3);\n",
            "return var3;\n",
        );
        let out = lane_locals(text);
        assert!(out.contains("uint32_t var1, var2;"), "{out}");
        assert!(out.contains("uint64_t var3, var4;"), "{out}");
        assert!(out.contains("var2 = var3 - 1;"), "{out}");
        assert!(out.contains("var2 = var3 - 1;"), "{out}");
    }

    /// A 32-bit counter compared as signed and the 32-bit sum it feeds are
    /// declared at those widths, so the compare cast and the truncation
    /// mask are the declaration's.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_32_bit_counter_and_its_sum_lose_the_truncation_mask() {
        let text = concat!(
            "// signature: uint64_t f()\n",
            "uint64_t var1, var2;\n",
            "\n",
            "var1 = var2 = 0;\n",
            "while ((int32_t)var2 < 5) {\n",
            "  var1 = (var1 + var2) & 0xffffffff;\n",
            "  var2 = (var2 + 1) & 0xffffffff;\n",
            "}\n",
            "return var1;\n",
        );
        let out = lane_locals(text);
        assert!(out.contains("int32_t var2;"), "{out}");
        assert!(out.contains("uint32_t var1;"), "{out}");
        assert!(out.contains("for (var2 = 0; var2 < 5; var2 += 1)"), "{out}");
        assert!(out.contains("var1 += var2;"), "{out}");
        assert!(!out.contains("0xffffffff"), "{out}");
        assert!(!out.contains("(int32_t)"), "{out}");
    }

    /// A shift of the same register after the truncating add reads the bits
    /// above 32, so the mask stays and the local stays `uint64_t`.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_later_wide_shift_keeps_the_truncation_mask() {
        let text = concat!(
            "uint64_t var1;\n",
            "\n",
            "var1 = (var1 + 1) & 0xffffffff;\n",
            "var1 <<= 4;\n",
            "return var1;\n",
        );
        let out = lane_locals(text);
        assert!(out.contains("uint64_t var1;"), "{out}");
        assert!(out.contains("0xffffffff"), "{out}");
        assert!(out.contains("var1 <<= 4;"), "{out}");
    }

    /// A counter used as an address index is the zero-extended value, so
    /// the mask becomes `+=` and the local is `uint32_t`.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_index_is_the_zero_extended_counter() {
        let text = concat!(
            "// signature: uint32_t f(uint64_t a1, uint8_t *a2, uint32_t a3)\n",
            "uint64_t var1;\n",
            "\n",
            "var1 = 0;\n",
            "do {\n",
            "  *(uint8_t*)(a2 + var1) = 65;\n",
            "  var1 = (var1 + 1) & 0xffffffff;\n",
            "} while ((uint32_t)var1 < a3);\n",
            "return 65;\n",
        );
        let out = lane_locals(text);
        assert!(out.contains("uint32_t var1;"), "{out}");
        assert_eq!(out.matches("var1 += 1;").count(), 1, "{out}");
        assert!(out.contains("while (var1 < a3);"), "{out}");
        assert!(!out.contains("0xffffffff"), "{out}");
    }

    /// A zero test of a counter every write masks reads the same at 32 bits.
    ///
    /// The counter is declared there and its masks go. A `+=`
    /// can carry into the high half, so beside one the test keeps the
    /// local at 64 bits.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_zero_test_of_a_masked_counter_is_a_32_bit_read() {
        let text = concat!(
            "uint64_t var1, var2;\n",
            "\n",
            "var2 = a2 & 0xffffffff;\n",
            "do {\n",
            "  var2 = (var2 - 1) & 0xffffffff;\n",
            "  if (var2 == 0 && *(uint8_t*)a1 == 62) {\n",
            "    return;\n",
            "  }\n",
            "} while ((int32_t)var2 > 0);\n",
            "var1 = a3 & 0xffffffff;\n",
            "var1 += 1;\n",
            "if (var1 != 0) {\n",
            "  return;\n",
            "}\n",
        );
        let out = lane_locals(text);
        assert!(out.contains("int32_t var2;"), "{out}");
        assert!(out.contains("var2 -= 1;"), "{out}");
        assert!(out.contains("if (var2 == 0 && "), "{out}");
        assert!(out.contains("while (var2 > 0);"), "{out}");
        assert!(out.contains("uint64_t var1;"), "{out}");
        assert!(out.contains("var1 = a3 & 0xffffffff;"), "{out}");
    }

    /// A lane local whose value is handed on whole is a `uint32_t`.
    ///
    /// A call's argument, a store's value or an assignment's each reads the
    /// same number at either width. A signed compare keeps its cast, and a
    /// use in a ternary arm keeps the local as it was.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_lane_handed_on_whole_is_unsigned() {
        let text = concat!(
            "uint64_t var1, var2, var3;
",
            "
",
            "var1 = *(uint32_t*)(a1 + 4);
",
            "var1 = (var1 + 1) & 0xffffffff;
",
            "if ((int32_t)var1 > 3) {
",
            "  sub_1(a1, var1);
",
            "}
",
            "*(uint32_t*)(a1 + 8) = var1;
",
            "var2 = var1;
",
            "var3 = (a2 - 1) & 0xffffffff;
",
            "var2 = a3 != 0 ? var3 : a2;
",
            "return sizeof(var3) + var2;
",
        );
        let out = lane_locals(text);
        assert!(out.contains("uint32_t var1;"), "{out}");
        assert!(out.contains("var1 += 1;"), "{out}");
        assert!(out.contains("if ((int32_t)var1 > 3) {"), "{out}");
        assert!(out.contains("uint64_t var2, var3;"), "{out}");
        assert!(out.contains("var3 = (a2 - 1) & 0xffffffff;"), "{out}");
    }

    /// A local every read of which takes its low byte is left to the
    /// typing that declares it a byte, though a 32-bit mask writes it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_local_read_as_a_byte_stays_for_the_byte_typing() {
        let text = concat!(
            "// signature: uint64_t f(uint64_t a1, uint64_t a2)
",
            "uint64_t var2;
",
            "
",
            "var2 = (a1 + 1) & 0xffffffff;
",
            "sub_1(((var2 & 0xff) | a2) != 0);
",
            "return var2 & 0xff;
",
        );
        let lanes = lane_locals(text);
        assert!(lanes.contains("uint64_t var2;"), "{lanes}");
        let out = super::type_locals(&lanes);
        assert!(out.contains("uint8_t var2;"), "{out}");
    }
}
