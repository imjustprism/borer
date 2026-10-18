//! Read-only tables a function indexes, written out as the arrays they are.
//!
//! A compiler turns a `switch` that only picks a value into a load from a
//! table in read-only data: `return a1 <= 6 ? ((uint32_t*)0xd68)[a1] : -1`.
//! The address alone says nothing a reader can use. When the text bounds
//! the index, the bytes at that address are the table's entries, fixed by
//! the file, so the text names the table `g32_d68` and declares it with
//! its values: `static const uint32_t g32_d68[7] = {2, 10, 11, 12, 13, 14,
//! 2};`. The name is the global spelling the rest of the decompiler reads
//! back (`g32_<address>`).

use super::*;

/// Most entries a table is written out with.
const ENTRIES_MAX: u64 = 256;

/// The element types an indexed load casts its table to, with their size in
/// bytes and whether they are signed.
const ELEMENTS: [(&str, u64, bool); 8] = [
    ("uint8_t", 1, false),
    ("uint16_t", 2, false),
    ("uint32_t", 4, false),
    ("uint64_t", 8, false),
    ("int8_t", 1, true),
    ("int16_t", 2, true),
    ("int32_t", 4, true),
    ("int64_t", 8, true),
];

/// One table the text indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Table {
    /// The cast the text spells, `((uint32_t*)0xd68)`.
    spelled: String,
    /// The element type.
    ty: &'static str,
    /// Bytes per element.
    size: u64,
    /// The element type is signed.
    signed: bool,
    /// The table's address.
    addr: u64,
    /// Entries the text's bound allows.
    len: u64,
}

/// Writes each bounded index into a read-only table as a named array the
/// text declares with its entries.
///
/// A table qualifies when it lies in a section that is readable and
/// neither writable nor executable, the file holds every entry, and the
/// text compares the very index it reads with against a constant
/// ([`bound`]), at most [`ENTRIES_MAX`] entries.
/// An index with no such bound stays an address: its table's end is not in
/// the text, and writing past it would invent entries.
///
/// # Arguments
///
/// * `text` - A finished decompilation.
/// * `program` - The image the tables are read from.
///
/// # Returns
///
/// The text with its tables named and declared, or unchanged.
pub(super) fn inline_tables(text: &str, program: &Program) -> String {
    let tables = find_tables(text, program);
    if tables.is_empty() {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    for t in &tables {
        let name = format!("g{}_{:x}", t.size * 8, t.addr);
        for line in lines.iter_mut().filter(|l| !l.starts_with("//")) {
            *line = line.replace(&t.spelled, &name);
        }
    }
    let decls: Vec<String> = tables
        .iter()
        .filter_map(|t| declaration(t, program))
        .collect();
    let at = lines
        .iter()
        .position(String::is_empty)
        .unwrap_or_else(|| lines.iter().take_while(|l| l.starts_with("//")).count());
    lines.splice(at..at, decls);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// The tables the text indexes with a bound, each once, in address order.
///
/// # Arguments
///
/// * `text` - The decompilation.
/// * `program` - The image.
fn find_tables(text: &str, program: &Program) -> Vec<Table> {
    let mut found: BTreeMap<u64, Table> = BTreeMap::new();
    for line in text.lines().filter(|l| !l.starts_with("//")) {
        for &(ty, size, signed) in &ELEMENTS {
            let head = format!("(({ty}*)0x");
            let mut rest = line;
            while let Some(k) = rest.find(&head) {
                let after = rest.get(k + head.len()..).unwrap_or("");
                rest = after;
                let digits = after
                    .find(|c: char| !c.is_ascii_hexdigit())
                    .unwrap_or(after.len());
                let Some(index) = after
                    .get(digits..)
                    .and_then(|t| t.strip_prefix(")["))
                    .and_then(bracketed)
                else {
                    continue;
                };
                let Ok(addr) = u64::from_str_radix(after.get(..digits).unwrap_or(""), 16) else {
                    continue;
                };
                let Some(len) = bound(text, index) else {
                    continue;
                };
                let readonly = program
                    .section_at(addr)
                    .is_some_and(|s| s.readable && !s.writable && !s.executable);
                let held = program
                    .read_va(addr, usize::try_from(len * size).unwrap_or(usize::MAX))
                    .is_some();
                if readonly && held && len <= ENTRIES_MAX {
                    let spelled = format!("{head}{})", after.get(..digits).unwrap_or(""));
                    found.entry(addr).or_insert(Table {
                        spelled,
                        ty,
                        size,
                        signed,
                        addr,
                        len,
                    });
                }
            }
        }
    }
    found.into_values().collect()
}

/// The text inside the brackets that `rest` starts within.
///
/// # Arguments
///
/// * `rest` - The text just past an index's `[`.
fn bracketed(rest: &str) -> Option<&str> {
    let mut depth = 0i32;
    for (i, c) in rest.char_indices() {
        match c {
            '[' | '(' => depth += 1,
            ']' if depth == 0 => return rest.get(..i),
            ']' | ')' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// The entry count the comparisons in the text allow `index`.
///
/// A guard on either side bounds it: `E <= K` and `E > K` (the early exit
/// of the same test) admit `K + 1` entries, `E < K` and `E >= K` admit
/// `K`, and so do the mirrored spellings. Of several, the widest wins, so
/// no entry an index the text allows can reach is left out.
///
/// # Arguments
///
/// * `text` - The decompilation.
/// * `index` - The index expression, as spelled.
///
/// # Returns
///
/// One past the largest index the bounds admit, `None` when the text has
/// no bound on it or it admits none.
fn bound(text: &str, index: &str) -> Option<u64> {
    let index = index.trim();
    let forms: [(String, bool, u64); 8] = [
        (format!("{index} <= "), true, 1),
        (format!("{index} > "), true, 1),
        (format!("{index} < "), true, 0),
        (format!("{index} >= "), true, 0),
        (format!(" >= {index}"), false, 1),
        (format!(" < {index}"), false, 1),
        (format!(" > {index}"), false, 0),
        (format!(" <= {index}"), false, 0),
    ];
    let mut widest: Option<u64> = None;
    for line in text.lines().filter(|l| !l.starts_with("//")) {
        for (form, after, extra) in &forms {
            for (k, _) in line.match_indices(form.as_str()) {
                let constant = if *after {
                    let tail = line.get(k + form.len()..).unwrap_or("");
                    tail.get(..tail.find([')', ' ', ';']).unwrap_or(tail.len()))
                } else {
                    let head = line.get(..k).unwrap_or("");
                    head.get(head.rfind(['(', ' ']).map_or(0, |p| p + 1)..)
                };
                if let Some(n) = constant
                    .and_then(parse_const)
                    .and_then(|c| c.checked_add(*extra))
                    .filter(|&n| n > 0)
                {
                    widest = Some(widest.map_or(n, |w| w.max(n)));
                }
            }
        }
    }
    widest
}

/// The declaration of one table, with its entries read from the image.
///
/// # Arguments
///
/// * `t` - The table.
/// * `program` - The image.
fn declaration(t: &Table, program: &Program) -> Option<String> {
    let bytes = program.read_va(t.addr, usize::try_from(t.len * t.size).ok()?)?;
    let width = usize::try_from(t.size).ok()?;
    let values: Vec<String> = bytes
        .chunks_exact(width)
        .map(|chunk| {
            let mut raw = [0u8; 8];
            raw.get_mut(..width)?.copy_from_slice(chunk);
            let v = u64::from_le_bytes(raw);
            Some(entry(v, t.size, t.signed))
        })
        .collect::<Option<Vec<String>>>()?;
    Some(format!(
        "static const {} g{}_{:x}[{}] = {{{}}};",
        t.ty,
        t.size * 8,
        t.addr,
        t.len,
        values.join(", ")
    ))
}

/// One entry as C spells it: a signed type's negative entries with their
/// sign, a small one in decimal, a large one in hex.
///
/// # Arguments
///
/// * `v` - The entry's bits, zero-extended.
/// * `size` - Its width in bytes.
/// * `signed` - The element type is signed.
fn entry(v: u64, size: u64, signed: bool) -> String {
    let bits = u32::try_from(size * 8).unwrap_or(64);
    let sign_bit = 1u64.checked_shl(bits - 1).unwrap_or(0);
    if signed && v & sign_bit != 0 {
        let magnitude = (!v).wrapping_add(1) & 1u64.checked_shl(bits).map_or(u64::MAX, |m| m - 1);
        return format!("-{magnitude}");
    }
    if v < 0x1_0000 {
        v.to_string()
    } else {
        format!("{v:#x}")
    }
}
