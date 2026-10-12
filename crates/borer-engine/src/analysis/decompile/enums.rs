//! Name tables: constants a function compares or passes, rendered by the member
//! names its callee encodes.

use super::*;
use crate::analysis::RefKind;

/// A name table recovered from a function's body: constants paired with
/// the string literals the code maps them to or from.
#[derive(Debug, Default, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EnumTable {
    /// What the values are: a parameter's type, the comparator called, or
    /// the variable tested.
    pub name: String,
    /// `(constant, literal)` pairs in the order the code tests them.
    pub members: Vec<(u64, String)>,
    /// For a constant-to-string table, the position (from zero) of the
    /// parameter it tests; `None` for a parser, whose result carries the
    /// value.
    pub param: Option<usize>,
}

impl EnumTable {
    /// The member named for `value`, if the table has one.
    ///
    /// # Arguments
    ///
    /// * `value` - The constant.
    pub(super) fn member(&self, value: u64) -> Option<&str> {
        self.members
            .iter()
            .find(|(k, _)| *k == value)
            .map(|(_, lit)| lit.as_str())
    }
}

/// The name in a `"..."` token, or `None` when the token is not a literal
/// or the literal is not a name.
///
/// A name table's literals are identifiers (`MouseOver`, `bmp`,
/// `Game::Hub`): one to 48 characters from letters, digits, `_`, `.`, `:`,
/// `/`, `-`. A literal with a space or other punctuation is a message, and a
/// function full of messages is not an enum.
///
/// # Arguments
///
/// * `t` - The token, quotes included.
pub(super) fn literal_of(t: &str) -> Option<&str> {
    /// Longest literal that still reads as a name.
    const NAME_MAX: usize = 48;
    let name = t.strip_prefix('"')?.strip_suffix('"')?;
    let ok = !name.is_empty()
        && name.len() <= NAME_MAX
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ':' | '/' | '-'));
    ok.then_some(name)
}

/// Recovers the name table of a decompiled function from its full text.
///
/// The parameters come from the `// signature:` line, so a table named by
/// a parameter's type keeps that name, and the body is read as
/// [`enum_table`] reads it.
///
/// # Arguments
///
/// * `text` - Output of [`decompile`].
///
/// # Returns
///
/// The table, or `None` when the function encodes none.
pub fn enum_of(text: &str) -> Option<EnumTable> {
    let params: Vec<String> = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .and_then(|sig| sig.rsplit_once('(').map(|(_, rest)| rest))
        .and_then(|rest| rest.rsplit_once(')').map(|(inner, _)| inner))
        .map(|inner| {
            split_arguments(inner)
                .into_iter()
                .filter(|p| !p.is_empty())
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();
    enum_table(text, &params)
}

/// Recovers every name table in a binary, one per function that encodes
/// one.
///
/// Every function shaped like a table ([`table_shaped`]) is read by
/// [`table_at`] across the cores: one referencing at least three distinct
/// string literals is decompiled and its text read by [`enum_of`]; the
/// result is what the `// enum` header lines say, gathered in one place.
/// Each function's table is memoized, so the tables a decompilation looked
/// up already ([`called_tables`]) are not read again.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and comments to apply.
///
/// # Returns
///
/// `(entry, table)` pairs in address order.
pub fn enum_tables(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
) -> Vec<(u64, EnumTable)> {
    let key = overlay.fingerprint();
    let shaped: Vec<u64> = analysis
        .functions
        .iter()
        .filter(|f| table_shaped(f))
        .map(|f| f.entry)
        .collect();
    let tables = crate::analysis::striped(&shaped, |&entry| {
        table_at(program, analysis, overlay, key, entry)
    });
    shaped
        .into_iter()
        .zip(tables)
        .filter_map(|(entry, table)| Some((entry, table?.as_ref().clone()?)))
        .collect()
}

/// Tells whether a function is shaped like a name table: at least six
/// blocks of at most five instructions each (a test and a jump, a load or
/// a return per member).
///
/// On the client the shape keeps every table while cutting the functions
/// worth decompiling by a third.
///
/// # Arguments
///
/// * `f` - The function.
fn table_shaped(f: &Function) -> bool {
    /// Fewest blocks a table has (two per member, near enough).
    const BLOCKS_MIN: usize = 6;
    /// Most instructions per block a table has: one test and one jump, a
    /// load or a return.
    const PER_BLOCK_MAX: usize = 5;
    f.blocks.len() >= BLOCKS_MIN && f.instr_count <= PER_BLOCK_MAX * f.blocks.len()
}

/// Returns the name table of the table-shaped function at `entry`, read
/// once per function and overlay through [`Analysis::derived`].
///
/// A function referencing fewer than three distinct string literals
/// encodes none and is not decompiled; any other is decompiled before the
/// final text passes ([`decompile_plain_full`]), which fold a compared
/// result into its test, and its text read by [`enum_of`]. Callers
/// pass an overlay without tables ([`Overlay::without_tables`]), so reading
/// a table never needs another.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis, holding the memo.
/// * `overlay` - Names and comments to apply.
/// * `overlay_key` - [`Overlay::fingerprint`] of `overlay`.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The shared table, `None` inside when the function encodes none.
fn table_at(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    overlay_key: u64,
    entry: u64,
) -> std::sync::Arc<Option<EnumTable>> {
    /// Fewest distinct string literals a table function references.
    const LITERALS_MIN: usize = 3;
    analysis.derived.get_or_build_item(
        "enum_table",
        overlay_key,
        entry,
        || {
            let strings: BTreeSet<u64> = analysis
                .refs_from(entry)
                .into_iter()
                .filter(|(_, site)| site.kind == RefKind::Data)
                .map(|(target, _)| target)
                .filter(|&target| cstr_at(program, target, 1, 64).is_some())
                .collect();
            (strings.len() >= LITERALS_MIN)
                .then(|| decompile_plain_full(program, analysis, overlay, entry))
                .flatten()
                .map(|d| d.text)
                .and_then(|text| enum_of(&text))
        },
        |table| {
            table.as_ref().map_or(0, |t| {
                t.name.capacity()
                    + t.members.capacity() * size_of::<(u64, String)>()
                    + t.members.iter().map(|(_, m)| m.capacity()).sum::<usize>()
            })
        },
    )
}

/// A display name the table-shaped functions go by, as [`called_tables`]
/// finds it in a body.
struct TableName {
    /// The name's bytes, last first: the rows sort by these, so a walk back
    /// from a `(` narrows to the names ending there one byte at a time.
    reversed: Vec<u8>,
    /// The name.
    name: String,
    /// The table-shaped functions going by it, in address order.
    entries: Vec<u64>,
}

/// Lists the display names of the table-shaped functions, sorted by their
/// reversed bytes, for [`called_tables`].
///
/// # Arguments
///
/// * `analysis` - Supplies the functions and their names.
/// * `overlay` - User names, which win.
fn table_names(analysis: &Analysis, overlay: &Overlay) -> Vec<TableName> {
    let mut by_name: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for f in analysis.functions.iter().filter(|f| table_shaped(f)) {
        by_name
            .entry(name_of(analysis, overlay, f.entry))
            .or_default()
            .push(f.entry);
    }
    let mut rows: Vec<TableName> = by_name
        .into_iter()
        .map(|(name, entries)| TableName {
            reversed: name.bytes().rev().collect(),
            name,
            entries,
        })
        .collect();
    rows.sort_unstable_by(|a, b| a.reversed.cmp(&b.reversed));
    rows
}

/// Returns the binary's name tables a body can render constants by: those
/// of the functions whose display name, followed by `(`, occurs in it.
///
/// [`apply_enums`] finds a table's function as `name(` anywhere in a line
/// (a call, or the tail of a longer name), so every name ending right
/// before a `(` is looked up, and where several functions go by one name
/// the last in address order with a table wins, as in [`enums_by_name`].
/// A member name only replaces a constant that a `,`, `)` or `:` follows,
/// so the renaming makes no `name(` the body did not have: the body renders
/// with these tables exactly as with every table of the binary, at the
/// cost of reading only the ones it names ([`table_at`]).
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis, holding the memo.
/// * `overlay` - Names and comments in force; its own tables are ignored.
/// * `body` - The cleaned body text.
///
/// # Returns
///
/// The tables by the display name of the function encoding each, the form
/// [`Overlay::enums`] takes.
pub(super) fn called_tables(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    body: &str,
) -> BTreeMap<String, EnumTable> {
    let plain = overlay.without_tables();
    let key = plain.fingerprint();
    let rows = analysis
        .derived
        .get_or_build_named("enum_table_names", key, (), || {
            table_names(analysis, &plain)
        });
    let bytes = body.as_bytes();
    let mut named: BTreeSet<usize> = BTreeSet::new();
    for (open, _) in bytes.iter().enumerate().filter(|(_, b)| **b == b'(') {
        let mut range = 0..rows.len();
        for depth in 0..=open {
            let span = rows.get(range.clone()).unwrap_or_default();
            let ended = span.partition_point(|r| r.reversed.len() <= depth);
            named.extend(range.start..range.start + ended);
            let Some(&c) = open.checked_sub(depth + 1).and_then(|i| bytes.get(i)) else {
                break;
            };
            let lo = span.partition_point(|r| r.reversed.get(depth) < Some(&c));
            let hi = span.partition_point(|r| r.reversed.get(depth) <= Some(&c));
            range = range.start + lo..range.start + hi;
            if range.is_empty() {
                break;
            }
        }
    }
    named
        .into_iter()
        .filter_map(|i| rows.get(i))
        .filter_map(|row| {
            let table = row.entries.iter().rev().find_map(|&entry| {
                table_at(program, analysis, &plain, key, entry)
                    .as_ref()
                    .clone()
            })?;
            Some((row.name.clone(), table))
        })
        .collect()
}

/// Recovers the name table a compare ladder or a constant-to-string chain
/// encodes.
///
/// Two shapes, each read off the cleaned body: `v = f(x, "LIT"); if (v != 0)
/// { return K; }` repeated with one comparator `f` (or, for a ladder's last
/// level, `if (v == 0) { return d; } return K;`; either with the call in
/// the condition, `if (f(x, "LIT") != 0)`) maps strings to constants
/// (a parser); `if (v == K) { return "LIT"; }` or `... { t =
/// "LIT"; }` arms, as a run or an `else if` chain (and `case K:` labels,
/// a last level inverted to `if (v != K) { return d; } return "LIT";`, and
/// `if (v != K) { ... } else { t = "LIT"; }` at any nesting, the `else`
/// naming `K` whatever the `if` holds), map constants to strings (a
/// `ToString`). A pair the body repeats counts
/// once; three pairs make a table. The
/// table takes its name from the tested parameter's declared type when the
/// signature has one that is not a plain integer, else from the comparator
/// or the variable.
///
/// # Arguments
///
/// * `body` - The cleaned body text.
/// * `params` - The signature's parameters as `type name` strings.
///
/// # Returns
///
/// The table, or `None` when the body encodes none.
pub fn enum_table(body: &str, params: &[String]) -> Option<EnumTable> {
    /// Fewest pairs that make a table.
    const MIN_MEMBERS: usize = 3;
    let raw: Vec<&str> = body.lines().collect();
    let indents: Vec<usize> = raw.iter().map(|l| indent_of(l)).collect();
    let lines: Vec<&str> = raw.iter().map(|l| l.trim()).collect();
    let mut forward: Vec<(u64, String)> = Vec::new();
    let mut comparator: Option<String> = None;
    let mut reverse: Vec<(u64, String)> = Vec::new();
    let mut tested: Option<String> = None;
    for (i, line) in lines.iter().enumerate() {
        let next = |k: usize| lines.get(i + k).copied().unwrap_or("");
        let assigned = || {
            let (var, call) = line.split_once(" = ")?;
            let test = |op: &str| next(1) == format!("if ({var} {op} 0) {{");
            let unequal = if test("!=") {
                true
            } else if test("==") {
                false
            } else {
                return None;
            };
            Some((call.strip_suffix(';')?, unequal, 1))
        };
        let in_test = || {
            let cond = line.strip_prefix("if (")?.strip_suffix(") {")?;
            match cond.strip_suffix(" != 0") {
                Some(call) => Some((call, true, 0)),
                None => Some((cond.strip_suffix(" == 0")?, false, 0)),
            }
        };
        if let Some((call, unequal, o)) = assigned().or_else(in_test)
            && let Some(args) = call.strip_suffix(')')
            && let Some((callee, args)) = args.split_once('(')
            && let Some((_, lit)) = args.rsplit_once(", ")
            && let Some(lit) = literal_of(lit)
            && comparator.as_deref().is_none_or(|c| c == callee)
        {
            let ret = |l: &str| {
                l.strip_prefix("return ")
                    .and_then(|r| r.strip_suffix(';'))
                    .and_then(parse_const)
            };
            let hit = if unequal && next(o + 2) == "}" {
                ret(next(o + 1))
            } else if !unequal && ret(next(o + 1)).is_some() && next(o + 2) == "}" {
                ret(next(o + 3))
            } else {
                None
            };
            if let Some(k) = hit {
                comparator = Some(callee.to_owned());
                forward.push((k, lit.to_owned()));
            }
        }
        // `switch (v) {` names the value the `case` lines below test.
        if let Some(v) = switch_opener(line)
            && tested.is_none()
        {
            tested = Some(v.to_owned());
        }
        let arm = guard_opener(line)
            .and_then(|c| c.split_once(" == "))
            .and_then(|(v, k)| parse_const(k).map(|k| (v, k)))
            .or_else(|| {
                line.strip_prefix("case ")
                    .map(|r| r.strip_suffix(" {").unwrap_or(r))
                    .and_then(|r| r.strip_suffix(':'))
                    .and_then(parse_const)
                    .map(|k| ("", k))
            });
        if let Some((var, k)) = arm
            && let Some(lit) = literal_set(next(1))
            && (next(2).starts_with('}') || next(2).starts_with("case ") || next(2) == "break;")
            && (var.is_empty() || tested.as_deref().is_none_or(|t| t == var))
        {
            if !var.is_empty() {
                tested = Some(var.to_owned());
            }
            reverse.push((k, lit.to_owned()));
        }
        if let Some((var, k)) = guard_opener(line)
            .and_then(|c| c.split_once(" != "))
            .and_then(|(v, k)| parse_const(k).map(|k| (v, k)))
            && let Some(else_at) = raw
                .get(i + 1..)
                .and_then(|rest| {
                    rest.iter()
                        .position(|l| indent_of(l) == indents[i] && l.trim() == "} else {")
                })
                .map(|pos| i + 1 + pos)
            && next(else_at - i + 2) == "}"
            && let Some(lit) = literal_set(next(else_at - i + 1))
            && tested.as_deref().is_none_or(|t| t == var)
        {
            tested = Some(var.to_owned());
            reverse.push((k, lit.to_owned()));
        }
        if let Some((var, k)) = if_opener(line)
            .and_then(|c| c.split_once(" != "))
            .and_then(|(v, k)| parse_const(k).map(|k| (v, k)))
            && next(2) == "}"
            && let Some(lit) = literal_set(next(3))
            && tested.as_deref().is_none_or(|t| t == var)
        {
            tested = Some(var.to_owned());
            reverse.push((k, lit.to_owned()));
        }
    }
    for list in [&mut forward, &mut reverse] {
        let mut seen: BTreeSet<(u64, String)> = BTreeSet::new();
        list.retain(|pair| seen.insert(pair.clone()));
    }
    let (members, name) = if forward.len() >= reverse.len() {
        (forward, comparator.map(|c| format!("by {c} compare")))
    } else {
        let typed = tested.as_deref().and_then(|v| {
            params
                .iter()
                .find_map(|p| p.strip_suffix(v).map(str::trim))
                .filter(|t| !t.is_empty() && !t.starts_with("uint") && !t.starts_with("int"))
                .map(|t| t.trim_end_matches('*').trim().to_owned())
        });
        (
            reverse,
            typed.or_else(|| tested.as_ref().map(|v| format!("values of {v}"))),
        )
    };
    // INVARIANT: a name table maps names to distinct values; one value
    // under every name is a flag tested the same way in every arm, and its
    // "members" are the other branch's literals.
    let distinct: BTreeSet<u64> = members.iter().map(|(k, _)| *k).collect();
    if members.len() < MIN_MEMBERS || distinct.len() < 2 {
        return None;
    }
    let param = tested
        .as_deref()
        .and_then(|v| v.strip_prefix('a'))
        .and_then(|n| n.parse::<usize>().ok())
        .and_then(|n| n.checked_sub(1));
    Some(EnumTable {
        name: name.unwrap_or_default(),
        members,
        param,
    })
}

/// The name literal a `return "LIT";` or `v = "LIT";` statement sets.
///
/// # Arguments
///
/// * `stmt` - The trimmed statement.
fn literal_set(stmt: &str) -> Option<&str> {
    stmt.strip_prefix("return ")
        .or_else(|| stmt.split_once(" = ").map(|(_, r)| r))
        .and_then(|r| r.strip_suffix(';'))
        .and_then(literal_of)
}

/// Renders constants by their member names wherever a body compares a
/// parser's result or passes a constant to a name table.
///
/// A parser's result (`v = T(...)`) carries `T`'s table until `v` is
/// assigned again: `v == K`, `v != K` and the `case K:` lines of a
/// `switch (v)` name the member. A constant-to-string table names the
/// constant passed at its tested parameter (`T(x, K)`). Only a constant the
/// table has a member for changes.
///
/// # Arguments
///
/// * `body` - The cleaned body text.
/// * `enums` - Tables by the display name of the function encoding each.
///
/// # Returns
///
/// The body with member names in place of the constants.
pub fn apply_enums(body: &str, enums: &BTreeMap<String, EnumTable>) -> String {
    if enums.is_empty() {
        return body.to_owned();
    }
    let mut carriers: BTreeMap<String, &EnumTable> = BTreeMap::new();
    let mut switches: Vec<(usize, &EnumTable)> = Vec::new();
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        let t = line.trim();
        let ind = indent_of(line);
        let mut text = line.to_owned();
        switches.retain(|(depth, _)| *depth < ind || t != "}");
        if t.starts_with("case ")
            && let Some((_, table)) = switches.last()
            && let Some(k) = t
                .strip_prefix("case ")
                .and_then(|r| r.strip_suffix(':'))
                .and_then(parse_const)
            && let Some(name) = table.member(k)
        {
            text = format!("{}case {name}:", " ".repeat(ind));
        }
        if let Some(inner) = switch_opener(t)
            && let Some(table) = carriers.get(inner.trim())
        {
            switches.push((ind, table));
        }
        for (var, table) in &carriers {
            text = rename_compared(&text, var, table);
        }
        for (callee, table) in enums {
            match table.param {
                Some(pos) => text = rename_argument(&text, callee, pos, table),
                None => {
                    text =
                        rename_call_compared(&text, callee, |k| table.member(k).map(str::to_owned));
                }
            }
        }
        if let Some((lhs, rhs)) = t.split_once(" = ")
            && is_ident(lhs)
        {
            match rhs
                .split_once('(')
                .and_then(|(callee, _)| enums.get(callee))
                .filter(|table| table.param.is_none())
            {
                Some(table) => {
                    carriers.insert(lhs.to_owned(), table);
                }
                None => {
                    carriers.remove(lhs);
                }
            }
        }
        out.push_str(&text);
        out.push('\n');
    }
    out
}

/// Names the constants a library call's result is compared with
/// (`rax == INVALID_HANDLE_VALUE`, `rax != WAIT_OBJECT_0`), by the group its
/// declaration gives the result ([`crate::analysis::typelib`]).
///
/// A variable assigned such a call's result carries the group until it is
/// assigned again, as a parser's result carries its table in
/// [`apply_enums`]; an `==` or `!=` between it and a number names the
/// number by the group at the result's width, negative numbers included.
///
/// # Arguments
///
/// * `body` - The body text.
/// * `groups` - Callee text to its result's group and width in bits.
///
/// # Returns
///
/// The body with the compared constants named.
pub(super) fn apply_results(body: &str, groups: &BTreeMap<String, (&'static str, u8)>) -> String {
    if groups.is_empty() {
        return body.to_owned();
    }
    let mut carriers: BTreeMap<String, (&crate::analysis::typelib::Group, u8)> = BTreeMap::new();
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        let mut text = line.to_owned();
        for (var, (group, bits)) in &carriers {
            text = rename_against(&text, var, |v| {
                crate::analysis::typelib::render(group, v, *bits)
            });
        }
        for (callee, (g, bits)) in groups {
            if let Some(group) = crate::analysis::typelib::group(g) {
                text = rename_call_compared(&text, callee, |v| {
                    crate::analysis::typelib::render(group, v, *bits)
                });
            }
        }
        let t = line.trim();
        if let Some((lhs, rhs)) = t.split_once(" = ")
            && is_ident(lhs)
        {
            let carried = rhs
                .split_once('(')
                .and_then(|(callee, _)| groups.get(callee))
                .and_then(|(g, bits)| Some((crate::analysis::typelib::group(g)?, *bits)));
            match carried {
                Some(c) => {
                    carriers.insert(lhs.to_owned(), c);
                }
                None => {
                    carriers.remove(lhs);
                }
            }
        }
        out.push_str(&text);
        out.push('\n');
    }
    out
}

/// Names the numbers a call's own result is compared with on one line:
/// `callee(...) == K`, where a condition took the call in rather than
/// assigning its result first.
///
/// # Arguments
///
/// * `line` - The line.
/// * `callee` - The function called.
/// * `name` - Names a value, or says it has no name.
fn rename_call_compared(line: &str, callee: &str, name: impl Fn(u64) -> Option<String>) -> String {
    let mut text = line.to_owned();
    for at in word_positions(line, callee).into_iter().rev() {
        let open = at + callee.len();
        if text.as_bytes().get(open) != Some(&b'(') {
            continue;
        }
        let Some(after) = matching_paren(&text, open).map(|close| close + 1) else {
            continue;
        };
        for op in [" == ", " != "] {
            let Some(rest) = text.get(after..).and_then(|r| r.strip_prefix(op)) else {
                continue;
            };
            let sign = usize::from(rest.starts_with('-'));
            let len = sign
                + rest
                    .get(sign..)
                    .unwrap_or("")
                    .find(|c: char| !c.is_ascii_alphanumeric())
                    .unwrap_or(rest.len() - sign);
            let token = rest.get(..len).unwrap_or("");
            let value = token.strip_prefix('-').map_or_else(
                || parse_const(token),
                |m| parse_const(m).map(u64::wrapping_neg),
            );
            if let Some(named) = value.and_then(&name) {
                let start = after + op.len();
                text.replace_range(start..start + len, &named);
            }
        }
    }
    text
}

/// Names the numbers compared against `var` on one line by `name`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The variable compared.
/// * `name` - Names a value, or says it has no name.
fn rename_against(line: &str, var: &str, name: impl Fn(u64) -> Option<String>) -> String {
    let mut text = line.to_owned();
    for op in [" == ", " != "] {
        let mut from = 0;
        while let Some(at) = text.get(from..).and_then(|rest| rest.find(op)) {
            let at = from + at;
            let left_ok = text.get(..at).is_some_and(|l| {
                l.ends_with(var)
                    && !l
                        .get(..l.len() - var.len())
                        .and_then(|b| b.chars().next_back())
                        .is_some_and(is_ident_char)
            });
            let start = at + op.len();
            let rest = text.get(start..).unwrap_or("");
            let sign = usize::from(rest.starts_with('-'));
            let len = sign
                + rest
                    .get(sign..)
                    .unwrap_or("")
                    .find(|c: char| !c.is_ascii_alphanumeric())
                    .unwrap_or(rest.len() - sign);
            let token = rest.get(..len).unwrap_or("");
            let value = token.strip_prefix('-').map_or_else(
                || parse_const(token),
                |m| parse_const(m).map(u64::wrapping_neg),
            );
            match value.filter(|_| left_ok).and_then(&name) {
                Some(named) => {
                    text.replace_range(start..start + len, &named);
                    from = start + named.len();
                }
                None => from = start,
            }
        }
    }
    text
}

/// Names the constant compared against `var` on one line.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The variable carrying the table.
/// * `table` - Its table.
pub(super) fn rename_compared(line: &str, var: &str, table: &EnumTable) -> String {
    let mut text = line.to_owned();
    for op in [" == ", " != "] {
        let mut from = 0;
        while let Some(at) = text.get(from..).and_then(|rest| rest.find(op)) {
            let at = from + at;
            let left_ok = text
                .get(..at)
                .map(|l| l.trim_end_matches(')'))
                .is_some_and(|l| {
                    l.ends_with(var)
                        && !l
                            .get(..l.len() - var.len())
                            .and_then(|b| b.chars().next_back())
                            .is_some_and(is_ident_char)
                });
            let value_end = text.get(at + op.len()..).map_or(0, |r| {
                at + op.len()
                    + r.find(|c: char| !(c.is_ascii_alphanumeric()))
                        .unwrap_or(r.len())
            });
            let renamed = text
                .get(at + op.len()..value_end)
                .and_then(parse_const)
                .and_then(|k| table.member(k))
                .filter(|_| left_ok)
                .map(str::to_owned);
            match renamed {
                Some(name) => {
                    text.replace_range(at + op.len()..value_end, &name);
                    from = at + op.len() + name.len();
                }
                None => from = at + op.len(),
            }
        }
    }
    text
}

/// Names the constant passed at `pos` in every call of `callee` on one line.
///
/// # Arguments
///
/// * `line` - The line.
/// * `callee` - The table function's display name.
/// * `pos` - The argument position, from zero.
/// * `table` - Its table.
pub(super) fn rename_argument(line: &str, callee: &str, pos: usize, table: &EnumTable) -> String {
    let needle = format!("{callee}(");
    let Some(start) = line.find(&needle) else {
        return line.to_owned();
    };
    let open = start + needle.len();
    let mut depth = 0usize;
    let mut close = None;
    for (i, c) in line.get(open..).unwrap_or("").char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth == 0 => {
                close = Some(open + i);
                break;
            }
            ')' => depth -= 1,
            _ => {}
        }
    }
    let Some(close) = close else {
        return line.to_owned();
    };
    let Some(args) = line.get(open..close) else {
        return line.to_owned();
    };
    let mut parts: Vec<String> = split_arguments(args)
        .into_iter()
        .map(str::to_owned)
        .collect();
    let renamed = parts
        .get(pos)
        .and_then(|a| parse_const(a))
        .and_then(|k| table.member(k))
        .map(str::to_owned);
    match (renamed, parts.get_mut(pos)) {
        (Some(name), Some(slot)) => {
            *slot = name;
            format!(
                "{}{}{}",
                line.get(..open).unwrap_or(""),
                parts.join(", "),
                line.get(close..).unwrap_or("")
            )
        }
        _ => line.to_owned(),
    }
}

/// Keys a set of tables by the display name of the function encoding each,
/// the form [`Overlay::enums`] takes.
///
/// # Arguments
///
/// * `analysis` - Supplies function names.
/// * `overlay` - User names, which win.
/// * `tables` - Output of [`enum_tables`].
pub fn enums_by_name(
    analysis: &Analysis,
    overlay: &Overlay,
    tables: &[(u64, EnumTable)],
) -> BTreeMap<String, EnumTable> {
    tables
        .iter()
        .map(|(entry, table)| (name_of(analysis, overlay, *entry), table.clone()))
        .collect()
}

/// The user-applied enums of a function: the variable each enum-typed
/// global renders as, with the table of the enum its applied type states.
///
/// A global is enum-typed when [`Overlay::applied`] states a type at its
/// address that names a user enum (through aliases, not pointers), and the
/// function reads it at exactly the enum's width: a compare the load does
/// not explain stays as it was, since renaming its constant would state a
/// width the enum does not. The same global read at two widths keeps one
/// entry, the width that matches.
///
/// A global whose applied type points at a user struct contributes one
/// entry per enum-typed field, keyed by the access the typed-field pass
/// ([`super::fields::rename_typed`]) renders, `v->state`, so the same
/// naming below reaches a field through a pointer. No width is checked
/// here: the field access only renders under that name once the load
/// matched the field's stated width, so a compare at the wrong width never
/// meets the key and stays as it was.
///
/// # Arguments
///
/// * `overlay` - The user types and applications.
/// * `globals` - The absolute accesses the function hoisted to globals.
/// * `names` - The name resolver, for each global's rendered variable.
///
/// # Returns
///
/// The enum table by the variable each typed global renders as, and by the
/// named access of each enum-typed field of a struct-typed one.
pub(super) fn user_enum_globals(
    overlay: &Overlay,
    globals: &BTreeSet<(u64, Ty)>,
    names: &Names<'_>,
) -> BTreeMap<String, EnumTable> {
    let mut out: BTreeMap<String, EnumTable> = BTreeMap::new();
    for &(addr, ty) in globals {
        let Some(expr) = overlay.applied.get(&addr) else {
            continue;
        };
        let table_of = |ty: &crate::analysis::utypes::TypeExpr,
                        e: &crate::analysis::utypes::UserEnum| {
            EnumTable {
                name: ty.spell(),
                members: e.values.clone(),
                param: None,
            }
        };
        if let Some(e) = crate::analysis::utypes::named_enum(&overlay.types, expr)
            && u64::from(ty.bits()) == e.size * 8
        {
            let key = names.key(Key::Global(addr, ty.bits()));
            out.entry(key).or_insert_with(|| table_of(expr, e));
        }
        let Some(s) = crate::analysis::utypes::pointee_struct(&overlay.types, expr) else {
            continue;
        };
        for f in s.fields.values() {
            let Some(e) = crate::analysis::utypes::named_enum(&overlay.types, &f.ty) else {
                continue;
            };
            let key = format!("{}->{}", names.key(Key::Global(addr, ty.bits())), f.name);
            out.entry(key).or_insert_with(|| table_of(&f.ty, e));
        }
    }
    out
}

/// Renders constants compared against a user-enum-typed global by their
/// member names ([`user_enum_globals`]).
///
/// The same shapes [`apply_enums`] renames for the binary's tables, with the
/// table's carrier stated by the user instead of recovered from a call: the
/// global's own variable, an enum-typed field's access (`v->state`), a
/// `switch` over either, and a local it moves through (`v = g;`) all name
/// their constants, until the local is assigned something else. No call
/// arguments are renamed: a user enum types a value, not a parameter.
///
/// # Arguments
///
/// * `body` - The cleaned body text.
/// * `enums` - The tables of [`user_enum_globals`].
///
/// # Returns
///
/// The body with member names in place of the constants.
pub(super) fn apply_user_enums(body: &str, enums: &BTreeMap<String, EnumTable>) -> String {
    let mut carriers: BTreeMap<String, &EnumTable> = BTreeMap::new();
    let mut switches: Vec<(usize, &EnumTable)> = Vec::new();
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        let t = line.trim();
        let ind = indent_of(line);
        let mut text = line.to_owned();
        switches.retain(|(depth, _)| *depth < ind || t != "}");
        if t.starts_with("case ")
            && let Some((_, table)) = switches.last()
            && let Some(k) = t
                .strip_prefix("case ")
                .and_then(|r| r.strip_suffix(':'))
                .and_then(parse_const)
            && let Some(name) = table.member(k)
        {
            text = format!("{}case {name}:", " ".repeat(ind));
        }
        if let Some(inner) = switch_opener(t)
            && let Some(table) = enums
                .get(inner.trim())
                .or_else(|| carriers.get(inner.trim()).copied())
        {
            switches.push((ind, table));
        }
        for (var, table) in enums.iter().chain(carriers.iter().map(|(v, t)| (v, *t))) {
            text = rename_compared(&text, var, table);
        }
        if let Some((lhs, rhs)) = t.strip_suffix(';').and_then(|s| s.split_once(" = "))
            && is_ident(lhs)
        {
            match enums.get(rhs.trim()) {
                Some(table) => {
                    carriers.insert(lhs.to_owned(), table);
                }
                None => {
                    carriers.remove(lhs);
                }
            }
        }
        out.push_str(&text);
        out.push('\n');
    }
    out
}
