//! The members of `this` an assertion spells, and the one field a guarded
//! assert ties one of them to.
//!
//! This is the reading [`super::classes`] names fields with and
//! `borer://asserts` pairs members with offsets from.

use std::collections::{BTreeMap, BTreeSet};

use super::classes::{FieldUse, parse_number};
use super::single;

/// Longest assert condition read when looking for a member to pair, in
/// characters: a member spelled past it is not paired.
pub(crate) const MEMBER_STRING_CAP: usize = 160;

/// Returns the members asserted at more than one offset.
///
/// A member whose guards read 0x10 in one method and 0x18 in another is
/// at one of them at most; naming both would print it twice, and choosing
/// one would resolve what `borer://asserts` lists as contested. Neither
/// offset takes its name. Getter votes (`IsSet()`) name no field and are
/// not counted.
///
/// # Arguments
///
/// * `fields` - The class's field uses by offset, its own and its
///   siblings'.
pub(crate) fn spread_members<'a>(
    fields: impl Iterator<Item = (&'a u64, &'a FieldUse)>,
) -> BTreeSet<String> {
    let mut at: BTreeMap<&str, BTreeSet<u64>> = BTreeMap::new();
    for (off, u) in fields {
        for member in u.names.keys().filter(|n| !n.ends_with(')')) {
            at.entry(member).or_default().insert(*off);
        }
    }
    at.into_iter()
        .filter(|(_, offs)| offs.len() > 1)
        .map(|(member, _)| member.to_owned())
        .collect()
}

/// How a condition spells a member of `this`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Spelled {
    /// Read as a value (`this->m_name`): the field itself.
    Member,
    /// Called (`this->IsSet()`): a getter, not a member.
    Called,
    /// Reached into (`this->m_rect.w`, `this->m_items[2]`,
    /// `this->m_owner->id`): the member holds what the condition reads, so
    /// a guard's field may be a part of it, not it.
    Sub,
}

/// Returns every member of `this` a condition spells, each with how.
///
/// Only the first [`MEMBER_STRING_CAP`] characters are read, and a name
/// must end inside them and not at a cut (`this->m_na...`): a member cut
/// short would be a name the source never had.
///
/// # Arguments
///
/// * `text` - The condition as its bytes hold it, unquoted and unescaped.
///
/// # Returns
///
/// `(member, how)` in the order they appear.
pub(crate) fn this_members(text: &str) -> Vec<(&str, Spelled)> {
    let shown = text.get(..MEMBER_STRING_CAP.min(text.len())).unwrap_or("");
    shown
        .match_indices("this->")
        .filter_map(|(at, _)| {
            let start = at + 6;
            let rest = shown.get(start..)?;
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            let after = text.get(start + end..)?;
            let whole = start + end < shown.len() || shown.len() == text.len();
            let how = if after.starts_with('(') {
                Spelled::Called
            } else if after.starts_with(['.', '[']) || after.starts_with("->") {
                Spelled::Sub
            } else {
                Spelled::Member
            };
            (end > 0 && whole && after != "...").then(|| (rest.get(..end).unwrap_or(""), how))
        })
        .collect()
}

/// Returns the text of the first string literal on a decompiled line, its
/// escapes undone, so a condition reads as its bytes do.
///
/// # Arguments
///
/// * `line` - The line.
///
/// # Returns
///
/// The text, or `None` when the line holds no whole literal, one holding
/// a quote (the catalog reads the bytes and this the rendering, and on a
/// quote the two once split a condition apart), or one the renderer cut
/// (`..."`), which may have dropped a member.
fn first_literal(line: &str) -> Option<String> {
    let (_, rest) = line.split_once('"')?;
    let mut out = String::new();
    let mut chars = rest.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next()? {
                '"' => return None,
                escaped => out.push(escaped),
            },
            '"' => return (!out.ends_with("...")).then_some(out),
            other => out.push(other),
        }
    }
    None
}

/// Tells whether the `(this + N)` at byte `at` of a guard reads the field
/// itself, not a pointer the field holds.
///
/// That is, it sits inside no operand of a dereference
/// (`*(T*)(*(uint64_t*)(this + 0x40) + 8)` reads a field of what +0x40 points
/// at).
///
/// # Arguments
///
/// * `guard` - The `if (...) {` line.
/// * `at` - Where `(this + ` starts in it.
fn read_directly(guard: &str, at: usize) -> bool {
    let mut open: Vec<usize> = Vec::new();
    for (i, c) in guard.char_indices().take_while(|(i, _)| *i < at) {
        match c {
            '(' => open.push(i),
            ')' => {
                open.pop();
            }
            _ => {}
        }
    }
    !open.iter().any(|&j| {
        guard
            .get(..j)
            .is_some_and(|head| head.trim_end().ends_with("*)"))
    })
}

/// Names a field from a guarded assert.
///
/// `if (COND) {` followed by `helper("EXPR", ..., __FUNCSIG__...);` ties the
/// one field `COND` reads directly (`(this + off)`, [`read_directly`]) to
/// the one `this->member` `EXPR` spells ([`this_members`]), the way `if
/// (*(uint32_t*)(this + 0x38) < 0) { n_assert("i <= this->strLen") }`
/// names `Util::String`'s field 0x38 `strLen`. A getter votes as
/// `IsSet()`. Anything with several fields or several members is skipped,
/// and so is a member reached into (`this->m_rect.w`) and an expression
/// the text cut ([`first_literal`]).
///
/// # Arguments
///
/// * `guard` - The previous line.
/// * `call` - The current line.
/// * `fields` - Field uses; the vote lands on the field's offset.
pub(crate) fn collect_assert_names(guard: &str, call: &str, fields: &mut BTreeMap<u64, FieldUse>) {
    if !(guard.starts_with("if (") && guard.ends_with('{') && call.contains("__FUNCSIG__")) {
        return;
    }
    let Some(expr) = first_literal(call) else {
        return;
    };
    let members: BTreeSet<String> = this_members(&expr)
        .into_iter()
        .map(|(member, how)| match how {
            Spelled::Member => member.to_owned(),
            Spelled::Called => format!("{member}()"),
            Spelled::Sub => format!("{member}."),
        })
        .collect();
    let offsets: BTreeSet<u64> = guard
        .match_indices("(this + ")
        .filter(|(at, _)| read_directly(guard, *at))
        .filter_map(|(at, _)| {
            let rest = guard.get(at + 8..)?;
            let end = rest.find(')')?;
            parse_number(rest.get(..end)?).map(|(v, _)| v)
        })
        .collect();
    let (Some(member), Some(off)) = (single(&members), single(&offsets)) else {
        return;
    };
    if member.ends_with('.') {
        return;
    }
    *fields
        .entry(*off)
        .or_default()
        .names
        .entry(member.clone())
        .or_insert(0) += 1;
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{BTreeMap, Spelled, collect_assert_names, first_literal, this_members};

    /// A member is read with how it is spelled, and one cut short or past
    /// the cap is not read at all.
    #[test]
    fn members_are_whole_names() {
        assert_eq!(
            this_members("this->m_a < this->IsSet() && this->m_r.w && this->m_v[1]"),
            [
                ("m_a", Spelled::Member),
                ("IsSet", Spelled::Called),
                ("m_r", Spelled::Sub),
                ("m_v", Spelled::Sub)
            ]
        );
        assert_eq!(this_members("this->m_name"), [("m_name", Spelled::Member)]);
        assert_eq!(this_members("this->m_p->id"), [("m_p", Spelled::Sub)]);
        assert!(this_members("this->m_na...").is_empty());
        let far = format!("{}this->m_far", "x".repeat(200));
        assert!(this_members(&far).is_empty());
    }

    /// A literal reads as its bytes do, and one holding a quote or cut by
    /// the text is not read.
    #[test]
    fn a_literal_is_read_unescaped_and_whole() {
        assert_eq!(
            first_literal(r#"f("a\\b && this->m_x", "a.cc");"#).as_deref(),
            Some(r"a\b && this->m_x")
        );
        assert_eq!(
            first_literal(r#"f("this->m_key == \"\" || this->m_val", "a.cc");"#),
            None
        );
        assert_eq!(first_literal(r#"f("this->m_na...", "a.cc");"#), None);
        assert_eq!(first_literal("f(1);"), None);
    }

    /// A guard that reads a field of what a field points at names neither
    /// field, a member reached into names none, and an expression holding
    /// a quote names none.
    #[test]
    fn only_a_field_read_directly_is_named() {
        let call = "f(\"this->m_size\", \"a.cc\", 1, __FUNCSIG__);";
        let direct = "if (*(uint32_t*)(this + 0x40) == 0) {";
        let mut fields = BTreeMap::new();
        collect_assert_names(
            "if (*(uint32_t*)(*(uint64_t*)(this + 0x40) + 8) == 0) {",
            call,
            &mut fields,
        );
        collect_assert_names(
            direct,
            "f(\"this->m_rect.w > 0\", \"a.cc\", 1, __FUNCSIG__);",
            &mut fields,
        );
        collect_assert_names(
            direct,
            r#"f("this->m_key == \"\" || this->m_val", "a.cc", 1, __FUNCSIG__);"#,
            &mut fields,
        );
        assert!(fields.is_empty(), "{fields:?}");
        collect_assert_names(direct, call, &mut fields);
        assert_eq!(fields.get(&0x40).map(|f| f.names.len()), Some(1));
    }
}
