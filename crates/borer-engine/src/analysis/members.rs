//! The members of `this` an assertion spells, and the one field a guarded
//! assert ties one of them to.
//!
//! This is the reading [`super::classes`] names fields with and
//! `borer://asserts` pairs members with offsets from.

use std::collections::{BTreeMap, BTreeSet};

use super::classes::{FieldUse, parse_number};
use super::{Analysis, naming, single};
use crate::program::Program;

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

/// How a condition spells the members of `this` it names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Receiver {
    /// After `this->`: members of `this` for certain.
    This,
    /// Bare (`!m_stop`, `m_items.size()`): member candidates, which a
    /// local or a parameter spells the same way.
    Bare,
}

/// Returns the members a condition names and how it spells them.
///
/// A condition that spells any member after `this->` names those
/// ([`this_members`]); its bare words are its locals and parameters then.
/// One that spells none names its bare candidates: each identifier that
/// is no keyword, literal, call, scope, member of something else, cast
/// type or name in capitals
/// ([`subjects`](crate::analysis::decompile::subjects)), none when the
/// condition calls a free function or runs past [`MEMBER_STRING_CAP`].
///
/// # Arguments
///
/// * `text` - The condition as its bytes hold it, unquoted and unescaped.
///
/// # Returns
///
/// `(member, how)` in the order they appear, and which spelling they are;
/// a bare candidate is never [`Spelled::Called`].
pub(crate) fn condition_members(text: &str) -> (Vec<(String, Spelled)>, Receiver) {
    let this = this_members(text);
    if !this.is_empty() {
        let named = this.into_iter().map(|(m, how)| (m.to_owned(), how));
        return (named.collect(), Receiver::This);
    }
    let bare = (text.len() <= MEMBER_STRING_CAP)
        .then(|| crate::analysis::decompile::subjects(text))
        .flatten()
        .unwrap_or_default()
        .into_iter()
        .filter(|(w, _)| w.chars().any(|c| c.is_ascii_lowercase()))
        .collect();
    (bare, Receiver::Bare)
}

/// Most bytes between the reference to an assert's expression and the
/// references to its source path and its signature: one reporter call's
/// argument set-up.
const ASSERT_CALL_SPAN: u64 = 48;

/// Longest signature literal read when telling an assert call apart.
const SIGNATURE_CAP: usize = 1024;

/// Tells whether a literal names a C or C++ source file: no space, a known
/// extension.
///
/// # Arguments
///
/// * `text` - The literal's text, unquoted.
pub(crate) fn is_source_path(text: &str) -> bool {
    const EXTENSIONS: [&str; 10] = [
        ".h", ".hpp", ".hh", ".hxx", ".inl", ".c", ".cc", ".cpp", ".cxx", ".inc",
    ];
    !text.contains(' ')
        && EXTENSIONS
            .iter()
            .any(|e| text.len() > e.len() && text.ends_with(e))
}

/// Returns the conditions a function passes to an assert reporter, read
/// from its bytes.
///
/// A condition is each literal it references within [`ASSERT_CALL_SPAN`]
/// bytes of both a reference to a source path ([`is_source_path`]) and one
/// to a function signature, the `(expression, file, line, signature)` call
/// GCC's, Clang's and most engines' asserts make.
///
/// # Arguments
///
/// * `program` - The loaded image, read for the strings.
/// * `analysis` - Cross-references.
/// * `entry` - The function.
///
/// # Returns
///
/// `(address, text)` of each condition no longer than
/// [`MEMBER_STRING_CAP`], in reference order, repeats included.
pub(crate) fn assert_conditions(
    program: &Program,
    analysis: &Analysis,
    entry: u64,
) -> Vec<(u64, String)> {
    #[derive(PartialEq)]
    enum Role {
        Path,
        Signature,
        Other,
    }
    let mut lits: Vec<(u64, u64, Role, String)> = analysis
        .refs_from(entry)
        .into_iter()
        .filter(|(t, _)| program.section_at(*t).is_some_and(|s| !s.executable))
        .filter_map(|(t, site)| {
            let (_, text) = crate::strings::cstr_at(program, t, 1, SIGNATURE_CAP)?;
            let role = if is_source_path(&text) {
                Role::Path
            } else if naming::is_signature(&text) {
                Role::Signature
            } else {
                Role::Other
            };
            Some((site.va, t, role, text))
        })
        .collect();
    lits.sort_by_key(|l| l.0);
    let near = |va: u64, role: Role| {
        let from = lits.partition_point(|l| l.0 < va.saturating_sub(ASSERT_CALL_SPAN));
        lits.iter()
            .skip(from)
            .take_while(|l| l.0 <= va.saturating_add(ASSERT_CALL_SPAN))
            .any(|l| l.2 == role)
    };
    lits.iter()
        .filter(|l| l.2 == Role::Other && l.3.len() <= MEMBER_STRING_CAP)
        .filter(|l| near(l.0, Role::Path) && near(l.0, Role::Signature))
        .map(|l| (l.1, l.3.clone()))
        .collect()
}

/// Tells whether a function's asserts can name a member under a spelling.
///
/// It reads the bytes alone: a decompile costs far more than this read,
/// and the classes with the most methods are the ones where that matters.
/// After `this->`, some string it references mentions `this->`; bare,
/// some condition it passes to an assert reporter ([`assert_conditions`])
/// spells a bare candidate ([`condition_members`]).
///
/// # Arguments
///
/// * `program` - The loaded image, read for the strings.
/// * `analysis` - Cross-references.
/// * `entry` - The function's entry address.
/// * `receiver` - The spelling asked about.
pub(crate) fn asserts_a_member(
    program: &Program,
    analysis: &Analysis,
    entry: u64,
    receiver: Receiver,
) -> bool {
    match receiver {
        Receiver::This => analysis.refs_from(entry).iter().any(|&(target, _)| {
            program
                .section_at(target)
                .is_some_and(|s| !s.executable)
                .then(|| crate::strings::cstr_at(program, target, 4, MEMBER_STRING_CAP))
                .flatten()
                .is_some_and(|(_, t)| t.contains("this->"))
        }),
        Receiver::Bare => assert_conditions(program, analysis, entry).iter().any(
            |(_, text)| matches!(condition_members(text), (m, Receiver::Bare) if !m.is_empty()),
        ),
    }
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

/// Returns the votes of a function's guarded asserts
/// ([`collect_assert_names`]) by offset, in [`FieldUse::names`].
///
/// # Arguments
///
/// * `text` - The function's decompiled text.
/// * `receiver` - The spelling read; a condition spelled the other way
///   votes nothing.
/// * `class` - The function's class, which an inlined assert's signature
///   must name ([`own_signature`]).
pub(crate) fn votes_in(
    text: &str,
    receiver: Receiver,
    class: Option<&str>,
) -> BTreeMap<u64, FieldUse> {
    let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
    let mut prev = "";
    for line in text.lines() {
        collect_assert_names(prev, line.trim(), receiver, class, &mut fields);
        prev = line.trim();
    }
    fields
}

/// Tells whether an assert call's signature is its function's own or that
/// of a method of its function's class, so the members it names are of a
/// `this` its guard can read.
///
/// An assert inlined from another class's method (`__FUNCSIG__(B::Get)` in
/// a method of `A`) names `B`'s members, and its guard reads whatever `A`
/// holds there.
///
/// # Arguments
///
/// * `call` - The call line.
/// * `class` - The function's class.
fn own_signature(call: &str, class: Option<&str>) -> bool {
    let Some((_, rest)) = call.split_once("__FUNCSIG__") else {
        return false;
    };
    let Some(named) = rest.strip_prefix('(') else {
        return true;
    };
    let name = named.split_once(')').map_or(named, |(n, _)| n);
    class.is_some_and(|c| super::classes::class_of(name) == Some(c))
}

/// Names a field from a guarded assert.
///
/// `if (COND) {` followed by `helper("EXPR", ..., __FUNCSIG__...);` ties the
/// one field `COND` reads directly (`(this + off)`, [`read_directly`]) to
/// the one member `EXPR` names ([`condition_members`]), the way `if
/// (*(uint32_t*)(this + 0x38) < 0) { n_assert("i <= this->strLen") }`
/// names `Util::String`'s field 0x38 `strLen`. A getter votes as
/// `IsSet()`. Anything with several fields or several members is skipped,
/// and so is a member reached into (`this->m_rect.w`), an expression the
/// text cut ([`first_literal`]), one spelled other than `receiver`, a
/// bare one whose call cites no source file, and one inlined from another
/// class's method ([`own_signature`]).
///
/// # Arguments
///
/// * `guard` - The previous line.
/// * `call` - The current line.
/// * `receiver` - The spelling read.
/// * `class` - The function's class.
/// * `fields` - Field uses; the vote lands on the field's offset.
fn collect_assert_names(
    guard: &str,
    call: &str,
    receiver: Receiver,
    class: Option<&str>,
    fields: &mut BTreeMap<u64, FieldUse>,
) {
    if !(guard.starts_with("if (") && guard.ends_with('{') && own_signature(call, class)) {
        return;
    }
    let Some(expr) = first_literal(call) else {
        return;
    };
    let (named, how) = condition_members(&expr);
    let cites = || call.split('"').skip(3).step_by(2).any(is_source_path);
    if how != receiver || (how == Receiver::Bare && !cites()) {
        return;
    }
    let members: BTreeSet<String> = named
        .into_iter()
        .map(|(member, how)| match how {
            Spelled::Member => member,
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
    use super::{
        BTreeMap, Receiver, Spelled, collect_assert_names, condition_members, first_literal,
        this_members, votes_in,
    };

    /// Returns the members a condition names, a reached-into one ending
    /// in `.`, and which spelling they are.
    fn named(text: &str) -> (Vec<String>, Receiver) {
        let (members, how) = condition_members(text);
        let shown = members.into_iter().map(|(m, s)| match s {
            Spelled::Member => m,
            Spelled::Called => format!("{m}()"),
            Spelled::Sub => format!("{m}."),
        });
        (shown.collect(), how)
    }

    /// A condition with no `this->` names its bare candidates.
    ///
    /// That is no keyword, call, scope, member of another, cast type or
    /// capitals, and none at all past a free call or the cap; one with
    /// `this->` names only those.
    #[test]
    fn bare_candidates_are_identifiers_used_as_values() {
        assert_eq!(
            named("!m_stop"),
            (vec!["m_stop".to_owned()], Receiver::Bare)
        );
        assert_eq!(
            named("index >= 0 && index < (int)m_replicas.size()").0,
            ["index", "m_replicas."]
        );
        assert_eq!(named("m_a.size() == m_b.size()").0, ["m_a.", "m_b."]);
        assert_eq!(named("p->x && q[2] && (Foo *)r").0, ["p.", "q.", "r"]);
        assert_eq!(named("n < MAX_N && n != SIZE2 && ns::k && T").0, ["n"]);
        assert_eq!(named("m_x && m_x.y").0, ["m_x."]);
        assert!(named("false && \"no member here\" && nullptr").0.is_empty());
        assert!(named("IsValid(m_x)").0.is_empty());
        assert_eq!(
            named("i <= this->strLen"),
            (vec!["strLen".to_owned()], Receiver::This)
        );
        let far = format!("{}m_far", "x && ".repeat(40));
        assert!(named(&far).0.is_empty());
    }

    /// A bare condition votes only where it was asked for, only from a
    /// call that cites its source file, and only with one candidate.
    #[test]
    fn a_bare_condition_votes_once_alone() {
        let assert = |cond: &str, path: &str| {
            format!(
                "if (*(uint8_t*)(this + 0x20) == 0) {{\nf(\"{cond}\", \"{path}\", 1, __FUNCSIG__);\n"
            )
        };
        let text = assert("!m_stop", "src/a.cpp");
        assert!(votes_in(&text, Receiver::This, None).is_empty());
        let votes = votes_in(&text, Receiver::Bare, None);
        let names = votes
            .get(&0x20)
            .map(|f| f.names.keys().cloned().collect::<Vec<_>>());
        assert_eq!(names, Some(vec!["m_stop".to_owned()]));
        for (cond, path) in [
            ("!m_stop", "a message"),
            ("index < m_count", "src/a.cpp"),
            ("m_items.size()", "src/a.cpp"),
            ("this->m_stop", "src/a.cpp"),
        ] {
            let text = assert(cond, path);
            assert!(votes_in(&text, Receiver::Bare, None).is_empty(), "{cond}");
        }
    }

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
            Receiver::This,
            None,
            &mut fields,
        );
        collect_assert_names(
            direct,
            "f(\"this->m_rect.w > 0\", \"a.cc\", 1, __FUNCSIG__);",
            Receiver::This,
            None,
            &mut fields,
        );
        collect_assert_names(
            direct,
            r#"f("this->m_key == \"\" || this->m_val", "a.cc", 1, __FUNCSIG__);"#,
            Receiver::This,
            None,
            &mut fields,
        );
        assert!(fields.is_empty(), "{fields:?}");
        collect_assert_names(direct, call, Receiver::This, None, &mut fields);
        assert_eq!(fields.get(&0x40).map(|f| f.names.len()), Some(1));
    }

    /// A quote in a template signature's bindings stays inside its literal.
    ///
    /// The line's first literal is that signature, skipped for its quote,
    /// not the text between it and the condition (`'>]), `).
    #[test]
    fn a_quote_in_template_bindings_stays_in_its_literal() {
        use crate::program::{Arch, Program, Section};
        let rdata = Section::mapped(".rdata", 0x2000, 0, 0x28, false, false);
        let mut bytes = b"void A<S>::f() [with S = Str<'\"'>]".to_vec();
        bytes.resize(0x28, 0);
        let p = Program::raw(bytes, Arch::X86_64, 0, None, vec![rdata]);
        let shown = crate::analysis::decompile::literal_at(&p, 0x2000, "sub_1000");
        let line = format!("f({}, \"this->m_count\");", shown.unwrap_or_default());
        assert_eq!(first_literal(&line), None, "{line}");
    }

    /// An assert inlined from another class's method votes for none of the
    /// caller's fields; its own and its class's methods' asserts do.
    #[test]
    fn an_inlined_assert_votes_only_for_its_own_class() {
        let votes = |sig: &str, class: Option<&str>| {
            let text = format!(
                "if (*(uint32_t*)(this + 0x38) == 0) {{\nf(\"this->m_owner\", \"a.cc\", 1, {sig});\n"
            );
            votes_in(&text, Receiver::This, class).len()
        };
        assert_eq!(votes("__FUNCSIG__(B::Get)", Some("A")), 0);
        assert_eq!(votes("__FUNCSIG__(B::Get)", None), 0);
        assert_eq!(votes("__FUNCSIG__(ns::A::Get)", Some("A")), 0);
        assert_eq!(votes("__FUNCSIG__(A::Get)", Some("A")), 1);
        assert_eq!(votes("__FUNCSIG__", Some("A")), 1);
        assert_eq!(votes("__FUNCSIG__", None), 1);
    }
}
