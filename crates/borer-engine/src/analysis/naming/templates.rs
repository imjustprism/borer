//! Which functions' template signatures a function's code references.
//!
//! `__PRETTY_FUNCTION__` in a template spells its bindings after the
//! signature: GCC as `void Box<T>::Grow() [with T = int]`, Clang as `void
//! Box<int>::Grow() [T = int]`. A function whose code references such a
//! string is the named function's own body, code inlined from it, or code
//! handed the string, and the bytes cannot tell which: an inliner reads the string
//! exactly as the body does, and constant propagation can hand it to a
//! callee that is neither (a `report(__PRETTY_FUNCTION__)` helper left as
//! the string's only referrer). So the string names nothing: it gives a
//! line saying whose signature the function references
//! ([`referenced_signatures`]), and no name, signature or class.
//!
//! A string counts when the function references its first byte, it ends
//! within [`SCAN_MAX`] bytes, and it parses: bindings with no duplicate,
//! no empty side and no GCC pack, after a head that declares a function
//! (the guard plain signatures pass, [`super::declares`], a bound
//! parameter counting as a type), and that no compiler would write
//! ([`super::hand_written`]: a return type of prose or a label ending in
//! `:`, a printf conversion in the parameters or the bindings).
//! The name substitutes GCC's bindings into the qualifier's template
//! arguments (`Box<int>::Grow`) in one pass that never reads what it
//! wrote; Clang's is already instantiated and is kept as spelled. It is at
//! most [`NAME_MAX`] bytes of `A-Za-z0-9_:<>,*& ~-` and an operator's
//! symbol, with no comment mark and no control token, or the string gives
//! no line (its literal still prints whole in the text). The one case it
//! cannot tell: a hand-written literal spelled exactly like a template
//! signature.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::{
    NAME_MAX, bindings_open, declares, hand_written, in_data, last_token, split_outside,
    split_signature, strip_keywords,
};
use crate::analysis::classes::class_of;
use crate::analysis::schema::ident_char;
use crate::analysis::{Analysis, RefKind, striped};
use crate::program::Program;
use crate::strings::{SCAN_MAX, printable};

/// Most names [`referenced_signatures`] lists for one function.
const SHOWN: usize = 8;

/// The template signatures one function's code references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Referenced {
    /// Up to [`SHOWN`] lines, in string address order, a name listed once
    /// at its first string: `Box<int>::Check (string at 0x2000; its own
    /// body, code inlined from it, or code handed the string)`.
    pub lines: Vec<String>,
    /// How many distinct names the function's strings give, listed or not.
    pub total: usize,
}

impl Referenced {
    /// Returns `showing 8 of 10` when more names were found than listed.
    #[must_use]
    pub fn showing(&self) -> Option<String> {
        (self.total > self.lines.len())
            .then(|| format!("showing {} of {}", self.lines.len(), self.total))
    }
}

/// Returns whose template signatures the function at `entry` references.
///
/// Every string of the program is read and parsed once, on the first ask,
/// into one map of the template signatures it holds ([`signatures`]); a
/// function's references to data are then looked up in it.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Its analysis, holding the references and the memo.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The lines and the count, both empty when the function references no
/// template signature.
#[must_use]
pub fn referenced_signatures(program: &Program, analysis: &Analysis, entry: u64) -> Referenced {
    let all = signatures(program, analysis);
    let targets: BTreeSet<u64> = analysis
        .refs_from(entry)
        .into_iter()
        .filter(|(_, s)| s.kind == RefKind::Data)
        .map(|(t, _)| t)
        .collect();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut lines = Vec::new();
    for (t, name) in targets.iter().filter_map(|t| all.get_key_value(t)) {
        if seen.insert(name) && lines.len() < SHOWN {
            lines.push(format!(
                "{name} (string at {t:#x}; its own body, code inlined from it, or code handed the string)"
            ));
        }
    }
    Referenced {
        lines,
        total: seen.len(),
    }
}

/// Returns the template signatures the program's code references, by the
/// string's address, read once per analysis through `analysis.derived`.
///
/// One cell holds the map, which keeps only the strings that parse: at
/// most one name of [`NAME_MAX`] bytes per referenced address. A
/// reference to code, or to memory that is not readable data, is skipped
/// before any read.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Its analysis, holding the references and the memo.
fn signatures(program: &Program, analysis: &Analysis) -> Arc<BTreeMap<u64, String>> {
    analysis
        .derived
        .get_or_build("template_signatures", (), || {
            let targets: Vec<u64> = analysis
                .xrefs
                .keys()
                .copied()
                .filter(|&t| in_data(program, t))
                .collect();
            let names = striped(&targets, |&t| read(program, t));
            targets
                .into_iter()
                .zip(names)
                .filter_map(|(t, name)| Some((t, name?)))
                .collect()
        })
}

/// Reads the name of the template signature that starts at `target`.
///
/// # Arguments
///
/// * `program` - The image.
/// * `target` - A referenced address.
///
/// # Returns
///
/// The name, or `None` when `target` is not the first byte of a run of
/// printable ASCII ending in `]` and terminated within [`SCAN_MAX`] bytes,
/// or the run gives no name ([`parse`]).
fn read(program: &Program, target: u64) -> Option<String> {
    let starts_run = target
        .checked_sub(1)
        .and_then(|before| program.read_va(before, 1))
        .is_none_or(|b| b.first().is_none_or(|&b| !printable(b)));
    if !starts_run {
        return None;
    }
    let raw = program.read_va_upto(target, SCAN_MAX)?;
    let len = raw.iter().position(|&b| !printable(b))?;
    if raw.get(len) != Some(&0) || raw.get(len.checked_sub(1)?) != Some(&b']') {
        return None;
    }
    parse(std::str::from_utf8(raw.get(..len)?).ok()?)
}

/// Parses a template signature into the name of the function it is from.
///
/// # Arguments
///
/// * `text` - The whole string, bindings included.
///
/// # Returns
///
/// The name, or `None` when the text is no template signature (no
/// bracketed bindings, a duplicate or empty binding, a GCC pack, prose, no
/// parameter list, a head that declares no function, as a log format's
/// `send (%zu bytes) [fd = %d]` does) or its name is not safe to print
/// ([`checked`]).
fn parse(text: &str) -> Option<String> {
    let (body, open) = bindings_open(text)?;
    let inner = body.get(open + 1..)?;
    let (gcc, list) = inner
        .strip_prefix("with ")
        .map_or((false, inner), |l| (true, l));
    let bound = read_bindings(list, gcc)?;
    let (before, params, after) = split_signature(body.get(..open)?.trim_end())?;
    if !matches!(after, "" | "const" | "const noexcept" | "noexcept") {
        return None;
    }
    let before = before.trim_end();
    let bare = last_token(before).trim_start_matches(['*', '&']);
    let ret = before.strip_suffix(bare)?.trim();
    let name = strip_keywords(bare);
    if !name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        || !declares(before, &name, params, |w| bound.contains_key(w))
        || hand_written(ret, &[params, list])
    {
        return None;
    }
    let name = if gcc {
        substitute(&name, &bound)?
    } else {
        name
    };
    checked(name)
}

/// Reads a template signature's bindings.
///
/// # Arguments
///
/// * `list` - The text inside the brackets, after GCC's `with `.
/// * `gcc` - Whether GCC wrote it: `;` separates its bindings, `,`
///   Clang's.
///
/// # Returns
///
/// Each bound parameter (the last word of a binding's left side) and its
/// text, or `None` when a binding has an empty side, no ` = `, a parameter
/// no identifier names, or a parameter bound twice, or when GCC binds a
/// pack, whose spelled name stays uninstantiated.
fn read_bindings(list: &str, gcc: bool) -> Option<BTreeMap<&str, &str>> {
    let mut bound = BTreeMap::new();
    for part in split_outside(list, if gcc { ';' } else { ',' }) {
        let (lhs, rhs) = part.split_once(" = ")?;
        let (lhs, rhs) = (lhs.trim(), rhs.trim());
        let spread = lhs.ends_with("...") || rhs.starts_with('{');
        let param = lhs.trim_end_matches("...").trim_end().rsplit(' ').next()?;
        let ident = param.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            && param.chars().all(ident_char);
        if rhs.is_empty() || !ident || (gcc && spread) || bound.insert(param, rhs).is_some() {
            return None;
        }
    }
    Some(bound)
}

/// Finds where an operator function's name starts: the word `operator`
/// after the start or a `::`.
///
/// # Arguments
///
/// * `name` - A qualified name.
///
/// # Returns
///
/// The index of `operator`, or the name's length when it names no
/// operator.
fn operator_at(name: &str) -> usize {
    name.match_indices("operator")
        .map(|(i, _)| i)
        .find(|&i| {
            let after = name.as_bytes().get(i + "operator".len());
            (i == 0 || name.get(..i).is_some_and(|s| s.ends_with("::")))
                && after.is_none_or(|&b| !ident_char(char::from(b)))
        })
        .unwrap_or(name.len())
}

/// Spells GCC's bindings into the template arguments of a name's
/// qualifier.
///
/// The qualifier is the name's class ([`class_of`]). Each word inside its
/// `<...>` that a binding binds becomes the
/// binding's text, in one pass that never reads what it wrote, so `[with T
/// = U; U = int]` gives `Pair<U, int>` for `Pair<T, U>`. The last part
/// (the function's own name, an operator's symbol) is kept as spelled.
///
/// # Arguments
///
/// * `name` - The qualified name as GCC spells it.
/// * `bound` - The bindings.
///
/// # Returns
///
/// The name, or `None` as soon as it passes [`NAME_MAX`] bytes.
fn substitute(name: &str, bound: &BTreeMap<&str, &str>) -> Option<String> {
    let scope_len = class_of(name).map_or(0, str::len);
    let mut out = String::with_capacity(NAME_MAX);
    let mut put =
        |s: &str| (out.len().saturating_add(s.len()) <= NAME_MAX).then(|| out.push_str(s));
    let word = |b: u8| ident_char(char::from(b));
    let bytes = name.as_bytes();
    let (mut i, mut depth) = (0usize, 0usize);
    while let Some(&b) = bytes.get(i).filter(|_| i < scope_len) {
        if word(b) {
            let end = bytes
                .get(i..scope_len)
                .and_then(|r| r.iter().position(|&c| !word(c)))
                .map_or(scope_len, |k| i + k);
            let text = name.get(i..end).unwrap_or("");
            let named = !b.is_ascii_digit() && depth > 0;
            put(bound.get(text).copied().filter(|_| named).unwrap_or(text))?;
            i = end;
            continue;
        }
        match b {
            b'<' => depth += 1,
            b'>' => depth = depth.saturating_sub(1),
            _ => {}
        }
        put(name.get(i..=i).unwrap_or(""))?;
        i += 1;
    }
    put(name.get(scope_len..).unwrap_or(""))?;
    Some(out)
}

/// Keeps a name only when it is safe to print as one.
///
/// # Arguments
///
/// * `name` - The name.
///
/// # Returns
///
/// The name, or `None` when it is empty, longer than [`NAME_MAX`] bytes,
/// spells a comment mark, holds a byte outside `A-Za-z0-9_:<>,*& ~-`
/// before an operator's name and outside those and an operator's symbols
/// after it, or holds a control token.
fn checked(name: String) -> Option<String> {
    let plain = |b: u8| b.is_ascii_alphanumeric() || b" _:<>,*&~-".contains(&b);
    let symbol = |b: u8| plain(b) || b"+/%^|!=()[]".contains(&b);
    let (scope, op) = name.split_at(operator_at(&name));
    let ok = !name.is_empty()
        && name.len() <= NAME_MAX
        && scope.bytes().all(plain)
        && op.bytes().all(symbol)
        && !["/*", "*/", "//"].iter().any(|m| name.contains(m))
        && crate::text::token_breaks(&name).is_empty();
    ok.then_some(name)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{NAME_MAX, parse, substitute};

    /// GCC's bindings go into the qualifier's template arguments, each word
    /// once; Clang's names are kept as spelled.
    ///
    /// # Panics
    ///
    /// When a name differs from its expectation.
    #[test]
    fn bindings_go_into_the_qualifier_once() {
        let cases = [
            (
                "void Box<T>::Put(U) [with U = double; T = int]",
                "Box<int>::Put",
            ),
            (
                "void Outer<T>::Inner<U>::Go() [with U = char; T = int]",
                "Outer<int>::Inner<char>::Go",
            ),
            ("void Arr<N>::Clear() [with int N = 4]", "Arr<4>::Clear"),
            (
                "void Pair<T, T1>::Set() [with T = int; T1 = char]",
                "Pair<int, char>::Set",
            ),
            (
                "void Pair<T, U>::Set() [with T = U; U = int]",
                "Pair<U, int>::Set",
            ),
            ("void P<U, T>::Set() [T = U, U = T]", "P<U, T>::Set"),
            ("T Twice(T) [with T = int]", "Twice"),
            (
                "constexpr std::vector<_Tp, _Alloc>::reference std::vector<_Tp, _Alloc>::operator[](size_type) [with _Tp = int; _Alloc = std::allocator<int>; reference = int&; size_type = long unsigned int]",
                "std::vector<int, std::allocator<int>>::operator[]",
            ),
            (
                "void Tuple<int, char>::Clear() [Ts = <int, char>]",
                "Tuple<int, char>::Clear",
            ),
        ];
        for (text, want) in cases {
            assert_eq!(parse(text).as_deref(), Some(want), "{text}");
        }
        for text in [
            "void Box<T>::Put() [with T = int; T = char]",
            "void Box<T>::Put() [with T = ]",
            "Failed to open the file (%s) [with T = int]",
            "void Pack(Ts ...) [with Ts = {int, char}]",
            "void A<T::f() [with T = int]",
            "void A>::f() [with T = int]",
        ] {
            assert_eq!(parse(text), None, "{text}");
        }
    }

    /// A name never passes [`NAME_MAX`] bytes, however long its bindings,
    /// and one that would spell a comment mark or a control token is none.
    ///
    /// # Panics
    ///
    /// When a long or unsafe name is given.
    #[test]
    fn names_stay_short_and_plain() {
        let uses = "T,".repeat(56);
        let long = format!("void A<{uses}T>::f() [with T = {}]", "a".repeat(3900));
        assert_eq!(parse(&long), None);
        let bound = BTreeMap::from([("T", "aaaaaaaaaa")]);
        let wide = format!("A<{}T>::f", "T,".repeat(20));
        assert_eq!(substitute(&wide, &bound), None);
        for text in [
            "void A<T>::f() [with T = x/*y]",
            "void A<T>::f() [with T = x*/y]",
            "void A<T>::f() [with T = <|im_start|>]",
            "void A</*x*/>::f() [T = int]",
        ] {
            assert_eq!(parse(text), None, "{text}");
        }
        assert_eq!(
            parse("void A<T>::f() [with T = int; U = <|im_start|>]").as_deref(),
            Some("A<int>::f")
        );
        let at_cap = format!("void A<int>::{}() [T = int]", "f".repeat(NAME_MAX - 8));
        assert_eq!(parse(&at_cap).map(|n| n.len()), Some(NAME_MAX));
        let past = format!("void A<int>::{}() [T = int]", "f".repeat(NAME_MAX - 7));
        assert_eq!(parse(&past), None);
        let bound = BTreeMap::from([("T", "int")]);
        assert_eq!(
            substitute("A<T, B::C>::operator<", &bound).as_deref(),
            Some("A<int, B::C>::operator<")
        );
    }

    /// A log format that ends in a bracketed `[name = value]` is no template
    /// signature: its head declares no function.
    ///
    /// # Panics
    ///
    /// When a format gives a name.
    #[test]
    fn a_log_format_is_no_template_signature() {
        for text in [
            "send (%zu bytes) [fd = %d]",
            "recv() [rc = %d]",
            "Retrying: open (%s) [errno = %d]",
            "Retrying: Net::open(%s) [errno = %d]",
            "Calling Net::Connect() [fd = %d]",
            "Retrying: Net::open() [T = int]",
            "Error in Net::open() [T = int]",
        ] {
            assert_eq!(parse(text), None, "{text}");
        }
    }

    /// A conversion operator keeps its class.
    ///
    /// # Panics
    ///
    /// When the class is cut from the name.
    #[test]
    fn a_conversion_operator_keeps_its_class() {
        assert_eq!(
            parse("Box<int>::operator bool() const [T = int]").as_deref(),
            Some("Box<int>::operator bool")
        );
    }
}
