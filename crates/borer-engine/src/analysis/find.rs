//! One search over every name table the engine holds: what a person types
//! into a find box, parsed once at the boundary.

use crate::fileinfo::Place;
use crate::strings::walk::Needle;

/// Most characters of a query's needle; the rest is cut before it is
/// lowered, so a pasted megabyte costs no more than a word.
pub const NEEDLE_MAX: usize = 256;

/// Which tables a query searches, from its kind prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// No prefix: every table, and first the place the text spells as an
    /// address, if it spells one: `0x`-hex, `rva:<n>`, `off:<n>`, or a bare
    /// number of decimal digits alone, where `borer://addr` also reads bare
    /// hex.
    All(Option<Place>),
    /// `@`: the discovered functions.
    Functions,
    /// `"`: the strings.
    Strings,
    /// `t:`: the user and debug types and the recovered classes.
    Types,
    /// `#`: the user's names and comments.
    Notes,
}

/// A find query: the tables it searches and the needle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    /// The tables searched.
    pub scope: Scope,
    /// The text sought, at most [`NEEDLE_MAX`] characters, lowered.
    pub needle: Needle,
    /// The text was longer than [`NEEDLE_MAX`] characters and was cut, so
    /// no hit is known to match it whole.
    pub cut: bool,
}

impl Query {
    /// Returns the query `text` spells.
    ///
    /// A kind prefix (`@`, `"`, `t:`, `#`) narrows the tables; any other
    /// text searches them all, and an address form among it ([`Place`];
    /// a bare number only when it is decimal digits, so `add` or `beef` is
    /// a word) is answered first; text cut at [`NEEDLE_MAX`] spells none. A `"` query may close with a `"` too. A prefix the
    /// grammar lacks is plain text.
    ///
    /// # Arguments
    ///
    /// * `text` - The query as typed, of any length.
    #[must_use]
    pub fn parse(text: &str) -> Self {
        let text = text.trim();
        let (scope, rest) = if let Some(rest) = text.strip_prefix('@') {
            (Some(Scope::Functions), rest)
        } else if let Some(rest) = text.strip_prefix('"') {
            (Some(Scope::Strings), rest.strip_suffix('"').unwrap_or(rest))
        } else if let Some(rest) = text.strip_prefix("t:") {
            (Some(Scope::Types), rest)
        } else if let Some(rest) = text.strip_prefix('#') {
            (Some(Scope::Notes), rest)
        } else {
            (None, text)
        };
        let (rest, cut) = head(rest, NEEDLE_MAX);
        let decimal = rest.bytes().all(|b| b.is_ascii_digit());
        let place = Place::parse(rest).filter(|place| {
            !cut && match place {
                Place::Number(_) => decimal,
                Place::Va(_) | Place::Rva(_) | Place::Off(_) => true,
            }
        });
        Self {
            scope: scope.unwrap_or(Scope::All(place)),
            needle: Needle::new(rest),
            cut,
        }
    }
}

/// Returns the first `max` characters of `text` and whether any were left
/// out.
///
/// # Arguments
///
/// * `text` - The text cut.
/// * `max` - Most characters kept.
fn head(text: &str, max: usize) -> (&str, bool) {
    text.char_indices()
        .nth(max)
        .and_then(|(at, _)| text.get(..at))
        .map_or((text, false), |kept| (kept, true))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each kind prefix narrows the scope and leaves the needle lowered;
    /// a prefix the grammar lacks is plain text.
    ///
    /// # Panics
    ///
    /// When a scope or a needle differs.
    #[test]
    fn a_prefix_picks_the_tables() {
        let parsed = |text: &str| {
            let q = Query::parse(text);
            (q.scope, q.needle.as_str().to_owned())
        };
        assert_eq!(parsed("Crypt"), (Scope::All(None), "crypt".to_owned()));
        assert_eq!(parsed("@Crypt"), (Scope::Functions, "crypt".to_owned()));
        assert_eq!(parsed("\"cry"), (Scope::Strings, "cry".to_owned()));
        assert_eq!(parsed("\"cry\""), (Scope::Strings, "cry".to_owned()));
        assert_eq!(parsed("t:ctx"), (Scope::Types, "ctx".to_owned()));
        assert_eq!(parsed("#key"), (Scope::Notes, "key".to_owned()));
        assert_eq!(parsed("x:key"), (Scope::All(None), "x:key".to_owned()));
    }

    /// The address forms are read only without a prefix, as `borer://addr`
    /// reads them ([`Place::parse`]), and text that is not a number in its
    /// form is no address.
    ///
    /// # Panics
    ///
    /// When a scope differs.
    #[test]
    fn an_address_form_is_a_place() {
        let place = |text: &str| Query::parse(text).scope;
        assert_eq!(place("0x401000"), Scope::All(Some(Place::Va(0x40_1000))));
        assert_eq!(place("4198400"), Scope::All(Some(Place::Number(4_198_400))));
        assert_eq!(place("rva:0x1000"), Scope::All(Some(Place::Rva(0x1000))));
        assert_eq!(place("rva:1a00"), Scope::All(Some(Place::Rva(0x1a00))));
        assert_eq!(place("off:0x400"), Scope::All(Some(Place::Off(0x400))));
        assert_eq!(place("0xzz"), Scope::All(None));
        assert_eq!(place("rva:zz"), Scope::All(None));
        assert_eq!(place("crypt"), Scope::All(None));
        assert_eq!(place("add"), Scope::All(None));
        assert_eq!(place("beef"), Scope::All(None));
        assert_eq!(place("99999999999999999999999"), Scope::All(None));
        assert_eq!(place("@0x401000"), Scope::Functions);
    }

    /// A needle is cut to [`NEEDLE_MAX`] characters before it is lowered,
    /// whatever the text is made of, and says it was; an empty query is an
    /// empty needle.
    ///
    /// # Panics
    ///
    /// When a needle is longer than the cap or its cut is not said.
    #[test]
    fn a_needle_is_capped() {
        let long = "a".repeat(1 << 20);
        let marks = "\u{301}".repeat(1 << 16);
        for text in [long.as_str(), marks.as_str()] {
            let q = Query::parse(text);
            assert!(q.needle.as_str().chars().count() <= NEEDLE_MAX);
            assert!(q.cut);
        }
        for text in ["", "@", "t:", "\"", "crypt"] {
            assert!(!Query::parse(text).cut, "{text}");
        }
        assert_eq!(Query::parse("").needle.as_str(), "");
        let padded = format!("0x{}401000", "0".repeat(NEEDLE_MAX - 6));
        assert_eq!(padded.chars().count(), NEEDLE_MAX + 2);
        assert_eq!(Query::parse(&padded).scope, Scope::All(None));
    }
}
