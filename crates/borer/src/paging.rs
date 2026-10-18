//! What a resource URI asks for beyond its resource: the suffixes a reader
//! appends, read off its end in any order.
//!
//! `!offset=<n>` and `!limit=<n>` page a listing as `offset` and `limit`
//! page a list tool; `!since=<tag>` passes back the tag of the answer the
//! reader holds, and `!fresh` asks for the text whole whatever tag comes
//! with it ([`crate::recall`]). A `!` inside the resource's own argument (a
//! `borer://calls` filter `a2!=0`) stays where it is: only a trailing
//! suffix naming one of these is read off.

use std::fmt::Write as _;

use borer_engine::table::{Window, row_limit, row_offset};

use crate::recall::{FRESH_SUFFIX, SINCE_SUFFIX, Tag};

/// What a URI ends with, before a row count, to skip that many rows of a
/// listing.
pub(crate) const OFFSET_SUFFIX: &str = "!offset=";
/// What a URI ends with, before a row count, to show at most that many
/// rows of a listing.
pub(crate) const LIMIT_SUFFIX: &str = "!limit=";

/// A resource URI with its suffixes read off.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Asked {
    /// The URI without any suffix: the resource and its argument.
    pub(crate) core: String,
    /// Rows to skip, when `!offset=` asked.
    pub(crate) offset: Option<usize>,
    /// Most rows to show, when `!limit=` asked.
    pub(crate) limit: Option<usize>,
    /// The tag `!since=` passed back, unless `!fresh` asked for the text
    /// whole.
    pub(crate) since: Option<Tag>,
}

impl Asked {
    /// Reads a URI's suffixes off its end.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI as the reader sent it.
    ///
    /// # Returns
    ///
    /// The URI's resource and what its suffixes ask for.
    ///
    /// # Errors
    ///
    /// When a suffix is given twice, a row count is not one, or a tag is
    /// not one, each with the form it takes.
    pub(crate) fn read(uri: &str) -> Result<Asked, String> {
        let twice = |name: &str| {
            format!(
                "{name} is given twice in {}; give it once",
                borer_engine::text::one_line(uri)
            )
        };
        let (mut rest, mut fresh) = (uri, false);
        let (mut offset, mut limit, mut since) = (None, None, None);
        while let Some(at) = rest.rfind('!') {
            let (core, suffix) = rest.split_at(at);
            if suffix == FRESH_SUFFIX {
                fresh = true;
            } else if let Some(tag) = suffix.strip_prefix(SINCE_SUFFIX) {
                if since.replace(Tag::parse(tag)?).is_some() {
                    return Err(twice(SINCE_SUFFIX));
                }
            } else if let Some(n) = suffix.strip_prefix(OFFSET_SUFFIX) {
                if offset.replace(row_offset(n)?).is_some() {
                    return Err(twice(OFFSET_SUFFIX));
                }
            } else if let Some(n) = suffix.strip_prefix(LIMIT_SUFFIX) {
                if limit.replace(row_limit(n)?).is_some() {
                    return Err(twice(LIMIT_SUFFIX));
                }
            } else {
                break;
            }
            rest = core;
        }
        Ok(Asked {
            core: rest.to_owned(),
            offset,
            limit,
            since: since.filter(|_| !fresh),
        })
    }

    /// A URI read as it is, no suffix taken off, as the tests read one.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI, suffixes already taken off.
    #[cfg(test)]
    pub(crate) fn whole(uri: &str) -> Asked {
        Asked {
            core: uri.to_owned(),
            offset: None,
            limit: None,
            since: None,
        }
    }

    /// Whether a page was asked for.
    pub(crate) fn paged(&self) -> bool {
        self.offset.is_some() || self.limit.is_some()
    }

    /// The URI as answered: the resource, then the page asked for. The
    /// answer memory files the answer under it, and the answer names it.
    pub(crate) fn key(&self) -> String {
        let mut key = self.core.clone();
        if let Some(n) = self.offset {
            let _ = write!(key, "{OFFSET_SUFFIX}{n}");
        }
        if let Some(n) = self.limit {
            let _ = write!(key, "{LIMIT_SUFFIX}{n}");
        }
        key
    }

    /// The URI the line naming the next page appends its offset to: the
    /// resource and the limit asked for.
    pub(crate) fn again(&self) -> String {
        match self.limit {
            Some(n) => format!("{}{LIMIT_SUFFIX}{n}", self.core),
            None => self.core.clone(),
        }
    }

    /// The window a listing that pages itself shows: from the offset asked,
    /// at most `page` rows, fewer when the limit asks for fewer.
    ///
    /// # Arguments
    ///
    /// * `page` - The most rows the listing shows in one answer.
    /// * `again` - [`Asked::again`], for the line naming the next page.
    pub(crate) fn window<'a>(&self, page: usize, again: &'a str) -> Window<'a> {
        Window {
            skip: self.offset.unwrap_or(0),
            limit: self.limit.map_or(page, |n| n.min(page)),
            again: Some(again),
        }
    }

    /// A spec that pages itself by `offset=` and `limit=` words, with the
    /// page asked for added: `borer://iocs` and `borer://calls` read these.
    ///
    /// # Arguments
    ///
    /// * `spec` - The resource's argument, empty for none.
    pub(crate) fn spec_words(&self, spec: &str) -> String {
        let mut words: Vec<String> = Some(spec.to_owned())
            .filter(|s| !s.is_empty())
            .into_iter()
            .collect();
        words.extend(self.offset.map(|n| format!("offset={n}")));
        words.extend(self.limit.map(|n| format!("limit={n}")));
        words.join(",")
    }
}

/// Percent-decodes a resource URI argument.
///
/// A URI carries an argument in a path segment, where `,`, `=` and `:` are
/// reserved, so a correct client may send them escaped: an experiment spec
/// like `0x1400,rax=1` can arrive as `0x1400%2Crax%3D1`. The escaped form is
/// canonical, so decoding it is what makes those URIs resolve. A `%` that
/// does not begin a valid escape is left alone, so a name containing one
/// still resolves, and bytes that are not UTF-8 leave the text as it came.
///
/// # Arguments
///
/// * `text` - The raw path segment.
///
/// # Returns
///
/// The decoded argument.
pub(crate) fn percent_decode(text: &str) -> String {
    if !text.contains('%') {
        return text.to_owned();
    }
    let raw = text.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let escape = if raw[i] == b'%' {
            let hex = |k: usize| {
                raw.get(k)
                    .copied()
                    .map(char::from)
                    .and_then(|c| c.to_digit(16))
            };
            hex(i + 1).zip(hex(i + 2))
        } else {
            None
        };
        if let Some((high, low)) = escape {
            out.push(u8::try_from(high * 16 + low).unwrap_or(b'%'));
            i += 3;
        } else {
            out.push(raw[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_owned())
}

#[cfg(test)]
mod tests {
    use super::{Asked, percent_decode};

    /// Suffixes come off in any order, a `!` in the argument stays, a
    /// suffix given twice or a count that is not one is refused, and
    /// `!fresh` drops the tag.
    ///
    /// # Panics
    ///
    /// When a suffix is misread or a bad one is taken.
    #[test]
    fn suffixes_come_off_in_any_order() {
        let read = |uri: &str| Asked::read(uri).expect("reads");
        let a = read("borer://calls/f,a2!=0!limit=5!offset=10");
        assert_eq!(
            (a.core.as_str(), a.offset, a.limit, a.since),
            ("borer://calls/f,a2!=0", Some(10), Some(5), None)
        );
        assert_eq!(a.key(), "borer://calls/f,a2!=0!offset=10!limit=5");
        assert_eq!(a.again(), "borer://calls/f,a2!=0!limit=5");
        assert_eq!(a.spec_words("f,a2!=0"), "f,a2!=0,offset=10,limit=5");
        let b = read("borer://attrs!offset=200!since=0000abcd!fresh");
        assert_eq!(
            (b.core.as_str(), b.offset, b.since),
            ("borer://attrs", Some(200), None)
        );
        assert!(read("borer://attrs!since=0000abcd").since.is_some());
        assert!(!read("borer://info").paged());
        for bad in [
            "borer://attrs!offset=1!offset=2",
            "borer://attrs!limit=0",
            "borer://attrs!offset=x",
            "borer://attrs!since=zz",
        ] {
            assert!(Asked::read(bad).is_err(), "{bad}");
        }
        assert_eq!(read("borer://iocs!offset=3").spec_words(""), "offset=3");
    }

    /// An escaped experiment spec decodes to the same spec sent plainly.
    ///
    /// A URI path segment reserves `,` and `=`, so a correct client may send
    /// them escaped; both spellings have to reach the harness as one spec.
    ///
    /// # Panics
    ///
    /// When an escaped spec does not decode to the plain one.

    #[test]
    fn an_escaped_spec_decodes() {
        assert_eq!(
            percent_decode("0x1400%2Crax%3D1%2Cw0x1400%3D90c3"),
            "0x1400,rax=1,w0x1400=90c3"
        );
        assert_eq!(percent_decode("0x1400%2crax%3d1"), "0x1400,rax=1");
        assert_eq!(percent_decode("0x1400,rax=1"), "0x1400,rax=1");
        assert_eq!(
            percent_decode("std%3A%3Astring%3A%3Aresize"),
            "std::string::resize"
        );
    }

    /// A `%` that begins no escape is left as it came.
    ///
    /// A name or filter can contain one, and mangling it would lose a lookup
    /// that works today.
    ///
    /// # Panics
    ///
    /// When a stray percent is altered.
    #[test]
    fn a_stray_percent_survives() {
        assert_eq!(percent_decode("100%"), "100%");
        assert_eq!(percent_decode("%zz"), "%zz");
        assert_eq!(percent_decode("%"), "%");
        assert_eq!(percent_decode("%2"), "%2");
        assert_eq!(percent_decode("a%%20b"), "a% b");
    }
}
