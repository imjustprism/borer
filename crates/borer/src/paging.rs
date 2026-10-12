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

#[cfg(test)]
mod tests {
    use super::Asked;

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
}
