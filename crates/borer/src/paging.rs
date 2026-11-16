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
use std::num::NonZeroUsize;

pub(crate) use borer_engine::answer::percent_decode;
use borer_engine::answer::{LIMIT_SUFFIX, OFFSET_SUFFIX, Page, Suffixed};

use crate::recall::Tag;

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
        let read = Suffixed::read(uri)?;
        let since = read.since.map(Tag::parse).transpose()?;
        Ok(Asked {
            core: read.core.to_owned(),
            offset: read.offset,
            limit: read.limit.map(NonZeroUsize::get),
            since: since.filter(|_| !read.fresh),
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
        borer_engine::answer::again(&self.core, self.limit.and_then(NonZeroUsize::new))
    }

    /// The page asked, for a listing that pages itself
    /// ([`borer_engine::answer::Page`]).
    ///
    /// # Arguments
    ///
    /// * `again` - [`Asked::again`], for the line naming the next page.
    pub(crate) fn page<'a>(&self, again: &'a str) -> Page<'a> {
        Page {
            offset: self.offset,
            limit: self.limit.and_then(NonZeroUsize::new),
            again,
        }
    }
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
        assert_eq!(
            a.page("").spec_words("f,a2!=0"),
            "f,a2!=0,offset=10,limit=5"
        );
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
        assert_eq!(
            read("borer://iocs!offset=3").page("").spec_words(""),
            "offset=3"
        );
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
