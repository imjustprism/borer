//! The string-walk cache: one program's ASCII and UTF-16LE runs, walked
//! once and held for every `strings` call of the session.
//!
//! The `strings` tool answers from rows a walk already produced, and a
//! session asks more than once - another encoding, another filter, another
//! page - while the bytes it walked never change: `load_binary` is the only
//! event that can, and it resets the cache. The entry is still keyed by the
//! program's bytes (pointer and length), so a walk can only be served to
//! the allocation it was walked from, the way the decompile index is keyed
//! per program (`index::index_key`) with the session in place of the file.
//!
//! The cached rows are spans, not texts: sixteen bytes per string and no
//! allocation, where a materialized row is a heap `String` each - fifty
//! thousand of those on a large image. The filter tests the span's bytes
//! where they lie in the program, and a page materializes only the rows it
//! prints.

use std::sync::{Arc, RwLock};

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;
use borer_engine::strings::{
    RawStringSpan, StringHit, drop_code_runs, find_ascii_spans, find_wide_spans,
};

use crate::params::StringEncoding;
use crate::{read_lock, write_lock};

/// Shortest run the cached walks keep: the `strings` default, so every
/// default call's rows are one filter away.
///
/// The tool clamps `min_length` to 4, but a floor call is not worth the
/// rows: a 44 MB image holds about thirteen times as many four-character
/// runs as five-character ones, all of them noise. The tool walks a floor
/// call itself instead of asking the cache.
pub(crate) const WALK_MIN: usize = 5;

/// One row the strings listing shows: a span of the program's bytes, or a
/// .NET user string kept whole.
///
/// A walked run's display text is what its bytes decode to, so a span
/// materializes it only when shown. A `#US` literal's display text is
/// escaped and one-lined, which the raw bytes do not spell, so its row
/// keeps the text the heap read.
#[derive(Debug, Clone)]
pub(crate) enum StringRow {
    /// A walked ASCII or UTF-16LE run, its text still in the program's
    /// bytes.
    Span(RawStringSpan),
    /// A .NET user string, materialized by the heap reader.
    Hit(StringHit),
}

impl StringRow {
    /// The row's file offset.
    pub(crate) fn off(&self) -> u64 {
        match self {
            StringRow::Span(s) => s.off,
            StringRow::Hit(h) => h.off,
        }
    }

    /// The row's length in characters, bytes for ASCII and code units for
    /// UTF-16.
    pub(crate) fn len(&self) -> usize {
        match self {
            StringRow::Span(s) => usize::try_from(s.len).unwrap_or(usize::MAX),
            StringRow::Hit(h) => h.len,
        }
    }

    /// The row's encoding name.
    pub(crate) fn encoding(&self) -> borer_engine::strings::Encoding {
        match self {
            StringRow::Span(s) => s.encoding,
            StringRow::Hit(h) => h.encoding,
        }
    }

    /// The row's whole text, borrowed from the bytes for a span and taken
    /// as held for a hit.
    ///
    /// A walked run holds only printable ASCII, which is UTF-8 as it
    /// stands, so a span's whole text borrows its bytes with no copy at
    /// all - the zero-copy path a filter takes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The program's bytes, which a span indexes.
    pub(crate) fn full_text<'a>(&'a self, bytes: &'a [u8]) -> std::borrow::Cow<'a, str> {
        match self {
            StringRow::Span(s) => match s.encoding {
                borer_engine::strings::Encoding::Ascii => {
                    let raw = s.raw_bytes(bytes);
                    std::str::from_utf8(raw).map_or_else(
                        |_| std::borrow::Cow::Owned(String::from_utf8_lossy(raw).into_owned()),
                        std::borrow::Cow::Borrowed,
                    )
                }
                _ => std::borrow::Cow::Owned(
                    String::from_utf8_lossy(
                        &s.raw_bytes(bytes)
                            .iter()
                            .step_by(2)
                            .copied()
                            .collect::<Vec<u8>>(),
                    )
                    .into_owned(),
                ),
            },
            StringRow::Hit(h) => h.full_text(bytes),
        }
    }

    /// The row's display text, materialized from the bytes for a span and
    /// taken as held for a hit.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The program's bytes, which a span indexes.
    pub(crate) fn display_text(&self, bytes: &[u8]) -> String {
        match self {
            StringRow::Span(s) => s.text(bytes),
            StringRow::Hit(h) => h.text.clone(),
        }
    }
}

/// One program's string rows, in offset order per encoding.
#[derive(Debug)]
pub(crate) struct StringWalks {
    /// The program's bytes the rows were walked from, by pointer and
    /// length: an entry is served only while those still name the loaded
    /// program's allocation.
    key: (usize, usize),
    /// ASCII runs of at least [`WALK_MIN`] bytes.
    ascii: Vec<RawStringSpan>,
    /// UTF-16LE runs of at least [`WALK_MIN`] code units outside a `#US`
    /// heap.
    utf16: Vec<RawStringSpan>,
    /// A .NET assembly's user strings in place of the runs walked in its
    /// `#US`; empty for every other program.
    user: Vec<StringHit>,
}

impl StringWalks {
    /// The rows one encoding asks for, cut to runs of `min` or more.
    ///
    /// # Arguments
    ///
    /// * `encoding` - Which walks' rows, or both merged by offset.
    /// * `min` - Shortest run kept, at least [`WALK_MIN`] so the filter
    ///   only drops rows the caller's own minimum excludes.
    ///
    /// # Returns
    ///
    /// The rows in offset order, an ASCII row before a UTF-16LE one at
    /// the same offset.
    pub(crate) fn rows(&self, encoding: StringEncoding, min: usize) -> Vec<StringRow> {
        /// The spans of one walk, cut to runs of `min` or more.
        fn picked(spans: &[RawStringSpan], min: usize) -> Vec<StringRow> {
            spans
                .iter()
                .filter(|s| usize::try_from(s.len).unwrap_or(usize::MAX) >= min)
                .map(|&s| StringRow::Span(s))
                .collect()
        }
        match encoding {
            StringEncoding::Ascii => picked(&self.ascii, min),
            StringEncoding::Utf16 => {
                let mut all = picked(&self.utf16, min);
                all.extend(self.user.iter().cloned().map(StringRow::Hit));
                all
            }
            StringEncoding::Both => {
                let mut all = picked(&self.ascii, min);
                all.extend(picked(&self.utf16, min));
                all.extend(self.user.iter().cloned().map(StringRow::Hit));
                all.sort_by_key(StringRow::off);
                all
            }
        }
    }
}

/// Returns the loaded program's string rows, walking and caching them on
/// first use.
///
/// Two calls that race both walk and the later store wins; the rows are a
/// pure function of the bytes, so either answer is the same one.
///
/// # Arguments
///
/// * `cache` - The server's walk cache, reset by `load_binary`.
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, whose decoded code the walks leave out
///   ([`drop_code_runs`]).
///
/// # Returns
///
/// The walks, shared with every later `strings` call of the session.
pub(crate) fn load_or_build(
    cache: &RwLock<Option<Arc<StringWalks>>>,
    program: &Program,
    analysis: &Analysis,
) -> Arc<StringWalks> {
    let key = (program.bytes.as_ptr() as usize, program.bytes.len());
    if let Some(walks) = read_lock(cache).as_ref().filter(|w| w.key == key) {
        return Arc::clone(walks);
    }
    let (utf16, user) = borer_engine::clr::split_user_strings(
        program,
        find_wide_spans(&program.bytes, WALK_MIN),
        WALK_MIN,
    );
    let walks = Arc::new(StringWalks {
        key,
        ascii: drop_code_runs(
            program,
            analysis,
            find_ascii_spans(&program.bytes, WALK_MIN),
            WALK_MIN,
        ),
        utf16: drop_code_runs(program, analysis, utf16, WALK_MIN),
        user,
    });
    *write_lock(cache) = Some(Arc::clone(&walks));
    walks
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A raw program whose bytes carry the shapes the cache must keep.
    ///
    /// Runs at the cached minimum, runs above it, and runs the minimum
    /// excludes: a 4-byte ASCII run and a 4-unit wide run.
    fn program() -> Program {
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(b"abcdefgh\x00");
        bytes.extend_from_slice(b"abcd\x00");
        bytes.extend_from_slice(b"ijklmno\x00");
        for b in b"wide string" {
            bytes.extend_from_slice(&[*b, 0]);
        }
        bytes.extend_from_slice(&[b'x', 0, b'y', 0, b'z', 0, b'w', 0]);
        bytes.push(0);
        Program::raw(
            bytes,
            borer_engine::program::Arch::X86_64,
            0,
            None,
            Vec::new(),
        )
    }

    /// The cached rows answer what walking the bytes at the caller's own
    /// minimum answers, for every encoding.
    ///
    /// # Panics
    ///
    /// When a cached page disagrees with a fresh walk.
    #[test]
    fn rows_answer_what_a_walk_at_the_minimum_answers() {
        let p = program();
        let walks = StringWalks {
            key: (0, 0),
            ascii: find_ascii_spans(&p.bytes, WALK_MIN),
            utf16: find_wide_spans(&p.bytes, WALK_MIN),
            user: Vec::new(),
        };
        for encoding in [
            StringEncoding::Ascii,
            StringEncoding::Utf16,
            StringEncoding::Both,
        ] {
            for min in WALK_MIN..9 {
                let cached: Vec<(u64, usize)> = walks
                    .rows(encoding, min)
                    .iter()
                    .map(|r| (r.off(), r.len()))
                    .collect();
                let walked: Vec<(u64, usize)> = match encoding {
                    StringEncoding::Ascii => find_ascii_spans(&p.bytes, min),
                    StringEncoding::Utf16 => find_wide_spans(&p.bytes, min),
                    StringEncoding::Both => {
                        let mut all = find_ascii_spans(&p.bytes, min);
                        all.extend(find_wide_spans(&p.bytes, min));
                        all.sort_by_key(|s| s.off);
                        all
                    }
                }
                .iter()
                .map(|s| (s.off, usize::try_from(s.len).unwrap_or(usize::MAX)))
                .collect();
                assert_eq!(cached, walked, "{encoding:?} min {min}");
            }
        }
    }

    /// The second call shares the first's walks, and a load resets them.
    ///
    /// # Panics
    ///
    /// When a cached walk is rebuilt or survives its program.
    #[test]
    fn load_or_build_builds_once_and_resets_with_the_program() {
        let cache: RwLock<Option<Arc<StringWalks>>> = RwLock::new(None);
        let p = program();
        let a = Analysis::default();
        let first = load_or_build(&cache, &p, &a);
        let second = load_or_build(&cache, &p, &a);
        assert!(
            Arc::ptr_eq(&first, &second),
            "the second call walks nothing"
        );
        *write_lock(&cache) = None;
        let third = load_or_build(&cache, &p, &a);
        assert!(
            !Arc::ptr_eq(&first, &third),
            "a reset program walks again, sharing nothing with the stale rows"
        );
    }

    /// A span row's whole text borrows an ASCII run's bytes and decodes a
    /// UTF-16LE run's low halves.
    ///
    /// Its display text is the span's own materialization: cut with
    /// `...` past two hundred characters while the whole text keeps every
    /// one.
    ///
    /// # Panics
    ///
    /// When a row's texts disagree with its bytes.
    #[test]
    fn span_rows_answer_whole_and_display_texts() {
        let mut bytes: Vec<u8> = b"ascii run\x00".to_vec();
        bytes.extend(b"wide run".iter().flat_map(|b| [*b, 0]));
        bytes.push(0xff);
        bytes.extend(std::iter::repeat_n(b'q', 300));
        bytes.push(0);
        let p = Program::raw(
            bytes,
            borer_engine::program::Arch::X86_64,
            0,
            None,
            Vec::new(),
        );

        let ascii = find_ascii_spans(&p.bytes, 5);
        assert_eq!(ascii.len(), 2, "{ascii:?}");
        let narrow = StringRow::Span(ascii[0]);
        assert_eq!(narrow.full_text(&p.bytes), "ascii run");
        assert_eq!(narrow.display_text(&p.bytes), "ascii run");

        let wide = find_wide_spans(&p.bytes, 5);
        assert_eq!(wide.len(), 1, "{wide:?}");
        let wide_row = StringRow::Span(wide[0]);
        assert_eq!(wide_row.full_text(&p.bytes), "wide run");
        assert_eq!(wide_row.display_text(&p.bytes), "wide run");

        let long = StringRow::Span(ascii[1]);
        let shown = long.display_text(&p.bytes);
        assert_eq!(shown.chars().count(), 203);
        assert!(shown.ends_with("..."));
        assert_eq!(long.full_text(&p.bytes).chars().count(), 300);
        assert!(long.full_text(&p.bytes).ends_with("qqq"));
    }

    /// A row whose span no longer stands in the program's bytes answers
    /// empty texts rather than a panic, the way a stale page after a
    /// reload must.
    ///
    /// # Panics
    ///
    /// When a vanished span panics or answers text.
    #[test]
    fn span_rows_of_vanished_bytes_answer_empty() {
        let p = Program::raw(
            b"ab\x00".to_vec(),
            borer_engine::program::Arch::Unknown,
            0,
            None,
            Vec::new(),
        );
        let gone = StringRow::Span(RawStringSpan {
            off: 50,
            len: 4,
            encoding: borer_engine::strings::Encoding::Ascii,
        });
        assert_eq!(gone.full_text(&p.bytes), "");
        assert_eq!(gone.display_text(&p.bytes), "");
        let overrun = StringRow::Span(RawStringSpan {
            off: 0,
            len: 9,
            encoding: borer_engine::strings::Encoding::Utf16,
        });
        assert_eq!(overrun.full_text(&p.bytes), "");
        assert_eq!(overrun.display_text(&p.bytes), "");
    }
}
