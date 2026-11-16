//! The string walk: one program's ASCII and UTF-16LE runs, walked once per
//! analysis and held in its memo ([`Analysis::derived`]), and the paged
//! table of strings read off them.
//!
//! The `strings` table answers from rows a walk already produced, and a
//! session asks more than once (another encoding, another filter, another
//! page) while the bytes it walked never change.
//!
//! The walked rows are spans, not texts: sixteen bytes per string and no
//! allocation, where a materialized row is a heap `String` each, fifty
//! thousand of those on a large image. The filter tests the span's bytes
//! where they lie in the program, and a page materializes only the rows it
//! shows.

use std::borrow::Cow;
use std::fmt::Write as _;
use std::sync::Arc;

use super::{
    Encoding, RawStringSpan, StringHit, drop_code_runs, find_ascii_spans, find_wide_spans,
};
use crate::analysis::Analysis;
use crate::num::from_usize;
use crate::program::Program;

/// Shortest run the memoized walks keep: the `strings` default, so every
/// default call's rows are one filter away.
///
/// The `strings` tool takes 4, but a floor call is not worth the rows: a
/// 44 MB image holds about thirteen times as many four-character runs as
/// five-character ones, all of them noise. A call under it walks the bytes
/// itself instead of asking the memo.
pub const WALK_MIN: usize = 5;

/// Which strings a walk reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StringEncoding {
    /// Byte strings only.
    Ascii,
    /// UTF-16 strings only, a .NET assembly's user strings among them.
    Utf16,
    /// Both, in offset order.
    #[default]
    Both,
}

impl StringEncoding {
    /// Returns the word a header spells: `ascii`, `utf16` or `both`.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Ascii => "ascii",
            Self::Utf16 => "utf16",
            Self::Both => "both",
        }
    }
}

/// One string a walk found: a span of the program's bytes, or a .NET user
/// string kept whole.
///
/// A walked run's display text is what its bytes decode to, so a span
/// materializes it only when shown. A `#US` literal's display text is
/// escaped and one-lined, which the raw bytes do not spell, so its row
/// keeps the text the heap read.
#[derive(Debug, Clone)]
pub enum StringRow {
    /// A walked ASCII or UTF-16LE run, its text still in the program's
    /// bytes.
    Span(RawStringSpan),
    /// A .NET user string, materialized by the heap reader.
    Hit(StringHit),
}

impl StringRow {
    /// Returns the row's file offset.
    #[must_use]
    pub fn off(&self) -> u64 {
        match self {
            StringRow::Span(s) => s.off,
            StringRow::Hit(h) => h.off,
        }
    }

    /// Returns the row's length in characters: bytes for ASCII, code units
    /// for UTF-16.
    #[must_use]
    pub fn char_len(&self) -> usize {
        match self {
            StringRow::Span(s) => usize::try_from(s.len).unwrap_or(usize::MAX),
            StringRow::Hit(h) => h.len,
        }
    }

    /// Returns the row's encoding.
    #[must_use]
    pub fn encoding(&self) -> Encoding {
        match self {
            StringRow::Span(s) => s.encoding,
            StringRow::Hit(h) => h.encoding,
        }
    }

    /// Returns the row's whole text, borrowed from the bytes for a span and
    /// taken as held for a hit.
    ///
    /// A walked run holds only printable ASCII, which is UTF-8 as it
    /// stands, so a span's whole text borrows its bytes with no copy at
    /// all, the zero-copy path a filter takes
    /// ([`RawStringSpan::whole_text`]).
    ///
    /// # Arguments
    ///
    /// * `bytes` - The program's bytes, which a span indexes.
    #[must_use]
    pub fn full_text<'a>(&'a self, bytes: &'a [u8]) -> Cow<'a, str> {
        match self {
            StringRow::Span(s) => s.whole_text(bytes),
            StringRow::Hit(h) => h.full_text(bytes),
        }
    }

    /// Returns the row's display text, materialized from the bytes for a
    /// span and taken as held for a hit.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The program's bytes, which a span indexes.
    /// * `literals` - The literals the walk's runs are lines of
    ///   ([`super::literals`]), whose control tokens a span's text breaks
    ///   too ([`RawStringSpan::text_in`]).
    #[must_use]
    pub fn display_text(&self, bytes: &[u8], literals: &[RawStringSpan]) -> String {
        match self {
            StringRow::Span(s) => s.text_in(bytes, literals),
            StringRow::Hit(h) => h.text.clone(),
        }
    }
}

/// One program's walked strings, in offset order per encoding.
#[derive(Debug)]
struct StringWalks {
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
    /// Returns the rows one encoding asks for, cut to runs of `min` or more.
    ///
    /// # Arguments
    ///
    /// * `encoding` - Which walks' rows, or both merged by offset.
    /// * `min` - Shortest run kept, at least [`WALK_MIN`] so the cut only
    ///   drops rows the caller's own minimum excludes.
    ///
    /// # Returns
    ///
    /// The rows in offset order, an ASCII row before a UTF-16LE one at the
    /// same offset.
    fn rows(&self, encoding: StringEncoding, min: usize) -> Vec<StringRow> {
        let picked = |spans: &[RawStringSpan]| {
            spans
                .iter()
                .filter(|s| usize::try_from(s.len).unwrap_or(usize::MAX) >= min)
                .map(|&s| StringRow::Span(s))
                .collect::<Vec<_>>()
        };
        let user = self.user.iter().cloned().map(StringRow::Hit);
        match encoding {
            StringEncoding::Ascii => picked(&self.ascii),
            StringEncoding::Utf16 => {
                let mut all = picked(&self.utf16);
                all.extend(user);
                all
            }
            StringEncoding::Both => {
                let mut all = picked(&self.ascii);
                all.extend(picked(&self.utf16));
                all.extend(user);
                all.sort_by_key(StringRow::off);
                all
            }
        }
    }
}

/// Returns the program's walked strings, walked on the first ask and kept
/// in the analysis's memo ([`Analysis::derived`]) for every later one.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose decoded code the walks leave out
///   ([`drop_code_runs`]) and whose memo keeps them.
fn walks(p: &Program, a: &Analysis) -> Arc<StringWalks> {
    a.derived.get_or_build("string_walks", (), || {
        let (utf16, user) =
            crate::clr::split_user_strings(p, find_wide_spans(&p.bytes, WALK_MIN), WALK_MIN);
        StringWalks {
            ascii: drop_code_runs(p, a, find_ascii_spans(&p.bytes, WALK_MIN), WALK_MIN),
            utf16: drop_code_runs(p, a, utf16, WALK_MIN),
            user,
        }
    })
}

/// Returns where the program's walked strings lie in the file, read off
/// the memoized walks ([`walks`]): every run of [`WALK_MIN`] or more
/// characters outside code, and a .NET assembly's user strings.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the walks.
///
/// # Returns
///
/// `(start, end)` file offsets per string, end exclusive, in start order;
/// two may overlap.
pub(crate) fn string_extents(p: &Program, a: &Analysis) -> Vec<(u64, u64)> {
    walks(p, a)
        .rows(StringEncoding::Both, WALK_MIN)
        .iter()
        .map(|row| {
            let bytes = match row {
                StringRow::Span(s) => s.raw_bytes(&p.bytes).len(),
                StringRow::Hit(h) => h.len.saturating_mul(h.encoding.unit()),
            };
            (row.off(), row.off().saturating_add(from_usize(bytes)))
        })
        .collect()
}

/// Visits every string the memoized walks hold, both encodings, as spans
/// in no promised order: a .NET user string as the span of its units.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the walks.
/// * `visit` - Called with each string's span.
pub(crate) fn for_each_walked(p: &Program, a: &Analysis, mut visit: impl FnMut(RawStringSpan)) {
    let w = walks(p, a);
    w.ascii.iter().chain(&w.utf16).copied().for_each(&mut visit);
    for h in &w.user {
        visit(RawStringSpan {
            off: h.off,
            len: u32::try_from(h.len).unwrap_or(u32::MAX),
            encoding: h.encoding,
        });
    }
}

/// Walks a program's strings of one encoding, without the memo.
///
/// A .NET assembly's user strings are read whole from its `#US` heap in
/// place of the UTF-16LE runs the walk finds there
/// ([`crate::clr::split_user_strings`]).
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose decoded code the walks leave out
///   ([`drop_code_runs`]).
/// * `encoding` - Which walks: ASCII, UTF-16LE, or both merged by offset.
/// * `min` - Shortest run kept.
///
/// # Returns
///
/// The rows in offset order.
fn walk_rows(p: &Program, a: &Analysis, encoding: StringEncoding, min: usize) -> Vec<StringRow> {
    let ascii = || {
        drop_code_runs(p, a, find_ascii_spans(&p.bytes, min), min)
            .into_iter()
            .map(StringRow::Span)
    };
    let wide = || {
        let (spans, user) = crate::clr::split_user_strings(p, find_wide_spans(&p.bytes, min), min);
        drop_code_runs(p, a, spans, min)
            .into_iter()
            .map(StringRow::Span)
            .chain(user.into_iter().map(StringRow::Hit))
    };
    match encoding {
        StringEncoding::Ascii => ascii().collect(),
        StringEncoding::Utf16 => wide().collect(),
        StringEncoding::Both => {
            let mut all: Vec<StringRow> = ascii().chain(wide()).collect();
            all.sort_by_key(StringRow::off);
            all
        }
    }
}

/// Returns whether `raw` holds `needle` under ASCII case folding, byte for
/// byte with no copy of the text.
///
/// # Arguments
///
/// * `raw` - The bytes a string's whole text spells.
/// * `needle` - The lowered filter text, all ASCII.
fn contains_fold_ascii(raw: &[u8], needle: &[u8]) -> bool {
    needle.is_empty()
        || raw.len() >= needle.len()
            && raw
                .windows(needle.len())
                .any(|w| w.iter().zip(needle).all(|(b, n)| b.eq_ignore_ascii_case(n)))
}

/// Returns whether the UTF-16LE code units `raw` spells hold `needle` under
/// ASCII case folding, tested against the units in place.
///
/// # Arguments
///
/// * `raw` - The run's bytes: one ASCII low byte and one zero high byte
///   per unit.
/// * `needle` - The lowered filter text, all ASCII.
fn contains_fold_wide(raw: &[u8], needle: &[u8]) -> bool {
    let units = raw.len() / 2;
    if needle.is_empty() {
        return true;
    }
    if units < needle.len() {
        return false;
    }
    (0..=units - needle.len()).any(|u| {
        needle
            .iter()
            .enumerate()
            .all(|(k, n)| raw[2 * (u + k) + 1] == 0 && raw[2 * (u + k)].eq_ignore_ascii_case(n))
    })
}

/// A string filter, lowered once, so every row it tests is folded against
/// the same text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Needle(String);

impl Needle {
    /// Returns the filter `text`, lowered.
    ///
    /// # Arguments
    ///
    /// * `text` - The filter as given, in any case.
    #[must_use]
    pub fn new(text: &str) -> Self {
        Self(text.to_lowercase())
    }

    /// Returns the lowered text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Returns whether one row passes a filter, the span's bytes tested where
/// they lie in the program and no text decoded.
///
/// A span's whole text is pure printable ASCII, so an ASCII needle is a
/// folded byte search over the run and any other needle answers `false`
/// without a copy; a .NET user string's text may hold what its bytes' walk
/// could not, so its row decodes.
///
/// # Arguments
///
/// * `p` - The loaded program, for the bytes a span indexes.
/// * `row` - The row tested.
/// * `needle` - The filter: a row passes when its text contains it in any
///   case; `None` passes every row.
#[must_use]
pub fn row_matches(p: &Program, row: &StringRow, needle: Option<&Needle>) -> bool {
    let Some(Needle(needle)) = needle else {
        return true;
    };
    match row {
        StringRow::Span(s) if needle.is_ascii() => {
            let raw = s.raw_bytes(&p.bytes);
            if s.encoding == Encoding::Ascii {
                contains_fold_ascii(raw, needle.as_bytes())
            } else {
                contains_fold_wide(raw, needle.as_bytes())
            }
        }
        StringRow::Span(_) => false,
        StringRow::Hit(_) => row
            .full_text(&p.bytes)
            .to_lowercase()
            .contains(needle.as_str()),
    }
}

/// One row of a page of strings: the facts its line spells.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLine {
    /// File offset of the first byte.
    pub off: u64,
    /// Where the string loads; `None` for bytes no section maps.
    pub va: Option<u64>,
    /// Length in characters: bytes for ASCII, code units for UTF-16.
    pub len: usize,
    /// The string's encoding.
    pub encoding: Encoding,
    /// The text shown: escaped, one line, cut past two hundred characters.
    pub text: String,
}

/// One page of the strings table, with what its header counts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringRows {
    /// Shortest run listed.
    pub min: usize,
    /// Which strings were walked.
    pub encoding: StringEncoding,
    /// Strings the filter kept, on every page.
    pub total: usize,
    /// The page's rows, in offset order.
    pub rows: Vec<StringLine>,
}

impl StringRows {
    /// Returns the page as the `strings` tool and the CLI print it.
    ///
    /// # Returns
    ///
    /// A `# showing N of M matches` header, a column header and one
    /// `va len enc "text"` row per string, `off=<n>` for bytes no section
    /// maps.
    #[must_use]
    pub fn spell(&self) -> String {
        let mut out = format!(
            "# showing {} of {} matches (min_len={}, encoding={}; filter=/offset= to narrow)\n# va len enc text\n",
            self.rows.len(),
            self.total,
            self.min,
            self.encoding.word()
        );
        for r in &self.rows {
            let _ = match r.va {
                Some(va) => write!(out, "{va:#x}"),
                None => write!(out, "off={:#x}", r.off),
            };
            let _ = writeln!(out, " {} {} \"{}\"", r.len, r.encoding.name(), r.text);
        }
        out
    }

    /// Returns the `count_only` answer: the header's count alone.
    #[must_use]
    pub fn counted(&self) -> String {
        format!(
            "# {} matches (min_len={}, encoding={})\n",
            self.total,
            self.min,
            self.encoding.word()
        )
    }
}

/// Returns one page of the program's strings as rows.
///
/// A run of `min` or more is read off the memoized walks
/// ([`walks`]); a shorter `min` walks the bytes again, uncached. The filter
/// tests a row's whole text ([`StringRow::full_text`]), not the display
/// text a long string is cut to, and a span's text is tested in place:
/// only the rows the page shows are materialized. A row is fenced where
/// the literal it is a line of addresses a model, so an element opened and
/// closed on lines of their own is broken on each.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose code the walks leave out and whose memo
///   keeps them.
/// * `encoding` - Which strings: ASCII, UTF-16LE or both.
/// * `min` - Shortest run listed.
/// * `filter` - Case-insensitive substring of the whole text; `None` keeps
///   every string.
/// * `offset` - Matches to skip first (paging).
/// * `limit` - Maximum rows.
///
/// # Returns
///
/// The page's rows with the total the filter kept.
#[must_use]
pub fn string_rows(
    p: &Program,
    a: &Analysis,
    encoding: StringEncoding,
    min: usize,
    filter: Option<&str>,
    offset: usize,
    limit: usize,
) -> StringRows {
    let rows = if min >= WALK_MIN {
        walks(p, a).rows(encoding, min)
    } else {
        walk_rows(p, a, encoding, min)
    };
    let lowered = filter.map(Needle::new);
    let needle = lowered.as_ref();
    let kept = || rows.iter().filter(move |row| row_matches(p, row, needle));
    let page: Vec<&StringRow> = kept().skip(offset).take(limit).collect();
    let literals = if page.is_empty() {
        Vec::new()
    } else {
        let spans = rows.iter().filter_map(|row| match row {
            StringRow::Span(s) => Some(*s),
            StringRow::Hit(_) => None,
        });
        super::literals(&p.bytes, spans.collect())
    };
    StringRows {
        min,
        encoding,
        total: kept().count(),
        rows: page
            .into_iter()
            .map(|row| StringLine {
                off: row.off(),
                va: p.offset_to_va(row.off()),
                len: row.char_len(),
                encoding: row.encoding(),
                text: row.display_text(&p.bytes, &literals),
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Arch;

    /// Builds a raw program from `bytes`, mapped by no section.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The file.
    fn raw(bytes: Vec<u8>) -> Program {
        Program::raw(bytes, Arch::X86_64, 0, None, Vec::new())
    }

    /// Builds a raw program whose bytes carry the shapes the memo must
    /// keep ([`shapes`]).
    fn program() -> Program {
        raw(shapes())
    }

    /// Returns bytes carrying the shapes the memo must keep: runs at the
    /// walked minimum, runs above it, and runs it excludes, a 4-byte ASCII
    /// run and a 4-unit wide run.
    fn shapes() -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(b"abcdefgh\x00");
        bytes.extend_from_slice(b"abcd\x00");
        bytes.extend_from_slice(b"ijklmno\x00");
        for b in b"wide string" {
            bytes.extend_from_slice(&[*b, 0]);
        }
        bytes.extend_from_slice(&[b'x', 0, b'y', 0, b'z', 0, b'w', 0]);
        bytes.push(0);
        bytes
    }

    /// The memoized rows answer what walking the bytes at the caller's own
    /// minimum answers, for every encoding.
    ///
    /// # Panics
    ///
    /// When a memoized page disagrees with a fresh walk.
    #[test]
    fn rows_answer_what_a_walk_at_the_minimum_answers() {
        let p = program();
        let walks = StringWalks {
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
                    .map(|r| (r.off(), r.char_len()))
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

    /// One analysis walks once: two pages under different filters and
    /// encodings share the walk, a floor minimum walks uncached, and a
    /// fresh analysis walks again.
    ///
    /// # Panics
    ///
    /// When a page walks again or a fresh analysis shares a stale walk.
    #[test]
    fn the_walk_is_built_once_per_analysis() {
        let p = program();
        let a = Analysis::default();
        let held = || a.derived.held("string_walks");
        let first = string_rows(&p, &a, StringEncoding::Both, 5, Some("abc"), 0, 10);
        let builds = a.derived.builds();
        assert_eq!((held(), first.total), (1, 1), "{first:?}");
        let second = string_rows(&p, &a, StringEncoding::Ascii, 6, Some("ij"), 0, 10);
        assert_eq!(second.total, 1, "{second:?}");
        assert_eq!(a.derived.builds(), builds, "the second page walks nothing");
        let floor = string_rows(&p, &a, StringEncoding::Ascii, 4, None, 0, 10);
        assert_eq!(floor.total, 3, "{floor:?}");
        assert_eq!(a.derived.builds(), builds, "a floor page asks no memo");
        assert!(Arc::ptr_eq(&walks(&p, &a), &walks(&p, &a)));
        let fresh = Analysis::default();
        assert!(!Arc::ptr_eq(&walks(&p, &a), &walks(&p, &fresh)));
    }

    /// A page carries each string's facts and spells the text the strings
    /// table printed before it had rows; the count is its header alone, and
    /// a page past the end lists nothing under the whole total.
    ///
    /// # Panics
    ///
    /// When a fact, the total or the spelled text differs.
    #[test]
    fn string_rows_spell_the_page_the_text_printed() {
        let rdata = crate::program::Section::mapped(".rdata", 0x4000, 0, 9, false, false);
        let p = Program::raw(shapes(), Arch::X86_64, 0, None, vec![rdata]);
        let both = string_rows(
            &p,
            &Analysis::default(),
            StringEncoding::Both,
            5,
            None,
            0,
            2,
        );
        assert_eq!(both.total, 3);
        assert_eq!(
            both.rows[0],
            StringLine {
                off: 0,
                va: Some(0x4000),
                len: 8,
                encoding: Encoding::Ascii,
                text: "abcdefgh".to_owned(),
            }
        );
        assert_eq!(both.rows[1].va, None);
        assert_eq!(
            both.spell(),
            "# showing 2 of 3 matches (min_len=5, encoding=both; filter=/offset= to narrow)
# va len enc text
0x4000 8 ascii \"abcdefgh\"
off=0xe 7 ascii \"ijklmno\"
"
        );
        let wide = string_rows(
            &p,
            &Analysis::default(),
            StringEncoding::Utf16,
            5,
            Some("WIDE"),
            0,
            10,
        );
        assert_eq!(wide.counted(), "# 1 matches (min_len=5, encoding=utf16)\n");
        assert_eq!(
            wide.spell(),
            "# showing 1 of 1 matches (min_len=5, encoding=utf16; filter=/offset= to narrow)
# va len enc text
off=0x16 15 utf16 \"wide stringxyzw\"
"
        );
        let past = string_rows(
            &p,
            &Analysis::default(),
            StringEncoding::Ascii,
            5,
            None,
            9,
            10,
        );
        assert_eq!((past.rows.len(), past.total), (0, 2));
    }

    /// A span row's whole text borrows an ASCII run's bytes and decodes a
    /// UTF-16LE run's low halves.
    ///
    /// Its display text is the span's own materialization: cut with `...`
    /// past two hundred characters while the whole text keeps every one.
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
        let p = raw(bytes);

        let ascii = find_ascii_spans(&p.bytes, 5);
        assert_eq!(ascii.len(), 2, "{ascii:?}");
        let narrow = StringRow::Span(ascii[0]);
        assert_eq!(narrow.full_text(&p.bytes), "ascii run");
        assert_eq!(narrow.display_text(&p.bytes, &[]), "ascii run");

        let wide = find_wide_spans(&p.bytes, 5);
        assert_eq!(wide.len(), 1, "{wide:?}");
        let wide_row = StringRow::Span(wide[0]);
        assert_eq!(wide_row.full_text(&p.bytes), "wide run");
        assert_eq!(wide_row.display_text(&p.bytes, &[]), "wide run");

        let long = StringRow::Span(ascii[1]);
        let shown = long.display_text(&p.bytes, &[]);
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
        let p = Program::raw(b"ab\x00".to_vec(), Arch::Unknown, 0, None, Vec::new());
        let gone = StringRow::Span(RawStringSpan {
            off: 50,
            len: 4,
            encoding: Encoding::Ascii,
        });
        assert_eq!(gone.full_text(&p.bytes), "");
        assert_eq!(gone.display_text(&p.bytes, &[]), "");
        let overrun = StringRow::Span(RawStringSpan {
            off: 0,
            len: 9,
            encoding: Encoding::Utf16,
        });
        assert_eq!(overrun.full_text(&p.bytes), "");
        assert_eq!(overrun.display_text(&p.bytes, &[]), "");
    }

    /// A page fences an element's tag lines by the literal they are lines
    /// of, a page that starts past the opening tag included, and the
    /// answer counts them.
    ///
    /// # Panics
    ///
    /// When a tag line prints as it stands or goes uncounted.
    #[test]
    fn a_page_fences_an_element_s_tag_lines() {
        let p = raw(b"\0<system>\nbe brief\n</system>\0".to_vec());
        let page = |offset| {
            string_rows(
                &p,
                &Analysis::default(),
                StringEncoding::Ascii,
                5,
                None,
                offset,
                10,
            )
            .spell()
        };
        let all = page(0);
        assert!(all.contains("0x1 8 ascii \"<\\system>\""), "{all}");
        assert!(all.contains("0x13 9 ascii \"<\\/system>\""), "{all}");
        assert_eq!(crate::text::aimed_lines(&all), 2, "{all}");
        let last = page(2);
        assert!(last.contains("0x13 9 ascii \"<\\/system>\""), "{last}");
    }

    /// Returns what the text filter answers of a row: its whole text
    /// lowered contains the lowered needle.
    ///
    /// # Arguments
    ///
    /// * `p` - The program the row indexes.
    /// * `row` - The row.
    /// * `needle` - The filter as given.
    fn text_accepts(p: &Program, row: &StringRow, needle: &str) -> bool {
        row.full_text(&p.bytes)
            .to_lowercase()
            .contains(&needle.to_lowercase())
    }

    /// A filter given in any case matches a span and a .NET user string
    /// holding it in another.
    ///
    /// # Panics
    ///
    /// When either row is missed.
    #[test]
    fn a_needle_matches_in_any_case() {
        let p = raw(b"a foo here\0".to_vec());
        let span = StringRow::Span(find_ascii_spans(&p.bytes, 5)[0]);
        let hit = StringRow::Hit(StringHit {
            off: 0,
            len: 10,
            text: "a fOO here".to_owned(),
            encoding: Encoding::DotnetUs,
        });
        let needle = Needle::new("Foo");
        assert!(row_matches(&p, &span, Some(&needle)));
        assert!(row_matches(&p, &hit, Some(&needle)));
    }

    /// The zero-copy span filter answers what the text filter answers for
    /// every row shape: ASCII and UTF-16 spans, case folds, a needle past
    /// the display cut, and a non-ASCII needle no walked text holds.
    ///
    /// # Panics
    ///
    /// When the byte test disagrees with the lowered-text test.
    #[test]
    fn span_filter_answers_what_the_text_filter_answers() {
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(b"Kernel32.DLL\x00");
        bytes.extend_from_slice(b"short\x00");
        bytes.extend_from_slice(&[
            b'L', 0, b'o', 0, b'N', 0, b'g', 0, b'W', 0, b'i', 0, b'd', 0, b'e', 0,
        ]);
        bytes.push(0);
        let long: Vec<u8> = b"xyzABCDEFGH".iter().cycle().take(600).copied().collect();
        bytes.extend_from_slice(&long);
        bytes.push(0);
        let p = raw(bytes);
        let rows: Vec<StringRow> = find_ascii_spans(&p.bytes, 4)
            .into_iter()
            .map(StringRow::Span)
            .chain(
                find_wide_spans(&p.bytes, 4)
                    .into_iter()
                    .map(StringRow::Span),
            )
            .collect();
        assert_eq!(rows.len(), 4, "{rows:?}");
        for needle in [
            "kernel32",
            "KERNEL32.DLL",
            "short",
            "wide",
            "lOnGwIdE",
            "xyzabcdefgh",
            "ü",
            "",
        ] {
            for row in &rows {
                let want = text_accepts(&p, row, needle);
                assert_eq!(
                    row_matches(&p, row, Some(&Needle::new(needle))),
                    want,
                    "{needle:?} at {:?}",
                    row.full_text(&p.bytes)
                );
            }
        }
    }

    /// The span filter and the text filter agree on the needle edge
    /// cases: mixed case, a needle longer than the string, one that is
    /// the string, and one holding NULs.
    ///
    /// # Panics
    ///
    /// When the span filter and the text filter disagree on a needle.
    #[test]
    fn span_filter_agrees_on_needle_edge_cases() {
        let mut bytes: Vec<u8> = b"Kernel32.DLL\x00".to_vec();
        bytes.extend(b"LoNgWiDe".iter().flat_map(|b| [*b, 0]));
        bytes.push(0);
        let p = raw(bytes);
        let rows: Vec<StringRow> = find_ascii_spans(&p.bytes, 4)
            .into_iter()
            .map(StringRow::Span)
            .chain(
                find_wide_spans(&p.bytes, 4)
                    .into_iter()
                    .map(StringRow::Span),
            )
            .collect();
        assert_eq!(rows.len(), 2, "{rows:?}");
        for needle in [
            "Kernel32.DLL",
            "KERNEL32.dll",
            "LoNgWiDe",
            "lOnGwIdE",
            "Kernel32.DLL_EXTRA",
            "\0",
            "32.D\0L",
        ] {
            for row in &rows {
                let want = text_accepts(&p, row, needle);
                assert_eq!(
                    row_matches(&p, row, Some(&Needle::new(needle))),
                    want,
                    "needle {needle:?} on {:?}",
                    row.full_text(&p.bytes)
                );
            }
        }
    }
}
