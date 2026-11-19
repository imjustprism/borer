//! Byte-pattern and text search over every byte of the file, and the
//! search form that combines patterns, texts and values ([`spec`],
//! [`form`]).

use crate::program::Program;

mod code;
pub mod form;
pub mod spec;

/// Hard cap on reported hits per query.
pub const HITS_MAX: usize = 500;

/// Parses an AOB pattern of whole bytes such as `48 8b ?? ff`: the
/// whole-byte form of what [`parse_masked`] reads.
///
/// # Arguments
///
/// * `s` - Whitespace-separated tokens: two hex digits, or `?`/`??` for a wildcard.
///
/// # Returns
///
/// One entry per token (`None` is a wildcard), or `None` when
/// [`parse_masked`] refuses the pattern or a token fixes a nibble alone.
pub fn parse_pattern(s: &str) -> Option<Vec<Option<u8>>> {
    parse_masked(s)
        .ok()?
        .lanes()
        .iter()
        .map(|l| match l.mask {
            0xff => Some(Some(l.value)),
            0 => Some(None),
            _ => None,
        })
        .collect()
}

/// Most bytes one masked pattern holds: past it every candidate's verify
/// costs more than the scan it narrows.
pub const PATTERN_MAX: usize = 4096;

/// One byte of a masked pattern: the bits it fixes and their value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lane {
    /// The fixed bits' value; zero outside `mask`.
    pub value: u8,
    /// The bits the pattern fixes: `0xff` a whole byte, `0xf0` or `0x0f` a
    /// nibble, `0` any byte.
    pub mask: u8,
}

/// A masked byte pattern: one to [`PATTERN_MAX`] lanes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern(Vec<Lane>);

impl Pattern {
    /// Returns the pattern of these lanes.
    ///
    /// # Arguments
    ///
    /// * `lanes` - The lanes, first byte first.
    ///
    /// # Returns
    ///
    /// The pattern, or `None` when it has no lane or more than
    /// [`PATTERN_MAX`].
    #[must_use]
    pub fn new(lanes: Vec<Lane>) -> Option<Self> {
        (!lanes.is_empty() && lanes.len() <= PATTERN_MAX).then_some(Pattern(lanes))
    }

    /// Returns the pattern's lanes, never empty.
    #[must_use]
    pub fn lanes(&self) -> &[Lane] {
        &self.0
    }

    /// Returns the bytes past its first a match covers: its length less one.
    pub(crate) fn reach(&self) -> usize {
        self.0.len().saturating_sub(1)
    }
}

impl From<Option<u8>> for Lane {
    /// Returns a whole fixed byte, or any byte for `None`.
    fn from(b: Option<u8>) -> Self {
        b.map_or(Lane { value: 0, mask: 0 }, |value| Lane {
            value,
            mask: 0xff,
        })
    }
}

/// Parses a masked byte pattern such as `48 8b 4? ?? ff`.
///
/// # Arguments
///
/// * `s` - Whitespace-separated tokens: two hex digits (`8b`), a hex digit
///   and `?` for a nibble (`4?` fixes the high one, `?8` the low one), or
///   `?`/`??` for any byte.
///
/// # Returns
///
/// The pattern.
///
/// # Errors
///
/// When the pattern has no token, more than [`PATTERN_MAX`], or a token of
/// another form, naming its column (characters from 1) and the forms a
/// token takes.
pub fn parse_masked(s: &str) -> Result<Pattern, String> {
    masked_at(s, 0).map_err(|(at, why)| format!("column {}: {why}", column(s, at)))
}

/// Returns the column of a byte offset in a text: characters from 1.
///
/// # Arguments
///
/// * `text` - The text.
/// * `at` - A byte offset in it.
pub(crate) fn column(text: &str, at: usize) -> usize {
    text.get(..at)
        .map_or(at, |head| head.chars().count())
        .saturating_add(1)
}

/// Parses a masked byte pattern that starts `base` bytes into a longer
/// text ([`parse_masked`]).
///
/// # Arguments
///
/// * `s` - The pattern.
/// * `base` - Its byte offset in the text it came from.
///
/// # Returns
///
/// The pattern.
///
/// # Errors
///
/// As [`parse_masked`], with the byte offset of the fault in the longer
/// text.
pub(crate) fn masked_at(s: &str, base: usize) -> Result<Pattern, (usize, String)> {
    let mut lanes = Vec::new();
    for (at, tok) in words(s) {
        let at = at.saturating_add(base);
        let lane = lane(tok).ok_or_else(|| {
            (
                at,
                format!(
                    "{} is not a byte; write two hex digits (8b), a hex digit and ? for a nibble (4? or ?8), or ? or ?? for any byte",
                    crate::text::quoted(tok)
                ),
            )
        })?;
        if lanes.len() == PATTERN_MAX {
            return Err((
                at,
                format!("a byte pattern holds at most {PATTERN_MAX} bytes"),
            ));
        }
        lanes.push(lane);
    }
    Pattern::new(lanes).ok_or_else(|| {
        (
            base,
            "the byte pattern has no byte; write hex bytes such as 48 8b ?? 4?".to_owned(),
        )
    })
}

/// Returns the whitespace-separated words of `s`, each with the byte
/// offset it starts at.
///
/// # Arguments
///
/// * `s` - The text.
pub(crate) fn words(s: &str) -> impl Iterator<Item = (usize, &str)> {
    s.char_indices()
        .filter(|&(i, c)| {
            !c.is_whitespace()
                && s.get(..i)
                    .and_then(|head| head.chars().next_back())
                    .is_none_or(char::is_whitespace)
        })
        .filter_map(|(i, _)| {
            let tail = s.get(i..)?;
            tail.split(char::is_whitespace).next().map(|w| (i, w))
        })
}

/// Reads one masked pattern token.
///
/// # Arguments
///
/// * `tok` - The token: `8b`, `4?`, `?8`, `??` or `?`.
///
/// # Returns
///
/// The lane, or `None` for any other token.
fn lane(tok: &str) -> Option<Lane> {
    let nibble = |c: u8| match c {
        b'?' => Some(None),
        b'0'..=b'9' => Some(Some(c - b'0')),
        b'a'..=b'f' => Some(Some(c - b'a' + 10)),
        b'A'..=b'F' => Some(Some(c - b'A' + 10)),
        _ => None,
    };
    let (hi, lo) = match tok.as_bytes() {
        [b'?'] => (None, None),
        [h, l] => (nibble(*h)?, nibble(*l)?),
        _ => return None,
    };
    Some(Lane {
        value: (hi.unwrap_or(0) << 4) | lo.unwrap_or(0),
        mask: hi.map_or(0, |_| 0xf0) | lo.map_or(0, |_| 0x0f),
    })
}

/// One search match.
#[derive(Debug, Clone)]
pub struct Hit {
    /// Virtual address of the match, when the bytes are mapped.
    pub va: Option<u64>,
    /// File offset of the match.
    pub file_off: u64,
}

/// One page of a search and the count of every match.
#[derive(Debug, Default)]
pub struct Hits {
    /// The page: hits in section order, then address order, then those in
    /// bytes no section maps in file order; at most [`HITS_MAX`] of them.
    pub hits: Vec<Hit>,
    /// Every match in the image, the page and the skipped ones included.
    pub total: usize,
}

/// Scans every section, then the bytes no section maps, for `pattern`.
///
/// The whole-byte case of [`find_masked`]: each `None` is any byte.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `pattern` - Bytes with `None` wildcards, as produced by [`parse_pattern`].
/// * `offset` - Matches to skip before the page starts.
///
/// # Returns
///
/// The page after `offset` and the total, both empty for an empty pattern
/// or one longer than [`PATTERN_MAX`].
///
/// # Errors
///
/// When some file byte is mapped at more addresses than a byte or text
/// search walks ([`form::page`]).
pub fn find_bytes(
    program: &Program,
    pattern: &[Option<u8>],
    offset: usize,
) -> Result<Hits, String> {
    Pattern::new(pattern.iter().map(|&b| Lane::from(b)).collect())
        .map_or_else(|| Ok(Hits::default()), |p| find_masked(program, &p, offset))
}

/// Scans every section, then the bytes no section maps, for a masked
/// pattern, each file byte once.
///
/// The search form's scan ([`form::page`]) with no deadline. The scan is
/// anchored: the pattern's rarest fully fixed byte names an anchor, and
/// eight bytes are tested at a time with [`eq_mask`], so a word with no
/// anchor byte in it is rejected in a handful of instructions instead of
/// one window compare per offset. Each candidate is then verified by
/// whole-word compares against the pattern compiled into `(expected,
/// mask)` chunks ([`compile_pattern`]): one xor, and and a test cover
/// eight pattern bytes, nibbles and wildcards included. A pattern with no
/// fully fixed byte has no anchor and keeps the per-window walk, which for
/// wildcards alone answers a match at every offset. A verify costs time in
/// proportion to the pattern's length, so a scan where most offsets are
/// candidates costs the file's length times the pattern's; the search
/// form's chunks shrink as the pattern grows, so the deadline is read as
/// often.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `pattern` - The pattern, as produced by [`parse_masked`].
/// * `offset` - Matches to skip before the page starts.
///
/// # Returns
///
/// The page after `offset` and the total.
///
/// # Errors
///
/// When some file byte is mapped at more addresses than a byte or text
/// search walks ([`form::page`]).
pub fn find_masked(program: &Program, pattern: &Pattern, offset: usize) -> Result<Hits, String> {
    form::page(program, form::Needle::Bytes(pattern), offset, &mut |_| {
        false
    })
}

/// A masked pattern ready to scan: its lanes, its compare chunks and its
/// anchor.
#[derive(Debug)]
pub(crate) struct Finder<'p> {
    /// The pattern.
    lanes: &'p [Lane],
    /// The pattern as [`compile_pattern`] holds it: its chunks that fix
    /// a bit.
    chunks: Vec<Chunk>,
    /// The anchor's offset in the pattern and its byte ([`anchor_of`]);
    /// `None` when no byte is fully fixed.
    anchor: Option<(usize, u8)>,
}

impl<'p> Finder<'p> {
    /// Compiles a pattern and chooses its anchor from a sample of `file`.
    ///
    /// # Arguments
    ///
    /// * `pattern` - The pattern.
    /// * `file` - The file the scan will walk, for the anchor's sample.
    pub(crate) fn new(pattern: &'p Pattern, file: &[u8]) -> Self {
        let lanes = pattern.lanes();
        Finder {
            lanes,
            chunks: compile_pattern(lanes),
            anchor: anchor_of(lanes, file),
        }
    }

    /// Hands `visit` the offset in the span of each match starting in
    /// its run, ascending.
    ///
    /// # Arguments
    ///
    /// * `span` - The run and the bytes after it a match may cover.
    /// * `visit` - Called with each match's offset in the span.
    pub(crate) fn each(&self, span: &Span<'_>, mut visit: impl FnMut(u64)) {
        let Some(last) = span.data.len().checked_sub(self.lanes.len()) else {
            return;
        };
        let Some((anchor_at, anchor)) = self.anchor else {
            for (i, w) in (0..span.own).zip(span.data.windows(self.lanes.len())) {
                if compiled_match(w, self.lanes, &self.chunks) {
                    visit(i);
                }
            }
            return;
        };
        let mut test = |z: usize| {
            if let Some(i) = z.checked_sub(anchor_at)
                && i <= last
                && crate::num::from_usize(i) < span.own
                && compiled_match(&span.data[i..], self.lanes, &self.chunks)
            {
                visit(crate::num::from_usize(i));
            }
        };
        let (words, _tail) = span.data.as_chunks::<8>();
        for (k, w) in words.iter().enumerate() {
            let mut m = eq_mask(u64::from_le_bytes(*w), anchor);
            while m != 0 {
                test(k * 8 + crate::num::saturating_usize(u64::from(m.trailing_zeros() / 8)));
                m &= m - 1;
            }
        }
        for z in words.len() * 8..span.data.len() {
            if span.data[z] == anchor {
                test(z);
            }
        }
    }
}

/// Bytes of the file the anchor's frequency is counted over, a bound on
/// the cost of choosing it.
const ANCHOR_SAMPLE: usize = 32 << 10;
/// Most distinct fixed bytes one pattern's anchor choice considers; a
/// longer pattern's bytes repeat these or lose nothing by it.
const ANCHOR_CANDIDATES: usize = 8;

/// Chooses the pattern's anchor: the position and value of the fully
/// fixed byte least frequent in a sample of the file.
///
/// Every candidate the scan tests is an anchor hit, and the anchor is
/// the one byte a pattern can pick to be tested least: a frequency count
/// over the file's head answers which fixed byte that is, and the rarest
/// one wins, ties to the smallest byte value. A byte the sample never
/// sees is the rarest of all; should the file hold a section that begins
/// with it, the verify each candidate pays stays correct, only less
/// selective. At most [`ANCHOR_CANDIDATES`] distinct bytes are counted,
/// each a word-wise pass over [`ANCHOR_SAMPLE`] bytes, so the choice
/// costs microseconds against the whole-file scan it narrows. A nibble
/// is never an anchor: the word test compares whole bytes.
///
/// # Arguments
///
/// * `lanes` - The pattern, as produced by [`parse_masked`].
/// * `file` - The file the scan will walk, for the frequency sample.
///
/// # Returns
///
/// The anchor's offset in the pattern and its byte, or `None` when no
/// byte is fully fixed.
fn anchor_of(lanes: &[Lane], file: &[u8]) -> Option<(usize, u8)> {
    let mut candidates: Vec<u8> = Vec::new();
    for l in lanes.iter().filter(|l| l.mask == 0xff) {
        if !candidates.contains(&l.value) && candidates.len() < ANCHOR_CANDIDATES {
            candidates.push(l.value);
        }
    }
    let sample = &file[..file.len().min(ANCHOR_SAMPLE)];
    let (words, _tail) = sample.as_chunks::<8>();
    let best = candidates
        .iter()
        .map(|&b| {
            let hits = words
                .iter()
                .map(|w| eq_mask(u64::from_le_bytes(*w), b).count_ones())
                .sum::<u32>()
                + u32::try_from(
                    sample[words.len() * 8..]
                        .iter()
                        .filter(|&&x| x == b)
                        .count(),
                )
                .unwrap_or(u32::MAX);
            (hits, b)
        })
        .min_by_key(|&(hits, b)| (hits, b))
        .map(|(_, b)| b)?;
    let at = lanes
        .iter()
        .position(|l| l.mask == 0xff && l.value == best)?;
    Some((at, best))
}

/// One eight-byte compare of a compiled pattern: the offset of its first
/// lane in the pattern, the fixed bits' values and the mask of the fixed
/// bits.
type Chunk = (usize, u64, u64);

/// Compiles a masked pattern into eight-byte `(base, expected, mask)`
/// compares, keeping only the chunks that fix a bit.
///
/// Chunk `k` covers the pattern's bytes `8k..8k+8`: `expected` holds each
/// lane's fixed bits in its lane, and `mask` the lane's mask (`0xff` a
/// whole byte, `0xf0` or `0x0f` a nibble, zero any byte). A window chunk
/// matches when `(window_word ^ expected) & mask` is zero, eight bytes
/// compared with three instructions whatever the wildcards; a chunk of
/// wildcards alone compares nothing and is dropped, so a pattern of them
/// costs nothing per window.
///
/// # Arguments
///
/// * `lanes` - The pattern's lanes.
///
/// # Returns
///
/// The compares in pattern order, the last possibly short.
fn compile_pattern(lanes: &[Lane]) -> Vec<Chunk> {
    lanes
        .chunks(8)
        .enumerate()
        .map(|(k, chunk)| {
            let (mut expected, mut mask) = (0u64, 0u64);
            for (lane, l) in chunk.iter().enumerate() {
                expected |= u64::from(l.value & l.mask) << (8 * lane);
                mask |= u64::from(l.mask) << (8 * lane);
            }
            (8 * k, expected, mask)
        })
        .filter(|&(_, _, mask)| mask != 0)
        .collect()
}

/// Whether the pattern holds at the head of `rest`, one whole word at a
/// time.
///
/// Each chunk's eight bytes compare in a single xor and and against the
/// rest as it lies, wildcards masked away; the last chunk may be short,
/// where its remaining lanes compare byte by byte. The caller guarantees
/// `rest` holds at least the pattern's length, so a whole-chunk compare
/// never reads past what stands there.
///
/// # Arguments
///
/// * `rest` - The bytes from the candidate position on.
/// * `lanes` - The pattern sought.
/// * `chunks` - The pattern as [`compile_pattern`] holds it.
///
/// # Returns
///
/// Whether every fixed bit of the pattern equals the rest's bit at its
/// place.
fn compiled_match(rest: &[u8], lanes: &[Lane], chunks: &[Chunk]) -> bool {
    chunks.iter().all(|&(base, expected, mask)| {
        match rest.get(base..).and_then(|r| r.first_chunk::<8>()) {
            Some(word) => (u64::from_le_bytes(*word) ^ expected) & mask == 0,
            None => lanes
                .get(base..)
                .unwrap_or_default()
                .iter()
                .zip(rest.get(base..).unwrap_or_default())
                .all(|(l, b)| b & l.mask == l.value & l.mask),
        }
    })
}

/// Scans every section, then the bytes no section maps, for a text needle,
/// folding ASCII case and finding its UTF-16LE spelling too.
///
/// Matching is case-insensitive for ASCII letters, like the `strings`
/// filter, so a lower-case query finds a capitalized identifier. Each match
/// is sought both as the needle's UTF-8 bytes and as its UTF-16LE code
/// units, because some programs store UI and locale keys as wide strings that
/// a byte-only scan never sees. A needle outside ASCII is encoded as UTF-16
/// itself: spreading its UTF-8 bytes over zero high halves spelled no wide
/// string at all. Hits stay in section-then-address order.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `needle` - The text to find.
/// * `offset` - Matches to skip before the page starts.
///
/// # Returns
///
/// The page after `offset` and the total, both empty for an empty needle.
///
/// # Errors
///
/// When some file byte is mapped at more addresses than a byte or text
/// search walks ([`form::page`]).
pub fn find_text(program: &Program, needle: &str, offset: usize) -> Result<Hits, String> {
    spec::Text::new(needle).map_or_else(
        || Ok(Hits::default()),
        |t| form::page(program, form::Needle::Text(&t), offset, &mut |_| false),
    )
}

/// Returns a page of a needle's hits in the order the file is walked, and
/// their count, stopping at the request's deadline ([`crate::cancel`]).
///
/// # Arguments
///
/// * `program` - The program.
/// * `needle` - What to find.
/// * `offset` - Hits to skip before the page.
///
/// # Returns
///
/// The page, at most [`HITS_MAX`] hits, and the total.
///
/// # Errors
///
/// When some file byte is mapped at more than 8 addresses (the search
/// refuses rather than walk it once per address, [`form::page`]), or
/// when the request's deadline passes before the walk ends.
pub fn find(program: &Program, needle: form::Needle<'_>, offset: usize) -> Result<Hits, String> {
    form::page(program, needle, offset, &mut |_| {
        crate::cancel::Cancel::raised()
    })
}

/// How a text hit is spelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Spelling {
    /// As its UTF-8 bytes.
    Utf8,
    /// As UTF-16LE code units.
    Utf16,
}

/// Returns where a text starts in a span's run, ascending, each with its
/// spelling; where both spellings start at one offset, the UTF-8 one.
///
/// # Arguments
///
/// * `span` - The run and the bytes after it a match may cover.
/// * `narrow` - The text's UTF-8 bytes.
/// * `wide` - Its UTF-16LE code units, low byte first.
/// * `limit` - Most hits worth keeping; the first ones are kept.
pub(crate) fn text_hits(
    span: &Span<'_>,
    narrow: &[u8],
    wide: &[u8],
    limit: usize,
) -> Vec<(u64, Spelling)> {
    let mut here: Vec<(u64, Spelling)> = Vec::new();
    ascii_hits(span.data, narrow, span.own, limit, &mut here);
    wide_hits(span.data, wide, span.own, limit, &mut here);
    here.sort_unstable();
    here.dedup_by_key(|h| h.0);
    here.truncate(limit);
    here
}

/// Collects the offsets where `data` holds `needle` under ASCII case folding.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The bytes sought; nothing is collected for an empty one.
/// * `own` - Offsets a match may start before.
/// * `limit` - Most hits collected.
/// * `out` - Where the matching offsets go, ascending, as UTF-8 hits.
fn ascii_hits(data: &[u8], needle: &[u8], own: u64, limit: usize, out: &mut Vec<(u64, Spelling)>) {
    let Some(&first) = needle.first() else {
        return;
    };
    let mut kept = 0;
    candidate_hits(
        data,
        needle.len(),
        folded_pair(first),
        |w| w.eq_ignore_ascii_case(needle),
        |i| {
            if i >= own {
                return true;
            }
            out.push((i, Spelling::Utf8));
            kept += 1;
            kept >= limit
        },
    );
}

/// Collects the offsets where `data` holds the UTF-16LE code units `wide`,
/// an ASCII unit's letter compared under case folding.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `wide` - The code units sought, low byte first; nothing is collected
///   for an empty one.
/// * `own` - Offsets a match may start before.
/// * `limit` - Most hits collected.
/// * `out` - Where the matching offsets go, ascending, as UTF-16 hits.
fn wide_hits(data: &[u8], wide: &[u8], own: u64, limit: usize, out: &mut Vec<(u64, Spelling)>) {
    let [lo, hi, ..] = *wide else {
        return;
    };
    let first = if hi == 0 { folded_pair(lo) } else { (lo, lo) };
    let mut kept = 0;
    candidate_hits(
        data,
        wide.len(),
        first,
        |w| utf16le_eq_ignore_ascii_case(w, wide),
        |i| {
            if i >= own {
                return true;
            }
            out.push((i, Spelling::Utf16));
            kept += 1;
            kept >= limit
        },
    );
}

/// Tells whether `data` holds `needle` verbatim somewhere.
///
/// The candidate scan of [`candidate_hits`], stopped at the first match,
/// where a window-by-window compare took a tenth of a second per needle on
/// a hundred-megabyte file.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The bytes sought; an empty one is never held.
pub(crate) fn holds(data: &[u8], needle: &[u8]) -> bool {
    let Some(&first) = needle.first() else {
        return false;
    };
    candidate_hits(
        data,
        needle.len(),
        (first, first),
        |w| w == needle,
        |_| true,
    )
}

/// Hands `hit` the offset of each window of `data` that `matches` accepts,
/// in ascending order until it says stop, testing only the windows whose
/// first byte is one of `first`.
///
/// The first byte picks the positions the full compare runs at: a text
/// search tests every byte offset of every section, and the compare at
/// every window was the whole cost of the query. The candidate scan reads
/// eight bytes at a time ([`eq_mask`]), the tail byte by byte.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `n` - The window length.
/// * `first` - The two spellings of the window's first byte.
/// * `matches` - The full compare of one window.
/// * `hit` - Called with each matching offset; `true` ends the scan.
///
/// # Returns
///
/// Whether `hit` ended the scan.
fn candidate_hits(
    data: &[u8],
    n: usize,
    first: (u8, u8),
    matches: impl Fn(&[u8]) -> bool,
    mut hit: impl FnMut(u64) -> bool,
) -> bool {
    let Some(last) = data.len().checked_sub(n) else {
        return false;
    };
    let (lo, hi) = first;
    let (words, _tail) = data.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let word = u64::from_le_bytes(*w);
        let mut m = eq_mask(word, lo) | eq_mask(word, hi);
        while m != 0 {
            let i = k * 8 + crate::num::saturating_usize(u64::from(m.trailing_zeros() / 8));
            m &= m - 1;
            if i <= last && matches(&data[i..i + n]) && hit(crate::num::from_usize(i)) {
                return true;
            }
        }
    }
    for i in words.len() * 8..=last {
        let b = data[i];
        if (b == lo || b == hi) && matches(&data[i..i + n]) && hit(crate::num::from_usize(i)) {
            return true;
        }
    }
    false
}

/// A `u64` of `0x01` bytes, the subtrahend of the byte-equal test.
const ONES: u64 = 0x0101_0101_0101_0101;
/// A `u64` of `0x80` bytes, one high bit per byte of a mask.
const HIGH: u64 = 0x8080_8080_8080_8080;

/// The bytes of `word` equal to `v`, as one bit per byte at the byte's own
/// place (bit `8 * k` for byte `k`).
///
/// The borrow trick: a zero byte of `x = word ^ v` turns the subtraction's
/// borrow into a high bit that `!x` keeps. A borrow that crosses a `0x01`
/// byte flags that byte too, so the mask is a superset of the equal bytes:
/// a false candidate only costs the full compare the caller runs, and a
/// true one is never missed.
///
/// # Arguments
///
/// * `word` - The eight bytes tested.
/// * `v` - The byte sought.
///
/// # Returns
///
/// The equality mask.
pub(crate) fn eq_mask(word: u64, v: u8) -> u64 {
    let x = word ^ (u64::from(v) * ONES);
    x.wrapping_sub(ONES) & !x & HIGH
}

/// The two spellings a case-folded compare of `b` accepts.
///
/// A byte with no ASCII case yields itself twice, so the pair test that
/// picks candidate positions never rejects the one spelling that matches.
///
/// # Arguments
///
/// * `b` - The needle byte whose positions are candidates.
///
/// # Returns
///
/// `(lower, upper)` spellings of `b`.
fn folded_pair(b: u8) -> (u8, u8) {
    (b.to_ascii_lowercase(), b.to_ascii_uppercase())
}

/// One run of bytes a search walks, with the bytes after it that a match
/// starting inside it may run on into.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Span<'a> {
    /// The run's bytes, then up to the search's reach of the file's next
    /// bytes.
    data: &'a [u8],
    /// Length of the run itself in bytes; a match must start before it.
    own: u64,
    /// File offset of the run's first byte.
    off: u64,
    /// Virtual address of the run's first byte; `None` where no section
    /// maps it.
    va: Option<u64>,
}

/// Whether `window` holds the UTF-16LE code units `wide`, case-folded where
/// a unit is ASCII.
///
/// A unit with a zero high byte compares its low byte under ASCII case
/// folding; any other unit compares exactly, so a high byte that happens to
/// spell a letter is never folded.
///
/// # Arguments
///
/// * `window` - A slice exactly as long as `wide`.
/// * `wide` - The code units, low byte first.
fn utf16le_eq_ignore_ascii_case(window: &[u8], wide: &[u8]) -> bool {
    window.len() == wide.len()
        && window
            .chunks_exact(2)
            .zip(wide.chunks_exact(2))
            .all(|(w, n)| {
                w[1] == n[1]
                    && if n[1] == 0 {
                        w[0].eq_ignore_ascii_case(&n[0])
                    } else {
                        w[0] == n[0]
                    }
            })
}

/// Demangles a decorated symbol, or returns the name unchanged.
///
/// MSVC names start with `?`; Itanium C++ and Rust names start with `_Z`
/// (Rust legacy) or `_R` (Rust v0). Rust is tried first because its legacy
/// scheme is a subset of Itanium's; the Rust hash suffix is dropped.
///
/// # Arguments
///
/// * `name` - A symbol name in any scheme.
///
/// # Returns
///
/// The demangled signature (`space::foo(int, bool, char)`,
/// `core::ptr::drop_in_place`), or `name` itself when it is not decorated
/// or cannot be demangled.
pub fn demangled_or_raw(name: &str) -> String {
    demangle(name, Demangled::Signature)
}

/// Demangles a decorated symbol to its bare qualified name.
///
/// The form used for function names in listings and pseudo-C: no return
/// type, no parameter list, no access specifiers (`space::foo`,
/// `type_info::~type_info`). Compiler clone suffixes (`.cold.12`, `.part.3`,
/// `.constprop.0`) stay appended to the demangled head.
///
/// # Arguments
///
/// * `name` - A symbol name in any scheme.
///
/// # Returns
///
/// The bare name, or `name` itself when it is not decorated or cannot be demangled.
pub fn demangled_name(name: &str) -> String {
    demangle(name, Demangled::Name)
}

/// How much of a demangled symbol is kept.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Demangled {
    /// The whole signature: return type, parameters and access specifiers.
    Signature,
    /// The qualified name alone.
    Name,
}

/// Demangles MSVC (`?`), Rust (`_Z`/`_R`, tried first: its legacy scheme is a
/// subset of Itanium's) and Itanium C++ (`_Z`) names.
///
/// An import carries its library as a `dll!` prefix; the prefix stays and the
/// name after it is what gets demangled, since every scheme is recognized by
/// its first character and the prefix would hide it.
///
/// # Arguments
///
/// * `name` - A symbol name in any scheme, with or without a `dll!` prefix.
/// * `keep` - The whole signature, or the name alone.
///
/// # Returns
///
/// The demangled text, or `name` itself when nothing applies.
fn demangle(name: &str, keep: Demangled) -> String {
    if let Some((dll, tail)) = name.split_once('!') {
        return format!("{dll}!{}", demangle(tail, keep));
    }
    if name.starts_with('?') {
        let flags = match keep {
            Demangled::Name => msvc_demangler::DemangleFlags::NAME_ONLY,
            Demangled::Signature => msvc_demangler::DemangleFlags::COMPLETE,
        };
        return msvc_demangler::demangle(name, flags).unwrap_or_else(|_| name.to_owned());
    }
    if !(name.starts_with("_Z") || name.starts_with("_R")) {
        return name.to_owned();
    }
    let (head, suffix) = name.find('.').map_or((name, ""), |i| name.split_at(i));
    if let Ok(rust) = rustc_demangle::try_demangle(head) {
        return format!("{rust:#}{suffix}");
    }
    let options = match keep {
        Demangled::Name => cpp_demangle::DemangleOptions::new()
            .no_params()
            .no_return_type(),
        Demangled::Signature => cpp_demangle::DemangleOptions::new(),
    };
    if let Ok(sym) = cpp_demangle::Symbol::new(head)
        && let Ok(text) = sym.demangle_with_options(&options)
    {
        return format!("{text}{suffix}");
    }
    name.to_owned()
}

#[cfg(test)]
mod tests {
    use super::{Lane, compile_pattern, holds};

    /// A chunk of wildcards alone compares nothing and is dropped, so a
    /// pattern of them costs nothing per window; a chunk with one fixed
    /// bit is kept.
    ///
    /// # Panics
    ///
    /// When a wildcard chunk is kept or a fixed one dropped.
    #[test]
    fn a_chunk_of_wildcards_compares_nothing() {
        assert!(compile_pattern(&[Lane::from(None); 16]).is_empty());
        let mut lanes = [Lane::from(None); 16];
        lanes[9] = Lane {
            value: 1,
            mask: 0x0f,
        };
        assert_eq!(compile_pattern(&lanes), vec![(8, 0x100, 0xf00)]);
    }

    /// A needle is found wherever it sits: at the start, across a word
    /// boundary, in the tail the word scan leaves, and among many copies;
    /// an absent, empty or longer needle is not.
    ///
    /// # Panics
    ///
    /// When a needle is found or missed wrongly.
    #[test]
    fn holds_finds_a_needle_anywhere_and_nothing_else() {
        let data = b"abcdefghijklmnopqrstuvwxyz0123456789";
        assert!(holds(data, b"abc"), "at the start");
        assert!(holds(data, b"ghijk"), "across a word boundary");
        assert!(holds(data, b"6789"), "in the tail");
        assert!(holds(data, data), "the whole");
        assert!(holds(&[b'x'; 4096], b"xxxx"), "among many copies");
        assert!(!holds(data, b"abx"), "a near miss");
        assert!(!holds(data, b""), "an empty needle");
        assert!(!holds(b"abc", b"abcd"), "a needle longer than the bytes");
    }
}
