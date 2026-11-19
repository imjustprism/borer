//! Byte-pattern and text search over every byte of the file, and the
//! search form that combines patterns, texts and values ([`spec`],
//! [`form`]).

use crate::program::{Program, Section};

pub mod form;
pub mod spec;

/// Hard cap on reported hits per query.
pub const HITS_MAX: usize = 500;

/// Parses an AOB pattern such as `48 8b ?? ff` into bytes with wildcards.
///
/// # Arguments
///
/// * `s` - Whitespace-separated tokens: two hex digits, or `?`/`??` for a wildcard.
///
/// # Returns
///
/// One entry per token (`None` is a wildcard), or `None` when any token is
/// malformed: a sign is not a hex digit, though `u8::from_str_radix` takes
/// `+1` for `01`.
pub fn parse_pattern(s: &str) -> Option<Vec<Option<u8>>> {
    s.split_whitespace()
        .map(|tok| match tok {
            "?" | "??" => Some(None),
            t if t.len() == 2 && t.bytes().all(|b| b.is_ascii_hexdigit()) => {
                u8::from_str_radix(t, 16).ok().map(Some)
            }
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
/// One [`Lane`] per token.
///
/// # Errors
///
/// When the pattern has no token, more than [`PATTERN_MAX`], or a token of
/// another form, naming its 1-based column and the forms a token takes.
pub fn parse_masked(s: &str) -> Result<Vec<Lane>, String> {
    masked_at(s, 0)
}

/// Parses a masked byte pattern that starts `base` bytes into a longer
/// text, so a refusal names the column in that text ([`parse_masked`]).
///
/// # Arguments
///
/// * `s` - The pattern.
/// * `base` - Its byte offset in the text it came from.
///
/// # Errors
///
/// As [`parse_masked`].
pub(crate) fn masked_at(s: &str, base: usize) -> Result<Vec<Lane>, String> {
    let mut lanes = Vec::new();
    for (at, tok) in words(s) {
        let at = at.saturating_add(base);
        let lane = lane(tok).ok_or_else(|| {
            format!(
                "column {}: {} is not a byte; write two hex digits (8b), a hex digit and ? for a nibble (4? or ?8), or ? or ?? for any byte",
                at.saturating_add(1),
                crate::text::quoted(tok)
            )
        })?;
        if lanes.len() == PATTERN_MAX {
            return Err(format!(
                "column {}: a byte pattern holds at most {PATTERN_MAX} bytes",
                at.saturating_add(1)
            ));
        }
        lanes.push(lane);
    }
    if lanes.is_empty() {
        return Err("the byte pattern has no byte; write hex bytes such as 48 8b ?? 4?".to_owned());
    }
    Ok(lanes)
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
/// The page after `offset` and the total, both empty for an empty pattern.
pub fn find_bytes(program: &Program, pattern: &[Option<u8>], offset: usize) -> Hits {
    let lanes: Vec<Lane> = pattern.iter().map(|&b| Lane::from(b)).collect();
    find_masked(program, &lanes, offset)
}

/// Scans every section, then the bytes no section maps, for a masked
/// pattern.
///
/// The scan is anchored: the pattern's rarest fully fixed byte names an
/// anchor, and eight bytes are tested at a time with [`eq_mask`], so a
/// word with no anchor byte in it is rejected in a handful of
/// instructions instead of one window compare per offset. Each candidate
/// is then verified by whole-word compares against the pattern compiled
/// into `(expected, mask)` chunks ([`compile_pattern`]): one xor, and and
/// a test cover eight pattern bytes, nibbles and wildcards included. A
/// pattern with no fully fixed byte has no anchor and keeps the
/// per-window walk, which for wildcards alone answers a match at every
/// offset.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `lanes` - The pattern, as produced by [`parse_masked`].
/// * `offset` - Matches to skip before the page starts.
///
/// # Returns
///
/// The page after `offset` and the total, both empty for an empty pattern.
pub fn find_masked(program: &Program, lanes: &[Lane], offset: usize) -> Hits {
    let mut out = Hits::default();
    let Some(reach) = lanes.len().checked_sub(1) else {
        return out;
    };
    let finder = Finder::new(lanes, program.bytes.as_slice());
    for span in spans(program, reach) {
        finder.each(&span, |i| out.push(&span, i, offset));
    }
    out
}

/// A masked pattern ready to scan: its lanes, its compare chunks and its
/// anchor.
#[derive(Debug)]
pub(crate) struct Finder<'p> {
    /// The pattern.
    lanes: &'p [Lane],
    /// The pattern as [`compile_pattern`] holds it.
    chunks: Vec<(u64, u64)>,
    /// The anchor's offset in the pattern and its byte ([`anchor_of`]);
    /// `None` when no byte is fully fixed.
    anchor: Option<(usize, u8)>,
}

impl<'p> Finder<'p> {
    /// Compiles a pattern and chooses its anchor from a sample of `file`.
    ///
    /// # Arguments
    ///
    /// * `lanes` - The pattern; not empty.
    /// * `file` - The file the scan will walk, for the anchor's sample.
    pub(crate) fn new(lanes: &'p [Lane], file: &[u8]) -> Self {
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

/// Compiles a masked pattern into eight-byte `(expected, mask)` compare
/// chunks.
///
/// Chunk `k` covers the pattern's bytes `8k..8k+8`: `expected` holds each
/// lane's fixed bits in its lane, and `mask` the lane's mask (`0xff` a
/// whole byte, `0xf0` or `0x0f` a nibble, zero any byte). A window chunk
/// matches when `(window_word ^ expected) & mask` is zero, eight bytes
/// compared with three instructions whatever the wildcards.
///
/// # Arguments
///
/// * `lanes` - The pattern, as produced by [`parse_masked`].
///
/// # Returns
///
/// One chunk per eight pattern bytes, the last short.
fn compile_pattern(lanes: &[Lane]) -> Vec<(u64, u64)> {
    lanes
        .chunks(8)
        .map(|chunk| {
            let (mut expected, mut mask) = (0u64, 0u64);
            for (lane, l) in chunk.iter().enumerate() {
                expected |= u64::from(l.value & l.mask) << (8 * lane);
                mask |= u64::from(l.mask) << (8 * lane);
            }
            (expected, mask)
        })
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
fn compiled_match(rest: &[u8], lanes: &[Lane], chunks: &[(u64, u64)]) -> bool {
    for (k, (expected, mask)) in chunks.iter().enumerate() {
        let base = 8 * k;
        if mask == &0 {
            continue;
        }
        if let Some(word) = rest.get(base..).and_then(|r| r.first_chunk::<8>()) {
            if (u64::from_le_bytes(*word) ^ expected) & mask != 0 {
                return false;
            }
        } else {
            return lanes[base..]
                .iter()
                .zip(rest.get(base..).unwrap_or(&[]))
                .all(|(l, b)| b & l.mask == l.value & l.mask);
        }
    }
    true
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
pub fn find_text(program: &Program, needle: &str, offset: usize) -> Hits {
    let mut out = Hits::default();
    let narrow = needle.as_bytes();
    let wide: Vec<u8> = needle.encode_utf16().flat_map(u16::to_le_bytes).collect();
    let Some(reach) = narrow.len().max(wide.len()).checked_sub(1) else {
        return out;
    };
    for span in spans(program, reach) {
        for (i, _) in text_hits(&span, narrow, &wide) {
            out.push(&span, i, offset);
        }
    }
    out
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
pub(crate) fn text_hits(span: &Span<'_>, narrow: &[u8], wide: &[u8]) -> Vec<(u64, Spelling)> {
    let mut here: Vec<(u64, Spelling)> = Vec::new();
    ascii_hits(span.data, narrow, &mut here);
    wide_hits(span.data, wide, &mut here);
    here.retain(|&(i, _)| i < span.own);
    here.sort_unstable();
    here.dedup_by_key(|h| h.0);
    here
}

impl Hits {
    /// Counts one match and keeps it when it falls on the page.
    ///
    /// # Arguments
    ///
    /// * `span` - The run the match starts in.
    /// * `i` - The match's offset inside the run.
    /// * `offset` - Matches to skip before the page starts.
    fn push(&mut self, span: &Span<'_>, i: u64, offset: usize) {
        if self.total >= offset && self.hits.len() < HITS_MAX {
            self.hits.push(Hit {
                va: span.va.map(|v| v.saturating_add(i)),
                file_off: span.off.saturating_add(i),
            });
        }
        self.total += 1;
    }
}

/// Collects the offsets where `data` holds `needle` under ASCII case folding.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The bytes sought; nothing is collected for an empty one.
/// * `out` - Where the matching offsets go, ascending, as UTF-8 hits.
fn ascii_hits(data: &[u8], needle: &[u8], out: &mut Vec<(u64, Spelling)>) {
    let Some(&first) = needle.first() else {
        return;
    };
    candidate_hits(
        data,
        needle.len(),
        folded_pair(first),
        |w| w.eq_ignore_ascii_case(needle),
        |i| {
            out.push((i, Spelling::Utf8));
            false
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
/// * `out` - Where the matching offsets go, ascending, as UTF-16 hits.
fn wide_hits(data: &[u8], wide: &[u8], out: &mut Vec<(u64, Spelling)>) {
    let [lo, hi, ..] = *wide else {
        return;
    };
    let first = if hi == 0 { folded_pair(lo) } else { (lo, lo) };
    candidate_hits(
        data,
        wide.len(),
        first,
        |w| utf16le_eq_ignore_ascii_case(w, wide),
        |i| {
            out.push((i, Spelling::Utf16));
            false
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

/// Returns the bytes a search walks: each section's file extent with its
/// address, then the runs no section maps ([`Program::unmapped`]), which
/// have none.
///
/// An overlay, the headers and a file with no sections at all hold bytes
/// worth finding; a search confined to the sections would skip every byte
/// of a file that has none. Each run carries the `reach` bytes the file
/// holds after it, so a match that starts in one section and ends in the
/// next is found where it starts: cut at the section's end, it was found
/// nowhere.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `reach` - Bytes past a run's end a match may cover: the pattern's
///   length less one.
///
/// # Returns
///
/// One [`Span`] per run.
fn spans(program: &Program, reach: usize) -> Vec<Span<'_>> {
    let mut spans = section_spans(program, reach, |_| true);
    spans.extend(
        program
            .unmapped()
            .into_iter()
            .filter_map(|(off, b)| span_at(program, b, off, None, reach)),
    );
    spans
}

/// Returns the file extents of the sections `keep` accepts, each with its
/// address and the `reach` bytes the file holds after it ([`spans`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `reach` - Bytes past a run's end a match may cover.
/// * `keep` - Whether a section is walked.
fn section_spans(
    program: &Program,
    reach: usize,
    keep: impl Fn(&Section) -> bool,
) -> Vec<Span<'_>> {
    program
        .sections
        .iter()
        .filter(|s| s.file_size > 0 && keep(s))
        .filter_map(|s| {
            span_at(
                program,
                program.section_bytes(s)?,
                s.file_off.0,
                Some(s.va.0),
                reach,
            )
        })
        .collect()
}

/// Returns one run of the file as a [`Span`], with the `reach` bytes the
/// file holds after it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `run` - The run's bytes, a slice of the file.
/// * `off` - Its file offset.
/// * `va` - Its address; `None` where no section maps it.
/// * `reach` - Bytes past its end a match may cover.
///
/// # Returns
///
/// The span, or `None` when the offset does not fit the file.
fn span_at<'p>(
    program: &'p Program,
    run: &[u8],
    off: u64,
    va: Option<u64>,
    reach: usize,
) -> Option<Span<'p>> {
    let file = program.bytes.as_slice();
    let start = usize::try_from(off).ok()?;
    let end = start
        .checked_add(run.len())?
        .saturating_add(reach)
        .min(file.len());
    Some(Span {
        data: file.get(start..end)?,
        own: crate::num::from_usize(run.len()),
        off,
        va,
    })
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
    use super::holds;

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
