//! Printable string extraction (ASCII and UTF-16LE) as pure functions.

use crate::analysis::Analysis;
use crate::program::Program;
use crate::search::eq_mask;

/// Character encoding of an extracted string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Encoding {
    /// Printable 7-bit ASCII, one byte per character.
    Ascii,
    /// UTF-16LE with ASCII code points, two bytes per character.
    Utf16,
    /// A .NET user string (`#US`), UTF-16LE whole, read from the heap
    /// rather than walked ([`crate::clr`]).
    DotnetUs,
}

impl Encoding {
    /// Returns the lowercase name used in tool output (`ascii`, `utf16`
    /// or `dotnet-us`).
    pub fn name(self) -> &'static str {
        match self {
            Encoding::Ascii => "ascii",
            Encoding::Utf16 => "utf16",
            Encoding::DotnetUs => "dotnet-us",
        }
    }
}

/// One extracted string.
#[derive(Debug, Clone)]
pub struct StringHit {
    /// File offset of the first byte.
    pub off: u64,
    /// Length in characters (bytes for ASCII, code units for UTF-16).
    pub len: usize,
    /// The text, cut to [`DISPLAY_MAX`] characters with a `...` marker.
    pub text: String,
    /// How the bytes were decoded.
    pub encoding: Encoding,
}

/// One extracted string as a span of the bytes it was found in, without
/// the text materialized.
///
/// A walk of a large image finds tens of thousands of strings, and a
/// [`StringHit`] holds a heap `String` for every one of them; a span is
/// sixteen bytes with no allocation at all, and the page a query shows
/// materializes the few rows it prints through [`RawStringSpan::hit`].
/// The span index a session holds between `strings` calls is these.
///
/// `len` counts characters — bytes for [`Encoding::Ascii`], code units
/// for the UTF-16 encodings — the same count [`StringHit::len`] reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawStringSpan {
    /// File offset of the first byte.
    pub off: u64,
    /// Length in characters, saturated at `u32::MAX`; no run a walk
    /// reports reaches a fraction of that.
    pub len: u32,
    /// How the bytes decode.
    pub encoding: Encoding,
}

impl RawStringSpan {
    /// Materializes the span as the listing row over the bytes it was
    /// walked from.
    ///
    /// The text is decoded again from `bytes` and cut to
    /// [`DISPLAY_MAX`], exactly what a direct walk reports for the same
    /// run: a span is only the run's extent, never a copy of its text.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes the span was walked from, which
    ///   [`RawStringSpan::off`] indexes; out-of-range extents yield an
    ///   empty text.
    ///
    /// # Returns
    ///
    /// The hit for the run.
    #[must_use]
    pub fn hit(self, bytes: &[u8]) -> StringHit {
        StringHit {
            off: self.off,
            len: usize::try_from(self.len).unwrap_or(usize::MAX),
            text: self.text(bytes),
            encoding: self.encoding,
        }
    }

    /// Decodes the span's display text from `bytes`.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes the span was walked from, which
    ///   [`RawStringSpan::off`] indexes; out-of-range extents yield an
    ///   empty text.
    ///
    /// # Returns
    ///
    /// The text cut to [`DISPLAY_MAX`] characters, `...` appended when it
    /// was cut.
    #[must_use]
    pub fn text(self, bytes: &[u8]) -> String {
        match self.encoding {
            Encoding::Ascii => display_text(self.raw(bytes, 1)),
            Encoding::Utf16 => {
                let raw: Vec<u8> = self.raw(bytes, 2).iter().step_by(2).copied().collect();
                display_text(&raw)
            }
            Encoding::DotnetUs => {
                let raw = self.raw(bytes, 2);
                let text: String = char::decode_utf16(
                    raw.chunks_exact(2)
                        .filter_map(|c| c.first_chunk::<2>().map(|b| u16::from_le_bytes(*b))),
                )
                .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
                .collect();
                cut_decoded(text)
            }
        }
    }

    /// The span's bytes in `bytes`, empty when they no longer stand there.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes the span was walked from.
    /// * `unit` - Bytes per character: one for ASCII, two for UTF-16.
    fn raw(self, bytes: &[u8], unit: usize) -> &[u8] {
        let chars = usize::try_from(self.len).unwrap_or(usize::MAX);
        usize::try_from(self.off)
            .ok()
            .and_then(|start| bytes.get(start..start.checked_add(chars.checked_mul(unit)?)?))
            .unwrap_or(&[])
    }

    /// The span's whole bytes in `bytes`, whatever its encoding: one byte
    /// per ASCII character, two per UTF-16 code unit.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes the span was walked from.
    ///
    /// # Returns
    ///
    /// The run, empty when it no longer stands in `bytes`.
    #[must_use]
    pub fn raw_bytes(self, bytes: &[u8]) -> &[u8] {
        let unit = match self.encoding {
            Encoding::Ascii => 1,
            Encoding::Utf16 | Encoding::DotnetUs => 2,
        };
        self.raw(bytes, unit)
    }
}

impl StringHit {
    /// Returns the whole text of the string, past the cut its display text
    /// makes.
    ///
    /// A filter tests this: one tested against the display text missed
    /// every match past the [`DISPLAY_MAX`]th character of a long string.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes the hit was found in, which [`StringHit::off`]
    ///   indexes.
    ///
    /// # Returns
    ///
    /// The display text itself when it was not cut, else the text decoded
    /// again from `bytes`; the display text when `bytes` no longer holds
    /// the run.
    #[must_use]
    pub fn full_text<'a>(&'a self, bytes: &[u8]) -> std::borrow::Cow<'a, str> {
        if self.len <= DISPLAY_MAX {
            return std::borrow::Cow::Borrowed(&self.text);
        }
        let units = match self.encoding {
            Encoding::Ascii => 1,
            Encoding::Utf16 | Encoding::DotnetUs => 2,
        };
        let run = usize::try_from(self.off)
            .ok()
            .and_then(|start| bytes.get(start..start.checked_add(self.len.checked_mul(units)?)?));
        match (run, self.encoding) {
            (Some(raw), Encoding::DotnetUs) => std::borrow::Cow::Owned(
                char::decode_utf16(
                    raw.chunks_exact(2)
                        .filter_map(|c| c.first_chunk::<2>().map(|b| u16::from_le_bytes(*b))),
                )
                .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
                .collect(),
            ),
            (Some(raw), Encoding::Ascii | Encoding::Utf16) => {
                let text: Vec<u8> = raw.iter().step_by(units).copied().collect();
                std::borrow::Cow::Owned(String::from_utf8_lossy(&text).into_owned())
            }
            (None, _) => std::borrow::Cow::Borrowed(&self.text),
        }
    }
}

/// Longest text rendered in full; longer hits are cut with `...`.
const DISPLAY_MAX: usize = 200;
/// How far [`cstr_at`] / [`wstr_at`] look for a terminator, in bytes.
pub(crate) const SCAN_MAX: usize = 4096;

/// Tells whether `b` is printable ASCII (`0x20..=0x7e`).
pub fn printable(b: u8) -> bool {
    (0x20..=0x7e).contains(&b)
}

/// Finds runs of printable ASCII of at least `min_len` bytes.
///
/// The scan is word-wise: eight bytes are tested at a time with
/// [`unprintable_mask`], and a word inside a run — no separator byte in
/// it — costs the one test, while the run's extents fall out of the
/// separator positions. The spans hold no text; the rows a query shows
/// materialize through [`RawStringSpan::hit`].
///
/// # Arguments
///
/// * `bytes` - The bytes to scan; offsets in the result are relative to it.
/// * `min_len` - Shortest run reported, in bytes.
///
/// # Returns
/// The runs in offset order.
pub fn find_ascii_spans(bytes: &[u8], min_len: usize) -> Vec<RawStringSpan> {
    /// Reports the run `from..to` when it is long enough.
    ///
    /// # Arguments
    ///
    /// * `spans` - Where the run goes.
    /// * `from` - Offset of the run's first byte.
    /// * `to` - Offset one past the run's last byte.
    fn emit(spans: &mut Vec<RawStringSpan>, from: usize, to: usize, min_len: usize) {
        if to <= from || to - from < min_len {
            return;
        }
        spans.push(RawStringSpan {
            off: crate::num::from_usize(from),
            len: u32::try_from(to - from).unwrap_or(u32::MAX),
            encoding: Encoding::Ascii,
        });
    }
    let mut spans = Vec::new();
    let mut ended = None;
    let (words, tail) = bytes.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let mut m = unprintable_mask(u64::from_le_bytes(*w));
        if m == HIGH {
            emit(&mut spans, ended.map_or(0, |e| e + 1), 8 * k, min_len);
            ended = Some(8 * k + 7);
            continue;
        }
        while m != 0 {
            let z = k * 8 + crate::num::saturating_usize(u64::from(m.trailing_zeros() / 8));
            m &= m - 1;
            emit(&mut spans, ended.map_or(0, |e| e + 1), z, min_len);
            ended = Some(z);
        }
    }
    for (j, &b) in tail.iter().enumerate() {
        if printable(b) {
            continue;
        }
        let z = words.len() * 8 + j;
        emit(&mut spans, ended.map_or(0, |e| e + 1), z, min_len);
        ended = Some(z);
    }
    emit(&mut spans, ended.map_or(0, |e| e + 1), bytes.len(), min_len);
    spans
}

/// The bytes of `word` outside printable ASCII, as one high bit per byte
/// at the byte's own place.
///
/// Three lane-exact tests decide every byte at once: the lanes whose high
/// bit is clear name the ASCII bytes (`high_clear`), adding `0x60` to
/// those lanes carries into the high bit exactly for the bytes of `0x20`
/// and above (`ge20`), and adding one carries only for `0x7f`, the last
/// byte past printable (`above`). Neither add leaves its lane - the first
/// adds to bytes already masked below `0x80`, the second to the same -
/// so no borrow or carry crosses a lane and the mask is exact for every
/// word, bytes with their high bit set included: those lanes hold no
/// `high_clear` bit, so they are separators outright.
///
/// # Arguments
///
/// * `word` - The eight bytes tested.
///
/// # Returns
///
/// The separator mask, bit `8k + 7` for byte `k`.
fn unprintable_mask(word: u64) -> u64 {
    let ascii = word & !HIGH;
    let high_clear = !word & HIGH;
    let ge20 = ascii.wrapping_add(0x60 * ONES) & HIGH;
    let above = ascii.wrapping_add(ONES) & HIGH;
    let printable = ge20 & !above & high_clear;
    HIGH & !printable
}

/// A `u64` of `0x01` bytes, the subtrahend of the byte tests.
const ONES: u64 = 0x0101_0101_0101_0101;
/// A `u64` of `0x80` bytes, one high bit per byte of a mask.
const HIGH: u64 = 0x8080_8080_8080_8080;

/// Finds runs of printable ASCII of at least `min_len` bytes, with each
/// run's text materialized.
///
/// The spans come from [`find_ascii_spans`]; this walk answers with the
/// full rows, text and all, which a caller that wants every string's
/// text — an IOC sweep, a triage — takes as-is.
///
/// # Arguments
///
/// * `bytes` - The bytes to scan; offsets in the result are relative to it.
/// * `min_len` - Shortest run reported, in bytes.
///
/// # Returns
///
/// The runs in offset order.
pub fn find_strings(bytes: &[u8], min_len: usize) -> Vec<StringHit> {
    find_ascii_spans(bytes, min_len)
        .into_iter()
        .map(|s| s.hit(bytes))
        .collect()
}

/// Finds runs of UTF-16LE code units at least `min_len` characters long.
///
/// A code unit counts when its low byte is printable ASCII and its high byte
/// is zero. Runs may start at any byte offset, odd ones included, except one
/// whose preceding byte is printable ASCII: there the first code unit is the
/// last character of an adjacent ASCII string paired with that string's
/// terminator, and taking it yields a character that is not in the data.
/// `"rand_s\0" L"advapi32.dll"` read that way gives `L"sadvapi32.dll"`.
///
/// Every unit's high byte is zero, so the scan flags zero bytes eight at a
/// time ([`crate::search::eq_mask`]) and tests the byte before each as a
/// unit's low half; units two bytes apart chain into one run, which the
/// start rule trims by a unit when its first sits on an ASCII tail. The
/// runs are spans; a query's page materializes the rows it prints.
///
/// # Arguments
///
/// * `bytes` - The bytes to scan; offsets in the result are relative to it.
/// * `min_len` - Shortest run reported, in characters.
///
/// # Returns
///
/// The runs in offset order.
pub fn find_wide_spans(bytes: &[u8], min_len: usize) -> Vec<RawStringSpan> {
    /// Reports one run of units spanning `first..end`.
    ///
    /// A run the trim empties reports nothing, at any minimum: a run of
    /// zero characters is no string (the ASCII walk's own guard, which a
    /// `min_len` of zero must not talk out of).
    ///
    /// # Arguments
    ///
    /// * `spans` - Where the run goes.
    /// * `bytes` - The buffer scanned.
    /// * `first` - Offset of the run's first unit's low byte.
    /// * `end` - Offset one past the run's last unit's high byte.
    /// * `min_len` - Shortest run reported, in code units.
    fn emit(
        spans: &mut Vec<RawStringSpan>,
        bytes: &[u8],
        first: usize,
        end: usize,
        min_len: usize,
    ) {
        let start = if first > 0 && printable(bytes[first - 1]) {
            first + 2
        } else {
            first
        };
        let len = (end - start) / 2;
        if len == 0 || len < min_len {
            return;
        }
        spans.push(RawStringSpan {
            off: crate::num::from_usize(start),
            len: u32::try_from(len).unwrap_or(u32::MAX),
            encoding: Encoding::Utf16,
        });
    }

    /// Folds the wide unit whose low byte is `lo` into the run being built,
    /// reporting that run when `lo` does not continue it.
    ///
    /// # Arguments
    ///
    /// * `spans` - Where a finished run goes.
    /// * `bytes` - The buffer scanned.
    /// * `run` - The run being built: its first unit's low byte and its end.
    /// * `lo` - The unit's low byte's offset.
    /// * `min_len` - Shortest run reported, in code units.
    fn see(
        spans: &mut Vec<RawStringSpan>,
        bytes: &[u8],
        run: &mut Option<(usize, usize)>,
        lo: usize,
        min_len: usize,
    ) {
        match *run {
            Some((first, end)) if lo == end => *run = Some((first, end + 2)),
            Some((first, end)) => {
                emit(spans, bytes, first, end, min_len);
                *run = Some((lo, lo + 2));
            }
            None => *run = Some((lo, lo + 2)),
        }
    }

    let mut spans = Vec::new();
    let mut run: Option<(usize, usize)> = None;
    let (words, tail) = bytes.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let mut m = eq_mask(u64::from_le_bytes(*w), 0);
        while m != 0 {
            let z = k * 8 + m.trailing_zeros() as usize / 8;
            m &= m - 1;
            if let Some(lo) = z.checked_sub(1).filter(|lo| printable(bytes[*lo])) {
                see(&mut spans, bytes, &mut run, lo, min_len);
            }
        }
    }
    for (z, &b) in tail.iter().enumerate() {
        if b == 0
            && let Some(lo) = (words.len() * 8 + z)
                .checked_sub(1)
                .filter(|lo| printable(bytes[*lo]))
        {
            see(&mut spans, bytes, &mut run, lo, min_len);
        }
    }
    if let Some((first, end)) = run {
        emit(&mut spans, bytes, first, end, min_len);
    }
    spans
}

/// Finds runs of UTF-16LE code units at least `min_len` characters long,
/// with each run's text materialized.
///
/// The spans come from [`find_wide_spans`]; this walk answers with the
/// full rows, text and all.
///
/// # Arguments
///
/// * `bytes` - The bytes to scan; offsets in the result are relative to it.
/// * `min_len` - Shortest run reported, in characters.
///
/// # Returns
///
/// The runs in offset order.
pub fn find_wide_strings(bytes: &[u8], min_len: usize) -> Vec<StringHit> {
    find_wide_spans(bytes, min_len)
        .into_iter()
        .map(|s| s.hit(bytes))
        .collect()
}

/// Drops the runs that are instruction bytes rather than text.
///
/// A walk of an executable section reads opcodes as text: `push r14;
/// push r13; push r12; push rsi; ...` spells `AVAUATVW`, and a multi-byte
/// `nop` between functions spells `fffff.`. A run is code when the bytes
/// left of it outside every decoded basic block, and outside the `nop` and
/// `int3` padding after one, hold no stretch of `min_len` characters. A
/// string the compiler put in `.text` after a `ret`, which no block
/// decodes, stays; so does every run outside the code, and every run of a
/// program whose analysis found no functions.
///
/// # Arguments
///
/// * `program` - The image the spans were walked from.
/// * `analysis` - Its analysis, whose blocks are the decoded code.
/// * `spans` - The walked runs, offsets into `program`'s bytes.
/// * `min_len` - Shortest run the walk reports, in characters.
///
/// # Returns
///
/// The runs that are not code, in their order.
#[must_use]
pub fn drop_code_runs(
    program: &Program,
    analysis: &Analysis,
    spans: Vec<RawStringSpan>,
    min_len: usize,
) -> Vec<RawStringSpan> {
    let code = code_ranges(program, analysis);
    if code.is_empty() {
        return spans;
    }
    spans
        .into_iter()
        .filter(|s| !is_code_run(program, &code, *s, min_len))
        .collect()
}

/// The program's decoded code as sorted, disjoint `[start, end)` address
/// ranges: every basic block, each with the `nop` and `int3` padding that
/// follows it.
///
/// # Arguments
///
/// * `program` - The image, read for the padding.
/// * `analysis` - The analysis whose blocks are the code.
///
/// # Returns
///
/// The ranges in address order, empty when no function was found.
fn code_ranges(program: &Program, analysis: &Analysis) -> Vec<(u64, u64)> {
    let mut blocks: Vec<(u64, u64)> = analysis
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter().map(|b| (b.start, b.end)))
        .collect();
    blocks.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::with_capacity(blocks.len());
    for (start, end) in blocks {
        match merged.last_mut() {
            Some(last) if start <= last.1 => last.1 = last.1.max(end),
            _ => merged.push((start, end)),
        }
    }
    if let Some(bits) = program.arch.bitness() {
        let next: Vec<u64> = merged.iter().skip(1).map(|r| r.0).collect();
        for (r, hi) in merged
            .iter_mut()
            .zip(next.into_iter().chain(std::iter::once(u64::MAX)))
        {
            r.1 = crate::analysis::functions::padding_end(program, bits, r.1, hi);
        }
    }
    merged
}

/// Tells whether one run lies in the code `code` covers, with no stretch
/// of `min_len` characters outside it.
///
/// # Arguments
///
/// * `program` - The image, for the run's address.
/// * `code` - The code ranges, sorted and disjoint.
/// * `span` - The run.
/// * `min_len` - Shortest stretch that is a string of its own.
///
/// # Returns
///
/// `true` when the run overlaps the code and what is left is shorter than
/// `min_len`; `false` for a run at no address.
fn is_code_run(
    program: &Program,
    code: &[(u64, u64)],
    span: RawStringSpan,
    min_len: usize,
) -> bool {
    let Some(va) = program.offset_to_va(span.off) else {
        return false;
    };
    let unit: u64 = match span.encoding {
        Encoding::Ascii => 1,
        Encoding::Utf16 | Encoding::DotnetUs => 2,
    };
    let end = va.saturating_add(u64::from(span.len).saturating_mul(unit));
    let first = code.partition_point(|&(_, hi)| hi <= va);
    let mut cur = va;
    let mut longest = 0;
    for &(lo, hi) in code.get(first..).unwrap_or(&[]) {
        if lo >= end {
            break;
        }
        longest = longest.max(lo.saturating_sub(cur));
        cur = cur.max(hi);
    }
    if cur == va {
        return false;
    }
    longest = longest.max(end.saturating_sub(cur));
    longest / unit < crate::num::from_usize(min_len)
}

/// Tells whether the two bytes at `i` form a printable UTF-16LE ASCII unit.
///
/// # Arguments
///
/// * `bytes` - The buffer.
/// * `i` - Offset of the unit's low byte; out-of-range offsets yield `false`.
fn wide_unit(bytes: &[u8], i: usize) -> bool {
    i + 1 < bytes.len() && printable(bytes[i]) && bytes[i + 1] == 0
}

/// Tells whether a UTF-16LE run may begin at `va`.
///
/// The address form of the rule [`find_wide_strings`] applies: a run whose
/// preceding byte is printable ASCII starts on the last character of an
/// adjacent ASCII string rather than on a string of its own. A genuine run
/// follows a terminator or padding, so the test costs one byte and rejects
/// only the overlap.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the candidate first code unit.
///
/// # Returns
///
/// `true` when the preceding byte is unmapped or outside printable ASCII.
pub fn wide_run_start(program: &Program, va: u64) -> bool {
    va.checked_sub(1)
        .and_then(|p| program.read_va_upto(p, 1))
        .and_then(|b| b.first().copied())
        .is_none_or(|b| !printable(b))
}

/// Decodes `raw` as lossy UTF-8 and cuts it to [`DISPLAY_MAX`] characters.
///
/// # Arguments
///
/// * `raw` - The string bytes.
///
/// # Returns
///
/// The text, with `...` appended when it was cut, so one monster string
/// cannot fill a context window.
fn display_text(raw: &[u8]) -> String {
    cut_decoded(String::from_utf8_lossy(raw).into_owned())
}

/// Cuts decoded text to [`DISPLAY_MAX`] characters.
///
/// # Arguments
///
/// * `text` - The decoded text.
///
/// # Returns
///
/// The text, with `...` appended when it was cut; multi-byte characters
/// are counted, not split.
fn cut_decoded(text: String) -> String {
    if text.chars().count() <= DISPLAY_MAX {
        return text;
    }
    let mut t: String = text.chars().take(DISPLAY_MAX).collect();
    t.push_str("...");
    t
}

/// Escapes text for a double-quoted C literal.
///
/// # Arguments
///
/// * `text` - The text.
///
/// # Returns
///
/// The text with backslashes, double quotes, tabs and line ends escaped.
#[must_use]
pub fn escape_text(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\t', "\\t")
        .replace('\r', "\\r")
        .replace('\n', "\\n")
}

/// Reads the printable ASCII run that starts exactly at `va`.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the first byte.
/// * `min` - Shortest run accepted, in bytes.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length in bytes, text)`, or `None` when `va` is unmapped or the run
/// is shorter than `min`. The scan looks at most [`SCAN_MAX`] bytes ahead.
pub fn cstr_at(program: &Program, va: u64, min: usize, cap: usize) -> Option<(usize, String)> {
    cstr_in(program.read_va_upto(va, SCAN_MAX)?, min, cap)
}

/// Reads the printable ASCII run that starts at the first byte of `raw`.
///
/// # Arguments
///
/// * `raw` - The bytes from the run's start, up to [`SCAN_MAX`] of them.
/// * `min` - Shortest run accepted, in bytes.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length in bytes, text)`, or `None` when the run is shorter than
/// `min`.
pub(crate) fn cstr_in(raw: &[u8], min: usize, cap: usize) -> Option<(usize, String)> {
    let len = raw.iter().position(|&b| !printable(b)).unwrap_or(raw.len());
    if len < min {
        return None;
    }
    Some(capped(len, &raw[..len.min(cap)], cap))
}

/// Tells whether `b` belongs in a string literal: printable ASCII, or one
/// of the tab, newline and carriage return a literal escapes.
///
/// # Arguments
///
/// * `b` - The byte.
pub fn literal_byte(b: u8) -> bool {
    printable(b) || matches!(b, b'\t' | b'\n' | b'\r')
}

/// Reads the C string at `va` the way a literal is written, so a run holding
/// a tab or a newline is still one string.
///
/// [`cstr_at`] stops at the first byte outside printable ASCII, which cuts a
/// charset table like `" \t-+0123456789"` after its first character and
/// leaves the caller printing an address. This one runs to the terminator
/// over the bytes a literal can escape.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the first byte.
/// * `min` - Shortest run accepted, in bytes.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length, text with the control bytes still in it)`, or `None` when
/// `va` is unmapped or the run is shorter than `min`.
pub fn cstr_text_at(program: &Program, va: u64, min: usize, cap: usize) -> Option<(usize, String)> {
    let raw = program.read_va_upto(va, SCAN_MAX)?;
    let len = raw
        .iter()
        .position(|&b| !literal_byte(b))
        .unwrap_or(raw.len());
    if len < min {
        return None;
    }
    Some(capped(len, raw.get(..len.min(cap))?, cap))
}

/// Reads the UTF-16LE run that starts exactly at `va`.
///
/// The counterpart of [`cstr_at`]; lengths are in code units.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the first code unit.
/// * `min` - Shortest run accepted, in code units.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length in code units, text)`, or `None` when `va` is unmapped or the
/// run is shorter than `min`.
pub fn wstr_at(program: &Program, va: u64, min: usize, cap: usize) -> Option<(usize, String)> {
    wstr_in(program.read_va_upto(va, SCAN_MAX * 2)?, min, cap)
}

/// Reads the UTF-16LE run that starts at the first byte of `raw`.
///
/// # Arguments
///
/// * `raw` - The bytes from the run's start, up to twice [`SCAN_MAX`].
/// * `min` - Shortest run accepted, in code units.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length in code units, text)`, or `None` when the run is shorter
/// than `min`.
pub(crate) fn wstr_in(raw: &[u8], min: usize, cap: usize) -> Option<(usize, String)> {
    let mut len = 0;
    while wide_unit(raw, len * 2) {
        len += 1;
    }
    if len < min {
        return None;
    }
    let chars: Vec<u8> = raw[..len.min(cap) * 2].iter().step_by(2).copied().collect();
    Some(capped(len, &chars, cap))
}

/// Reads the UTF-16LE string at `va` the way a wide literal is written, so
/// a run holding a tab or a newline is still one string.
///
/// The wide counterpart of [`cstr_text_at`]: [`wstr_at`] stops at the
/// first unit outside printable ASCII, which cut `L"%ws%ws %ws:\n"` before
/// its newline, so the run had no terminator and the caller printed the
/// one-character narrow reading `"%"` instead. This one runs to the
/// terminator over the units a literal can escape.
///
/// # Arguments
///
/// * `program` - The loaded image to read from.
/// * `va` - Virtual address of the first code unit.
/// * `min` - Shortest run accepted, in code units.
/// * `cap` - Longest text returned in full; longer runs end with `...`.
///
/// # Returns
///
/// `(run length in code units, text with the control characters still in
/// it)`, or `None` when `va` is unmapped or the run is shorter than `min`.
pub fn wstr_text_at(program: &Program, va: u64, min: usize, cap: usize) -> Option<(usize, String)> {
    let raw = program.read_va_upto(va, SCAN_MAX * 2)?;
    let len = raw
        .chunks_exact(2)
        .position(|u| u.get(1) != Some(&0) || u.first().is_none_or(|b| !literal_byte(*b)))
        .unwrap_or(raw.len() / 2);
    if len < min {
        return None;
    }
    let chars: Vec<u8> = raw
        .get(..len.min(cap) * 2)?
        .iter()
        .step_by(2)
        .copied()
        .collect();
    Some(capped(len, &chars, cap))
}

/// Pairs a run length with its display text, marking a cut with `...`.
///
/// # Arguments
///
/// * `len` - Full length of the run.
/// * `raw` - The bytes kept for display (already cut to `cap`).
/// * `cap` - The display cap that `raw` was cut to.
///
/// # Returns
///
/// `(len, text)` with `...` appended when `len` exceeds `cap`.
fn capped(len: usize, raw: &[u8], cap: usize) -> (usize, String) {
    let mut t = String::from_utf8_lossy(raw).into_owned();
    if len > cap {
        t.push_str("...");
    }
    (len, t)
}
