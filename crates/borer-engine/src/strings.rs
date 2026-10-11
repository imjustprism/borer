//! Printable string extraction (ASCII and UTF-16LE) as pure functions.

use crate::program::Program;
use crate::search::eq_mask;

/// Character encoding of an extracted string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Encoding {
    /// Printable 7-bit ASCII, one byte per character.
    Ascii,
    /// UTF-16LE with ASCII code points, two bytes per character.
    Utf16,
}

impl Encoding {
    /// Returns the lowercase name used in tool output (`ascii` or `utf16`).
    pub fn name(self) -> &'static str {
        match self {
            Encoding::Ascii => "ascii",
            Encoding::Utf16 => "utf16",
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
/// The scan hops from run to run: a run starts at the next printable byte
/// and ends at the next one outside printable ASCII, each found by a tight
/// `position` loop, so a whole image costs one pass without per-byte state.
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
    let mut hits = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let Some(rel) = bytes[i..].iter().position(|&b| printable(b)) else {
            break;
        };
        let start = i + rel;
        let run = &bytes[start..];
        let end = start + run.iter().position(|&b| !printable(b)).unwrap_or(run.len());
        if end - start >= min_len {
            hits.push(ascii_hit(start, &bytes[start..end]));
        }
        i = end;
    }
    hits
}

/// Builds the [`StringHit`] for an ASCII run.
///
/// # Arguments
///
/// * `off` - Offset of the run's first byte.
/// * `raw` - The run's bytes.
///
/// # Returns
///
/// The hit with its display text cut to [`DISPLAY_MAX`].
fn ascii_hit(off: usize, raw: &[u8]) -> StringHit {
    StringHit {
        off: off as u64,
        len: raw.len(),
        text: display_text(raw),
        encoding: Encoding::Ascii,
    }
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
/// start rule trims by a unit when its first sits on an ASCII tail.
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
    /// Reports one run of units spanning `first..end`.
    ///
    /// # Arguments
    ///
    /// * `hits` - Where the run goes.
    /// * `bytes` - The buffer scanned.
    /// * `first` - Offset of the run's first unit's low byte.
    /// * `end` - Offset one past the run's last unit's high byte.
    /// * `min_len` - Shortest run reported, in code units.
    fn emit(hits: &mut Vec<StringHit>, bytes: &[u8], first: usize, end: usize, min_len: usize) {
        // INVARIANT: inside a run every unit's high byte is zero, so only the
        // first can sit on an ASCII tail; the run is then reported from its
        // second unit, which is what the per-byte walk answered.
        let start = if first > 0 && printable(bytes[first - 1]) {
            first + 2
        } else {
            first
        };
        let len = (end - start) / 2;
        if len < min_len {
            return;
        }
        let raw: Vec<u8> = bytes[start..end].iter().step_by(2).copied().collect();
        hits.push(StringHit {
            off: start as u64,
            len,
            text: display_text(&raw),
            encoding: Encoding::Utf16,
        });
    }

    /// Folds the wide unit whose low byte is `lo` into the run being built,
    /// reporting that run when `lo` does not continue it.
    ///
    /// # Arguments
    ///
    /// * `hits` - Where a finished run goes.
    /// * `bytes` - The buffer scanned.
    /// * `run` - The run being built: its first unit's low byte and its end.
    /// * `lo` - The unit's low byte's offset.
    /// * `min_len` - Shortest run reported, in code units.
    fn see(
        hits: &mut Vec<StringHit>,
        bytes: &[u8],
        run: &mut Option<(usize, usize)>,
        lo: usize,
        min_len: usize,
    ) {
        match *run {
            Some((first, end)) if lo == end => *run = Some((first, end + 2)),
            Some((first, end)) => {
                emit(hits, bytes, first, end, min_len);
                *run = Some((lo, lo + 2));
            }
            None => *run = Some((lo, lo + 2)),
        }
    }

    let mut hits = Vec::new();
    let mut run: Option<(usize, usize)> = None;
    let (words, tail) = bytes.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let mut m = eq_mask(u64::from_le_bytes(*w), 0);
        while m != 0 {
            let z = k * 8 + m.trailing_zeros() as usize / 8;
            m &= m - 1;
            if let Some(lo) = z.checked_sub(1).filter(|lo| printable(bytes[*lo])) {
                see(&mut hits, bytes, &mut run, lo, min_len);
            }
        }
    }
    for (z, &b) in tail.iter().enumerate() {
        if b == 0
            && let Some(lo) = (words.len() * 8 + z)
                .checked_sub(1)
                .filter(|lo| printable(bytes[*lo]))
        {
            see(&mut hits, bytes, &mut run, lo, min_len);
        }
    }
    if let Some((first, end)) = run {
        emit(&mut hits, bytes, first, end, min_len);
    }
    hits
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
    let mut t = String::from_utf8_lossy(raw).to_string();
    if t.len() > DISPLAY_MAX {
        t.truncate(DISPLAY_MAX);
        t.push_str("...");
    }
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
