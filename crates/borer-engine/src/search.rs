//! Byte-pattern and text search over every byte of the file.

use crate::program::Program;

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
    scan(program, pattern.len(), offset, |w| {
        w.iter()
            .zip(pattern.iter())
            .all(|(b, p)| p.is_none_or(|p| *b == p))
    })
}

/// Scans every section, then the bytes no section maps, for a text needle,
/// folding ASCII case and finding its UTF-16LE spelling too.
///
/// Matching is case-insensitive for ASCII letters, like the `strings`
/// filter, so a lower-case query finds a capitalized identifier. Each match
/// is sought both as the needle's UTF-8 bytes and as its UTF-16LE code
/// units, because Qt and Nebula hold UI and locale keys as wide strings that
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
        // Collect both encodings' offsets, then report them in address order.
        let mut here: Vec<u64> = Vec::new();
        ascii_hits(span.data, narrow, &mut here);
        wide_hits(span.data, &wide, &mut here);
        here.retain(|&i| i < span.own);
        here.sort_unstable();
        here.dedup();
        for i in here {
            out.push(&span, i, offset);
        }
    }
    out
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
                va: span.va.map(|v| v + i),
                file_off: span.off + i,
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
/// * `out` - Where the matching offsets go, ascending.
fn ascii_hits(data: &[u8], needle: &[u8], out: &mut Vec<u64>) {
    let Some(&first) = needle.first() else {
        return;
    };
    candidate_hits(
        data,
        needle.len(),
        folded_pair(first),
        |w| w.eq_ignore_ascii_case(needle),
        out,
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
/// * `out` - Where the matching offsets go, ascending.
fn wide_hits(data: &[u8], wide: &[u8], out: &mut Vec<u64>) {
    let [lo, hi, ..] = *wide else {
        return;
    };
    let first = if hi == 0 { folded_pair(lo) } else { (lo, lo) };
    candidate_hits(
        data,
        wide.len(),
        first,
        |w| utf16le_eq_ignore_ascii_case(w, wide),
        out,
    );
}

/// Collects the offsets of every window of `data` that `matches` accepts,
/// testing only the windows whose first byte is one of `first`.
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
/// * `out` - Where the matching offsets go, ascending.
fn candidate_hits(
    data: &[u8],
    n: usize,
    first: (u8, u8),
    matches: impl Fn(&[u8]) -> bool,
    out: &mut Vec<u64>,
) {
    let Some(last) = data.len().checked_sub(n) else {
        return;
    };
    let (lo, hi) = first;
    let (words, _tail) = data.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let word = u64::from_le_bytes(*w);
        let mut m = eq_mask(word, lo) | eq_mask(word, hi);
        while m != 0 {
            let i = k * 8 + m.trailing_zeros() as usize / 8;
            m &= m - 1;
            if i <= last && matches(&data[i..i + n]) {
                out.push(i as u64);
            }
        }
    }
    for i in words.len() * 8..=last {
        let b = data[i];
        if (b == lo || b == hi) && matches(&data[i..i + n]) {
            out.push(i as u64);
        }
    }
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
struct Span<'a> {
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
    let file = program.bytes.as_slice();
    let span = |run: &[u8], off: u64, va: Option<u64>| -> Option<Span<'_>> {
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
    };
    let mut spans: Vec<Span<'_>> = program
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .filter_map(|s| span(program.section_bytes(s)?, s.file_off, Some(s.va)))
        .collect();
    spans.extend(
        program
            .unmapped()
            .into_iter()
            .filter_map(|(off, b)| span(b, off, None)),
    );
    spans
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

/// Walks every window of every section and of the bytes no section maps,
/// counting the matches and keeping the page of them after `offset`.
///
/// The walk never stops early: the total is what tells a caller how far
/// the pages go, and a section is a memory compare per window. A window may
/// run past its run's end into the file's next bytes ([`spans`]).
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `len` - The window length; zero matches nothing.
/// * `offset` - Matches to skip before the page starts.
/// * `matches` - Tells whether one window is a hit.
fn scan(program: &Program, len: usize, offset: usize, matches: impl Fn(&[u8]) -> bool) -> Hits {
    let mut out = Hits::default();
    let Some(reach) = len.checked_sub(1) else {
        return out;
    };
    for span in spans(program, reach) {
        for (i, w) in (0..span.own).zip(span.data.windows(len)) {
            if matches(w) {
                out.push(&span, i, offset);
            }
        }
    }
    out
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
