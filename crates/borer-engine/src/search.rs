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

/// Scans every section, then the bytes no section maps, for an ASCII needle,
/// folding case and finding its UTF-16LE spelling too.
///
/// Matching is case-insensitive, like the `strings` filter, so a lower-case
/// query finds a capitalized identifier. Each match is sought both as the
/// bytes themselves (ASCII/UTF-8) and as UTF-16LE (each byte followed by a
/// zero), because Qt and Nebula hold UI and locale keys as wide strings that
/// an ASCII-only scan never sees. Hits stay in section-then-address order.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `needle` - The ASCII bytes to find.
/// * `offset` - Matches to skip before the page starts.
///
/// # Returns
///
/// The page after `offset` and the total, both empty for an empty needle.
pub fn find_text(program: &Program, needle: &[u8], offset: usize) -> Hits {
    let mut out = Hits::default();
    if needle.is_empty() {
        return out;
    }
    for (data, off, va) in spans(program) {
        // Collect both encodings' offsets, then report them in address order.
        let mut here: Vec<u64> = Vec::new();
        ascii_hits(data, needle, &mut here);
        wide_hits(data, needle, &mut here);
        here.sort_unstable();
        here.dedup();
        for i in here {
            if out.total >= offset && out.hits.len() < HITS_MAX {
                out.hits.push(Hit {
                    va: va.map(|v| v + i),
                    file_off: off + i,
                });
            }
            out.total += 1;
        }
    }
    out
}

/// Collects the offsets where `data` holds `needle` under ASCII case folding.
///
/// The needle's first byte, in either spelling, picks the positions the full
/// folded compare runs at ([`folded_pair`]): a text search tests every byte
/// offset of every section, and the folded compare at every window was the
/// whole cost of the query. The candidate scan reads eight bytes at a time
/// ([`eq_mask`]), the tail byte by byte.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The ASCII bytes sought; non-empty.
/// * `out` - Where the matching offsets go, ascending.
fn ascii_hits(data: &[u8], needle: &[u8], out: &mut Vec<u64>) {
    let n = needle.len();
    if data.len() < n {
        return;
    }
    let last = data.len() - n;
    let (lo, hi) = folded_pair(needle[0]);
    let (words, _tail) = data.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let word = u64::from_le_bytes(*w);
        let mut m = eq_mask(word, lo) | eq_mask(word, hi);
        while m != 0 {
            let i = k * 8 + m.trailing_zeros() as usize / 8;
            m &= m - 1;
            if i <= last && data[i..i + n].eq_ignore_ascii_case(needle) {
                out.push(i as u64);
            }
        }
    }
    for i in words.len() * 8..=last {
        let b = data[i];
        if (b == lo || b == hi) && data[i..i + n].eq_ignore_ascii_case(needle) {
            out.push(i as u64);
        }
    }
}

/// Collects the offsets where `data` holds the UTF-16LE spelling of `needle`
/// under ASCII case folding.
///
/// A match's second byte is always zero, the high half of an ASCII code
/// point, so the candidate scan flags zero bytes ([`eq_mask`]) and tests the
/// byte before each as the code unit's low half; only a low byte that folds
/// to the needle's first byte runs [`utf16le_eq_ignore_ascii_case`].
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The ASCII bytes sought; non-empty.
/// * `out` - Where the matching offsets go, ascending.
fn wide_hits(data: &[u8], needle: &[u8], out: &mut Vec<u64>) {
    let wide = needle.len() * 2;
    if data.len() < wide {
        return;
    }
    let last = data.len() - wide;
    let (lo, hi) = folded_pair(needle[0]);
    let (words, tail) = data.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let mut m = eq_mask(u64::from_le_bytes(*w), 0);
        while m != 0 {
            let z = k * 8 + m.trailing_zeros() as usize / 8;
            m &= m - 1;
            let Some(i) = z.checked_sub(1).filter(|i| *i <= last) else {
                continue;
            };
            let b = data[i];
            if (b == lo || b == hi) && utf16le_eq_ignore_ascii_case(&data[i..i + wide], needle) {
                out.push(i as u64);
            }
        }
    }
    for (z, &high_byte) in tail.iter().enumerate() {
        if high_byte != 0 {
            continue;
        }
        let Some(i) = (words.len() * 8 + z).checked_sub(1).filter(|i| *i <= last) else {
            continue;
        };
        let b = data[i];
        if (b == lo || b == hi) && utf16le_eq_ignore_ascii_case(&data[i..i + wide], needle) {
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

/// Returns the bytes a search walks: each section's file extent with its
/// address, then the runs no section maps ([`Program::unmapped`]), which
/// have none.
///
/// An overlay, the headers and a file with no sections at all hold bytes
/// worth finding; a search confined to the sections would skip every byte
/// of a file that has none.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// `(bytes, file offset, virtual address)` per run.
fn spans(program: &Program) -> Vec<(&[u8], u64, Option<u64>)> {
    let mut spans: Vec<(&[u8], u64, Option<u64>)> = program
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .filter_map(|s| Some((program.section_bytes(s)?, s.file_off, Some(s.va))))
        .collect();
    spans.extend(
        program
            .unmapped()
            .into_iter()
            .map(|(off, b)| (b, off, None)),
    );
    spans
}

/// Whether `window` is the UTF-16LE spelling of the ASCII `needle`, case-folded.
///
/// Each needle byte must appear low-byte-first with a zero high byte, the
/// layout of an ASCII code point in UTF-16LE.
///
/// # Arguments
///
/// * `window` - A slice exactly twice the needle's length.
/// * `needle` - The ASCII bytes.
fn utf16le_eq_ignore_ascii_case(window: &[u8], needle: &[u8]) -> bool {
    window.len() == needle.len() * 2
        && needle
            .iter()
            .enumerate()
            .all(|(k, n)| window[k * 2].eq_ignore_ascii_case(n) && window[k * 2 + 1] == 0)
}

/// Walks every window of every section and of the bytes no section maps,
/// counting the matches and keeping the page of them after `offset`.
///
/// The walk never stops early: the total is what tells a caller how far
/// the pages go, and a section is a memory compare per window.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `len` - The window length; zero matches nothing.
/// * `offset` - Matches to skip before the page starts.
/// * `matches` - Tells whether one window is a hit.
fn scan(program: &Program, len: usize, offset: usize, matches: impl Fn(&[u8]) -> bool) -> Hits {
    let mut out = Hits::default();
    if len == 0 {
        return out;
    }
    for (data, off, va) in spans(program) {
        for (i, w) in (0u64..).zip(data.windows(len)) {
            if !matches(w) {
                continue;
            }
            if out.total >= offset && out.hits.len() < HITS_MAX {
                out.hits.push(Hit {
                    va: va.map(|v| v + i),
                    file_off: off + i,
                });
            }
            out.total += 1;
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
