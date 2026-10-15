//! Search tests: AOB patterns with wildcards, text search, demangling.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Arch, FileOff, Program, Section, Va};
use borer_engine::search::{
    HITS_MAX, demangled_name, demangled_or_raw, find_bytes, find_text, parse_pattern,
};

/// Builds a one-section program: `48 8b 41 05` at 0x1000, `48 8b 99 05` at
/// 0x1010 (the wildcard slot differs), and `needle` at 0x1020.
fn fixture() -> Program {
    let mut bytes = vec![0u8; 0x40];
    bytes[0x00..0x04].copy_from_slice(&[0x48, 0x8b, 0x41, 0x05]);
    bytes[0x10..0x14].copy_from_slice(&[0x48, 0x8b, 0x99, 0x05]);
    bytes[0x20..0x26].copy_from_slice(b"needle");
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x40, false, true)],
    )
}

/// Patterns accept hex tokens and `??`/`?` wildcards and reject anything else.
#[test]
fn parse_pattern_forms() {
    assert_eq!(
        parse_pattern("48 8b ?? 05"),
        Some(vec![Some(0x48), Some(0x8b), None, Some(0x05)])
    );
    assert_eq!(parse_pattern("?"), Some(vec![None]));
    assert_eq!(parse_pattern("zz"), None);
    assert_eq!(parse_pattern("123"), None);
}

/// A sign is not a hex digit: `+1` was read as the byte `01`.
#[test]
fn parse_pattern_refuses_signed_tokens() {
    assert_eq!(parse_pattern("+1"), None);
    assert_eq!(parse_pattern("48 +2"), None);
    assert_eq!(parse_pattern("-1"), None);
    assert_eq!(parse_pattern("0a"), Some(vec![Some(0x0a)]));
}

/// A wildcard matches both encodings.
#[test]
fn find_bytes_with_wildcard() {
    let p = fixture();
    let hits = find_bytes(&p, &parse_pattern("48 8b ?? 05").unwrap(), 0);
    let vas: Vec<u64> = hits.hits.iter().filter_map(|h| h.va).collect();
    assert_eq!(vas, vec![0x1000, 0x1010]);
    assert_eq!(hits.total, 2);
}

/// A page after an offset skips that many matches and still counts them
/// all: the second of two hits, with a total of two.
#[test]
fn find_bytes_pages_from_an_offset() {
    let p = fixture();
    let page = find_bytes(&p, &parse_pattern("48 8b ?? 05").unwrap(), 1);
    let vas: Vec<u64> = page.hits.iter().filter_map(|h| h.va).collect();
    assert_eq!(vas, vec![0x1010]);
    assert_eq!(page.total, 2);
    let past = find_bytes(&p, &parse_pattern("48 8b ?? 05").unwrap(), 5);
    assert!(past.hits.is_empty());
    assert_eq!(past.total, 2);
}

/// An exact pattern matches once, with its address and file offset.
#[test]
fn find_bytes_exact() {
    let p = fixture();
    let hits = find_bytes(&p, &parse_pattern("48 8b 41 05").unwrap(), 0).hits;
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].va, Some(0x1000));
    assert_eq!(hits[0].file_off, 0);
}

/// A pattern of pure wildcards has no anchor and matches at every offset.
#[test]
fn find_bytes_all_wildcards() {
    let p = fixture();
    let hits = find_bytes(&p, &parse_pattern("? ? ? ?").unwrap(), 0);
    assert_eq!(hits.total, 0x40 - 3);
    assert_eq!(hits.hits.len(), 0x40 - 3);
}

/// Leading wildcards leave the anchor inside the pattern; a candidate hit
/// whose window would start before the run is skipped, the rest matched.
#[test]
fn find_bytes_leading_wildcards() {
    let p = fixture();
    let hits = find_bytes(&p, &parse_pattern("? 8b 99 05").unwrap(), 0);
    let vas: Vec<u64> = hits.hits.iter().filter_map(|h| h.va).collect();
    assert_eq!(vas, vec![0x1010]);
    assert_eq!(hits.total, 1);
}

/// A pattern longer than one compare chunk verifies chunk by chunk and
/// lane by lane in its short tail chunk.
#[test]
fn find_bytes_long_pattern_with_tail_chunk() {
    let p = fixture();
    let hits = find_bytes(
        &p,
        &parse_pattern("48 8b 41 05 00 00 00 00 00 00 10").unwrap(),
        0,
    );
    assert_eq!(hits.total, 0);
    let near = find_bytes(
        &p,
        &parse_pattern("48 8b 41 05 00 00 00 00 00 00 00").unwrap(),
        0,
    );
    let vas: Vec<u64> = near.hits.iter().filter_map(|h| h.va).collect();
    assert_eq!(vas, vec![0x1000]);
    let wild = find_bytes(
        &p,
        &parse_pattern("48 8b ?? 05 ?? 00 ?? 00 ?? 00 00").unwrap(),
        0,
    );
    assert_eq!(wild.total, 2);
}

/// A one-byte pattern is its own anchor and matches that byte alone.
#[test]
fn find_bytes_single_byte() {
    let p = fixture();
    let hits = find_bytes(&p, &parse_pattern("8b").unwrap(), 0);
    assert_eq!(hits.total, 2);
    let vas: Vec<u64> = hits.hits.iter().filter_map(|h| h.va).collect();
    assert_eq!(vas, vec![0x1001, 0x1011]);
}

/// An anchor sitting in the scan's tail bytes, past the last whole word,
/// still finds its match.
#[test]
fn find_bytes_anchor_in_tail() {
    let mut bytes = vec![0u8; 9];
    bytes[8] = 0x41;
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 9, false, true)],
    );
    let hits = find_bytes(&p, &parse_pattern("41").unwrap(), 0);
    assert_eq!(hits.total, 1);
    assert_eq!(hits.hits[0].va, Some(0x1008));
}

/// Text search finds the literal and nothing for an absent one.
#[test]
fn find_text_hits() {
    let p = fixture();
    let hits = find_text(&p, "needle", 0).hits;
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].va, Some(0x1020));
    assert!(find_text(&p, "absent", 0).hits.is_empty());
}

/// Text search folds case and finds the UTF-16LE spelling, like `strings`.
#[test]
fn find_text_folds_case_and_finds_wide() {
    let mut bytes = vec![0u8; 0x40];
    bytes[0x00..0x06].copy_from_slice(b"Needle"); // capitalized
    for (k, b) in b"wide".iter().enumerate() {
        bytes[0x10 + k * 2] = *b; // UTF-16LE "wide" at 0x1010
    }
    let mut p = fixture();
    p.bytes = bytes;
    // A lower-case query finds the capitalized literal.
    let n = find_text(&p, "needle", 0);
    assert_eq!(n.total, 1);
    assert_eq!(n.hits[0].va, Some(0x1000));
    // An ASCII query finds the wide string, case-folded.
    assert_eq!(
        find_text(&p, "wide", 0).hits.first().and_then(|h| h.va),
        Some(0x1010)
    );
    assert_eq!(find_text(&p, "WIDE", 0).total, 1);
    assert!(find_text(&p, "absent", 0).hits.is_empty());
}

/// Text search answers what a compare at every window answers, on data built
/// to stress its word-at-a-time candidate scan.
///
/// The scan flags bytes by a borrow trick that can over-flag and reads eight
/// bytes at a time, so the data plants: ASCII matches across the eight-byte
/// word boundaries and at the last offset a window fits, wide matches with
/// their zero high half on either side of a boundary, and the pair a borrow
/// crosses (`X` followed by `X ^ 0x01`) right after a planted first byte.
/// Every needle's offsets must equal the naive per-window compare's.
#[test]
fn find_text_matches_the_naive_scan_on_adversarial_data() {
    /// Size of the pseudo-random buffer the matches are planted into.
    const LEN: usize = 0x4000;
    let mut x = 0x1234_5678_u32;
    let mut bytes: Vec<u8> = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        x = x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        bytes.push(borer_engine::num::lo8(u64::from(x >> 16)));
    }
    for at in [7, 8, 15, 16, 31, 32, LEN / 2, LEN - 7, LEN - 6] {
        bytes[at..at + 6].copy_from_slice(b"Needle");
    }
    for at in [6, 8, 14, 16, 30] {
        for (k, b) in b"Needle".iter().enumerate() {
            bytes[LEN / 2 + at + k * 2] = *b;
            bytes[LEN / 2 + at + k * 2 + 1] = 0;
        }
    }
    for at in [7, 15, 31] {
        bytes[at + 6] = b'N' ^ 0x01;
    }
    let p = Program::raw(
        bytes.clone(),
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text",
            0x1000,
            0,
            u64::try_from(LEN).unwrap(),
            false,
            true,
        )],
    );
    let needles: [&str; 6] = ["a", "Nee", "needle", "Needle", "7", "0123456789abcdef"];
    for needle in needles {
        let want = naive_text_hits(&bytes, needle.as_bytes());
        let got = find_text(&p, needle, 0);
        let offs: Vec<u64> = got.hits.iter().map(|h| h.file_off).collect();
        assert_eq!(offs, want, "needle {needle:?}");
        assert_eq!(got.total, want.len(), "needle {needle:?}");
    }
}

/// The per-window compare text search is defined by: both encodings, folded,
/// deduped, in offset order.
///
/// # Arguments
///
/// * `data` - The bytes searched.
/// * `needle` - The ASCII bytes sought.
///
/// # Returns
///
/// Every matching offset, the oracle [`find_text`] must reproduce.
fn naive_text_hits(data: &[u8], needle: &[u8]) -> Vec<u64> {
    let mut here: Vec<u64> = Vec::new();
    for (i, w) in data.windows(needle.len()).enumerate() {
        if w.eq_ignore_ascii_case(needle) {
            here.push(i as u64);
        }
    }
    let wide = needle.len() * 2;
    for (i, w) in data.windows(wide).enumerate() {
        if needle
            .iter()
            .enumerate()
            .all(|(k, n)| w[k * 2].eq_ignore_ascii_case(n) && w[k * 2 + 1] == 0)
        {
            here.push(i as u64);
        }
    }
    here.sort_unstable();
    here.dedup();
    here
}

/// A text needle outside ASCII is found as its UTF-16LE code units, not as
/// its UTF-8 bytes spread over zero high halves, and a high byte that spells
/// a letter is not case-folded.
#[test]
fn find_text_finds_the_wide_spelling_of_non_ascii_text() {
    let mut bytes = vec![0u8; 0x40];
    bytes[0x00..0x02].copy_from_slice("\u{e9}".as_bytes());
    bytes[0x08..0x0c].copy_from_slice(&[0xe9, 0x00, 0x2d, 0x4e]);
    bytes[0x10..0x12].copy_from_slice(&[0x2d, 0x6e]);
    let mut p = fixture();
    p.bytes = bytes;
    let found = |needle: &str| -> Vec<u64> {
        find_text(&p, needle, 0)
            .hits
            .iter()
            .map(|h| h.file_off)
            .collect()
    };
    assert_eq!(found("\u{e9}"), [0x00, 0x08]);
    assert_eq!(found("\u{e9}\u{4e2d}"), [0x08]);
    assert_eq!(found("\u{4e2d}"), [0x0a]);
}

/// A match that starts in one section and runs on into the next one's
/// file bytes is found, at the address it starts at; so is one running
/// from the bytes no section maps into a section.
#[test]
fn a_match_across_a_section_boundary_is_found() {
    let mut bytes = vec![0u8; 0x40];
    bytes[0x0e..0x12].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    bytes[0x1e..0x24].copy_from_slice(b"needle");
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x10, 0x10, false, true),
            Section::mapped(".data", 0x2000, 0x20, 0x20, true, false),
        ],
    );
    let aob = find_bytes(&p, &parse_pattern("de ad be ef").unwrap(), 0);
    assert_eq!(aob.total, 1);
    assert_eq!((aob.hits[0].va, aob.hits[0].file_off), (None, 0x0e));
    let text = find_text(&p, "needle", 0);
    assert_eq!(text.total, 1);
    assert_eq!(
        (text.hits[0].va, text.hits[0].file_off),
        (Some(0x100e), 0x1e)
    );
}

/// MSVC-mangled names demangle; plain C names pass through.
#[test]
fn demangles_msvc_symbols() {
    assert_eq!(demangled_or_raw("?x@@3HA"), "int x");
    assert_eq!(demangled_or_raw("plain_C_name"), "plain_C_name");
    assert_eq!(
        demangled_or_raw("??1type_info@@UEAA@XZ"),
        "public: virtual __cdecl type_info::~type_info(void)"
    );
}

/// Itanium C++ names demangle with their parameters, Rust names lose their
/// hash, and undecodable `_Z` names pass through.
#[test]
fn demangles_itanium_and_rust_symbols() {
    assert_eq!(
        demangled_or_raw("_ZN5space3fooEibc"),
        "space::foo(int, bool, char)"
    );
    assert_eq!(demangled_or_raw("_ZSt4cout"), "std::cout");
    assert_eq!(
        demangled_or_raw("_ZN4core3ptr13drop_in_place17h0123456789abcdefE"),
        "core::ptr::drop_in_place"
    );
    assert_eq!(demangled_or_raw("_Z"), "_Z");
}

/// The bare form keeps only the qualified name and any clone suffix.
#[test]
fn bare_names_drop_signatures() {
    assert_eq!(demangled_name("_ZN5space3fooEibc"), "space::foo");
    assert_eq!(
        demangled_name("??1type_info@@UEAA@XZ"),
        "type_info::~type_info"
    );
    assert_eq!(demangled_name("_ZN3app3fooEv.cold.12"), "app::foo.cold.12");
    assert_eq!(
        demangled_name("_ZN4core3ptr13drop_in_place17h0123456789abcdefE"),
        "core::ptr::drop_in_place"
    );
    assert_eq!(
        demangled_name("KERNEL32.dll!GetTickCount"),
        "KERNEL32.dll!GetTickCount"
    );
}

/// An import's `dll!` prefix does not hide the mangled name behind it.
#[test]
fn imports_demangle_behind_their_prefix() {
    assert_eq!(
        demangled_name("Qt5Core.dll!??0QString@@QAE@PBD@Z"),
        "Qt5Core.dll!QString::QString"
    );
    assert_eq!(
        demangled_or_raw("Qt5Core.dll!??0QString@@QAE@PBD@Z"),
        "Qt5Core.dll!public: __thiscall QString::QString(char const *)"
    );
    assert_eq!(
        demangled_name("libstdc++.so!_ZN5space3fooEibc"),
        "libstdc++.so!space::foo"
    );
}

/// Bytes no section maps are searched, and their hits carry no address.
///
/// A file with no sections is searched by file offset, and so are bytes
/// after a program's last section: a search confined to the sections
/// answered no hits for an encrypted file whose every byte it had skipped.
#[test]
fn bytes_no_section_maps_are_searched() {
    let mut bytes = vec![0u8; 0x40];
    bytes[0x30..0x36].copy_from_slice(b"needle");
    let raw = Program::raw(bytes, Arch::Unknown, 0, None, Vec::new());
    let hits = find_text(&raw, "needle", 0);
    assert_eq!(hits.total, 1);
    assert_eq!((hits.hits[0].va, hits.hits[0].file_off), (None, 0x30));

    let mut p = fixture();
    p.bytes.extend_from_slice(b"\0\0overlay needle\0");
    let hits = find_text(&p, "needle", 0).hits;
    let found: Vec<_> = hits.iter().map(|h| (h.va, h.file_off)).collect();
    assert_eq!(found, [(Some(0x1020), 0x20), (None, 0x4a)]);
    let aob = find_bytes(&raw, &parse_pattern("6e 65 ?? 64").unwrap(), 0);
    assert_eq!(
        aob.hits.iter().map(|h| h.file_off).collect::<Vec<_>>(),
        [0x30]
    );
}

/// The byte-by-byte reference `find_bytes` must equal.
///
/// Every file offset whose window holds the pattern, with the address of
/// the section that covers it, in the order `find_bytes` reports
/// (sections in declaration order, then the bytes no section maps in
/// file order).
///
/// # Arguments
///
/// * `p` - The program searched.
/// * `pattern` - Bytes with `None` wildcards.
///
/// # Returns
///
/// Every expected hit as `(va, file off)`, `None` where no section maps
/// the start.
fn naive_byte_hits(p: &Program, pattern: &[Option<u8>]) -> Vec<(Option<u64>, u64)> {
    let file = p.bytes.as_slice();
    let end = borer_engine::num::from_usize(file.len());
    // A section the file cannot wholly back contributes no span and no
    // covered range, the way `Program::unmapped` and `spans` skip it.
    let backed = |s: &Section| s.file_size > 0 && s.file_off.0.saturating_add(s.file_size) <= end;
    let holds = |off: usize| {
        pattern
            .iter()
            .enumerate()
            .all(|(k, pat)| pat.is_none_or(|b| file.get(off + k) == Some(&b)))
    };
    let va = |off: u64| {
        p.sections.iter().find_map(|s| {
            backed(s)
                .then(|| {
                    (off >= s.file_off.0 && off < s.file_off.0 + s.file_size)
                        .then(|| s.va.0 + off - s.file_off.0)
                })
                .flatten()
        })
    };
    let mut out: Vec<(Option<u64>, u64)> = p
        .sections
        .iter()
        .filter(|s| backed(s))
        .flat_map(|s| s.file_off.0..s.file_off.0 + s.file_size)
        .filter(|&off| {
            let o = borer_engine::num::saturating_usize(off);
            o + pattern.len() <= file.len() && holds(o)
        })
        .map(|off| (va(off), off))
        .collect();
    let covered = |off: u64| {
        p.sections
            .iter()
            .any(|s| backed(s) && off >= s.file_off.0 && off < s.file_off.0 + s.file_size)
    };
    for off in 0..end {
        if covered(off) {
            continue;
        }
        let o = borer_engine::num::saturating_usize(off);
        if o + pattern.len() <= file.len() && holds(o) {
            out.push((va(off), off));
        }
    }
    out
}

/// Asserts `find_bytes` answers exactly the naive reference: the page
/// (capped at [`HITS_MAX`], as the tool's page is) and the total.
///
/// # Panics
///
/// When the scan's page or total differs from the reference.
fn assert_naive(p: &Program, pattern: &[Option<u8>]) {
    let want = naive_byte_hits(p, pattern);
    let got = find_bytes(p, pattern, 0);
    assert_eq!(got.total, want.len());
    let list: Vec<(Option<u64>, u64)> = got.hits.iter().map(|h| (h.va, h.file_off)).collect();
    let page = &want[..want.len().min(HITS_MAX)];
    assert_eq!(list, page);
}

/// Writes a pattern's fixed bytes into `bytes` at `at`, leaving the
/// wildcards' lanes as they stand.
///
/// # Arguments
///
/// * `bytes` - The buffer planted into.
/// * `pattern` - Bytes with `None` wildcards.
/// * `at` - Offset of the pattern's first byte.
fn plant_at(bytes: &mut [u8], pattern: &[Option<u8>], at: usize) {
    for (k, p) in pattern.iter().enumerate() {
        if let Some(b) = p
            && let Some(slot) = bytes.get_mut(at + k)
        {
            *slot = *b;
        }
    }
}

/// A pattern of pure wildcards matches at every offset that fits it, one
/// byte long and one byte short of the whole section alike.
#[test]
fn all_wildcard_patterns_match_at_every_offset_by_length() {
    let p = fixture();
    for len in [1usize, 2, 3, 5, 0x40] {
        let pattern = vec![None; len];
        let hits = find_bytes(&p, &pattern, 0);
        let n = 0x40 - len + 1;
        assert_eq!(hits.total, n, "len {len}");
        assert_eq!(hits.hits.len(), n, "len {len}");
        assert_eq!(hits.hits.first().map(|h| h.file_off), Some(0), "len {len}");
        assert_eq!(
            hits.hits.last().map(|h| h.file_off),
            Some(u64::try_from(0x40 - len).unwrap()),
            "len {len}"
        );
    }
}

/// A pattern one byte longer than the whole file matches nothing, on the
/// anchored path and the all-wildcard walk alike.
#[test]
fn find_bytes_answers_nothing_when_the_pattern_outgrows_the_file() {
    let p = fixture();
    let fixed = vec![Some(0x48u8); 0x41];
    assert_eq!(find_bytes(&p, &fixed, 0).total, 0);
    let wild = vec![None; 0x41];
    let walked = find_bytes(&p, &wild, 0);
    assert_eq!(walked.total, 0);
    assert!(walked.hits.is_empty());
}

/// A pattern ending at the file's last byte is found wherever its anchor
/// sits: the pattern's first byte, its last, and the tail past the last
/// whole word.
#[test]
fn find_bytes_match_ending_at_the_last_byte_of_the_file() {
    let mut bytes = vec![0x44u8; 0x12];
    bytes[0x0e..0x12].copy_from_slice(&[0x48, 0x8b, 0x41, 0x05]);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x12, false, true)],
    );
    for (spec, off) in [
        ("48 8b 41 05", 0x0e),
        ("?? ?? 41 05", 0x0e),
        ("?? ?? ?? 05", 0x0e),
        ("48 ?? ?? ??", 0x0e),
        ("8b 41", 0x0f),
        ("05", 0x11),
    ] {
        let pattern = parse_pattern(spec).unwrap();
        let got = find_bytes(&p, &pattern, 0);
        assert_eq!(got.total, 1, "spec {spec}");
        assert_eq!(got.hits[0].file_off, off, "spec {spec}");
        assert_eq!(got.hits[0].va, Some(0x1000 + off), "spec {spec}");
        assert_naive(&p, &pattern);
    }
}

/// A pattern whose only fixed byte is the file's most common byte still
/// answers exactly.
///
/// Zero padding makes the anchor (a `0x00`) a candidate at nearly every
/// offset, and the compiled compare must keep every answer true.
#[test]
fn find_bytes_anchor_on_the_most_common_byte_stays_exact() {
    let mut bytes = vec![0u8; 0x100];
    for at in [0x1f, 0x40, 0x41, 0xf0] {
        bytes[at] = 0xf0;
    }
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x100, false, true)],
    );
    for spec in ["? 00 ? 00", "00 ?? 00", "?? 00 ?? 00 ?? 00"] {
        let pattern = parse_pattern(spec).unwrap();
        let got = find_bytes(&p, &pattern, 0);
        assert_naive(&p, &pattern);
        assert!(
            got.total > 0x80,
            "the padding keeps the anchor common: {spec}"
        );
    }
}

/// Patterns of two, three and four compare chunks match at every phase
/// of the section's words.
///
/// Lengths 8, 9, 17, 24 and 25 (an all-wildcard middle chunk among them)
/// are each planted at eight phases and in a window ending at the file's
/// last byte.
#[test]
fn find_bytes_long_patterns_across_chunk_boundaries() {
    let specs = [
        "48 8b 41 05 90 90 90 90",
        "48 8b 41 05 90 90 90 90 90",
        "48 ?? 8b ?? 41 ?? 05 ?? 90 ?? 11 ?? 22 ?? 33 ?? 44 ?? 55",
        "48 8b 41 05 90 90 90 90 11 22 33 44 55 66 77 88 de ad be ef 01 23 45 67 89",
        "48 8b 41 05 ?? ?? ?? ?? ?? ?? ?? ?? 11 22 33 44 55 66 77 88 de ad be ef aa",
    ];
    for spec in specs {
        let pattern = parse_pattern(spec).unwrap();
        let mut bytes = vec![0xc7u8; 0x120];
        let mut planted = Vec::new();
        for k in 0..8 {
            let at = 33 * k;
            plant_at(&mut bytes, &pattern, at);
            planted.push(at);
        }
        let last = bytes.len() - pattern.len();
        plant_at(&mut bytes, &pattern, last);
        planted.push(last);
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![Section::mapped(".text", 0x1000, 0, 0x120, false, true)],
        );
        assert_naive(&p, &pattern);
        let got = find_bytes(&p, &pattern, 0);
        for at in planted {
            assert!(
                got.hits
                    .iter()
                    .any(|h| h.file_off == u64::try_from(at).unwrap()),
                "spec {spec}: planting at {at} missing"
            );
        }
    }
}

/// An alternating fixed/wildcard pattern is found at every phase relative
/// to the section's eight-byte words.
#[test]
fn find_bytes_alternating_pattern_at_every_word_phase() {
    let spec = "48 ?? 8b ?? 89 ?? 05";
    let pattern = parse_pattern(spec).unwrap();
    let mut bytes = vec![0x31u8; 0x80];
    for phase in 0..8 {
        plant_at(&mut bytes, &pattern, 13 * phase);
    }
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x80, false, true)],
    );
    assert_naive(&p, &pattern);
    let got = find_bytes(&p, &pattern, 0);
    for phase in 0..8 {
        assert!(
            got.hits
                .iter()
                .any(|h| h.file_off == u64::try_from(13 * phase).unwrap()),
            "phase {phase} planting missing"
        );
    }
}

/// A match may start in either section or in the bytes no section maps
/// and run on into the next run's bytes.
///
/// Every match is reported exactly once, at the address of the section it
/// starts in, sections before gaps.
#[test]
fn find_bytes_across_sections_gaps_and_the_file_end() {
    let mut bytes = vec![0x55u8; 0x40];
    for at in [0x00, 0x0d, 0x1d, 0x3c] {
        bytes[at..at + 4].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    }
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x10, false, true),
            Section::mapped(".data", 0x2000, 0x20, 0x20, true, false),
        ],
    );
    for spec in ["de ad be ef", "de ?? be ef"] {
        let pattern = parse_pattern(spec).unwrap();
        let got = find_bytes(&p, &pattern, 0);
        assert_eq!(got.total, 4, "spec {spec}");
        let list: Vec<(Option<u64>, u64)> = got.hits.iter().map(|h| (h.va, h.file_off)).collect();
        assert_eq!(
            list,
            [
                (Some(0x1000), 0x00),
                (Some(0x100d), 0x0d),
                (Some(0x201c), 0x3c),
                (None, 0x1d),
            ],
            "spec {spec}"
        );
        assert_naive(&p, &pattern);
    }

    // Two contiguous sections: a match starting at .text's last byte runs
    // straight into .data's file bytes and is found where it starts.
    let mut bytes = vec![0x55u8; 0x40];
    bytes[0x0e..0x12].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x10, false, true),
            Section::mapped(".data", 0x2000, 0x10, 0x30, true, false),
        ],
    );
    let got = find_bytes(&p, &parse_pattern("de ad be ef").unwrap(), 0);
    assert_eq!(got.total, 1);
    assert_eq!((got.hits[0].va, got.hits[0].file_off), (Some(0x100e), 0x0e));
}

/// A section whose memory size exceeds its file bytes walks only the
/// file's extent.
///
/// A pattern at the extent's end is found there with the address the
/// section gives, and the file bytes past it belong to no section and say
/// so.
#[test]
fn find_bytes_at_the_end_of_a_short_file_extent() {
    let mut bytes = vec![0x66u8; 0x40];
    bytes[0x1d..0x21].copy_from_slice(&[0x12, 0x34, 0x56, 0x78]);
    bytes[0x25..0x29].copy_from_slice(&[0x12, 0x34, 0x56, 0x78]);
    let text = Section {
        name: ".text".to_owned(),
        va: Va(0x1000),
        vsize: 0x40,
        file_off: FileOff(0),
        file_size: 0x20,
        readable: true,
        writable: false,
        executable: true,
    };
    let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
    let pattern = parse_pattern("12 34 56 78").unwrap();
    let got = find_bytes(&p, &pattern, 0);
    let list: Vec<(Option<u64>, u64)> = got.hits.iter().map(|h| (h.va, h.file_off)).collect();
    assert_eq!(list, [(Some(0x101d), 0x1d), (None, 0x25)]);
    assert_eq!(got.total, 2);
    assert_naive(&p, &pattern);
}

/// The page holds at most [`HITS_MAX`] hits.
///
/// An offset at the total answers an empty page, one before it the last
/// hit alone, and one past it nothing at all - the anchored scan and the
/// all-wildcard walk alike.
#[test]
fn find_bytes_pages_at_and_beyond_the_total_and_caps_the_page() {
    let bytes = vec![0xaau8; 600];
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 600, false, true)],
    );
    for spec in ["aa", "?"] {
        let pattern = parse_pattern(spec).unwrap();
        let all = find_bytes(&p, &pattern, 0);
        assert_eq!(all.total, 600, "spec {spec}");
        assert_eq!(all.hits.len(), HITS_MAX, "spec {spec}");
        let tail = find_bytes(&p, &pattern, HITS_MAX);
        assert_eq!(tail.hits.len(), 100, "spec {spec}");
        assert_eq!(tail.total, 600, "spec {spec}");
        assert_eq!(
            tail.hits.first().map(|h| h.file_off),
            Some(500),
            "spec {spec}"
        );
        let last = find_bytes(&p, &pattern, 599);
        assert_eq!(last.hits.len(), 1, "spec {spec}");
        assert_eq!(last.hits[0].file_off, 599, "spec {spec}");
        for offset in [600, 601, 9999] {
            let page = find_bytes(&p, &pattern, offset);
            assert!(page.hits.is_empty(), "spec {spec} offset {offset}");
            assert_eq!(page.total, 600, "spec {spec} offset {offset}");
        }
    }
}

/// `find_bytes` answers what a byte-by-byte scan answers.
///
/// Two hundred pseudo-random five-to-twelve-byte patterns with wildcards,
/// planted into a four-kilobyte pseudo-random buffer that two sections
/// and three unmapped gaps divide, match the naive reference exactly, hit
/// for hit and in order.
#[test]
fn find_bytes_equals_the_naive_scan_on_planted_random_patterns() {
    /// Size of the pseudo-random buffer.
    const LEN: usize = 0x1000;
    /// Patterns tried.
    const PATTERNS: usize = 200;
    let mut x = 0x600d_1dea_u32;
    let mut step = || {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        x
    };
    let mut bytes: Vec<u8> = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        bytes.push(borer_engine::num::lo8(u64::from(step())));
    }
    let mut patterns: Vec<Vec<Option<u8>>> = Vec::with_capacity(PATTERNS);
    for k in 0..PATTERNS {
        let len = 5 + usize::try_from(step() % 8).unwrap();
        let mut pattern: Vec<Option<u8>> = (0..len)
            .map(|_| (step() % 4 == 0).then(|| borer_engine::num::lo8(u64::from(step()))))
            .collect();
        if !pattern.iter().any(|p| p.is_some()) {
            pattern[0] = Some(borer_engine::num::lo8(u64::from(step())));
        }
        plant_at(
            &mut bytes,
            &pattern,
            (k * 97 + 13) % (LEN - pattern.len() - 1),
        );
        patterns.push(pattern);
    }
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x10, 0x7f0, false, true),
            Section::mapped(".data", 0x2000, 0x900, 0x600, true, false),
        ],
    );
    let mut found = 0;
    for pattern in &patterns {
        let want = naive_byte_hits(&p, pattern);
        let got = find_bytes(&p, pattern, 0);
        assert_eq!(got.total, want.len());
        let list: Vec<(Option<u64>, u64)> = got.hits.iter().map(|h| (h.va, h.file_off)).collect();
        let page = &want[..want.len().min(HITS_MAX)];
        assert_eq!(list, page);
        found += got.total;
    }
    assert!(
        found >= PATTERNS / 2,
        "the plantings must be found, not only the absences: {found}"
    );
}
