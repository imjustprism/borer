//! Search tests: AOB patterns with wildcards, text search, demangling.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Arch, Program, Section};
use borer_engine::search::{
    demangled_name, demangled_or_raw, find_bytes, find_text, parse_pattern,
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

/// Text search finds the literal and nothing for an absent one.
#[test]
fn find_text_hits() {
    let p = fixture();
    let hits = find_text(&p, b"needle", 0).hits;
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].va, Some(0x1020));
    assert!(find_text(&p, b"absent", 0).hits.is_empty());
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
    let n = find_text(&p, b"needle", 0);
    assert_eq!(n.total, 1);
    assert_eq!(n.hits[0].va, Some(0x1000));
    // An ASCII query finds the wide string, case-folded.
    assert_eq!(
        find_text(&p, b"wide", 0).hits.first().and_then(|h| h.va),
        Some(0x1010)
    );
    assert_eq!(find_text(&p, b"WIDE", 0).total, 1);
    assert!(find_text(&p, b"absent", 0).hits.is_empty());
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
    let needles: [&[u8]; 6] = [
        b"a",
        b"Nee",
        b"needle",
        b"Needle",
        b"7",
        b"0123456789abcdef",
    ];
    for needle in needles {
        let want = naive_text_hits(&bytes, needle);
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
    let hits = find_text(&raw, b"needle", 0);
    assert_eq!(hits.total, 1);
    assert_eq!((hits.hits[0].va, hits.hits[0].file_off), (None, 0x30));

    let mut p = fixture();
    p.bytes.extend_from_slice(b"\0\0overlay needle\0");
    let hits = find_text(&p, b"needle", 0).hits;
    let found: Vec<_> = hits.iter().map(|h| (h.va, h.file_off)).collect();
    assert_eq!(found, [(Some(0x1020), 0x20), (None, 0x4a)]);
    let aob = find_bytes(&raw, &parse_pattern("6e 65 ?? 64").unwrap(), 0);
    assert_eq!(
        aob.hits.iter().map(|h| h.file_off).collect::<Vec<_>>(),
        [0x30]
    );
}
