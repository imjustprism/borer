//! Masked byte patterns: nibbles beside whole bytes and wildcards.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Arch, Program, Section};
use borer_engine::search::{HITS_MAX, Lane, PATTERN_MAX, find_masked, parse_masked};

/// Builds a one-section program at 0x1000 holding `48 8b` at 0x00, `41 8b`
/// at 0x10, `58 8b` at 0x20 and `49 8b` at 0x30, zeros elsewhere.
fn opcodes() -> Program {
    let mut bytes = vec![0u8; 0x40];
    for (at, b) in [(0x00, 0x48), (0x10, 0x41), (0x20, 0x58), (0x30, 0x49)] {
        bytes[at] = b;
        bytes[at + 1] = 0x8b;
    }
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x40, false, true)],
    )
}

/// Returns the addresses of a masked pattern's hits; none for a pattern
/// that does not parse.
fn vas(p: &Program, pattern: &str) -> Vec<u64> {
    let Ok(lanes) = parse_masked(pattern) else {
        return Vec::new();
    };
    find_masked(p, &lanes, 0)
        .hits
        .iter()
        .filter_map(|h| h.va)
        .collect()
}

/// A high nibble fixes the top four bits only, a low nibble the bottom
/// four: `4? 8b` finds 48 8b and 41 8b and 49 8b, not 58 8b; `?8 8b` finds
/// 48 8b and 58 8b, not 41 or 49.
#[test]
fn a_nibble_fixes_its_own_four_bits() {
    let p = opcodes();
    assert_eq!(vas(&p, "4? 8b"), vec![0x1000, 0x1010, 0x1030]);
    assert_eq!(vas(&p, "?8 8b"), vec![0x1000, 0x1020]);
    assert_eq!(vas(&p, "?9 8B"), vec![0x1030]);
}

/// A pattern of nibbles and wildcards has no whole byte to anchor on and
/// walks every window, still exact: `4? ?b` finds the three 4x 8b pairs.
#[test]
fn a_pattern_without_a_whole_byte_walks_every_window() {
    let p = opcodes();
    assert_eq!(vas(&p, "4? ?b"), vec![0x1000, 0x1010, 0x1030]);
    assert_eq!(vas(&p, "?? ?b"), vec![0x1000, 0x1010, 0x1020, 0x1030]);
}

/// Tokens read as lanes: whole bytes, both nibbles, and both wildcard
/// spellings.
#[test]
fn tokens_read_as_lanes() {
    let lane = |value, mask| Lane { value, mask };
    assert_eq!(
        parse_masked("8b 4? ?8 ?? ?").expect("lanes"),
        vec![
            lane(0x8b, 0xff),
            lane(0x40, 0xf0),
            lane(0x08, 0x0f),
            lane(0, 0),
            lane(0, 0)
        ]
    );
}

/// A bad token is refused with its 1-based column and the forms a token
/// takes; an empty pattern and one past the cap are refused too.
#[test]
fn a_bad_token_is_refused_at_its_column() {
    let why = parse_masked("48  4g").expect_err("4g is no token");
    assert!(why.starts_with("column 5: '4g' is not a byte"), "{why}");
    assert!(why.contains("4? or ?8"), "{why}");
    for bad in ["4", "123", "+1", "?x", "???"] {
        assert!(parse_masked(bad).is_err(), "{bad}");
    }
    assert!(
        parse_masked("   ")
            .expect_err("no byte")
            .contains("no byte")
    );
    let long = "00 ".repeat(PATTERN_MAX + 1);
    let why = parse_masked(&long).expect_err("past the cap");
    assert!(why.contains(&PATTERN_MAX.to_string()), "{why}");
    assert!(parse_masked(&"00 ".repeat(PATTERN_MAX)).is_ok());
}

/// `find_masked` answers what a lane-by-lane scan of every window
/// answers, over pseudo-random patterns of whole bytes, nibbles and
/// wildcards on pseudo-random bytes.
#[test]
fn find_masked_equals_the_naive_scan() {
    let mut x = 0x5eed_u32;
    let mut step = move || {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        x
    };
    let bytes: Vec<u8> = (0..0x800)
        .map(|_| borer_engine::num::lo8(u64::from(step() & 0x77)))
        .collect();
    let p = Program::raw(
        bytes.clone(),
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x800, false, true)],
    );
    let mut found = 0;
    for _ in 0..200 {
        let len = 1 + usize::try_from(step() % 11).expect("small");
        let lanes: Vec<Lane> = (0..len)
            .map(|_| {
                let mask = [0xff, 0xf0, 0x0f, 0][usize::try_from(step() % 4).expect("small")];
                Lane {
                    value: borer_engine::num::lo8(u64::from(step())) & mask,
                    mask,
                }
            })
            .collect();
        let want: Vec<u64> = (0..=bytes.len() - len)
            .filter(|&i| {
                lanes
                    .iter()
                    .zip(&bytes[i..])
                    .all(|(l, b)| b & l.mask == l.value)
            })
            .map(|i| 0x1000 + u64::try_from(i).expect("small"))
            .collect();
        let got = find_masked(&p, &lanes, 0);
        assert_eq!(got.total, want.len(), "{lanes:?}");
        let page: Vec<u64> = got.hits.iter().filter_map(|h| h.va).collect();
        assert_eq!(page, want[..want.len().min(HITS_MAX)], "{lanes:?}");
        found += got.total;
    }
    assert!(found > 0, "the patterns found something");
}
