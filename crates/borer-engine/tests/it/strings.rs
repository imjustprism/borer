//! Adversarial tests for the word-wise string walks: the ASCII and
//! UTF-16LE span scans and the spans' materialization, against per-byte
//! reference models.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::strings::{
    Encoding, RawStringSpan, find_ascii_spans, find_wide_spans, printable,
};

/// Longest text the engine renders in full before appending `...`
/// (strings.rs's private `DISPLAY_MAX`, mirrored here).
const DISPLAY_MAX: usize = 200;

/// Advances a deterministic xorshift32 generator by one step.
///
/// # Arguments
///
/// * `x` - The generator's state, updated in place.
///
/// # Returns
///
/// The next pseudo-random word.
fn step(x: &mut u32) -> u32 {
    *x ^= *x << 13;
    *x ^= *x >> 17;
    *x ^= *x << 5;
    *x
}

/// Cuts text as the engine's display does: [`DISPLAY_MAX`] characters,
/// then `...` when it was cut.
///
/// # Arguments
///
/// * `text` - The whole decoded text.
///
/// # Returns
///
/// The cut text.
fn cut(text: &str) -> String {
    if text.chars().count() <= DISPLAY_MAX {
        return text.to_owned();
    }
    let mut t: String = text.chars().take(DISPLAY_MAX).collect();
    t.push_str("...");
    t
}

/// The per-byte ASCII reference walk, the oracle the word-wise scan must
/// reproduce: maximal printable runs of at least `min_len` bytes.
///
/// # Arguments
///
/// * `bytes` - The buffer walked.
/// * `min_len` - Shortest run kept, in bytes.
///
/// # Returns
///
/// Every run as `(off, len, whole text)`.
fn ascii_reference(bytes: &[u8], min_len: usize) -> Vec<(u64, usize, String)> {
    let mut hits: Vec<(u64, usize, String)> = Vec::new();
    let mut start: Option<usize> = None;
    for (i, &b) in bytes.iter().enumerate() {
        match (start, printable(b)) {
            (None, true) => start = Some(i),
            (Some(s), false) => {
                if i - s >= min_len {
                    hits.push((
                        borer_engine::num::from_usize(s),
                        i - s,
                        String::from_utf8_lossy(&bytes[s..i]).into_owned(),
                    ));
                }
                start = None;
            }
            (None, false) | (Some(_), true) => {}
        }
    }
    if let Some(s) = start
        && bytes.len() - s >= min_len
    {
        hits.push((
            borer_engine::num::from_usize(s),
            bytes.len() - s,
            String::from_utf8_lossy(&bytes[s..]).into_owned(),
        ));
    }
    hits
}

/// The per-byte wide reference walk, the oracle the word-wise scan must
/// reproduce.
///
/// Maximal runs of printable UTF-16LE code units of at least `min_len`
/// units, none starting on the byte after a printable one.
///
/// # Arguments
///
/// * `bytes` - The buffer walked.
/// * `min_len` - Shortest run kept, in code units.
///
/// # Returns
///
/// Every run as `(off, len in units, whole text)`.
fn wide_reference(bytes: &[u8], min_len: usize) -> Vec<(u64, usize, String)> {
    let mut hits: Vec<(u64, usize, String)> = Vec::new();
    let mut i = 0;
    while i + 1 < bytes.len() {
        let unit = printable(bytes[i]) && bytes[i + 1] == 0;
        let tail = i > 0 && printable(bytes[i - 1]);
        if !unit || tail {
            i += 1;
            continue;
        }
        let start = i;
        while i + 1 < bytes.len() && printable(bytes[i]) && bytes[i + 1] == 0 {
            i += 2;
        }
        let len = (i - start) / 2;
        if len >= min_len {
            let lows: Vec<u8> = bytes[start..i].iter().step_by(2).copied().collect();
            hits.push((
                borer_engine::num::from_usize(start),
                len,
                String::from_utf8_lossy(&lows).into_owned(),
            ));
        }
    }
    hits
}

/// Asserts the ASCII walk answers the per-byte reference: every span, its
/// extent and its materialized display text.
///
/// # Panics
///
/// When a span, an extent or a text disagrees with the reference.
fn assert_ascii_walk(bytes: &[u8], min_len: usize) {
    let got: Vec<(u64, usize, String)> = find_ascii_spans(bytes, min_len)
        .iter()
        .map(|s| {
            let hit = s.hit(bytes);
            (
                s.off,
                usize::try_from(s.len).unwrap_or(usize::MAX),
                hit.text,
            )
        })
        .collect();
    let want: Vec<(u64, usize, String)> = ascii_reference(bytes, min_len)
        .iter()
        .map(|(o, l, t)| (*o, *l, cut(t)))
        .collect();
    assert_eq!(got, want, "ascii min {min_len}");
}

/// Asserts the wide walk answers the per-byte reference: every span, its
/// extent and its materialized display text.
///
/// # Panics
///
/// When a span, an extent or a text disagrees with the reference.
fn assert_wide_walk(bytes: &[u8], min_len: usize) {
    let got: Vec<(u64, usize, String)> = find_wide_spans(bytes, min_len)
        .iter()
        .map(|s| {
            let hit = s.hit(bytes);
            (
                s.off,
                usize::try_from(s.len).unwrap_or(usize::MAX),
                hit.text,
            )
        })
        .collect();
    let want: Vec<(u64, usize, String)> = wide_reference(bytes, min_len)
        .iter()
        .map(|(o, l, t)| (*o, *l, cut(t)))
        .collect();
    assert_eq!(got, want, "utf16 min {min_len}");
}

/// The separator mask decides the boundary printables and the high-bit
/// bytes exactly at the word seams.
///
/// 0x1f, 0x20, 0x7e, 0x7f, 0x80 and 0xff planted at both phases of every
/// seam, where one word's carry or borrow would cross.
#[test]
fn ascii_spans_decide_bytes_exactly_at_word_seams() {
    for sep in [0x1fu8, 0x20, 0x7e, 0x7f, 0x80, 0xff] {
        let mut bytes = vec![b'-'; 40];
        for at in [7, 8, 15, 16, 23, 24, 31, 32] {
            bytes[at] = sep;
        }
        for min_len in 1..6 {
            assert_ascii_walk(&bytes, min_len);
        }
    }
}

/// Every byte value decides the same at every alignment: eight buffers,
/// each padding its head so a run of one value starts at that phase of
/// the eight-byte words.
#[test]
fn ascii_spans_decide_every_byte_at_every_alignment() {
    for pad in 0..8 {
        let mut bytes = vec![0x01u8; pad];
        for b in 0..=255u8 {
            bytes.extend_from_slice(&[b; 8]);
            bytes.extend_from_slice(&[0x01; 8]);
        }
        for min_len in 1..9 {
            assert_ascii_walk(&bytes, min_len);
        }
    }
}

/// Runs of exactly the minimum are kept and one shorter is dropped.
///
/// A run may touch either end of the buffer, a word of separators alone
/// ends whatever run approached it, and `min_len` 0 and 1 answer the same
/// runs (a walk never reports an empty one).
#[test]
fn ascii_spans_keep_exactly_the_minimum_and_touch_both_ends() {
    let mut bytes: Vec<u8> = Vec::new();
    for len in 1..=9 {
        bytes.extend(std::iter::repeat_n(b'r', len));
        bytes.push(0x00);
    }
    bytes.extend_from_slice(b"tail");
    for min_len in 0..=10 {
        assert_ascii_walk(&bytes, min_len);
    }
    assert_eq!(
        find_ascii_spans(&bytes, 0),
        find_ascii_spans(&bytes, 1),
        "min_len 0 keeps the same runs as 1"
    );

    let mut blocked = b"left-side".to_vec();
    blocked.extend_from_slice(&[0x80u8; 24]);
    blocked.extend_from_slice(b"right-side");
    for min_len in 1..10 {
        assert_ascii_walk(&blocked, min_len);
    }

    assert_eq!(find_ascii_spans(b"", 0), Vec::new());
    assert_eq!(
        find_ascii_spans(&[0x00, 0x01, 0x1f, 0x7f, 0x80, 0xff], 0),
        Vec::new()
    );
}

/// A wide run one unit shorter than the minimum is dropped and one at it
/// is kept.
///
/// A run preceded by a printable byte is trimmed by that unit, and the
/// trim that empties a run reports nothing - at the buffer's very start
/// and at `min_len` 0 no less.
#[test]
fn wide_spans_trim_the_first_unit_and_respect_the_minimum() {
    assert_eq!(
        find_wide_spans(b"XA\x00\xff", 0),
        Vec::new(),
        "a printable byte before a one-unit run leaves no run to report"
    );
    let mut bytes: Vec<u8> = vec![0xff];
    for units in 1..=5 {
        bytes.extend(std::iter::repeat_n(b'w', units).flat_map(|b| [b, 0]));
        bytes.extend_from_slice(&[0xff, 0xff]);
    }
    // a printable byte before the last run: trimmed by one unit
    bytes.push(b'x');
    bytes.extend(b"zvuts".iter().flat_map(|b| [*b, 0]));
    for min_len in 0..=7 {
        assert_wide_walk(&bytes, min_len);
    }
    assert_eq!(
        find_wide_spans(&bytes, 0),
        find_wide_spans(&bytes, 1),
        "min_len 0 keeps the same runs as 1"
    );
}

/// The wide scan survives the borrow chains of its word-wise zero test.
///
/// The test over-flags bytes (a 0x01 after a zero); the printable check
/// must reject every false candidate on zero-dense pseudo-random data,
/// with runs planted at every phase, ASCII tails before half of them.
#[test]
fn wide_spans_survive_borrow_chain_zero_flags() {
    /// Size of the pseudo-random buffer.
    const LEN: usize = 0x600;
    let mut x = 0x0f0e_0d0c_u32;
    let mut bytes: Vec<u8> = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        let r = step(&mut x);
        bytes.push(match r % 4 {
            0 => 0,
            1 => 0x01,
            _ => borer_engine::num::lo8(u64::from(r >> 8)),
        });
    }
    for at in (16..LEN - 24).step_by(49) {
        let mut p = at;
        if (at / 49) % 2 == 0 {
            bytes[p..p + 4].copy_from_slice(b"abc\0");
            p += 4;
        }
        for b in b"wide" {
            bytes[p] = *b;
            bytes[p + 1] = 0;
            p += 2;
        }
    }
    for min_len in 0..=8 {
        assert_wide_walk(&bytes, min_len);
    }
}

/// Spans whose bytes no longer stand answer empty texts, never a panic:
/// offsets at and past the end, lengths that overrun, saturated counts,
/// and every encoding's decode.
#[test]
fn spans_of_bytes_that_no_longer_stand_answer_empty() {
    let bytes = b"ab";
    for span in [
        RawStringSpan {
            off: 2,
            len: 1,
            encoding: Encoding::Ascii,
        },
        RawStringSpan {
            off: 100,
            len: 5,
            encoding: Encoding::Ascii,
        },
        RawStringSpan {
            off: 0,
            len: 9,
            encoding: Encoding::Utf16,
        },
        RawStringSpan {
            off: u64::MAX,
            len: 1,
            encoding: Encoding::Utf16,
        },
        RawStringSpan {
            off: 0,
            len: u32::MAX,
            encoding: Encoding::DotnetUs,
        },
    ] {
        let hit = span.hit(bytes);
        assert_eq!(span.text(bytes), "", "{span:?}");
        assert!(span.raw_bytes(bytes).is_empty(), "{span:?}");
        assert_eq!(hit.text, "", "{span:?}");
        assert_eq!(hit.full_text(bytes), "", "{span:?}");
    }
}

/// A span materializes exactly the row a per-byte walk answers: offsets,
/// lengths and display texts agree for both encodings at every minimum,
/// and a cut display text still holds its whole text behind it.
#[test]
fn span_hits_round_trip_the_reference_walks() {
    /// Size of the pseudo-random buffer.
    const LEN: usize = 0x1800;
    let mut x = 0x7a11_5eed_u32;
    let mut bytes: Vec<u8> = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        let r = step(&mut x);
        bytes.push(match r % 8 {
            0 => 0,
            1..=3 => borer_engine::num::lo8(u64::from(0x20 + (r >> 8) % 95)),
            _ => borer_engine::num::lo8(u64::from(r >> 8)),
        });
    }
    for at in [0, 1, 7, 8, 15, 16, LEN / 2, LEN - 7, LEN - 6] {
        bytes[at..at + 6].copy_from_slice(b"Seam;!");
    }
    for (at, tail) in [
        (40usize, true),
        (LEN / 2 + 7, true),
        (LEN / 2 + 13, false),
        (LEN / 2 + 29, true),
    ] {
        let mut p = at;
        if tail {
            bytes[p..p + 4].copy_from_slice(b"abc\0");
            p += 4;
        }
        for b in b"wide" {
            bytes[p] = *b;
            bytes[p + 1] = 0;
            p += 2;
        }
    }
    let monster = LEN / 4;
    bytes[monster - 1] = 1; // a separator: the run's extent is exactly the plantings
    for k in 0..300 {
        bytes[monster + k] = b'm';
    }
    bytes[monster + 300] = 0;
    let wmonster = 3 * LEN / 4;
    bytes[wmonster - 1] = 1; // not printable: no ASCII tail trims the run's first unit
    for k in 0..300 {
        bytes[wmonster + k * 2] = b'w';
        bytes[wmonster + k * 2 + 1] = 0;
    }
    bytes[wmonster + 600] = 1;
    bytes[wmonster + 601] = 1;
    for min_len in 1..=8 {
        assert_ascii_walk(&bytes, min_len);
        assert_wide_walk(&bytes, min_len);
    }

    let ascii = find_ascii_spans(&bytes, 5);
    let big = ascii
        .iter()
        .find(|s| usize::try_from(s.len).unwrap() > DISPLAY_MAX)
        .unwrap();
    let hit = big.hit(&bytes);
    assert_eq!(hit.text.chars().count(), DISPLAY_MAX + 3);
    assert!(hit.text.ends_with("..."));
    assert_eq!(hit.full_text(&bytes).chars().count(), 300);
    assert!(hit.full_text(&bytes).ends_with("mmm"));

    let wide = find_wide_spans(&bytes, 5);
    let wbig = wide
        .iter()
        .find(|s| usize::try_from(s.len).unwrap() > DISPLAY_MAX)
        .unwrap();
    let whit = wbig.hit(&bytes);
    assert!(whit.text.ends_with("..."));
    assert_eq!(whit.full_text(&bytes).chars().count(), 300);
    assert!(whit.full_text(&bytes).ends_with("www"));
}
