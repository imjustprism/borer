//! Shannon entropy and windowed high-entropy region scanning, the packer and
//! embedded-payload heuristic.

use crate::num::{from_usize, saturating_usize, usize_f64};
use crate::program::Program;

/// Computes the Shannon entropy of `data` in bits per byte.
///
/// # Arguments
///
/// * `data` - The bytes to measure; the empty slice has entropy `0.0`.
///
/// # Returns
///
/// A value in `0.0..=8.0`; `8.0` means every byte value is equally likely.
pub fn shannon(data: &[u8]) -> f64 {
    let mut counts = [0usize; 256];
    for &b in data {
        counts[usize::from(b)] += 1;
    }
    of_counts(&counts, data.len())
}

/// Computes the Shannon entropy of a byte histogram in bits per byte.
///
/// # Arguments
///
/// * `counts` - How many times each byte value occurs.
/// * `n` - The sum of `counts`; `0` has entropy `0.0`.
///
/// # Returns
///
/// A value in `0.0..=8.0`, never `-0.0`: the terms are folded from `+0.0`,
/// since a float sum starts from `-0.0` and a histogram of one byte value
/// (one term of `-0.0`) printed as `-0.00`.
fn of_counts(counts: &[usize; 256], n: usize) -> f64 {
    if n == 0 {
        return 0.0;
    }
    let n = usize_f64(n);
    counts
        .iter()
        .filter(|&&c| c > 0)
        .map(|&c| {
            let p = usize_f64(c) / n;
            -p * p.log2()
        })
        .fold(0.0, |sum, term| sum + term)
}

/// A text encoding that carries binary data in printable characters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    /// Base64 in the standard (`+/`) or url-safe (`-_`) alphabet, with `=`
    /// padding and line breaks allowed.
    Base64,
    /// Hexadecimal digits of either case, two per byte, line breaks allowed.
    Hex,
}

impl Encoding {
    /// Returns the lowercase name used in tool output (`base64` or `hex`).
    pub fn name(self) -> &'static str {
        match self {
            Encoding::Base64 => "base64",
            Encoding::Hex => "hex",
        }
    }
}

/// A run of consecutive high-entropy windows of the file, or a run of
/// encoded text whose decoded bytes are high-entropy.
#[derive(Debug, Clone, PartialEq)]
pub struct Region {
    /// File offset of the first window.
    pub off: u64,
    /// Virtual address of the first window; `None` when no section maps
    /// those bytes (headers, gaps, an overlay, a file with no sections).
    pub va: Option<u64>,
    /// Length in bytes of the file: whole windows, the last one cut short
    /// where a section or an uncovered run ends, or the whole encoded text
    /// with its line breaks and padding.
    pub len: u64,
    /// Mean entropy of the windows making up the region, or of the decoded
    /// bytes of encoded text (bits per byte).
    pub entropy: f64,
    /// The encoding the text was decoded from before it was measured;
    /// `None` for the file's own bytes.
    pub encoding: Option<Encoding>,
}

/// Hard cap on the number of regions [`high_entropy_regions`] reports.
pub const REGIONS_MAX: usize = 200;
/// Smallest window accepted by [`high_entropy_regions`], in bytes.
pub const WINDOW_MIN: usize = 64;
/// Fewest decoded bytes an encoded run needs to be judged: below this a
/// random key and a word decode to entropies too close to tell apart.
pub const ENCODED_MIN: usize = 64;

/// Returns the entropy random data reads at, on average, in a window of
/// `window` bytes.
///
/// The plug-in estimate over `n` samples of 256 symbols sits about
/// `255 / (2 n ln 2)` bits below the true value: 7.28 bits in a 256-byte
/// window, 7.82 in 1,024 and 7.96 in 4,096. A threshold above this is one
/// no window of that size can meet, however random its bytes.
///
/// # Arguments
///
/// * `window` - Window size in bytes.
///
/// # Returns
///
/// The ceiling in bits per byte. The window is a byte count, exact as an
/// `f64` far past any size a scan uses.
pub fn ceiling(window: usize) -> f64 {
    8.0 - 255.0 / (2.0 * usize_f64(window) * std::f64::consts::LN_2)
}

/// Finds the high-entropy regions of every byte of the file.
///
/// Each section's file extent is cut into non-overlapping `window`-byte
/// chunks, the last one cut short where the extent ends; adjacent chunks
/// at or above `threshold` merge into one [`Region`]. The bytes no section covers are then scanned the same way,
/// one uncovered range at a time: the headers, gaps between sections, an
/// overlay appended after the last section (where installers and packers
/// keep their payload), and the whole of a file with no sections. The scan
/// stops after [`REGIONS_MAX`] regions.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `window` - Chunk size in bytes; values below [`WINDOW_MIN`] are raised to it.
/// * `threshold` - Minimum entropy in bits per byte for a chunk to count.
///
/// # Returns
///
/// The regions of the sections in section order, then address order; then
/// those of the uncovered bytes in file order.
pub fn high_entropy_regions(program: &Program, window: usize, threshold: f64) -> Vec<Region> {
    let window = window.max(WINDOW_MIN);
    let mut regions: Vec<Region> = Vec::new();
    for s in &program.sections {
        let Some(data) = program.section_bytes(s) else {
            continue;
        };
        let at = |off: u64| Some(s.va.0 + (off - s.file_off.0));
        if scan(data, s.file_off.0, at, window, threshold, &mut regions) {
            return regions;
        }
    }
    for (off, data) in program.unmapped() {
        let at = |off: u64| program.offset_to_va(off);
        if scan(data, off, at, window, threshold, &mut regions) {
            return regions;
        }
    }
    encoded_regions(program, window, threshold, &mut regions);
    regions
}

/// Appends the runs of base64 or hex text whose decoded bytes are
/// high-entropy.
///
/// Base64 of random bytes reads about 6 bits per byte and hex about 4, so
/// no byte threshold finds the encrypted blobs, keys and wrapped payloads
/// that binaries and data files most often store this way. A run is a
/// maximal stretch of one alphabet's characters and line breaks, with its
/// `=` padding; it is hex when every character is a hex digit, base64
/// otherwise. It is decoded and judged whole, against the ceiling for its
/// decoded size ([`ceiling`]): it must come as close to that ceiling as
/// `threshold` comes to the ceiling of a `window`-byte chunk. Runs that
/// decode to fewer than [`ENCODED_MIN`] bytes are skipped. One pass over
/// the file, and no run is decoded twice.
///
/// The pass finds the runs of alphabet characters and line breaks eight
/// bytes at a time, and only a run long enough to hold such text is
/// looked at byte by byte ([`encoded_run`]).
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `window` - The byte scan's chunk size, which places `threshold`.
/// * `threshold` - The byte scan's minimum entropy in bits per byte.
/// * `regions` - The list the regions are appended to, up to [`REGIONS_MAX`].
fn encoded_regions(program: &Program, window: usize, threshold: f64, regions: &mut Vec<Region>) {
    let bytes = &program.bytes;
    let margin = ceiling(window) - threshold;
    let text_byte: [bool; 256] = std::array::from_fn(|b| {
        u8::try_from(b).is_ok_and(|b| sextet(b).is_some() || b == b'\r' || b == b'\n')
    });
    let mut judge = |from: usize, to: usize| {
        to.saturating_sub(from).saturating_mul(3) >= ENCODED_MIN * 4
            && encoded_run(program, from, to, margin, regions)
    };
    let mut from = 0;
    let (words, tail) = bytes.as_chunks::<8>();
    for (k, w) in words.iter().enumerate() {
        let seps = (0..8).fold(0u32, |m, j| {
            m | (u32::from(!text_byte[usize::from(w[j])]) << j)
        });
        if seps == 0 {
            continue;
        }
        let at = 8 * k;
        if judge(
            from,
            at + saturating_usize(u64::from(seps.trailing_zeros())),
        ) {
            return;
        }
        from = at + saturating_usize(u64::from(u32::BITS - seps.leading_zeros()));
    }
    for (j, &b) in tail.iter().enumerate() {
        if !text_byte[usize::from(b)] {
            let at = 8 * words.len() + j;
            if judge(from, at) {
                return;
            }
            from = at + 1;
        }
    }
    judge(from, bytes.len());
}

/// Judges one maximal run of alphabet characters and line breaks, and
/// appends it as a region when its decoded bytes are high-entropy.
///
/// The text is the run without the line breaks it starts or ends with,
/// followed by up to two `=` of padding; it is hex when every character
/// is a hex digit, base64 otherwise.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `from` / `to` - The run's file offsets, `to` one past its last byte.
/// * `margin` - How far below its ceiling ([`ceiling`]) the decoded bytes
///   may read.
/// * `regions` - The list the region is appended to.
///
/// # Returns
///
/// Whether `regions` reached [`REGIONS_MAX`], which ends the scan.
fn encoded_run(
    program: &Program,
    from: usize,
    to: usize,
    margin: f64,
    regions: &mut Vec<Region>,
) -> bool {
    let bytes = &program.bytes;
    let run = bytes.get(from..to).unwrap_or_default();
    let (Some(first), Some(last)) = (
        run.iter().position(|&b| sextet(b).is_some()),
        run.iter().rposition(|&b| sextet(b).is_some()),
    ) else {
        return false;
    };
    let (start, end) = (from + first, from + last + 1);
    let text = &bytes[start..end];
    if text.len() * 3 < ENCODED_MIN * 4 {
        return false;
    }
    let pad = bytes[end..]
        .iter()
        .take(2)
        .take_while(|&&b| b == b'=')
        .count();
    let encoding = if text
        .iter()
        .all(|b| b.is_ascii_hexdigit() || *b == b'\r' || *b == b'\n')
    {
        Encoding::Hex
    } else {
        Encoding::Base64
    };
    let mut counts = [0usize; 256];
    let mut n = 0usize;
    decode(text, encoding, |b| {
        counts[usize::from(b)] += 1;
        n += 1;
    });
    let e = of_counts(&counts, n);
    if n >= ENCODED_MIN && e >= ceiling(n) - margin {
        let off = from_usize(start);
        regions.push(Region {
            off,
            va: program.offset_to_va(off),
            len: from_usize(end + pad - start),
            entropy: e,
            encoding: Some(encoding),
        });
    }
    regions.len() >= REGIONS_MAX
}

/// Returns the 6-bit value of a base64 character of either alphabet.
///
/// # Arguments
///
/// * `b` - The character.
///
/// # Returns
///
/// The value, or `None` when `b` is in neither alphabet (`=` included).
fn sextet(b: u8) -> Option<u8> {
    Some(match b {
        b'A'..=b'Z' => b - b'A',
        b'a'..=b'z' => b - b'a' + 26,
        b'0'..=b'9' => b - b'0' + 52,
        b'+' | b'-' => 62,
        b'/' | b'_' => 63,
        _ => return None,
    })
}

/// Decodes encoded text, skipping line breaks, and hands each byte to `emit`.
///
/// A trailing partial group (fewer than 8 bits) is dropped, as padding
/// would drop it.
///
/// # Arguments
///
/// * `text` - Characters of `encoding`'s alphabet and line breaks.
/// * `encoding` - How the text encodes its bytes.
/// * `emit` - Receives the decoded bytes in order.
pub(crate) fn decode(text: &[u8], encoding: Encoding, mut emit: impl FnMut(u8)) {
    let (bits, value): (u32, fn(u8) -> Option<u8>) = match encoding {
        Encoding::Base64 => (6, sextet),
        Encoding::Hex => (4, |b| {
            char::from(b)
                .to_digit(16)
                .and_then(|d| u8::try_from(d).ok())
        }),
    };
    let mut acc = 0u32;
    let mut held = 0u32;
    for v in text.iter().filter_map(|&b| value(b)) {
        acc = ((acc << bits) | u32::from(v)) & 0xffff;
        held += bits;
        if held >= 8 {
            held -= 8;
            emit(crate::num::lo8(u64::from(acc >> held)));
        }
    }
}

/// Scans one run of file bytes and appends its high-entropy regions.
///
/// The bytes after the last whole window are a chunk of their own, judged
/// over the last `window` bytes of the run (the whole run when it is
/// shorter), so their entropy is measured on as many samples as a whole
/// window's and meets the same threshold: a payload in the last kilobyte
/// of a section or of the file was never measured at all.
///
/// # Arguments
///
/// * `data` - The bytes, cut into `window`-byte chunks from its start.
/// * `off` - File offset of `data`'s first byte.
/// * `va_of` - Maps a file offset inside `data` to its virtual address.
/// * `window` - Chunk size in bytes.
/// * `threshold` - Minimum entropy in bits per byte for a chunk to count.
/// * `regions` - The list the regions are appended to.
///
/// # Returns
///
/// Whether `regions` reached [`REGIONS_MAX`], which ends the whole scan.
fn scan(
    data: &[u8],
    off: u64,
    va_of: impl Fn(u64) -> Option<u64>,
    window: usize,
    threshold: f64,
    regions: &mut Vec<Region>,
) -> bool {
    let step = from_usize(window);
    let whole = data.chunks_exact(window);
    let cut = whole.remainder().len();
    let last = (cut > 0).then(|| (cut, &data[data.len().saturating_sub(window)..]));
    let mut open: Option<(u64, u64, f64, u32)> = None;
    for (i, (len, chunk)) in (0u64..).zip(whole.map(|c| (window, c)).chain(last)) {
        let e = shannon(chunk);
        let len = from_usize(len);
        if e >= threshold {
            match open.as_mut() {
                Some((_, total, sum, n)) => {
                    *total += len;
                    *sum += e;
                    *n += 1;
                }
                None => open = Some((off + i * step, len, e, 1)),
            }
        } else if let Some(r) = open.take() {
            regions.push(close(r, &va_of));
            if regions.len() >= REGIONS_MAX {
                return true;
            }
        }
    }
    if let Some(r) = open {
        regions.push(close(r, &va_of));
    }
    regions.len() >= REGIONS_MAX
}

/// Turns an open `(off, len, entropy sum, window count)` run into a [`Region`].
///
/// # Arguments
///
/// * `run` - The accumulated run; `n` is at least 1.
/// * `va_of` - Maps the run's file offset to its virtual address.
///
/// # Returns
///
/// The region with the mean entropy of its windows.
fn close((off, len, sum, n): (u64, u64, f64, u32), va_of: impl Fn(u64) -> Option<u64>) -> Region {
    Region {
        off,
        va: va_of(off),
        len,
        entropy: sum / f64::from(n),
        encoding: None,
    }
}

/// Says why a threshold cannot be met, when it cannot.
///
/// Shared by the `entropy` tool and the `entropy` command, so the command
/// line refuses what the tool refuses. The value is echoed in exponent form
/// when it is huge or not finite: `1e308` echoed as its 309 digits.
///
/// # Arguments
///
/// * `threshold` - Bits per byte, as given.
///
/// # Returns
///
/// The message, or `None` for a value in `0..=8`.
#[must_use]
pub fn threshold_error(threshold: f64) -> Option<String> {
    /// Largest magnitude echoed in plain digits.
    const PLAIN_MAX: f64 = 1e6;
    (!(0.0..=8.0).contains(&threshold)).then(|| {
        let shown = if threshold.abs() < PLAIN_MAX {
            threshold.to_string()
        } else {
            format!("{threshold:e}")
        };
        format!("threshold {shown} is outside 0..8 bits per byte")
    })
}

/// Scans for high-entropy regions and renders one page of them.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `window` - Chunk size in bytes; values below [`WINDOW_MIN`] are raised to it.
/// * `threshold` - Minimum entropy in bits per byte, already checked
///   ([`threshold_error`]).
/// * `offset` - Regions to skip first (paging).
/// * `limit` - Most regions listed.
///
/// # Returns
///
/// A `# showing N of M high-entropy regions (window, threshold)` header,
/// saying when the scan stopped at [`REGIONS_MAX`] and where the next page
/// starts, a note when no window of that size can reach the threshold
/// ([`ceiling`]), then [`regions_tsv`] of the page.
#[must_use]
pub fn report(
    program: &Program,
    window: usize,
    threshold: f64,
    offset: usize,
    limit: usize,
) -> String {
    let window = window.max(WINDOW_MIN);
    let regions = high_entropy_regions(program, window, threshold);
    let total = regions.len();
    let start = offset.min(total);
    let end = start.saturating_add(limit).min(total);
    let mut out = format!(
        "# showing {} of {total} high-entropy regions (window={window}, threshold={threshold:.2})",
        end - start
    );
    if total >= REGIONS_MAX {
        out.push_str(&format!("; the scan stops at {REGIONS_MAX}"));
    }
    if end < total {
        out.push_str(&format!("; offset={end} for the next page"));
    }
    out.push('\n');
    let most = ceiling(window);
    if threshold > most {
        out.push_str(&format!(
            "# note: random data averages about {most:.2} bits in a {window}-byte window; above that only windows that beat chance pass, so widen the window or lower the threshold\n"
        ));
    }
    out.push_str(&regions_tsv(program, &regions[start..end]));
    out
}

/// Renders regions as `off va len entropy` rows under their column header.
///
/// A signed PE ends with its Authenticode certificate table, whose
/// signatures and certificates read as random. Once the scan covers the
/// bytes after the sections, every signed program reports regions there,
/// so a note says which file range is that table and an appended payload
/// is not looked for in it by mistake, nor a signature taken for one.
///
/// # Arguments
///
/// * `program` - The image the regions were found in.
/// * `regions` - The regions, in the order they are listed.
///
/// # Returns
///
/// The header line and one row per region; `-` stands for an address no
/// section maps, and encoded text ends its row with the encoding's name.
/// A note line follows when a region overlaps the certificate table.
pub fn regions_tsv(program: &Program, regions: &[Region]) -> String {
    let mut out = String::from("# off va len entropy [encoding]\n");
    for r in regions {
        let va = r.va.map_or_else(|| "-".to_owned(), |v| format!("{v:#x}"));
        let row = format!(
            "{:<10} {va:<12} {:<9} {:.2}",
            format!("{:#x}", r.off),
            format!("{:#x}", r.len),
            r.entropy
        );
        match r.encoding {
            Some(e) => out.push_str(&format!("{row} {}\n", e.name())),
            None => out.push_str(&format!("{row}\n")),
        }
    }
    if let Some((off, len)) = program.headers.certificates
        && regions
            .iter()
            .any(|r| r.off < off + len && off < r.off + r.len)
    {
        out.push_str(&format!(
            "# note: {off:#x}..{:#x} is the Authenticode certificate table; its signatures read as random\n",
            off + len
        ));
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::path::PathBuf;

    use super::{
        Encoding, ceiling, decode, high_entropy_regions, regions_tsv, report, shannon,
        threshold_error,
    };
    use crate::num::from_usize;
    use crate::program::{Arch, Program, Section};

    /// English prose, the content a base64 string most often carries that
    /// is not random.
    const PROSE: &str = "It was the best of times, it was the worst of times, it was the age \
        of wisdom, it was the age of foolishness, it was the epoch of belief, it was the epoch \
        of incredulity, it was the season of Light, it was the season of Darkness, it was the \
        spring of hope, it was the winter of despair, we had everything before us, we had \
        nothing before us, we were all going direct to Heaven, we were all going direct the \
        other way - in short, the period was so far like the present period, that some of its \
        noisiest authorities insisted on its being received, for good or for evil, in the \
        superlative degree of comparison only.";

    /// Encodes `data` as standard base64 with `=` padding, a line break
    /// every 76 characters as MIME writes it.
    fn base64(data: &[u8]) -> Vec<u8> {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut out = Vec::new();
        for (i, group) in data.chunks(3).enumerate() {
            if i > 0 && i % 19 == 0 {
                out.extend_from_slice(b"\r\n");
            }
            let word = group
                .iter()
                .enumerate()
                .fold(0u32, |w, (k, &b)| w | (u32::from(b) << (16 - 8 * k)));
            for k in 0..4 {
                out.push(if k <= group.len() {
                    ALPHABET[usize::try_from((word >> (18 - 6 * k)) & 63).unwrap_or(0)]
                } else {
                    b'='
                });
            }
        }
        out
    }

    /// Returns `n` bytes of a fixed pseudo-random stream (splitmix64), the
    /// stand-in for encrypted or compressed data.
    fn noise(n: usize) -> Vec<u8> {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut out = Vec::with_capacity(n + 8);
        while out.len() < n {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            out.extend_from_slice(&(z ^ (z >> 31)).to_le_bytes());
        }
        out.truncate(n);
        out
    }

    /// Builds a PE32+ with `overlay` appended after its one section.
    ///
    /// The layout is a linker's: 0x200 bytes of headers and a 0x200-byte
    /// `.text` mapped at `0x140001000`. The first `certificates` bytes of
    /// the overlay are the certificate table when that is not zero.
    fn pe_with_overlay(overlay: &[u8], certificates: u32) -> Program {
        /// The PE signature's file offset.
        const PE_AT: usize = 0x80;
        /// The optional header's file offset.
        const OPT: usize = PE_AT + 24;
        /// The section table's file offset, after a PE32+ optional header.
        const ROW: usize = OPT + 0xf0;
        let mut b = vec![0u8; 0x200];
        let mut put = |at: usize, v: &[u8]| b[at..at + v.len()].copy_from_slice(v);
        put(0, b"MZ");
        put(0x3c, &0x80u32.to_le_bytes());
        put(PE_AT, b"PE\0\0");
        put(PE_AT + 4, &0x8664u16.to_le_bytes());
        put(PE_AT + 6, &1u16.to_le_bytes());
        put(PE_AT + 20, &0xf0u16.to_le_bytes());
        put(PE_AT + 22, &0x22u16.to_le_bytes());
        put(OPT, &0x20bu16.to_le_bytes());
        put(OPT + 16, &0x1000u32.to_le_bytes());
        put(OPT + 24, &0x1_4000_0000u64.to_le_bytes());
        put(OPT + 32, &0x1000u32.to_le_bytes());
        put(OPT + 36, &0x200u32.to_le_bytes());
        put(OPT + 48, &6u16.to_le_bytes());
        put(OPT + 56, &0x2000u32.to_le_bytes());
        put(OPT + 60, &0x200u32.to_le_bytes());
        put(OPT + 68, &3u16.to_le_bytes());
        put(OPT + 108, &16u32.to_le_bytes());
        if certificates > 0 {
            put(OPT + 112 + 4 * 8, &0x400u32.to_le_bytes());
            put(OPT + 112 + 4 * 8 + 4, &certificates.to_le_bytes());
        }
        put(ROW, b".text");
        put(ROW + 8, &0x200u32.to_le_bytes());
        put(ROW + 12, &0x1000u32.to_le_bytes());
        put(ROW + 16, &0x200u32.to_le_bytes());
        put(ROW + 20, &0x200u32.to_le_bytes());
        put(ROW + 36, &0x6000_0020u32.to_le_bytes());
        b.push(0xc3);
        b.resize(0x400, 0xcc);
        b.extend_from_slice(overlay);
        Program::from_bytes(PathBuf::from("overlay.exe"), b).expect("the PE loads")
    }

    /// A file with no sections, the way an unrecognized format loads, is
    /// scanned whole: random bytes there were reported as no region at all.
    #[test]
    fn a_file_with_no_sections_is_scanned_whole() {
        let p = Program::raw(noise(0x10000), Arch::Unknown, 0, None, Vec::new());
        let regions = high_entropy_regions(&p, 1024, 7.2);
        assert_eq!(regions.len(), 1, "{regions:?}");
        assert_eq!((regions[0].off, regions[0].va), (0, None));
        assert_eq!(regions[0].len, 0x10000);
        assert!(regions[0].entropy > 7.7, "{regions:?}");
    }

    /// Random bytes appended after a PE's last section, where an installer
    /// or a packer keeps its payload, are reported with no address, while
    /// the headers and `.text` stay below the threshold.
    #[test]
    fn an_overlay_after_the_last_section_is_reported() {
        let p = pe_with_overlay(&noise(0x2000), 0);
        assert_eq!(p.sections.len(), 1);
        let regions = high_entropy_regions(&p, 1024, 7.2);
        assert_eq!(regions.len(), 1, "{regions:?}");
        assert_eq!((regions[0].off, regions[0].va), (0x400, None));
        assert_eq!(regions[0].len, 0x2000);
        let table = regions_tsv(&p, &regions);
        let row: Vec<&str> = table
            .lines()
            .nth(1)
            .unwrap_or("")
            .split_whitespace()
            .collect();
        assert_eq!(row[..3], ["0x400", "-", "0x2000"], "{table}");
        assert!(!table.contains("certificate"), "{table}");
    }

    /// The certificate table a signed PE ends with reads as random, so the
    /// table names it: every signed program has one, and it is no payload.
    #[test]
    fn a_signature_after_the_sections_is_named() {
        let mut table = Vec::from(0x2000u32.to_le_bytes());
        table.extend_from_slice(&0x0200u16.to_le_bytes());
        table.extend_from_slice(&0x0002u16.to_le_bytes());
        table.extend(noise(0x2000 - 8));
        let p = pe_with_overlay(&table, 0x2000);
        assert_eq!(p.headers.certificates, Some((0x400, 0x2000)));
        let regions = high_entropy_regions(&p, 1024, 7.2);
        assert_eq!(regions.len(), 1, "{regions:?}");
        let out = regions_tsv(&p, &regions);
        assert!(
            out.ends_with(
                "# note: 0x400..0x2400 is the Authenticode certificate table; its signatures read as random\n"
            ),
            "{out}"
        );
    }

    /// A section's region keeps the address it is mapped at, beside its
    /// file offset.
    #[test]
    fn a_section_region_has_its_address() {
        let mut bytes = vec![0u8; 0x400];
        bytes.extend(noise(0x1000));
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0x40_0000,
            None,
            vec![Section::mapped(
                ".data", 0x40_1000, 0x400, 0x1000, true, false,
            )],
        );
        let regions = high_entropy_regions(&p, 1024, 7.2);
        assert_eq!(regions.len(), 1, "{regions:?}");
        assert_eq!((regions[0].off, regions[0].va), (0x400, Some(0x40_1000)));
        assert_eq!(regions[0].len, 0x1000);
    }

    /// Random bytes after a section's last whole window are measured.
    ///
    /// The scan cut the extent into whole windows and never read the rest, so a
    /// payload in a section's last kilobyte was no region at all.
    #[test]
    fn the_bytes_after_the_last_whole_window_are_measured() {
        let mut bytes = vec![0u8; 0x1000];
        bytes.extend(noise(1000));
        let len = from_usize(bytes.len());
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0x40_0000,
            None,
            vec![Section::mapped(".data", 0x40_1000, 0, len, true, false)],
        );
        let regions = high_entropy_regions(&p, 1024, 7.2);
        assert_eq!(regions.len(), 1, "{regions:?}");
        assert_eq!((regions[0].off, regions[0].len), (0x1000, 1000));
        assert_eq!(regions[0].va, Some(0x40_2000));
        assert!(regions[0].entropy > 7.5, "{regions:?}");
    }

    /// A run of one byte value has no entropy and prints as `0.00`, never
    /// `-0.00`.
    #[test]
    fn one_byte_value_reads_positive_zero() {
        let e = shannon(&[7; 64]);
        assert!(e == 0.0 && e.is_sign_positive(), "{e}");
        assert_eq!(format!("{e:.2}"), "0.00");
    }

    /// A threshold outside 0..8 is refused in words that fit a line, whatever
    /// its size.
    ///
    /// The report pages its regions under a `showing` header.
    #[test]
    fn thresholds_are_checked_and_regions_paged() {
        assert_eq!(threshold_error(7.2), None);
        assert_eq!(
            threshold_error(9.0).as_deref(),
            Some("threshold 9 is outside 0..8 bits per byte")
        );
        assert_eq!(
            threshold_error(1e308).as_deref(),
            Some("threshold 1e308 is outside 0..8 bits per byte")
        );
        assert!(threshold_error(f64::NAN).is_some());
        assert!(threshold_error(-1.0).is_some());
        let mut bytes = Vec::new();
        for _ in 0..3 {
            bytes.extend(noise(0x400));
            bytes.extend(vec![0u8; 0x400]);
        }
        let p = Program::raw(bytes, Arch::Unknown, 0, None, Vec::new());
        let first = report(&p, 1024, 7.2, 0, 2);
        assert!(
            first.starts_with(
                "# showing 2 of 3 high-entropy regions (window=1024, threshold=7.20); offset=2 for the next page\n"
            ),
            "{first}"
        );
        let rest = report(&p, 1024, 7.2, 2, 2);
        assert!(
            rest.starts_with("# showing 1 of 3 high-entropy regions"),
            "{rest}"
        );
        assert!(rest.contains("\n0x1000 "), "{rest}");
    }

    /// A 256-byte window of random bytes reads about 7.28 bits, and the
    /// ceiling climbs toward 8 with the window.
    #[test]
    fn small_windows_cannot_reach_eight_bits() {
        assert!((ceiling(256) - 7.28).abs() < 0.01, "{}", ceiling(256));
        assert!((ceiling(1024) - 7.82).abs() < 0.01, "{}", ceiling(1024));
        assert!((ceiling(4096) - 7.955).abs() < 0.01, "{}", ceiling(4096));
        assert!(ceiling(1 << 20) > 7.99);
    }

    /// Base64 of either alphabet and hex of either case decode across line
    /// breaks, and padding ends the bytes.
    #[test]
    fn encoded_text_decodes() {
        let decoded = |text: &[u8], e: Encoding| {
            let mut out = Vec::new();
            decode(text, e, |b| out.push(b));
            out
        };
        assert_eq!(decoded(b"QklF\r\nMQ", Encoding::Base64), b"BIE1");
        assert_eq!(decoded(b"TWFu", Encoding::Base64), b"Man");
        assert_eq!(decoded(b"-_8", Encoding::Base64), [0xfb, 0xff]);
        assert_eq!(decoded(b"+/8", Encoding::Base64), [0xfb, 0xff]);
        assert_eq!(decoded(b"4D5a\n90", Encoding::Hex), [0x4d, 0x5a, 0x90]);
    }

    /// Encoded text is found wherever it sits against the scan's words.
    ///
    /// The line breaks before and after it are left out, its padding is
    /// kept, and a run reaching the file's last byte counts.
    #[test]
    fn encoded_text_is_found_at_every_alignment() {
        for b64 in [base64(&noise(300)), base64(&noise(301))] {
            for shift in 0..16 {
                for tail in [&b""[..], b"\r\n", b"\r\n\0\0\0"] {
                    let mut bytes = vec![0u8; shift];
                    bytes.extend_from_slice(b"\n\r");
                    let at = from_usize(bytes.len());
                    bytes.extend_from_slice(&b64);
                    bytes.extend_from_slice(tail);
                    let p = Program::raw(bytes, Arch::Unknown, 0, None, Vec::new());
                    let found: Vec<(u64, u64, Option<Encoding>)> =
                        high_entropy_regions(&p, 1024, 7.2)
                            .iter()
                            .map(|r| (r.off, r.len, r.encoding))
                            .collect();
                    let want = (at, from_usize(b64.len()), Some(Encoding::Base64));
                    assert_eq!(found, [want], "shift {shift}, tail {tail:?}");
                }
            }
        }
    }

    /// Random bytes stored as base64 or hex text read about 6 and 4 bits per
    /// byte, under any byte threshold; decoded, they are found and tagged.
    /// Base64 of English prose decodes to text and is not reported.
    #[test]
    fn encoded_random_bytes_are_found_and_prose_is_not() {
        let random = noise(4000);
        let gap = [0u8; 0x100];
        let mut bytes = gap.to_vec();
        let b64_at = bytes.len();
        let b64 = base64(&random[..3001]);
        bytes.extend_from_slice(&b64);
        bytes.extend_from_slice(&gap);
        bytes.extend_from_slice(&base64(PROSE.repeat(3).as_bytes()));
        bytes.extend_from_slice(&gap);
        let hex_at = bytes.len();
        let hex: String = random[3001..].iter().map(|b| format!("{b:02x}")).collect();
        bytes.extend_from_slice(hex.as_bytes());
        bytes.extend_from_slice(&gap);
        let p = Program::raw(bytes, Arch::Unknown, 0, None, Vec::new());
        let regions = high_entropy_regions(&p, 1024, 7.2);
        let found: Vec<_> = regions.iter().map(|r| (r.off, r.len, r.encoding)).collect();
        assert_eq!(
            found,
            [
                (
                    from_usize(b64_at),
                    from_usize(b64.len()),
                    Some(Encoding::Base64)
                ),
                (
                    from_usize(hex_at),
                    from_usize(hex.len()),
                    Some(Encoding::Hex)
                ),
            ],
            "{regions:?}"
        );
        assert!(b64.ends_with(b"=="), "the padding is part of the run");
        assert!(regions.iter().all(|r| r.entropy > 7.5), "{regions:?}");
        let table = regions_tsv(&p, &regions);
        assert!(
            table.lines().nth(1).is_some_and(|l| l.ends_with(" base64")),
            "{table}"
        );
    }
}
