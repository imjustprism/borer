//! Strings stored encoded: base64 and hexadecimal text whose decoded bytes
//! are text or a known file, the way a program hides a URL, a config or a
//! second stage from a plain strings listing.

use crate::entropy::{Encoding, decode};
use crate::program::Program;
use crate::strings::{Encoding as StrEncoding, find_strings, literal_byte};
use std::fmt::Write as _;

/// Shortest encoded text considered: shorter runs are as often identifiers
/// or hashes as data.
const ENCODED_MIN: usize = 16;

/// Most rows listed.
const ROWS_MAX: usize = 200;

/// Most decoded characters shown per row.
const SHOWN_MAX: usize = 100;

/// Which encoding a string's shape fits, if any.
///
/// # Arguments
///
/// * `s` - The string.
fn shape(s: &str) -> Option<Encoding> {
    if s.len() < ENCODED_MIN {
        return None;
    }
    let hex = s.len().is_multiple_of(2) && s.bytes().all(|b| b.is_ascii_hexdigit());
    if hex {
        return Some(Encoding::Hex);
    }
    let body = s.trim_end_matches('=');
    let whole = if body.len() < s.len() {
        s.len().is_multiple_of(4)
    } else {
        body.len() % 4 != 1
    };
    let base64 = whole
        && s.len() - body.len() <= 2
        && body
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'+' | b'/' | b'-' | b'_'));
    base64.then_some(Encoding::Base64)
}

/// What decoded bytes are, when they are worth showing: text, or a file a
/// signature names.
///
/// # Arguments
///
/// * `bytes` - The decoded bytes.
fn reading(bytes: &[u8]) -> Option<String> {
    if let Some(kind) = crate::headers::sniff_file(bytes) {
        return Some(format!("[{kind}, {} bytes]", bytes.len()));
    }
    /// Fewest different bytes decoded text has: a run of one digit
    /// repeated is padding or a constant, not hidden text.
    const VARIETY_MIN: usize = 6;
    let printable = bytes.iter().filter(|b| literal_byte(**b)).count();
    let distinct = bytes
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    if bytes.len() < 8
        || printable * 100 < bytes.len() * 95
        || distinct < VARIETY_MIN
        || !bytes.iter().any(u8::is_ascii_alphabetic)
    {
        return None;
    }
    let text: String = String::from_utf8_lossy(bytes)
        .chars()
        .map(|c| if c.is_control() { ' ' } else { c })
        .take(SHOWN_MAX)
        .collect();
    Some(format!(
        "\"{text}\"{}",
        if bytes.len() > SHOWN_MAX { "..." } else { "" }
    ))
}

/// One base64 or hexadecimal string of the image whose decoded bytes are
/// text or a known file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodedString {
    /// Address of its first character.
    pub va: u64,
    /// The encoding its shape fits.
    pub encoding: Encoding,
    /// Its length in characters.
    pub len: usize,
    /// What the decoded bytes read as, as a row shows it.
    pub value: String,
    /// The decoded bytes as text, lower-cased: what a filter is matched
    /// against.
    pub folded: String,
}

/// Finds the base64 and hexadecimal strings in the image whose decoded
/// bytes are text or a known file.
///
/// A filter is applied to them afterwards ([`encoded_strings_tsv`]), so
/// the walk over every section is done once whatever the filter.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// The strings in section then address order.
#[must_use]
pub fn encoded_strings(p: &Program) -> Vec<EncodedString> {
    let mut found = Vec::new();
    for s in &p.sections {
        let Some(data) = p.section_bytes(s) else {
            continue;
        };
        for hit in find_strings(data, ENCODED_MIN) {
            if hit.encoding != StrEncoding::Ascii {
                continue;
            }
            let start = crate::num::saturating_usize(hit.off);
            let Some(text) = data
                .get(start..start.saturating_add(hit.len))
                .and_then(|raw| std::str::from_utf8(raw).ok())
            else {
                continue;
            };
            let Some(encoding) = shape(text) else {
                continue;
            };
            let mut bytes = Vec::with_capacity(text.len());
            decode(text.as_bytes(), encoding, |b| bytes.push(b));
            let Some(value) = reading(&bytes) else {
                continue;
            };
            found.push(EncodedString {
                va: s.va.0 + hit.off,
                encoding,
                len: hit.len,
                value,
                folded: String::from_utf8_lossy(&bytes).to_lowercase(),
            });
        }
    }
    found
}

/// Lists the encoded strings a filter keeps.
///
/// # Arguments
///
/// * `found` - The image's encoded strings ([`encoded_strings`]).
/// * `filter` - Text the decoded value must contain, ignoring case; empty
///   keeps every row.
///
/// # Returns
///
/// A header counting the strings kept, then at most [`ROWS_MAX`] rows.
#[must_use]
pub fn encoded_strings_tsv(found: &[EncodedString], filter: &str) -> String {
    let want = filter.to_lowercase();
    let mut rows: Vec<String> = Vec::new();
    let mut total = 0usize;
    for e in found
        .iter()
        .filter(|e| want.is_empty() || e.folded.contains(&want))
    {
        total += 1;
        if rows.len() < ROWS_MAX {
            rows.push(format!(
                "{:<#14x} {:<8} {:<6} {}",
                e.va,
                e.encoding.name(),
                e.len,
                e.value
            ));
        }
    }
    let mut out = format!(
        "# {total} encoded string{} decode to text or a known file{}\n# va             encoding length decoded\n",
        if total == 1 { "" } else { "s" },
        if total > rows.len() {
            format!(" (showing {})", rows.len())
        } else {
            String::new()
        }
    );
    for r in rows {
        let _ = writeln!(out, "{r}");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{encoded_strings, encoded_strings_tsv, reading, shape};
    use crate::entropy::Encoding;
    use crate::program::{Arch, Program, Section};

    /// A base64 URL stored in data is listed at its address, decoded.
    ///
    /// # Panics
    ///
    /// When the row is missing or misplaced.
    #[test]
    fn a_stored_base64_url_is_listed_decoded() {
        let mut data = vec![0_u8; 0x100];
        let encoded = b"aHR0cHM6Ly9ib3Jlci5sb2wvZG9jcw==";
        data[0x10..0x10 + encoded.len()].copy_from_slice(encoded);
        let rdata = Section::mapped(".rdata", 0x2000, 0, 0x100, false, false);
        let p = Program::raw(data, Arch::X86_64, 0, None, vec![rdata]);
        let found = encoded_strings(&p);
        let out = encoded_strings_tsv(&found, "");
        assert!(out.starts_with("# 1 encoded string decode"), "{out}");
        assert!(out.contains("0x2010"), "{out}");
        assert!(out.contains("\"https://borer.lol/docs\""), "{out}");
        assert_eq!(
            encoded_strings_tsv(&found, "BORER.lol"),
            out,
            "a filter ignores case"
        );
        assert!(encoded_strings_tsv(&found, "nothing-like-it").starts_with("# 0 "));
    }

    /// Base64 and hex shapes are told apart, and identifiers are neither.
    ///
    /// # Panics
    ///
    /// When a shape reads otherwise.
    #[test]
    fn shapes_are_told_apart() {
        assert_eq!(
            shape("aHR0cHM6Ly9leGFtcGxlLmNvbS8="),
            Some(Encoding::Base64)
        );
        assert_eq!(shape("aHR0cHM6Ly9leGFtcGxlLmNvbS8"), Some(Encoding::Base64));
        assert_eq!(shape("aHR0cHM6Ly9leGFtcGxlLmNvbS8x="), None);
        assert_eq!(shape("68747470733a2f2f6578616d706c65"), Some(Encoding::Hex));
        assert_eq!(shape("QUJDREVGYWJjZGVm"), Some(Encoding::Base64));
        let mut bytes = Vec::new();
        crate::entropy::decode(b"GetProcAddressForCaller", Encoding::Base64, |b| {
            bytes.push(b);
        });
        assert_eq!(reading(&bytes), None, "an identifier decodes to no text");
        assert_eq!(shape("short"), None);
    }

    /// Text and known files read; random bytes do not.
    ///
    /// # Panics
    ///
    /// When one reads otherwise.
    #[test]
    fn only_text_and_known_files_read() {
        assert_eq!(
            reading(b"https://example.com/"),
            Some("\"https://example.com/\"".to_owned())
        );
        assert!(reading(b"PK\x03\x04\x14\x00\x00\x00").is_some_and(|r| r.contains("zip")));
        assert_eq!(
            reading(&[0x91, 0x02, 0xff, 0x13, 0x88, 0x7a, 0x00, 0xc3, 0x44]),
            None
        );
    }
}
