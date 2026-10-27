//! Facts about a file an analyst reads before its code.
//!
//! They are the hashes to look it up by, what the bytes appended past its last section are, the
//! language or packager that built it, and where an address sits in it.

use std::fmt::Write as _;

use crate::hashing::{imphash, md5, paired, sha256, tlsh};
use crate::program::Program;
use crate::text::hex;

/// Largest file [`hashes_line`] hashes: a summary of a bigger one stays
/// quick, and `borer://hashes` hashes it on request.
const HASH_FILE_MAX: usize = 64 << 20;

/// The `hashes:` line of a file summary: MD5 and SHA-256 of the whole file,
/// the import hash, and TLSH, the values a malware feed is searched by.
///
/// # Arguments
///
/// * `program` - The loaded file.
#[must_use]
pub fn hashes_line(program: &Program) -> String {
    if program.bytes.len() > HASH_FILE_MAX {
        return format!(
            "hashes:  not computed for a file over {} MB here; borer://hashes and `borer hashes` compute them",
            HASH_FILE_MAX >> 20
        );
    }
    let bytes = &program.bytes;
    let ((md5_sum, sha_sum), tlsh_sum) = paired(
        bytes.len(),
        || paired(bytes.len(), || md5(bytes), || sha256(bytes)),
        || tlsh(bytes),
    );
    let mut out = format!("hashes:  md5 {}  sha256 {}", hex(&md5_sum), hex(&sha_sum));
    if let Some(imp) = imphash(program) {
        let _ = write!(out, "  imphash {}", hex(&imp));
    }
    if let Some(t) = tlsh_sum {
        let _ = write!(out, "  tlsh {}", t.hex());
    }
    out
}

/// Bytes a file carries past the end of the last section its header maps,
/// where installers keep their payload and droppers their second stage.
#[derive(Debug, Clone, PartialEq)]
pub struct Appended {
    /// The file offset they start at.
    pub offset: u64,
    /// How many bytes.
    pub len: u64,
    /// Their Shannon entropy, bits per byte.
    pub entropy: f64,
    /// What they are, when a known signature starts them or a known
    /// installer's mark sits in their first few kilobytes.
    pub kind: Option<&'static str>,
}

/// The installers and bundlers that append their payload, by a mark the
/// appended bytes carry in their first few kilobytes, each back to front
/// ([`reversed`]).
const APPENDED_MARKS: [(&[u8], &str); 9] = [
    (&reversed(b"Nullsoft"), "NSIS installer data"),
    (&reversed(b"Inno Setup"), "Inno Setup installer data"),
    (&reversed(b"zlb\x1a"), "Inno Setup installer data"),
    (&reversed(b"idska32\x1a"), "Inno Setup installer data"),
    (&reversed(b"MEI\x0c\x0b\x0a\x0b\x0e"), "PyInstaller archive"),
    (&reversed(b"AU3!EA06"), "compiled AutoIt script"),
    (&reversed(b"MSCF"), "cabinet archive"),
    (&reversed(b"Rar!\x1a\x07"), "RAR archive"),
    (&reversed(b"7z\xbc\xaf\x27\x1c"), "7-Zip archive"),
];

/// Where `needle` first occurs in `hay`.
///
/// # Arguments
///
/// * `hay` - The bytes searched.
/// * `needle` - The bytes looked for.
///
/// # Returns
///
/// The offset of the first occurrence; `None` when there is none or the
/// needle is empty.
pub(crate) fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    let (&first, rest) = needle.split_first()?;
    let mut from = 0;
    while let Some(i) = hay.get(from..)?.iter().position(|&b| b == first) {
        let at = from + i;
        if hay.get(at + 1..)?.starts_with(rest) {
            return Some(at);
        }
        from = at + 1;
    }
    None
}

/// The runs of bytes appended past a PE file's last section, outside the
/// certificate table ([`crate::headers::Headers::overlay`]), each with its
/// entropy and what it is.
///
/// # Arguments
///
/// * `program` - The loaded file.
///
/// # Returns
///
/// The runs in file order; empty for a file with none.
#[must_use]
pub fn appended(program: &Program) -> Vec<Appended> {
    program
        .headers
        .overlay
        .iter()
        .filter_map(|&(offset, len)| {
            let start = crate::num::saturating_usize(offset);
            let bytes = program
                .bytes
                .get(start..start.saturating_add(crate::num::saturating_usize(len)))?;
            let head = bytes.get(..bytes.len().min(0x2000)).unwrap_or(bytes);
            let kind = crate::headers::sniff_file(bytes).or_else(|| {
                APPENDED_MARKS
                    .iter()
                    .find(|(mark, _)| has_mark(head, mark))
                    .map(|(_, what)| *what)
            });
            Some(Appended {
                offset,
                len,
                entropy: crate::entropy::shannon(bytes),
                kind,
            })
        })
        .collect()
}

/// The `overlay:` lines of a file summary, one per appended run: what it
/// is and its entropy, beside the `notes:` entry giving where it sits.
///
/// # Arguments
///
/// * `program` - The loaded file.
#[must_use]
pub fn appended_lines(program: &Program) -> Vec<String> {
    appended(program)
        .iter()
        .map(|a| {
            format!(
                "overlay: {} at {:#x} ({:#x} bytes), entropy {:.2}",
                a.kind
                    .unwrap_or("no known signature: data, a payload or padding"),
                a.offset,
                a.len,
                a.entropy
            )
        })
        .collect()
}

/// A mark stored back to front: borer's own binary then carries only the
/// reversed bytes, so a scan of borer, or of another tool built with it,
/// does not find every toolchain in its own tables.
///
/// # Arguments
///
/// * `mark` - The bytes as they appear in a file.
pub(crate) const fn reversed<const N: usize>(mark: &[u8; N]) -> [u8; N] {
    let mut out = [0u8; N];
    let mut i = 0;
    while i < N {
        out[i] = mark[N - 1 - i];
        i += 1;
    }
    out
}

/// Whether a reversed mark ([`reversed`]) occurs in `hay`.
///
/// # Arguments
///
/// * `hay` - The bytes searched.
/// * `mark` - The mark, back to front.
fn has_mark(hay: &[u8], mark: &[u8]) -> bool {
    find(hay, &forward(mark)).is_some()
}

/// A reversed mark ([`reversed`]) turned back the way a file spells it.
///
/// # Arguments
///
/// * `mark` - The mark, back to front.
pub(crate) fn forward(mark: &[u8]) -> Vec<u8> {
    mark.iter().rev().copied().collect()
}

/// The lines a file summary adds after its headers: what built and wraps
/// it ([`crate::toolchain::lines`]), what each appended run is
/// ([`appended_lines`]) and the hashes ([`hashes_line`]).
///
/// # Arguments
///
/// * `program` - The loaded file.
#[must_use]
pub fn summary_lines(program: &Program) -> String {
    let mut out = String::new();
    for line in crate::toolchain::lines(program, false)
        .into_iter()
        .chain(appended_lines(program))
        .chain([hashes_line(program)])
    {
        out.push_str(&line);
        out.push('\n');
    }
    out
}

/// The `#` lines a triage gives about the file before its code: the
/// debug information applied, what built and wraps it
/// ([`crate::toolchain::lines`]) and what each appended run is.
///
/// # Arguments
///
/// * `program` - The loaded file.
#[must_use]
pub fn triage_lines(program: &Program) -> String {
    let mut out = String::new();
    if !program.debug_functions.is_empty() {
        let _ = writeln!(
            out,
            "# debug info: {} functions named by the compiler",
            program.debug_functions.len()
        );
    }
    if let Some(outcome) = &program.pdb {
        let _ = writeln!(out, "# pdb: {}", outcome.render());
    }
    for built in crate::toolchain::lines(program, true) {
        let _ = writeln!(out, "# {built}");
    }
    for overlay in appended_lines(program) {
        let _ = writeln!(out, "# {overlay}");
    }
    out
}

/// Where a virtual address, a relative address or a file offset sits: all
/// three forms, the section, and the function holding it.
///
/// # Arguments
///
/// * `program` - The loaded file.
/// * `analysis` - Its functions, when analyzed.
/// * `overlay` - User names.
/// * `what` - `0x...` or a decimal number for a virtual address, `rva:<n>`
///   for one relative to the image base, `off:<n>` for a file offset.
///
/// # Errors
///
/// When the text is not a number in one of those forms, or nothing maps it.
pub fn locate(
    program: &Program,
    analysis: Option<&crate::analysis::Analysis>,
    overlay: &crate::analysis::Overlay,
    what: &str,
) -> Result<String, String> {
    let number = |t: &str| {
        let t = t.trim();
        t.strip_prefix("0x")
            .or_else(|| t.strip_prefix("0X"))
            .map_or_else(
                || t.parse::<u64>().ok(),
                |h| u64::from_str_radix(h, 16).ok(),
            )
    };
    let va = if let Some(rva) = what.strip_prefix("rva:") {
        program
            .image_base
            .checked_add(number(rva).ok_or_else(|| format!("bad rva {rva}"))?)
    } else if let Some(off) = what.strip_prefix("off:") {
        let off = number(off).ok_or_else(|| format!("bad file offset {off}"))?;
        Some(
            program
                .offset_to_va(off)
                .ok_or_else(|| format!("file offset {off:#x} is in no mapped section"))?,
        )
    } else {
        number(what)
    }
    .ok_or_else(|| format!("cannot read {what}: give a virtual address, rva:<n> or off:<n>"))?;
    let mut out = format!("va:       {va:#x}\n");
    let _ = writeln!(
        out,
        "rva:      {}",
        va.checked_sub(program.image_base).map_or_else(
            || "- (below the image base)".to_owned(),
            |r| format!("{r:#x}")
        )
    );
    let _ = writeln!(
        out,
        "offset:   {}",
        program
            .section_at(va)
            .filter(|s| va - s.va.0 < s.file_size)
            .and_then(|_| program.va_to_offset(va))
            .map_or_else(
                || "- (in no file bytes: uninitialized or unmapped)".to_owned(),
                |o| format!("{o:#x}")
            )
    );
    let _ = writeln!(
        out,
        "section:  {}",
        program.section_at(va).map_or("-", |s| s.name.as_str())
    );
    if let Some(a) = analysis
        && let Some(f) = a.function_at(va)
    {
        let _ = writeln!(
            out,
            "function: {} at {:#x} + {:#x}",
            crate::analysis::name_of(a, overlay, f.entry),
            f.entry,
            va - f.entry
        );
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{has_mark, locate, reversed};
    use crate::analysis::Overlay;
    use crate::program::{Arch, Program, Section};

    /// A reversed mark is found forward in a file, and borer's own copy of
    /// it is not the forward bytes.
    ///
    /// # Panics
    ///
    /// When a mark is missed or stored forward.
    #[test]
    fn marks_are_stored_back_to_front_and_found_forward() {
        let mark = reversed(b"abc");
        assert_eq!(&mark, b"cba");
        assert!(has_mark(b"xxabcxx", &mark));
        assert!(!has_mark(b"xxcbaxx", &mark));
    }

    /// A virtual address, a relative one and a file offset name the same
    /// place; one in no file bytes says so.
    ///
    /// # Panics
    ///
    /// When a form reads otherwise.
    #[test]
    fn every_form_of_an_address_names_one_place() {
        let mut text = Section::mapped(".text", 0x1000, 0x400, 0x200, false, true);
        text.vsize = 0x1000;
        let p = Program::raw(vec![0xc3; 0x600], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let o = Overlay::default();
        let tail = locate(&p, None, &o, "0x1300").expect("a va past the file bytes");
        assert!(tail.contains("offset:   - (in no file bytes"), "{tail}");
        assert!(tail.contains("section:  .text"), "{tail}");
        let by_va = locate(&p, None, &o, "0x1010").expect("a va");
        assert!(by_va.contains("offset:   0x410"), "{by_va}");
        assert!(by_va.contains("section:  .text"), "{by_va}");
        assert_eq!(locate(&p, None, &o, "off:0x410").expect("an offset"), by_va);
        assert_eq!(locate(&p, None, &o, "rva:0x1010").expect("an rva"), by_va);
        assert!(locate(&p, None, &o, "off:0x10").is_err());
        assert!(locate(&p, None, &o, "nowhere").is_err());
    }
}
