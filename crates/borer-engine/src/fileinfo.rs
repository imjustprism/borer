//! Facts about a file an analyst reads before its code.
//!
//! They are the hashes to look it up by, what the bytes appended past its last section are, the
//! language or packager that built it, and where an address sits in it: which region of the file a
//! byte lies in ([`region`]) says what a fact read from it is worth.

use std::fmt::Write as _;

use crate::analysis::{hex_prefixed, parse_addr};
use crate::hashing::{imphash, md5, paired, sha256, tlsh};
use crate::program::Program;
use crate::text::hex;

/// Largest file [`hashes_line`] hashes: a summary of a bigger one stays
/// quick, and `borer://hashes` hashes it on request.
pub(crate) const HASH_FILE_MAX: usize = 64 << 20;

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

/// The runs of bytes appended past everything a file's headers place
/// ([`crate::headers::Headers::overlay`]), each with its entropy and what it
/// is.
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

/// Where a byte of a file sits, the most trusted first: what a mark there
/// proves depends on whether the program loads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Region {
    /// A section that holds code.
    Code,
    /// Loaded data an instruction or a stored pointer the analysis found
    /// references.
    Referenced,
    /// Loaded data no reference the analysis found reaches, or loaded data
    /// read with no analysis to ask.
    Loaded,
    /// Bytes the headers place that the loader leaves unmapped: the
    /// headers themselves, a gap between sections, a section such as
    /// `.comment` or a symbol or debug table.
    Unmapped,
    /// Bytes past everything the headers place
    /// ([`crate::headers::Headers::overlay`]): appended data, which nothing
    /// loads and no instruction reaches.
    Appended,
}

impl Region {
    /// Returns the word a listing prints for the region: `unreferenced`
    /// for loaded data, which a listing names only when it asked an
    /// analysis.
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::Referenced => "referenced",
            Self::Loaded => "unreferenced",
            Self::Unmapped => "unmapped",
            Self::Appended => "appended",
        }
    }
}

/// Returns where the bytes at a file offset sit.
///
/// Loaded data is [`Region::Referenced`] when an analysis is given and one
/// of its references lands anywhere in the run.
///
/// # Arguments
///
/// * `program` - The loaded file.
/// * `analysis` - Its references, when it was analyzed.
/// * `off` - The run's file offset.
/// * `len` - The run's length in bytes.
#[must_use]
pub fn region(
    program: &Program,
    analysis: Option<&crate::analysis::Analysis>,
    off: u64,
    len: u64,
) -> Region {
    if program
        .headers
        .overlay
        .iter()
        .any(|&(at, len)| off.checked_sub(at).is_some_and(|d| d < len))
    {
        return Region::Appended;
    }
    let Some(va) = program.offset_to_va(off) else {
        return Region::Unmapped;
    };
    let end = va.saturating_add(len.max(1));
    match program.section_at(va) {
        Some(s) if s.executable => Region::Code,
        Some(s) if s.readable => {
            if analysis.is_some_and(|a| a.xrefs.range(va..end).next().is_some()) {
                Region::Referenced
            } else {
                Region::Loaded
            }
        }
        _ => Region::Unmapped,
    }
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

/// The lines a file summary ends with.
///
/// Its headers ([`crate::headers::Headers::render`]), what built and wraps
/// it ([`crate::toolchain::lines`]), what each appended run is
/// ([`appended_lines`]) and the hashes ([`hashes_line`]).
///
/// # Arguments
///
/// * `program` - The loaded file.
#[must_use]
pub fn summary_lines(program: &Program) -> String {
    let mut out = program.headers.render(&program.bytes);
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

/// A place as typed: an address in one of the forms `borer://addr` and a
/// find read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Place {
    /// `0x`-prefixed hex: a virtual address.
    Va(u64),
    /// A bare number as [`parse_addr`] reads it: decimal digits, or hex
    /// holding a hex letter. Where names are read too, a name that spells
    /// it wins ([`crate::analysis::resolve`]).
    Number(u64),
    /// `rva:<n>`: relative to the image base.
    Rva(u64),
    /// `off:<n>`: a file offset.
    Off(u64),
}

impl Place {
    /// Returns the place `text` spells.
    ///
    /// # Arguments
    ///
    /// * `text` - `0x`-hex, a bare number, `rva:<n>` or `off:<n>`, the
    ///   number after a prefix in any form [`parse_addr`] reads.
    ///
    /// # Returns
    ///
    /// The place, or `None` when `text` is no number in any of those forms.
    #[must_use]
    pub fn parse(text: &str) -> Option<Place> {
        if let Some(rva) = text.strip_prefix("rva:") {
            return parse_addr(rva).map(Place::Rva);
        }
        if let Some(off) = text.strip_prefix("off:") {
            return parse_addr(off).map(Place::Off);
        }
        let n = parse_addr(text)?;
        Some(if hex_prefixed(text) {
            Place::Va(n)
        } else {
            Place::Number(n)
        })
    }
}

/// Where a virtual address, a relative address or a file offset sits: all
/// three forms, the section, and the function holding it.
///
/// # Arguments
///
/// * `program` - The loaded file.
/// * `analysis` - Its functions, when analyzed.
/// * `overlay` - User names.
/// * `what` - A virtual address, `rva:<n>` for one relative to the image
///   base, `off:<n>` for a file offset, each number in any form
///   [`parse_addr`] reads ([`Place::parse`]).
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
    let cannot = || format!("cannot read {what}: give a virtual address, rva:<n> or off:<n>");
    let va = match Place::parse(what) {
        Some(Place::Va(va) | Place::Number(va)) => Some(va),
        Some(Place::Rva(rva)) => program.image_base.checked_add(rva),
        Some(Place::Off(off)) => Some(
            program
                .offset_to_va(off)
                .ok_or_else(|| format!("file offset {off:#x} is in no mapped section"))?,
        ),
        None => {
            return Err(
                match (what.strip_prefix("rva:"), what.strip_prefix("off:")) {
                    (Some(rva), _) => format!("bad rva {rva}"),
                    (None, Some(off)) => format!("bad file offset {off}"),
                    (None, None) => cannot(),
                },
            );
        }
    }
    .ok_or_else(cannot)?;
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
        program.va_to_offset(va).map_or_else(
            || "- (in no file bytes: uninitialized or unmapped)".to_owned(),
            |o| format!("{o:#x}")
        )
    );
    let _ = writeln!(
        out,
        "section:  {}",
        program.declared_at(va).map_or("-", |s| s.name.as_str())
    );
    if let Some(a) = analysis
        && let Some(f) = a.function_at(va)
    {
        let _ = writeln!(
            out,
            "function: {}{} (entry {:#x})",
            crate::analysis::name_of(a, overlay, f.entry),
            f.offset_of(va),
            f.entry
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

    /// An address in a section the file holds no bytes for names that
    /// section, with no file offset.
    ///
    /// # Panics
    ///
    /// When the section line says none.
    #[test]
    fn an_address_without_file_bytes_names_its_section() {
        let mut bss = Section::mapped(".bss", 0x2000, 0, 0x100, true, false);
        bss.file_size = 0;
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, None, vec![bss]);
        let at = locate(&p, None, &Overlay::default(), "0x2010").expect("a va");
        assert!(at.contains("section:  .bss\n"), "{at}");
        assert!(at.contains("offset:   - (in no file bytes"), "{at}");
    }

    /// A number with a hex letter and no `0x` reads as hex in every form,
    /// as an address argument reads it, and the refusals say which form
    /// did not read.
    ///
    /// # Panics
    ///
    /// When a form reads otherwise.
    #[test]
    fn bare_hex_reads_in_every_form() {
        let text = Section::mapped(".text", 0x1000, 0x400, 0x1000, false, true);
        let p = Program::raw(
            vec![0xc3; 0x1400],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text],
        );
        let o = Overlay::default();
        let by_va = locate(&p, None, &o, "0x1a00").expect("a va");
        assert_eq!(locate(&p, None, &o, "1a00").expect("bare hex"), by_va);
        assert_eq!(locate(&p, None, &o, "rva:1a00").expect("an rva"), by_va);
        assert_eq!(locate(&p, None, &o, "off:10a00").ok(), None);
        assert_eq!(locate(&p, None, &o, "off:e00").expect("an offset"), by_va);
        assert_eq!(locate(&p, None, &o, "rva:zz"), Err("bad rva zz".to_owned()));
        assert_eq!(
            locate(&p, None, &o, "off:zz"),
            Err("bad file offset zz".to_owned())
        );
    }
}
