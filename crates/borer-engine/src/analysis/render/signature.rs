//! Byte signatures and YARA rules: patterns that find the same code again in
//! another build or another sample.
//!
//! A signature is a function's leading bytes with every byte that moves
//! between builds wildcarded, the displacement of a RIP-relative operand,
//! an absolute address, a branch's offset, grown one instruction at a time
//! until the pattern matches the image exactly once. A YARA rule carries the
//! signatures of chosen functions and the strings they reference, with a
//! condition on the file's magic.

use super::summary::referenced_literal;
use super::{Analysis, Overlay, name_of};
use crate::isa::x86::{Decoder, DecoderOptions, FlowControl};
use crate::program::{Arch, BinaryFormat, Program};
use crate::search;
use std::fmt::Write as _;

/// Longest signature tried, in bytes.
const SIGNATURE_MAX: usize = 96;

/// Fixed bytes a signature holds at least before it is tested, so a short
/// common prologue is not reported as unique by chance.
const FIXED_MIN: usize = 6;

/// A function's byte signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// The bytes, `None` where a byte moves between builds.
    pub pattern: Vec<Option<u8>>,
    /// How many places in the image it matches.
    pub matches: usize,
}

impl Signature {
    /// The pattern as `search` and most tools write it: `48 8B ?? ??`.
    #[must_use]
    pub fn spaced(&self) -> String {
        self.pattern
            .iter()
            .map(|b| b.map_or_else(|| "??".to_owned(), |b| format!("{b:02X}")))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The pattern as a C string and mask, as code-scanning libraries take
    /// it: `\x48\x8B\x00` and `xx?`.
    #[must_use]
    pub fn code_and_mask(&self) -> (String, String) {
        let mut code = String::new();
        let mut mask = String::new();
        for b in &self.pattern {
            let _ = write!(code, "\\x{:02X}", b.unwrap_or(0));
            mask.push(if b.is_some() { 'x' } else { '?' });
        }
        (code, mask)
    }
}

/// Whether a value is an address inside the image, so the bytes that hold
/// it move when the image is rebuilt or rebased.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `value` - The operand's value.
fn in_image(p: &Program, value: u64) -> bool {
    p.section_at(value).is_some()
}

/// Builds the shortest byte signature for code at an address that matches
/// the image once.
///
/// It reads no further than `end`: a function's signature is its own
/// bytes, never the code that happens to follow it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - Where the code starts: a function's entry or any instruction.
/// * `end` - Where the code stops: the function's end, or `None` to read
///   up to the longest signature tried.
///
/// # Errors
///
/// When the image is not x86 or x86-64 code, or nothing is mapped at `va`.
pub fn signature(p: &Program, va: u64, end: Option<u64>) -> Result<Signature, String> {
    let bitness = match p.arch {
        Arch::X86_64 => 64,
        Arch::X86 => 32,
        other => {
            return Err(format!(
                "byte signatures read x86 and x86-64 code; this image is {}",
                other.name()
            ));
        }
    };
    let room = end.map_or(SIGNATURE_MAX, |e| {
        crate::num::saturating_usize(e.saturating_sub(va)).min(SIGNATURE_MAX)
    });
    let bytes = p
        .read_va_upto(va, room)
        .filter(|b| !b.is_empty())
        .ok_or_else(|| format!("nothing is mapped at {va:#x}"))?;
    let mut decoder = Decoder::with_ip(bitness, bytes, va, DecoderOptions::NONE);
    let mut pattern: Vec<Option<u8>> = Vec::new();
    let mut best = Signature {
        pattern: Vec::new(),
        matches: 0,
    };
    while decoder.can_decode() {
        let instr = decoder.decode();
        if instr.is_invalid() {
            break;
        }
        let offsets = decoder.get_constant_offsets(&instr);
        let start = crate::num::saturating_usize(instr.ip() - va);
        let mut moving = vec![false; instr.len()];
        let mut mark = |at: usize, size: usize| {
            for m in moving.iter_mut().skip(at).take(size) {
                *m = true;
            }
        };
        if offsets.has_displacement()
            && (instr.is_ip_rel_memory_operand()
                || (offsets.displacement_size() >= 4 && in_image(p, instr.memory_displacement64())))
        {
            mark(offsets.displacement_offset(), offsets.displacement_size());
        }
        let branch = matches!(
            instr.flow_control(),
            FlowControl::Call | FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch
        ) && instr.near_branch_target() != 0;
        let address = crate::analysis::sigs::immediate_operand(&instr)
            .is_some_and(|op| offsets.immediate_size() >= 4 && in_image(p, instr.immediate(op)));
        if offsets.has_immediate() && (branch || address) {
            mark(offsets.immediate_offset(), offsets.immediate_size());
        }
        let code = bytes.get(start..start + instr.len()).unwrap_or_default();
        pattern.extend(
            code.iter()
                .zip(&moving)
                .map(|(&b, &m)| if m { None } else { Some(b) }),
        );
        if pattern.iter().flatten().count() < FIXED_MIN {
            continue;
        }
        let mut trimmed = pattern.clone();
        while trimmed.last().is_some_and(Option::is_none) {
            trimmed.pop();
        }
        let matches = search::find_bytes(p, &trimmed, 0).total;
        best = Signature {
            pattern: trimmed,
            matches,
        };
        if matches <= 1 {
            break;
        }
    }
    if best.pattern.is_empty() {
        while pattern.last().is_some_and(Option::is_none) {
            pattern.pop();
        }
        if pattern.is_empty() {
            return Err(format!("no instruction decodes at {va:#x}"));
        }
        let matches = search::find_bytes(p, &pattern, 0).total;
        return Ok(Signature { pattern, matches });
    }
    Ok(best)
}

/// Renders a function's signature in the forms tools take, and whether it
/// is unique.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results, for the name.
/// * `o` - User names.
/// * `va` - The function's entry, or any code address.
///
/// # Errors
///
/// As [`signature`].
pub fn signature_tsv(p: &Program, a: &Analysis, o: &Overlay, va: u64) -> Result<String, String> {
    let end = a.function_at(va).map(|f| f.end);
    let sig = signature(p, va, end)?;
    let (code, mask) = sig.code_and_mask();
    let named = a.function_at(va).map_or_else(
        || format!("{va:#x}"),
        |f| {
            if f.entry == va {
                name_of(a, o, f.entry)
            } else {
                format!("{}+{:#x}", name_of(a, o, f.entry), va - f.entry)
            }
        },
    );
    let verdict = match sig.matches {
        1 => "unique in the image".to_owned(),
        0 => "matches nothing: the bytes were read past mapped code".to_owned(),
        n => format!(
            "still matches {n} places at the end of the code read: the function's body is duplicated; sign a caller instead"
        ),
    };
    Ok(format!(
        "# signature of {named} at {va:#x}: {} bytes, {} wildcarded, {verdict}\npattern  {}\ncode     {code}\nmask     {mask}\n# search with: borer search <binary> \"{}\"\n",
        sig.pattern.len(),
        sig.pattern.iter().filter(|b| b.is_none()).count(),
        sig.spaced(),
        sig.spaced()
    ))
}

/// A string's text as a YARA text string: quoted, with `\\`, `"` and
/// bytes outside printable ASCII escaped.
///
/// # Arguments
///
/// * `text` - The string as stored.
fn yara_quoted(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            ' '..='~' => out.push(c),
            c => {
                let mut buf = [0u8; 4];
                for b in c.encode_utf8(&mut buf).bytes() {
                    let _ = write!(out, "\\x{b:02x}");
                }
            }
        }
    }
    out.push('"');
    out
}

/// The string a function references at an address, as YARA writes it,
/// read from the image's bytes rather than a rendered literal.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results.
/// * `target` - The address the function refers to.
///
/// # Returns
///
/// The quoted text and whether it is UTF-16, or `None` when no string of
/// four characters or more is there.
fn yara_string(p: &Program, a: &Analysis, target: u64) -> Option<(String, bool)> {
    /// Longest string a rule matches whole; a longer one is matched by
    /// this much of its start.
    const CAP: usize = 120;
    let (start, lit) = referenced_literal(p, a, target, CAP)?;
    let wide = lit.starts_with('L');
    let (len, text) = if wide {
        crate::strings::wstr_at(p, start, 4, CAP)?
    } else {
        crate::strings::cstr_at(p, start, 4, CAP)?
    };
    let shown = if len > CAP {
        text.strip_suffix("...").unwrap_or(&text)
    } else {
        &text
    };
    (shown.chars().count() >= 4).then(|| (yara_quoted(shown), wide))
}

/// The YARA condition a file of this format meets by its first bytes.
///
/// That is a PE's `MZ`, an ELF's magic, a thin Mach-O's 32- or 64-bit magic
/// or a universal one's `CAFEBABE` (read big-endian, as the header stores
/// it).
///
/// # Arguments
///
/// * `format` - The file's format.
fn yara_magic(format: BinaryFormat) -> &'static str {
    match format {
        BinaryFormat::Pe => "uint16(0) == 0x5A4D",
        BinaryFormat::Elf => "uint32(0) == 0x464C457F",
        BinaryFormat::MachO => {
            "(uint32(0) == 0xFEEDFACF or uint32(0) == 0xFEEDFACE or uint32be(0) == 0xCAFEBABE)"
        }
        _ => "true",
    }
}

/// A YARA identifier from a file name: `borer_` and its letters, digits
/// and underscores, so no name is a keyword (`rule`, `global`) or starts
/// with a digit.
///
/// # Arguments
///
/// * `stem` - The file's name without its extension.
fn rule_name(stem: &str) -> String {
    let body: String = stem
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    format!("borer_{body}")
}

/// Writes a YARA rule that finds the given functions again: each one's
/// byte signature and the strings it references, under a condition on the
/// file's magic.
///
/// The condition asks for every signature, or, when the code moved, half
/// the strings, so a recompile that shifts the code still matches on what
/// the code says.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results.
/// * `o` - User names.
/// * `entries` - The functions the rule describes.
///
/// # Errors
///
/// When no entry is a function, or none yields a signature or a string.
pub fn yara_rule(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entries: &[u64],
) -> Result<String, String> {
    /// Strings the rule carries at most.
    const STRINGS_MAX: usize = 12;
    let mut sigs: Vec<(String, String)> = Vec::new();
    let mut texts: Vec<(String, bool)> = Vec::new();
    let mut notes: Vec<String> = Vec::new();
    for &entry in entries {
        let f = a
            .function_at(entry)
            .ok_or_else(|| format!("no function at {entry:#x}"))?;
        let name = name_of(a, o, f.entry);
        match signature(p, f.entry, Some(f.end)) {
            Ok(s) if s.matches == 1 => sigs.push((name.clone(), s.spaced())),
            Ok(s) => notes.push(format!(
                "{name}: its signature matches {} places, left out",
                s.matches
            )),
            Err(why) => notes.push(format!("{name}: {why}")),
        }
        for (target, _) in a.refs_from(f.entry) {
            if let Some(t) = yara_string(p, a, target)
                && !texts.contains(&t)
                && texts.len() < STRINGS_MAX
            {
                texts.push(t);
            }
        }
    }
    if sigs.is_empty() && texts.is_empty() {
        return Err(format!(
            "nothing to match on: {}",
            if notes.is_empty() {
                "the functions reference no strings".to_owned()
            } else {
                notes.join("; ")
            }
        ));
    }
    let stem = p
        .path
        .file_stem()
        .map_or_else(|| "sample".to_owned(), |s| s.to_string_lossy().into_owned());
    let magic = yara_magic(p.format);
    let mut out = String::new();
    for n in &notes {
        let _ = writeln!(out, "// {n}");
    }
    let _ = writeln!(out, "rule {} {{", rule_name(&stem));
    let _ = writeln!(out, "    meta:");
    let described = format!(
        "code and strings of {}",
        entries
            .iter()
            .filter_map(|&e| a.function_at(e).map(|f| name_of(a, o, f.entry)))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let _ = writeln!(out, "        description = {}", yara_quoted(&described));
    let _ = writeln!(out, "        generator = \"borer\"");
    let _ = writeln!(out, "    strings:");
    for (i, (name, pattern)) in sigs.iter().enumerate() {
        let _ = writeln!(out, "        $c{i} = {{ {pattern} }} // {name}");
    }
    for (i, (text, wide)) in texts.iter().enumerate() {
        let _ = writeln!(
            out,
            "        $s{i} = {text}{}",
            if *wide { " wide" } else { " ascii" }
        );
    }
    let code = (!sigs.is_empty()).then_some("all of ($c*)");
    let strs = (!texts.is_empty()).then(|| format!("{} of ($s*)", texts.len().div_ceil(2)));
    let either = match (code, strs) {
        (Some(c), Some(s)) => format!("({c} or {s})"),
        (Some(c), None) => c.to_owned(),
        (None, Some(s)) => s,
        (None, None) => "false".to_owned(),
    };
    let _ = writeln!(out, "    condition:");
    let _ = writeln!(out, "        {magic} and {either}");
    out.push_str("}\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{rule_name, signature, yara_magic, yara_quoted};
    use crate::program::BinaryFormat;

    /// Each format's rule opens on the bytes its files start with, a
    /// universal Mach-O's included.
    ///
    /// # Panics
    ///
    /// When a format's magic is missing.
    #[test]
    fn every_format_is_matched_by_its_magic() {
        assert_eq!(yara_magic(BinaryFormat::Pe), "uint16(0) == 0x5A4D");
        assert!(yara_magic(BinaryFormat::MachO).contains("uint32be(0) == 0xCAFEBABE"));
        assert!(yara_magic(BinaryFormat::MachO).contains("0xFEEDFACF"));
        assert_eq!(yara_magic(BinaryFormat::Raw), "true");
    }
    use crate::program::{Arch, Program, Section};

    /// An absolute address in an immediate operand that is not the first
    /// operand, `mov eax, <address>`, is wildcarded too.
    ///
    /// # Panics
    ///
    /// When the address bytes stay fixed.
    #[test]
    fn an_address_in_a_later_operand_is_wildcarded() {
        let mut code = vec![0xcc_u8; 0x1000];
        code[..10].copy_from_slice(&[0x55, 0x89, 0xe5, 0x53, 0x56, 0x57, 0xb8, 0x00, 0x18, 0x40]);
        code[10..12].copy_from_slice(&[0x00, 0xc3]);
        let text = Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86, 0x40_0000, Some(0x40_1000), vec![text]);
        let sig = signature(&p, 0x40_1000, None).expect("a signature");
        assert!(
            sig.spaced().starts_with("55 89 E5 53 56 57"),
            "{}",
            sig.spaced()
        );
        assert!(!sig.spaced().contains("00 18 40 00"), "{}", sig.spaced());
    }

    /// A function whose whole body is duplicated gets no signature borrowed
    /// from the bytes after it: it reports the places it matches.
    ///
    /// # Panics
    ///
    /// When the signature is called unique.
    #[test]
    fn a_duplicated_body_borrows_no_bytes_past_its_end() {
        let body = [0x55, 0x48, 0x89, 0xe5, 0x31, 0xc0, 0x5d, 0xc3];
        let mut code = vec![0xcc_u8; 0x1000];
        code[..8].copy_from_slice(&body);
        code[8] = 0x90;
        code[0x100..0x108].copy_from_slice(&body);
        code[0x108] = 0x91;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let sig = signature(&p, 0x1000, Some(0x1008)).expect("a signature");
        assert_eq!(sig.matches, 2, "{}", sig.spaced());
        assert_eq!(sig.pattern.len(), 8);
    }

    /// A signature grows past a prefix found twice, wildcarding the
    /// RIP-relative displacement it crosses, and stops once it is unique.
    ///
    /// # Panics
    ///
    /// When the pattern or its match count reads otherwise.
    #[test]
    fn a_signature_wildcards_what_moves_and_stops_when_unique() {
        let prefix = [0x55, 0x48, 0x89, 0xe5, 0x48, 0x8b, 0x05];
        let mut code = vec![0xcc_u8; 0x1000];
        code[..7].copy_from_slice(&prefix);
        code[7..11].copy_from_slice(&[0x10, 0x00, 0x00, 0x00]);
        code[11..16].copy_from_slice(&[0xe8, 0x00, 0x01, 0x00, 0x00]);
        code[16] = 0xc3;
        code[0x800..0x807].copy_from_slice(&prefix);
        code[0x807..0x80b].copy_from_slice(&[0x20, 0x00, 0x00, 0x00]);
        code[0x80b] = 0xc3;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let sig = signature(&p, 0x1000, None).expect("a signature");
        assert_eq!(sig.spaced(), "55 48 89 E5 48 8B 05 ?? ?? ?? ?? E8");
        assert_eq!(sig.matches, 1);
    }

    /// Backslashes, quotes and bytes past ASCII are escaped as YARA reads
    /// them; a Windows path keeps its backslashes as backslashes.
    ///
    /// # Panics
    ///
    /// When the quoting reads otherwise.
    #[test]
    fn text_is_quoted_as_yara_reads_it() {
        assert_eq!(
            yara_quoted("shell\\notepad\\np.cpp"),
            "\"shell\\\\notepad\\\\np.cpp\""
        );
        assert_eq!(
            yara_quoted("say \"hi\"\u{e9}"),
            "\"say \\\"hi\\\"\\xc3\\xa9\""
        );
    }

    /// Rule names are identifiers.
    ///
    /// # Panics
    ///
    /// When one is not.
    #[test]
    fn rule_names_are_identifiers() {
        assert_eq!(rule_name("notepad"), "borer_notepad");
        assert_eq!(rule_name("rule"), "borer_rule");
        assert_eq!(rule_name("7z-setup.x64"), "borer_7z_setup_x64");
    }
}
