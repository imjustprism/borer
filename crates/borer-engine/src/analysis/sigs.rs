//! Signatures: a function's first bytes with what moves between builds
//! masked, and the pack names that find functions by them.
//!
//! A name a user gave a function is tied to an address, and the address
//! moves when the program is rebuilt. The function's own bytes mostly do
//! not: what changes is the operands that point elsewhere (a call's or a
//! jump's displacement, a RIP-relative or absolute address, an address
//! loaded as a constant). A signature is the function's first bytes with
//! those masked, `48895C2408574883EC20488B05????????`, cut at the length
//! that no other function entry shares. A pack's `[names]` line
//! `fn <signature> <name>` names the one function whose entry matches it,
//! so a mapping made on one build names the next build's functions too,
//! and [`export_pack`] writes a session's names as such a pack.
//!
//! What the program itself says about a function outranks a pack: a pack
//! name goes on a function borer left unnamed or named by its vtable slot
//! only, and where the program names the function (a symbol, a signature
//! string, a handler's message) the two names are kept side by side, which
//! is also how often the byte match agrees with the program's own word.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::isa::x86::{Decoder, DecoderOptions, FlowControl, Instruction, OpKind, Register};

use super::{Analysis, NameSource, Overlay, is_imm, name_of};
use crate::program::Program;

/// Unsigned names an exported pack lists before it only counts the rest.
const UNSIGNED_LISTED: usize = 50;
/// Longest signature, in bytes.
pub const SIG_MAX: usize = 128;
/// Shortest signature, in bytes, however unique fewer would be.
pub const SIG_MIN: usize = 12;

/// One function entry's first bytes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Row {
    /// The first bytes, up to [`SIG_MAX`], fewer at the end of the section.
    bytes: Vec<u8>,
    /// The entry.
    entry: u64,
}

/// Every function entry's first bytes, sorted, for matching signatures.
#[derive(Debug, Default)]
pub struct EntryIndex {
    /// Each entry's row, sorted by the bytes.
    rows: Vec<Row>,
}

impl EntryIndex {
    /// Indexes every function the analysis found.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - The functions.
    #[must_use]
    pub fn build(program: &Program, analysis: &Analysis) -> EntryIndex {
        let mut rows: Vec<Row> = analysis
            .functions
            .iter()
            .filter_map(|f| {
                let bytes = program.read_va_upto(f.entry, SIG_MAX)?;
                Some(Row {
                    bytes: bytes.to_vec(),
                    entry: f.entry,
                })
            })
            .collect();
        rows.sort_unstable();
        EntryIndex { rows }
    }

    /// The rows whose bytes start with the pattern's bytes before its first
    /// wildcard, the only rows it can match.
    ///
    /// # Arguments
    ///
    /// * `pattern` - The signature.
    fn candidates(&self, pattern: &[Option<u8>]) -> &[Row] {
        let fixed: Vec<u8> = pattern.iter().map_while(|b| *b).collect();
        let lo = self
            .rows
            .partition_point(|r| r.bytes.as_slice() < fixed.as_slice());
        let hi = lo
            + self.rows.get(lo..).map_or(0, |rest| {
                rest.partition_point(|r| r.bytes.starts_with(&fixed))
            });
        self.rows.get(lo..hi).unwrap_or(&[])
    }

    /// The entries a signature matches.
    ///
    /// # Arguments
    ///
    /// * `pattern` - The signature.
    #[must_use]
    pub fn matches(&self, pattern: &[Option<u8>]) -> Vec<u64> {
        self.candidates(pattern)
            .iter()
            .filter(|r| agreement(pattern, &r.bytes) == pattern.len())
            .map(|r| r.entry)
            .collect()
    }
}

/// How many of a pattern's leading bytes a byte run agrees with, a
/// wildcard agreeing with anything and a missing byte with nothing.
///
/// # Arguments
///
/// * `pattern` - The signature.
/// * `bytes` - The bytes at an entry.
fn agreement(pattern: &[Option<u8>], bytes: &[u8]) -> usize {
    pattern
        .iter()
        .zip(bytes)
        .take_while(|(p, b)| p.is_none_or(|p| p == **b))
        .count()
}

/// A function's first bytes with what moves between builds masked.
///
/// Up to [`SIG_MAX`] bytes and not past its end, every byte of a branch's
/// or call's 32-bit displacement, of a RIP-relative displacement, and of a
/// displacement or constant that is an address inside the image's
/// sections is a wildcard.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The function's extent.
/// * `entry` - The function's entry.
#[must_use]
pub fn masked_bytes(program: &Program, analysis: &Analysis, entry: u64) -> Option<Vec<Option<u8>>> {
    let bitness = program.arch.bitness()?;
    let f = analysis.function(entry)?;
    let limit = usize::try_from(f.end.saturating_sub(entry))
        .unwrap_or(SIG_MAX)
        .clamp(1, SIG_MAX);
    let bytes = program.read_va_upto(entry, limit)?;
    let start = program.sections.iter().map(|s| s.va.0).min().unwrap_or(0);
    let end = program
        .sections
        .iter()
        .map(|s| s.va.0.saturating_add(s.vsize))
        .max()
        .unwrap_or(0);
    let image = start..end;
    let mut out: Vec<Option<u8>> = bytes.iter().copied().map(Some).collect();
    let mut decoder = Decoder::with_ip(bitness, bytes, entry, DecoderOptions::NONE);
    let mut instr = Instruction::default();
    while decoder.can_decode() {
        let at = usize::try_from(decoder.ip().saturating_sub(entry)).unwrap_or(usize::MAX);
        decoder.decode_out(&mut instr);
        if instr.is_invalid() {
            out.truncate(at);
            break;
        }
        let offsets = decoder.get_constant_offsets(&instr);
        let mut mask = |off: usize, size: usize| {
            for b in out.iter_mut().skip(at + off).take(size) {
                *b = None;
            }
        };
        let branch = matches!(
            instr.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        if offsets.has_immediate() {
            let size = offsets.immediate_size();
            let moves = if branch {
                size >= 4
            } else {
                immediate_operand(&instr).is_some_and(|op| image.contains(&instr.immediate(op)))
            };
            if moves {
                mask(offsets.immediate_offset(), size);
            }
        }
        if offsets.has_displacement() {
            let rip = matches!(instr.memory_base(), Register::RIP | Register::EIP);
            if rip || image.contains(&instr.memory_displacement64()) {
                mask(offsets.displacement_offset(), offsets.displacement_size());
            }
        }
        if matches!(
            instr.flow_control(),
            FlowControl::Return | FlowControl::UnconditionalBranch
        ) && instr.next_ip() >= f.end
        {
            out.truncate(at + instr.len());
            break;
        }
    }
    Some(out)
}

/// The operand index of an instruction's immediate, for reading it.
///
/// # Arguments
///
/// * `instr` - The instruction.
fn immediate_operand(instr: &Instruction) -> Option<u32> {
    (0..instr.op_count()).find(|&i| is_imm(instr.op_kind(i)))
}

/// A function's signature: its masked first bytes cut at the shortest
/// length, at least [`SIG_MIN`], that no other entry in the index matches.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions.
/// * `index` - Every entry's first bytes.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The signature, or `None` when another entry matches every byte of it (a
/// copy of the same code) or the function is too short to tell apart.
#[must_use]
pub fn signature(
    program: &Program,
    analysis: &Analysis,
    index: &EntryIndex,
    entry: u64,
) -> Option<Vec<Option<u8>>> {
    let full = masked_bytes(program, analysis, entry)?;
    let head = full.get(..SIG_MIN.min(full.len())).unwrap_or(&[]);
    let need = index
        .candidates(head)
        .iter()
        .filter(|r| r.entry != entry)
        .map(|r| agreement(&full, &r.bytes) + 1)
        .max()
        .unwrap_or(0)
        .max(SIG_MIN);
    let fixed = full.iter().take(need).filter(|b| b.is_some()).count();
    if fixed < SIG_MIN / 2 {
        return None;
    }
    full.get(..need).map(<[Option<u8>]>::to_vec)
}

/// Writes a signature as hex with `??` for a wildcard: `4889??08`.
///
/// # Arguments
///
/// * `pattern` - The signature.
#[must_use]
pub fn format_signature(pattern: &[Option<u8>]) -> String {
    let mut out = String::with_capacity(pattern.len() * 2);
    for b in pattern {
        match b {
            Some(b) => {
                let _ = write!(out, "{b:02X}");
            }
            None => out.push_str("??"),
        }
    }
    out
}

/// Reads a signature written by [`format_signature`]; spaces between
/// bytes are allowed.
///
/// # Arguments
///
/// * `text` - The signature.
#[must_use]
pub fn parse_signature(text: &str) -> Option<Vec<Option<u8>>> {
    let compact: Vec<u8> = text.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    if compact.is_empty() || !compact.len().is_multiple_of(2) {
        return None;
    }
    compact
        .chunks(2)
        .map(|pair| match pair {
            b"??" => Some(None),
            _ => std::str::from_utf8(pair)
                .ok()
                .and_then(|s| u8::from_str_radix(s, 16).ok())
                .map(Some),
        })
        .collect()
}

/// What a pack's `[names]` lines found in a program.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PackNames {
    /// The entries named, with their names.
    pub named: Vec<(u64, String)>,
    /// Entries a pack name matched that the program names itself: the
    /// entry, the pack's name and the program's.
    pub kept: Vec<(u64, String, String)>,
    /// Names whose signature matched no entry.
    pub missing: Vec<String>,
    /// Names whose signature matched several entries, with how many.
    pub ambiguous: Vec<(String, usize)>,
    /// Lines whose signature does not read.
    pub unreadable: Vec<String>,
}

/// Finds the functions a program's packs name by signature.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions, and the packs.
#[must_use]
pub fn find_pack_names(program: &Program, analysis: &Analysis) -> PackNames {
    let lines = analysis.packs.list("names", "fn");
    let mut out = PackNames::default();
    if lines.is_empty() {
        return out;
    }
    let index = EntryIndex::build(program, analysis);
    for line in lines {
        let Some((sig, name)) = line.split_once(char::is_whitespace) else {
            out.unreadable.push(line.to_owned());
            continue;
        };
        let name = name.trim().to_owned();
        let Some(pattern) = parse_signature(sig) else {
            out.unreadable.push(line.to_owned());
            continue;
        };
        match index.matches(&pattern).as_slice() {
            [] => out.missing.push(name),
            [entry] => out.named.push((*entry, name)),
            many => out.ambiguous.push((name, many.len())),
        }
    }
    out
}

/// Names the functions a program's packs find by signature where borer
/// left them unnamed or named them by vtable slot; a match on a function
/// the program names itself moves to `kept`.
///
/// # Arguments
///
/// * `analysis` - The analysis, named in place.
/// * `found` - What [`find_pack_names`] found, sorted into named and kept.
pub fn apply_pack_names(analysis: &mut Analysis, found: &mut PackNames) {
    found.named = apply_names(
        analysis,
        std::mem::take(&mut found.named),
        NameSource::Pack,
        &mut found.kept,
    );
}

/// Names the functions a pack found where borer left them unnamed or named
/// them by vtable slot; a match on a function the program names itself is
/// set aside.
///
/// # Arguments
///
/// * `analysis` - The analysis, named in place.
/// * `found` - The entries matched, with the names the pack gives them.
/// * `source` - What the names count as.
/// * `kept` - Receives each match on a function the program names itself:
///   the entry, the pack's name and the program's.
///
/// # Returns
///
/// The entries named, with their names.
pub(crate) fn apply_names(
    analysis: &mut Analysis,
    found: Vec<(u64, String)>,
    source: NameSource,
    kept: &mut Vec<(u64, String, String)>,
) -> Vec<(u64, String)> {
    let mut named = Vec::with_capacity(found.len());
    for (entry, name) in found {
        let Some(f) = analysis.function_mut(entry) else {
            continue;
        };
        if matches!(f.name_source, NameSource::None | NameSource::Slot) {
            f.name = Some(name.clone());
            f.name_inferred = false;
            f.name_source = source;
            named.push((entry, name));
        } else {
            let own = f.name.clone().unwrap_or_default();
            kept.push((entry, name, own));
        }
    }
    named
}

/// Tells whether a name is built from an address or a slot position
/// (`sub_140001000`, `class_1411c10b0::create`, `Foo::vfunc_3`), which
/// another build numbers differently.
///
/// # Arguments
///
/// * `name` - The name.
fn positional(name: &str) -> bool {
    name.split("::").any(|part| {
        ["sub_", "class_", "vfunc_"].iter().any(|p| {
            part.strip_prefix(p)
                .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_hexdigit()))
        })
    })
}

/// Writes a session's function names as a pack that names the same
/// functions in another build by their signatures.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their names.
/// * `overlay` - The names the user gave.
/// * `name` - The pack's name.
/// * `all` - Whether names the analysis recovered go in too, besides the
///   user's: not a symbol's (the next build has its own), and not a name
///   built from an address or a slot position.
///
/// # Returns
///
/// The pack's text.
#[must_use]
pub fn export_pack(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    name: &str,
    all: bool,
) -> String {
    let mut wanted: BTreeMap<u64, String> = BTreeMap::new();
    if all {
        for f in &analysis.functions {
            let name = name_of(analysis, overlay, f.entry);
            if f.name.is_some()
                && !matches!(
                    f.name_source,
                    NameSource::Symbol | NameSource::None | NameSource::Slot
                )
                && !positional(&name)
            {
                wanted.insert(f.entry, name);
            }
        }
    }
    for (&entry, given) in &overlay.names {
        if analysis.function(entry).is_some() {
            wanted.insert(entry, given.clone());
        }
    }
    let index = EntryIndex::build(program, analysis);
    let mut lines = Vec::new();
    let mut unsigned = Vec::new();
    for (&entry, fname) in &wanted {
        match signature(program, analysis, &index, entry) {
            Some(sig) => lines.push(format!("fn {} {fname}", format_signature(&sig))),
            None => unsigned.push(format!("{entry:#x} {fname}")),
        }
    }
    let file = program.path.file_name().map_or_else(
        || "the program".to_owned(),
        |f| f.to_string_lossy().into_owned(),
    );
    let mut out = format!(
        "# Exported by borer from {file}: {} of {} names by their functions' first bytes.\n",
        lines.len(),
        wanted.len()
    );
    out.push_str(
        "# Add a [match] section (a string only this program holds) to load it by itself.\n",
    );
    let _ = writeln!(out, "\npack {name} 1");
    let _ = writeln!(out, "about names exported from {file}");
    out.push_str("\n[names]\n");
    for line in &lines {
        out.push_str(line);
        out.push('\n');
    }
    if !unsigned.is_empty() {
        let _ = writeln!(
            out,
            "\n# No signature tells these apart from another function's first bytes:"
        );
        for u in unsigned.iter().take(UNSIGNED_LISTED) {
            let _ = writeln!(out, "# {u}");
        }
        if unsigned.len() > UNSIGNED_LISTED {
            let _ = writeln!(out, "# and {} more", unsigned.len() - UNSIGNED_LISTED);
        }
    }
    out
}

/// What the packs' `[names]` lines found, as a `#` summary and a row for
/// each name that named nothing; empty when no pack has such lines.
///
/// # Arguments
///
/// * `found` - What [`find_pack_names`] found.
#[must_use]
pub fn pack_names_tsv(found: &PackNames) -> String {
    let lines = found.named.len()
        + found.kept.len()
        + found.missing.len()
        + found.ambiguous.len()
        + found.unreadable.len();
    if lines == 0 {
        return String::new();
    }
    let same = found
        .kept
        .iter()
        .filter(|(_, pack, own)| pack == own)
        .count();
    let mut out = format!(
        "# pack names: {} of {lines} named a function, {} matched one the program names itself ({same} by the same name), {} matched no function entry, {} matched several, {} do not read\n",
        found.named.len(),
        found.kept.len(),
        found.missing.len(),
        found.ambiguous.len(),
        found.unreadable.len()
    );
    if found.named.len() + same == lines {
        return out;
    }
    out.push_str("name\tfound\n");
    for (entry, pack, own) in found.kept.iter().filter(|(_, pack, own)| pack != own) {
        let _ = writeln!(out, "{pack}\t{entry:#x}, which the program names {own}");
    }
    for name in &found.missing {
        let _ = writeln!(out, "{name}\tnone");
    }
    for (name, n) in &found.ambiguous {
        let _ = writeln!(out, "{name}\t{n} entries");
    }
    for line in &found.unreadable {
        let _ = writeln!(out, "{line}\tunreadable");
    }
    out
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::pack::{Pack, Packs};

    /// A caller and a distinctive callee, with `gap` bytes of padding
    /// before the callee, so the call's displacement and the callee's
    /// RIP-relative load differ between two builds.
    ///
    /// # Arguments
    ///
    /// * `gap` - Padding bytes before the callee.
    /// * `disp` - The callee's RIP-relative displacement.
    fn build(gap: usize, disp: u32) -> Vec<u8> {
        let callee = 0x10 + gap;
        let rel = u32::try_from(callee - 9).unwrap_or(0);
        let mut code = vec![0x48, 0x83, 0xec, 0x28, 0xe8]; // ASM: sub rsp, 0x28; call callee
        code.extend(rel.to_le_bytes());
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        code.resize(callee, 0xcc);
        code.extend([0x48, 0x8b, 0x05]); // ASM: mov rax, [rip+disp]
        code.extend(disp.to_le_bytes());
        code.extend([0x69, 0xc0, 0x67, 0x45, 0x23, 0x01]); // ASM: imul eax, eax, 0x1234567
        code.extend([0x83, 0xc0, 0x42]); // ASM: add eax, 0x42
        code.extend([0x31, 0xd2]); // ASM: xor edx, edx
        code.extend([0xb9, 0x07, 0x00, 0x00, 0x00]); // ASM: mov ecx, 7
        code.push(0xc3); // ASM: ret
        code
    }

    /// A signature masks the call's and the RIP-relative displacements,
    /// reads back as written, and names the moved callee of another build.
    ///
    /// # Panics
    ///
    /// When a byte is masked wrongly or the name does not follow the code.
    #[test]
    fn a_name_follows_its_function_to_another_build() {
        let one = Program::raw_x64(&build(0, 0x100));
        let a = Analysis::compute(&one);
        let masked = masked_bytes(&one, &a, 0x1010).expect("the callee has bytes");
        assert_eq!(
            format_signature(&masked),
            "488B05????????69C06745230183C04231D2B907000000C3"
        );
        let caller = masked_bytes(&one, &a, 0x1000).expect("the caller has bytes");
        assert_eq!(format_signature(&caller), "4883EC28E8????????4883C428C3");
        assert_eq!(
            parse_signature("48 8B ?? c3"),
            Some(vec![Some(0x48), Some(0x8b), None, Some(0xc3)])
        );
        assert_eq!(parse_signature("48 8"), None);

        let mut overlay = Overlay::default();
        overlay.names.insert(0x1010, "Mine::Thing".to_owned());
        let text = export_pack(&one, &a, &overlay, "mine", false);
        assert!(text.contains("\npack mine 1\n"), "{text}");
        assert!(
            text.contains("\nfn 488B05????????69C0674523 Mine::Thing\n"),
            "{text}"
        );
        let (pack, warnings) = Pack::parse(&text, "mine.borer").expect("the export reads");
        assert!(warnings.is_empty(), "{warnings:?}");

        let two = Program::raw_x64(&build(0x20, 0x340));
        let packs = Arc::new(Packs { packs: vec![pack] });
        let b = Analysis::compute_with(&two, packs);
        let moved = b.function(0x1030).expect("the moved callee is found");
        assert_eq!(moved.name.as_deref(), Some("Mine::Thing"));
        assert_eq!(moved.name_source, NameSource::Pack);
        assert_eq!(b.pack_names.named, vec![(0x1030, "Mine::Thing".to_owned())]);
        let report = pack_names_tsv(&b.pack_names);
        assert!(
            report.starts_with("# pack names: 1 of 1 named a function, 0 matched one"),
            "{report}"
        );
        assert!(positional("class_1411c10b0::create"));
        assert!(positional("Foo::vfunc_3"));
        assert!(!positional("Foo::subtract"));
    }

    /// Two functions that share their first 21 bytes get signatures
    /// long enough to tell them apart, each matching its own entry alone.
    ///
    /// # Panics
    ///
    /// When a signature is cut short or matches the other function.
    #[test]
    fn a_shared_prologue_makes_a_longer_signature() {
        let mut code = vec![0x48, 0x83, 0xec, 0x28]; // ASM: sub rsp, 0x28
        code.extend([0xe8, 0x17, 0x00, 0x00, 0x00]); // ASM: call 0x1020
        code.extend([0xe8, 0x32, 0x00, 0x00, 0x00]); // ASM: call 0x1040
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        for (at, value) in [(0x20, 1u8), (0x40, 2u8)] {
            code.resize(at, 0xcc);
            code.extend([0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp, 0x28
            code.extend([0x31, 0xc0].repeat(8)); // ASM: xor eax, eax (eight times)
            code.extend([0xb8, value, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, value; ret
        }
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let index = EntryIndex::build(&p, &a);
        for entry in [0x1020, 0x1040] {
            let sig = signature(&p, &a, &index, entry).expect("a signature");
            assert_eq!(sig.len(), 22, "{}", format_signature(&sig));
            assert_eq!(index.matches(&sig), vec![entry]);
        }
    }
}
