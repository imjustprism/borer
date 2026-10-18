//! Seeds from data: pointers in data sections, relocations and the GOT that
//! point at code no function covers yet.

use std::collections::{BTreeMap, BTreeSet};

use super::sets::{AddrSet, Covered};
use super::{SEEDS_MAX, push_site};
use crate::analysis::{RefKind, RefSite, le_word, pointer_size, read_word};
use crate::fxmap::FxHashSet;
use crate::isa::x86::{FlowControl, Instruction, OpKind, Register};
use crate::num::{from_usize, saturating_usize};
use crate::program::{Program, Section};

/// A data reference one instruction makes.
///
/// The kind is [`RefKind::Call`] or [`RefKind::Jmp`] when the instruction
/// branches through the referenced slot, which is how an import is called
/// on a PE (`call qword [rel <IAT slot>]`), [`RefKind::Index`] for the base
/// of a table an index register scales into, and [`RefKind::Data`] for a
/// plain load or an address-carrying immediate. Without the branch kinds
/// every direct call to an import reads as a data load and no import
/// appears in a caller's callee list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct DataRef {
    /// The referenced address.
    pub(super) target: u64,
    /// The referencing instruction's address.
    pub(super) va: u64,
    /// How the instruction uses the target.
    pub(super) kind: RefKind,
}

/// Returns the addresses between the first and the last mapped section.
///
/// A value outside it cannot reference the image, and most words in data
/// and most immediates in code are outside it, so the range rejects them
/// before any section lookup.
///
/// # Arguments
///
/// * `program` - The loaded image.
pub(super) fn mapped_range(program: &Program) -> std::ops::Range<u64> {
    let (lo, hi) =
        program
            .sections
            .iter()
            .filter(|s| s.file_size > 0)
            .fold((u64::MAX, 0), |(lo, hi), s| {
                (
                    lo.min(s.va.0),
                    hi.max(s.va.0.saturating_add(s.vsize.max(s.file_size))),
                )
            });
    lo..hi.max(lo)
}

/// Tells whether a section describes addresses rather than uses them.
///
/// An exception table names the function it covers, a relocation names
/// the word it patches, and a symbol table names everything; a word in
/// any of them is a description of the address, not a reference to it.
///
/// # Arguments
///
/// * `name` - The section name.
fn describes_addresses(name: &str) -> bool {
    matches!(
        name,
        ".pdata" | ".reloc" | ".eh_frame" | ".eh_frame_hdr" | ".dynamic" | ".dynsym" | ".symtab"
    ) || name.starts_with(".rel")
}

/// Tells whether a section holds resources rather than the program's data.
///
/// A PE's `.rsrc` holds icons, version blocks, manifests and string
/// tables: bytes that are what they are, not pointers, and a word there
/// that happens to spell a code address names no function.
///
/// # Arguments
///
/// * `name` - The section's name.
fn holds_resources(name: &str) -> bool {
    name == ".rsrc" || name.starts_with(".rsrc$")
}

/// The bytes of a section pointers are read from, as the image holds them.
///
/// That is a non-executable section that neither describes addresses
/// ([`describes_addresses`]) nor holds resources ([`holds_resources`]), at
/// least one word long. Its words are the relocated ones
/// ([`Program::section_bytes`]): a PIE lld linked keeps its vtables and
/// callback tables as zeros in the file.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `s` - The section.
/// * `word` - The pointer width in bytes.
///
/// # Returns
///
/// The section's bytes, or `None` when no pointer is read from it.
fn pointer_section_bytes<'a>(program: &'a Program, s: &Section, word: usize) -> Option<&'a [u8]> {
    if s.executable
        || describes_addresses(&s.name)
        || holds_resources(&s.name)
        || saturating_usize(s.file_size) < word
    {
        return None;
    }
    program.section_bytes(s)
}

/// Records a reference from every data pointer that names a function or
/// another data address.
///
/// A virtual method is reached through its class's table, a callback
/// through the table it was registered in, and neither leaves an
/// instruction that names the function; on this client that is 29,487
/// functions with no reference at all until the tables are read. A word
/// that lands in a data section is a `ptr` site the same way: the locator
/// naming a type descriptor, a table of string pointers, a static holding
/// the address of another. So is a word that lands in an executable
/// section where no block covers it, the data a linker merged into `.text`
/// (32-bit system binaries keep their strings and tables there). Every
/// non-executable section is scanned a word at a time, skipping those that
/// describe addresses rather than use them ([`describes_addresses`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entries` - Function entry addresses; most words in a data section
///   are not addresses at all, so a range check comes before the lookup.
/// * `covered` - The functions' blocks, which tell code from data in an
///   executable section.
/// * `xrefs` - Reference sites, extended in place.
pub(super) fn record_table_refs(
    program: &Program,
    entries: &BTreeSet<u64>,
    covered: &Covered,
    xrefs: &mut BTreeMap<u64, Vec<RefSite>>,
) {
    let word = saturating_usize(pointer_size(program));
    let sorted: Vec<u64> = entries.iter().copied().collect();
    let mapped = mapped_range(program);
    for s in &program.sections {
        let Some(data) = pointer_section_bytes(program, s, word) else {
            continue;
        };
        for (i, chunk) in data.chunks_exact(word).enumerate() {
            let v = le_word(program, chunk);
            if !mapped.contains(&v) {
                continue;
            }
            let slot = s.va.0 + from_usize(i * word);
            if sorted.binary_search(&v).is_ok() {
                push_site(xrefs, v, slot, RefKind::Table, None);
            } else if program
                .section_at(v)
                .is_some_and(|t| !t.executable || !covered.contains(v))
            {
                push_site(xrefs, v, slot, RefKind::Ptr, None);
            }
        }
    }
}

/// The code addresses that relocated words inside executable sections hold.
///
/// Only words no decoded instruction covers count: a table of callbacks a
/// linker without `.rdata` keeps in `.text`, which [`pointer_seeds`] never
/// reads.
///
/// A jump table is such a run of words too, and its entries are case
/// labels, not functions: a run whose every target lies just below it (a
/// function's cases precede its table) is left out, as is a word whose
/// target a block already covers.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `covered` - The blocks found so far.
///
/// # Returns
///
/// The targets, at most [`SEEDS_MAX`].
pub(super) fn reloc_seeds(program: &Program, covered: &Covered) -> Vec<u64> {
    /// Farthest below its table a case label lies.
    const CASES_REACH: u64 = 0x1_0000;
    let word = pointer_size(program);
    let mut sites: Vec<u64> = program
        .relocated_words()
        .into_iter()
        .filter(|&va| crate::analysis::is_executable_va(program, va) && !covered.contains(va))
        .collect();
    sites.sort_unstable();
    let mut out = Vec::new();
    let mut run: Vec<(u64, u64)> = Vec::new();
    let flush = |run: &mut Vec<(u64, u64)>, out: &mut Vec<u64>| {
        let Some(&(first, _)) = run.first() else {
            return;
        };
        let cases = run
            .iter()
            .all(|&(_, t)| t < first && first - t <= CASES_REACH);
        if !cases {
            out.extend(run.iter().map(|&(_, t)| t).filter(|&t| {
                crate::analysis::is_executable_va(program, t) && !covered.contains(t)
            }));
        }
        run.clear();
    };
    for va in sites {
        let Some(target) = read_word(program, va) else {
            continue;
        };
        if run.last().is_some_and(|&(prev, _)| prev + word != va) {
            flush(&mut run, &mut out);
        }
        run.push((va, target));
        if out.len() >= SEEDS_MAX {
            break;
        }
    }
    flush(&mut run, &mut out);
    out.truncate(SEEDS_MAX);
    out
}

/// Whether the `len` bytes at `at` lie inside text: a run of six or more
/// printable ASCII bytes, or three or more printable UTF-16 units.
///
/// A 32-bit image loads at `0x400000`, and a UTF-16 pair of letters from
/// `@` to `Q` is an address in its `.text` (`E\0C\0` is `0x00430045`), as
/// are the last bytes of a type name (`d@@\0`). A pointer table never
/// runs printable for that long: `0x00404064` next to `0x00404080` reads
/// `d@@\0\x80@@\0`.
///
/// The ASCII run is the printable bytes through the word's first printable
/// byte; the UTF-16 run is the printable units on even offsets through the
/// word.
///
/// # Arguments
///
/// * `data` - The section's bytes.
/// * `at` - Offset of the word.
/// * `len` - The word's width.
fn inside_text(data: &[u8], at: usize, len: usize) -> bool {
    let printable = |b: u8| (0x20..0x7f).contains(&b);
    let end = (at + len).min(data.len());
    if let Some(first) = (at..end).find(|&i| printable(data[i])) {
        let mut lo = first;
        while lo > 0 && printable(data[lo - 1]) {
            lo -= 1;
        }
        let mut hi = first;
        while hi < data.len() && printable(data[hi]) {
            hi += 1;
        }
        if hi - lo >= 6 {
            return true;
        }
    }
    let unit = |i: usize| i + 1 < data.len() && printable(data[i]) && data[i + 1] == 0;
    let base = at & !1;
    if (base..end).step_by(2).any(unit) {
        let first = (base..end).step_by(2).find(|&i| unit(i)).unwrap_or(base);
        let mut lo = first;
        while lo >= 2 && unit(lo - 2) {
            lo -= 2;
        }
        let mut hi = first;
        while unit(hi) {
            hi += 2;
        }
        if (hi - lo) / 2 >= 3 {
            return true;
        }
    }
    false
}

/// Collects data pointers (vtables, callbacks) that point into executable sections.
///
/// # Arguments
///
/// * `program` - The loaded image; every non-executable section is scanned
///   in word-sized steps.
/// * `sites` - The relocation sites, when the image has any: only a word
///   the loader relocates is a pointer then.
///
/// # Returns
///
/// The pointed-to addresses in scan order, at most [`SEEDS_MAX`].
pub(super) fn pointer_seeds(program: &Program, sites: Option<&FxHashSet<u64>>) -> Vec<u64> {
    let word = saturating_usize(pointer_size(program));
    let mut out = Vec::new();
    'sec: for s in &program.sections {
        let Some(data) = pointer_section_bytes(program, s, word) else {
            continue;
        };
        for (k, chunk) in data.chunks_exact(word).enumerate() {
            if sites.is_some_and(|set| !set.contains(&(s.va.0 + from_usize(k * word)))) {
                continue;
            }
            let v = le_word(program, chunk);
            if v != 0
                && crate::analysis::is_executable_va(program, v)
                && !inside_text(data, k * word, word)
            {
                out.push(v);
                if out.len() >= SEEDS_MAX {
                    break 'sec;
                }
            }
        }
    }
    out
}

/// Records the immediate and memory operands of `instr` that land in mapped
/// sections or in a PE's mapped headers.
///
/// The headers count because `lea rcx, [__ImageBase]` is how x64 code finds
/// its own image (the base of every RVA table it reads), and that
/// reference was dropped for want of a section. A memory operand counts
/// when it has no effective base: a bare
/// displacement (iced pre-computes rip-relative ones into absolute targets,
/// so the raw displacement is the address in both cases), or a scaled index
/// on a displacement, `[esi*4 + table]`, which is how 32-bit code reads a
/// table and the only reference a lookup table ever gets. A base register
/// makes the displacement a field offset, not an address. Most immediates
/// are small constants, so the range check rejects them before the section
/// lookup.
///
/// # Arguments
///
/// * `program` - The loaded image, for the section check.
/// * `mapped` - The addresses between the first and the last mapped section.
/// * `instr` - The decoded instruction.
/// * `va` - Its address, recorded as the referencing site.
/// * `out` - Receives `(target, va)` pairs.
/// * `patched` - The relocation sites and the operands' offsets inside
///   `instr`, in an image that relocates: an absolute operand the loader
///   does not patch is then a constant, whatever it looks like.
pub(super) fn record_data_refs(
    program: &Program,
    mapped: &std::ops::Range<u64>,
    instr: &Instruction,
    va: u64,
    out: &mut Vec<DataRef>,
    patched: Option<(&AddrSet, crate::isa::x86::ConstantOffsets)>,
) {
    let in_image =
        |v: u64| (mapped.contains(&v) && program.section_at(v).is_some()) || program.in_headers(v);
    let relocated = |offset: usize, size: usize| {
        patched.is_none_or(|(sites, _)| size >= 4 && sites.contains(va + from_usize(offset)))
    };
    for op in 0..instr.op_count() {
        match instr.op_kind(op) {
            OpKind::Memory => {
                let has_effective_base =
                    instr.memory_base() != Register::None && instr.memory_base() != Register::RIP;
                if has_effective_base {
                    continue;
                }
                if !instr.is_ip_rel_memory_operand()
                    && let Some((_, offsets)) = &patched
                    && !(offsets.has_displacement()
                        && relocated(offsets.displacement_offset(), offsets.displacement_size()))
                {
                    continue;
                }
                let target = instr.memory_displacement64();
                if in_image(target) {
                    let kind = if instr.memory_index() == Register::None {
                        match instr.flow_control() {
                            FlowControl::IndirectCall => RefKind::Call,
                            FlowControl::IndirectBranch => RefKind::Jmp,
                            FlowControl::Next
                            | FlowControl::UnconditionalBranch
                            | FlowControl::ConditionalBranch
                            | FlowControl::Return
                            | FlowControl::Call
                            | FlowControl::Interrupt
                            | FlowControl::Exception
                            | FlowControl::XbeginXabortXend => RefKind::Data,
                        }
                    } else {
                        RefKind::Index
                    };
                    out.push(DataRef { target, va, kind });
                }
            }
            OpKind::Immediate64
            | OpKind::Immediate32
            | OpKind::Immediate32to64
            | OpKind::Immediate8to64
            | OpKind::Immediate8to32 => {
                if let Some((_, offsets)) = &patched
                    && !(offsets.has_immediate()
                        && relocated(offsets.immediate_offset(), offsets.immediate_size()))
                {
                    continue;
                }
                let v = instr.immediate(op);
                if in_image(v) {
                    out.push(DataRef {
                        target: v,
                        va,
                        kind: RefKind::Data,
                    });
                }
            }
            _ => {}
        }
    }
}

/// Where `ebx` points in a 32-bit ELF's position-independent code: the
/// global offset table its PLT entries jump through as `jmp [ebx+N]`.
///
/// The i386 ABI keeps `_GLOBAL_OFFSET_TABLE_` at the start of `.got.plt`
/// (of `.got` when the linker made no `.got.plt`), and every PIC function
/// loads it into `ebx` before calling through the PLT. Without it no PLT
/// entry of a 32-bit shared object was named, and `xrefs(strlen)` found no
/// call.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The table's address, or `None` for a file that is not ELF or names
/// neither section.
pub(super) fn got_base(program: &Program) -> Option<u64> {
    if program.format != crate::program::BinaryFormat::Elf {
        return None;
    }
    let named = |name: &str| program.sections.iter().find(|s| s.name == name);
    named(".got.plt").or_else(|| named(".got")).map(|s| s.va.0)
}

/// The code address a slot holds once the loader has bound it.
///
/// A shared object's PLT entry for a function it defines itself jumps
/// through a GOT slot its `JUMP_SLOT` relocation fills with that
/// function's address, so the stub is that function under another
/// address and takes its name.
///
/// # Arguments
///
/// * `program` - The loaded image, its relocations applied.
/// * `bitness` - Pointer width in bits.
/// * `slot` - The slot's address.
///
/// # Returns
///
/// The bound address, or `None` when the slot cannot be read or is empty.
pub(super) fn bound_function(program: &Program, bitness: u32, slot: u64) -> Option<u64> {
    if slot == 0 {
        return None;
    }
    let word = program.read_va(slot, usize::try_from(bitness / 8).ok()?)?;
    let value = match *word {
        [a, b, c, d] => u64::from(u32::from_le_bytes([a, b, c, d])),
        [a, b, c, d, e, f, g, h] => u64::from_le_bytes([a, b, c, d, e, f, g, h]),
        _ => return None,
    };
    (value != 0).then_some(value)
}
