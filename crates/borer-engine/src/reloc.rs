//! ELF dynamic relocations, applied to the image the way the loader does.
//!
//! A position-independent ELF states every absolute pointer it holds as a
//! dynamic relocation: the `.rela.dyn`/`.rel.dyn` entries, the packed
//! `DT_RELR` table and the GOT slots `.rela.plt` binds. lld writes a value
//! into its slot only when asked (`--apply-dynamic-relocs`), so in the
//! clang, Android, Chromium and Rust builds it links, vtables, callback
//! arrays and `.data.rel.ro` tables are zeros on disk: a reader of the file
//! sees no pointer there, and the functions reached only through them go
//! missing. [`read_elf`] computes what the loader writes for an image
//! loaded at its link address (base 0 for a PIE, whose addresses are the
//! ones every tool prints) and keeps it beside the file in [`Relocs`]. The
//! file's own bytes never change, since its hash is what identifies it;
//! only the ranges a relocation writes into are copied, with the words in
//! place, and [`crate::program::Program`]'s reads of the image go through
//! them.
//!
//! Applied are `RELATIVE` (`B + A`), the absolute word (`R_X86_64_64`,
//! `R_386_32`, `R_AARCH64_ABS64`: `S + A`) and the GOT binds (`GLOB_DAT`,
//! `JUMP_SLOT`: `S`, or `S + A` on arm64) of x86-64, i386 and arm64. A word
//! bound to a symbol the image imports keeps what the file holds, and its
//! slot is handed back to be named after the import. Every other type
//! (`COPY`, the TLS and `IRELATIVE` types) is left alone. Entries whose slot
//! no file-backed section holds, that land on a word another entry already
//! wrote, or that come past the cap are refused and counted, never
//! applied.

use crate::num::saturating_usize;
use crate::program::Section;

/// Most entries read from one relocation table, whatever its size claims.
const ENTRIES_MAX: usize = 1 << 20;

/// Most relocated words claimed across every table: a `DT_RELR` word past
/// it is refused, since one bitmap word can claim 63.
const SITES_MAX: usize = 1 << 20;

/// `DT_RELRSZ`: the size in bytes of the `DT_RELR` table.
const DT_RELRSZ: u64 = 35;

/// `DT_RELR`: the address of the packed relative relocations.
const DT_RELR: u64 = 36;

/// `DT_RELRENT`: the size of one `DT_RELR` entry.
const DT_RELRENT: u64 = 37;

/// What a relocation type writes into its slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// `B + A`: an address in the image itself.
    Relative,
    /// `S + A`: a symbol's address plus an addend.
    Absolute,
    /// `S` (`S + A` on arm64): a GOT slot bound to a symbol.
    Bind,
}

/// Reads what a relocation type of a machine writes.
///
/// # Arguments
///
/// * `machine` - The ELF `e_machine`.
/// * `r_type` - The relocation type.
///
/// # Returns
///
/// The kind, or `None` for a type this does not apply.
fn kind(machine: u16, r_type: u32) -> Option<Kind> {
    /// `EM_386`.
    const EM_386: u16 = 3;
    /// `EM_X86_64`.
    const EM_X86_64: u16 = 62;
    /// `EM_AARCH64`.
    const EM_AARCH64: u16 = 183;
    // SPEC: System V ABI AMD64 4.4.1 and i386 4-x, `R_*_64`/`R_386_32` = 1,
    // `GLOB_DAT` = 6, `JUMP_SLOT` = 7, `RELATIVE` = 8; ELF for the Arm 64-bit
    // Architecture 5.7.12, `ABS64` = 257, `GLOB_DAT` = 1025, `JUMP_SLOT` =
    // 1026, `RELATIVE` = 1027.
    match (machine, r_type) {
        (EM_X86_64 | EM_386, 8) | (EM_AARCH64, 1027) => Some(Kind::Relative),
        (EM_X86_64 | EM_386, 1) | (EM_AARCH64, 257) => Some(Kind::Absolute),
        (EM_X86_64 | EM_386, 6 | 7) | (EM_AARCH64, 1025 | 1026) => Some(Kind::Bind),
        _ => None,
    }
}

/// The image as the dynamic relocations leave it.
///
/// Empty for every format but ELF, and for an ELF whose relocations write
/// nothing the file does not already hold (GNU ld writes the values into
/// the slots of a RELA image itself).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Relocs {
    /// Copies of the file ranges the relocations write into, as `(file
    /// offset, bytes)` with the relocated words in place: sorted by offset,
    /// disjoint, each the union of the section extents written to.
    patched: Vec<(u64, Vec<u8>)>,
    /// Every relocated pointer word's address (`RELATIVE`, absolute and
    /// `DT_RELR` entries) of a position-independent image (`ET_DYN`),
    /// sorted and unique: where a word the loader leaves alone is no
    /// pointer. Empty for any other image, whose pointers need none.
    pub(crate) sites: Vec<u64>,
    /// Entries applied: a word written, a pointer recorded, or an import's
    /// slot named.
    pub(crate) applied: usize,
    /// Entries refused: a slot no file-backed section holds, a word another
    /// entry already wrote, a malformed `DT_RELR` table, or past the cap.
    pub(crate) refused: usize,
}

impl Relocs {
    /// Reads the bytes at file offsets `start..end` as the loader leaves
    /// them.
    ///
    /// # Arguments
    ///
    /// * `start` - File offset of the first byte.
    /// * `end` - File offset one past the last byte.
    ///
    /// # Returns
    ///
    /// The relocated bytes, or `None` when no copied range holds the whole
    /// span, where the file's bytes are the image's.
    pub(crate) fn slice(&self, start: u64, end: u64) -> Option<&[u8]> {
        let k = self
            .patched
            .partition_point(|(off, _)| *off <= start)
            .checked_sub(1)?;
        let (off, bytes) = self.patched.get(k)?;
        let from = usize::try_from(start - off).ok()?;
        let to = usize::try_from(end.checked_sub(*off)?).ok()?;
        bytes.get(from..to)
    }

    /// Writes the relocated words over a copy of the file, for an image
    /// rebuilt from the file's bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The copy, in file order; a range past its end is skipped.
    pub(crate) fn bake(&self, bytes: &mut [u8]) {
        for (off, patched) in &self.patched {
            let start = saturating_usize(*off);
            if let Some(dst) = bytes.get_mut(start..start.saturating_add(patched.len())) {
                dst.copy_from_slice(patched);
            }
        }
    }

    /// Renders what was applied as a summary line, empty when the image has
    /// no dynamic relocations this applies.
    pub(crate) fn render(&self) -> String {
        if self.applied == 0 && self.refused == 0 {
            return String::new();
        }
        let mut out = format!(
            "relocs:  {} dynamic relocation(s) applied to the image",
            self.applied
        );
        if self.refused > 0 {
            out.push_str(&format!(
                "; {} refused (a slot outside the file-backed image, a word another entry wrote, a malformed DT_RELR table, or past the cap of {ENTRIES_MAX} per table)",
                self.refused
            ));
        }
        out.push('\n');
        out
    }
}

/// Where `len` bytes at `va` sit in the file.
///
/// # Arguments
///
/// * `sections` - The mapped sections, as the loader reads the image.
/// * `va` - The first byte's address.
/// * `len` - The byte count.
///
/// # Returns
///
/// The first byte's file offset and the file extent of the section holding
/// them all, or `None` when no file-backed section does.
fn file_range(sections: &[Section], va: u64, len: u64) -> Option<(u64, (u64, u64))> {
    let s = sections
        .iter()
        .find(|s| s.file_size > 0 && va >= s.va && va - s.va < s.vsize.max(s.file_size))?;
    let rel = va - s.va;
    let end = rel.checked_add(len)?;
    let extent_end = s.file_off.checked_add(s.file_size)?;
    (end <= s.file_size).then_some((s.file_off + rel, (s.file_off, extent_end)))
}

/// Reads a little-endian word of the file.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `off` - Its file offset.
/// * `word` - Its width in bytes, 4 or 8.
fn file_word(bytes: &[u8], off: u64, word: u64) -> Option<u64> {
    let start = usize::try_from(off).ok()?;
    let raw = bytes.get(start..start.checked_add(saturating_usize(word))?)?;
    let mut le = [0u8; 8];
    le.get_mut(..raw.len())?.copy_from_slice(raw);
    Some(u64::from_le_bytes(le))
}

/// What one ELF's dynamic relocations do to its image.
#[derive(Debug, Default)]
pub(crate) struct Applied {
    /// The relocated image.
    pub(crate) relocs: Relocs,
    /// The slots bound to a symbol the image imports, as `(dynamic symbol
    /// index, slot address)` in table order: each names its slot after
    /// the import.
    pub(crate) bound: Vec<(usize, u64)>,
}

/// Applies an ELF's dynamic relocations to its image.
///
/// # Arguments
///
/// * `elf` - The parsed ELF.
/// * `bytes` - The file.
/// * `sections` - The mapped sections, already fit to the file.
///
/// # Returns
///
/// The relocated image and the slots bound to imports; empty for an image
/// with no dynamic relocations.
pub(crate) fn read_elf(elf: &goblin::elf::Elf<'_>, bytes: &[u8], sections: &[Section]) -> Applied {
    let machine = elf.header.e_machine;
    let word: u64 = if elf.is_64 { 8 } else { 4 };
    let mut out = Applied::default();
    let mut claims: Vec<Claim> = Vec::new();
    for table in [&elf.dynrelas, &elf.dynrels, &elf.pltrelocs] {
        out.relocs.refused += table.len().saturating_sub(ENTRIES_MAX);
        for r in table.iter().take(ENTRIES_MAX) {
            let Some(kind) = kind(machine, r.r_type) else {
                continue;
            };
            let Some(at) = file_range(sections, r.r_offset, word) else {
                out.relocs.refused += 1;
                continue;
            };
            let sym = (r.r_sym != 0).then(|| elf.dynsyms.get(r.r_sym)).flatten();
            let defined = sym.as_ref().filter(|s| s.st_shndx != 0).map(|s| s.st_value);
            let addend = r.r_addend.map(i64::cast_unsigned);
            let implicit = || file_word(bytes, at.0, word);
            let value = match (kind, defined) {
                (Kind::Relative, _) => addend,
                (Kind::Absolute, Some(s)) => addend.or_else(implicit).map(|a| s.wrapping_add(a)),
                (Kind::Absolute, None) if r.r_sym == 0 => addend,
                (Kind::Bind, Some(s)) => Some(match machine {
                    goblin::elf::header::EM_AARCH64 => s.wrapping_add(addend.unwrap_or(0)),
                    _ => s,
                }),
                (Kind::Absolute | Kind::Bind, None) => {
                    out.bound.push((r.r_sym, r.r_offset));
                    out.relocs.applied += 1;
                    continue;
                }
            };
            claims.push(Claim {
                va: r.r_offset,
                at,
                value,
                site: matches!(kind, Kind::Relative | Kind::Absolute),
            });
        }
    }
    relr(elf, bytes, sections, word, &mut claims, &mut out.relocs);
    // INVARIANT: a word is written once: of the entries claiming one, the
    // lowest address wins, then the first in table order, so a hostile
    // table cannot make a write depend on anything but the file.
    claims.sort_by_key(|c| c.va);
    let pic = elf.header.e_type == goblin::elf::header::ET_DYN;
    let mut last_end = 0u64;
    let mut writes: Vec<(u64, (u64, u64), u64)> = Vec::new();
    for c in claims {
        if c.va < last_end {
            out.relocs.refused += 1;
            continue;
        }
        last_end = c.va.saturating_add(word);
        out.relocs.applied += 1;
        if c.site && pic {
            out.relocs.sites.push(c.va);
        }
        if let Some(v) = c.value {
            writes.push((c.at.0, c.at.1, v));
        }
    }
    out.relocs.patched = patch(bytes, &writes, word);
    out
}

/// One word a relocation claims, before overlaps are settled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Claim {
    /// The slot's address.
    va: u64,
    /// The slot's file offset and its section's file extent.
    at: (u64, (u64, u64)),
    /// The value the loader writes, `None` where the slot already holds it
    /// (an implicit addend, loaded at the link address).
    value: Option<u64>,
    /// Whether the word is a pointer into the image, which every relative
    /// and absolute word is and a GOT bind to a defined symbol is not.
    site: bool,
}

/// Decodes the packed `DT_RELR` table into the pointer words it relocates.
///
/// Each entry is relative with its addend in the slot, so loaded at the
/// link address it writes nothing; what it says is where the pointers are.
/// An even entry is a slot's address; an odd one a bitmap whose bit `i + 1`
/// stands for the word `i` words past the last slot, after which the
/// bitmap's reach moves on by the bits it has.
///
/// # Arguments
///
/// * `elf` - The parsed ELF.
/// * `bytes` - The file.
/// * `sections` - The mapped sections.
/// * `word` - The pointer width in bytes.
/// * `claims` - Receives the slots, as pointers with nothing to write.
/// * `relocs` - Counts what is refused.
fn relr(
    elf: &goblin::elf::Elf<'_>,
    bytes: &[u8],
    sections: &[Section],
    word: u64,
    claims: &mut Vec<Claim>,
    relocs: &mut Relocs,
) {
    let Some(dynamic) = &elf.dynamic else {
        return;
    };
    let tag = |t: u64| dynamic.dyns.iter().find(|d| d.d_tag == t).map(|d| d.d_val);
    let (Some(at), Some(size)) = (tag(DT_RELR), tag(DT_RELRSZ).filter(|s| *s > 0)) else {
        return;
    };
    let table = file_range(sections, at, size)
        .filter(|_| tag(DT_RELRENT).is_none_or(|e| e == word))
        .and_then(|(off, _)| {
            let start = usize::try_from(off).ok()?;
            bytes.get(start..start.checked_add(usize::try_from(size).ok()?)?)
        });
    let Some(table) = table else {
        relocs.refused += 1;
        return;
    };
    // SPEC: the generic ABI's SHT_RELR proposal (2018): an even entry is an
    // address, an odd one a bitmap of the `8 * word - 1` words after the
    // last address.
    let bits = word * 8 - 1;
    let mut next = 0u64;
    let mut record = |va: u64, relocs: &mut Relocs| match file_range(sections, va, word)
        .filter(|_| claims.len() < SITES_MAX)
    {
        Some(at) => claims.push(Claim {
            va,
            at,
            value: None,
            site: true,
        }),
        None => relocs.refused += 1,
    };
    let entries = table.chunks_exact(saturating_usize(word));
    relocs.refused += entries.len().saturating_sub(ENTRIES_MAX);
    for entry in entries.take(ENTRIES_MAX) {
        let mut le = [0u8; 8];
        let Some(dst) = le.get_mut(..entry.len()) else {
            continue;
        };
        dst.copy_from_slice(entry);
        let e = u64::from_le_bytes(le);
        if e & 1 == 0 {
            record(e, relocs);
            next = e.wrapping_add(word);
            continue;
        }
        for i in 0..bits {
            if (e >> (i + 1)) & 1 != 0 {
                record(next.wrapping_add(i.wrapping_mul(word)), relocs);
            }
        }
        next = next.wrapping_add(bits.wrapping_mul(word));
    }
}

/// Copies the section extents the writes land in and puts each word in
/// place.
///
/// Overlapping extents merge into one copy, so the copies together are at
/// most the file's size; a copy where no write changed a byte is dropped.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `writes` - The words to write, as `(file offset, section extent,
///   value)`, at disjoint offsets.
/// * `word` - The width of each word in bytes.
///
/// # Returns
///
/// The copies, sorted by file offset and disjoint.
fn patch(bytes: &[u8], writes: &[(u64, (u64, u64), u64)], word: u64) -> Vec<(u64, Vec<u8>)> {
    let mut extents: Vec<(u64, u64)> = writes.iter().map(|w| w.1).collect();
    extents.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (start, end) in extents {
        match merged.last_mut() {
            Some(last) if start <= last.1 => last.1 = last.1.max(end),
            _ => merged.push((start, end)),
        }
    }
    let width = saturating_usize(word);
    let mut out = Vec::new();
    for (start, end) in merged {
        let Some(file) = bytes.get(saturating_usize(start)..saturating_usize(end)) else {
            continue;
        };
        let mut copy = file.to_vec();
        for (off, _, v) in writes.iter().filter(|w| w.0 >= start && w.0 < end) {
            let at = saturating_usize(off - start);
            if let Some(dst) = copy.get_mut(at..at.saturating_add(width)) {
                let le = v.to_le_bytes();
                dst.copy_from_slice(le.get(..width).unwrap_or(&le));
            }
        }
        if copy != file {
            out.push((start, copy));
        }
    }
    out
}
