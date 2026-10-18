//! PE-specific reads of the file: the data directories, the section table,
//! imports and exports, the ARM64 exception data, and the loosening of a
//! header damaged on purpose.

use std::collections::BTreeSet;

use super::{Symbol, SymbolKind, caught};
use crate::num::{from_usize, u16_le, u32_le};

/// Loosens the PE header fields the Windows loader ignores and the parser
/// refuses outright, for the length of a parse.
///
/// The loader never reads the DOS stub, where a linker leaves its Rich
/// header, and reads at most sixteen data directories whatever
/// `NumberOfRvaAndSizes` states; the parser refused a whole file for one
/// flipped bit in the Rich header's `DanS` marker or a count of seventeen.
/// The Rich marker is hidden and the count capped at sixteen in place;
/// [`restore`] puts both back after the parse.
///
/// # Arguments
///
/// * `bytes` - The whole file, patched in place.
///
/// # Returns
///
/// What was patched, and a note for each change.
pub(super) fn loosen_pe(bytes: &mut [u8]) -> (Vec<Patch>, Vec<String>) {
    /// The data directories a PE optional header has room for.
    const DIRECTORIES_MAX: u32 = 16;
    /// The Rich header's end marker.
    const RICH: [u8; 4] = *b"Rich";
    /// Bytes of the DOS header; the stub, and any Rich header, follow it.
    const DOS_HEADER: usize = 0x40;
    let mut patches = Vec::new();
    let mut notes = Vec::new();
    let Some(pe) = pe_signature(bytes) else {
        return (patches, notes);
    };
    let damaged = caught(|| goblin::pe::header::RichHeader::parse(bytes).is_err()).unwrap_or(true);
    if damaged
        && let Some(at) = bytes
            .get(DOS_HEADER..pe)
            .and_then(|stub| stub.windows(4).position(|w| w == RICH))
            .map(|k| DOS_HEADER + k)
        && let Some(slot) = bytes.get_mut(at..at + 4)
    {
        patches.push(Patch::zeroed(at, slot));
        notes.push("the Rich header in the DOS stub is damaged; it is not read".to_owned());
    }
    let opt = pe + 24;
    let count_at = match u16_le(bytes, opt) {
        Some(0x10b) => opt + 92,
        Some(0x20b) => opt + 108,
        _ => return (patches, notes),
    };
    if let Some(count) = u32_le(bytes, count_at).filter(|&c| c > DIRECTORIES_MAX)
        && let Some(slot) = bytes.get_mut(count_at..count_at + 4)
    {
        let saved = Patch::zeroed(count_at, slot);
        slot.copy_from_slice(&DIRECTORIES_MAX.to_le_bytes());
        patches.push(saved);
        notes.push(format!(
            "the header states {count} data directories; the loader reads {DIRECTORIES_MAX}"
        ));
    }
    (patches, notes)
}

/// Four bytes of the file changed for the length of a parse.
#[derive(Debug, Clone, Copy)]
pub(super) struct Patch {
    /// File offset of the first byte.
    pub(super) at: usize,
    /// What the bytes held.
    pub(super) saved: [u8; 4],
}

impl Patch {
    /// Saves four bytes and zeroes them.
    ///
    /// # Arguments
    ///
    /// * `at` - The bytes' file offset.
    /// * `slot` - The four bytes, zeroed in place.
    pub(super) fn zeroed(at: usize, slot: &mut [u8]) -> Patch {
        let mut saved = [0u8; 4];
        saved.copy_from_slice(slot);
        slot.fill(0);
        Patch { at, saved }
    }
}

/// Puts back what [`loosen_pe`] changed.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `patches` - What was changed.
pub(super) fn restore(bytes: &mut [u8], patches: &[Patch]) {
    for p in patches {
        if let Some(slot) = bytes.get_mut(p.at..p.at + 4) {
            slot.copy_from_slice(&p.saved);
        }
    }
}

/// Most entries an import table may name before it is refused.
///
/// A module imports a few thousand names at most, and the hint/name table
/// of one DLL addresses 65,536; a directory that reaches past that is a
/// rewritten or shifted one, where every word of whatever it lands on
/// reads as an import.
const IMPORTS_MAX: u64 = 1 << 16;

/// Most entries an export table may name before it is refused.
///
/// An export is reached by a sixteen-bit ordinal, from the name table or
/// from the caller, so a table that claims more entries than that names
/// ones nothing can reach: the count is a damaged header, not a table.
pub(super) const EXPORTS_MAX: u32 = 1 << 16;

/// Bytes of one data directory entry: a virtual address and a size.
pub(super) const DIRECTORY_ENTRY: usize = 8;

/// Bytes of one section table row.
const SECTION_ROW: usize = 40;

/// Largest section size a sane image carries (1 GiB), in memory or in the file.
pub(super) const SANE_MAX: u64 = 1 << 30;

/// Where the PE signature of an `MZ` file sits.
///
/// # Arguments
///
/// * `bytes` - The whole file.
///
/// # Returns
///
/// The file offset of `PE\0\0`, or `None` when the file has no such header.
pub(crate) fn pe_signature(bytes: &[u8]) -> Option<usize> {
    if bytes.first_chunk::<2>() != Some(b"MZ") {
        return None;
    }
    let pe = usize::try_from(u32_le(bytes, 0x3c)?).ok()?;
    (bytes.get(pe..pe.checked_add(4)?)? == b"PE\0\0").then_some(pe)
}

/// Where a data directory entry sits in the file.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `index` - The entry's slot: `0` export, `1` import, `5` relocation.
///
/// # Returns
///
/// The file offset of the entry's eight bytes and whether the image is
/// PE32+ (eight-byte words), or `None` when the headers do not reach that
/// slot.
pub(crate) fn directory_entry(bytes: &[u8], index: usize) -> Option<(usize, bool)> {
    let opt = pe_signature(bytes)?.checked_add(24)?;
    let (count_at, plus) = match u16_le(bytes, opt)? {
        0x10b => (opt + 92, false),
        0x20b => (opt + 108, true),
        _ => return None,
    };
    if usize::try_from(u32_le(bytes, count_at)?).ok()? <= index {
        return None;
    }
    Some((count_at + 4 + index * DIRECTORY_ENTRY, plus))
}

/// A row of the section table as the file states it, before any sanity check.
#[derive(Debug, Clone, Copy)]
pub(super) struct RawSection {
    /// Where the section maps, relative to the image base.
    pub(super) rva: u64,
    /// Where its bytes sit in the file.
    pub(super) file_off: u64,
    /// How many of its bytes the file holds.
    pub(super) file_size: u64,
}

/// Reads the section table rows a PE's headers state.
///
/// # Arguments
///
/// * `bytes` - The whole file.
///
/// # Returns
///
/// The rows the file holds, in table order, or `None` for a file without a
/// PE header. A row whose bytes lie outside the file is kept with no file
/// size, so nothing maps into it.
pub(super) fn raw_sections(bytes: &[u8]) -> Option<Vec<RawSection>> {
    let pe = pe_signature(bytes)?;
    let count = usize::from(u16_le(bytes, pe + 6)?);
    let table = pe + 24 + usize::from(u16_le(bytes, pe + 20)?);
    let rows = count.min(bytes.len().saturating_sub(table) / SECTION_ROW);
    let file_len = from_usize(bytes.len());
    (0..rows)
        .map(|i| {
            let row = table + i * SECTION_ROW;
            let file_off = u64::from(u32_le(bytes, row + 20)?);
            let file_size =
                u64::from(u32_le(bytes, row + 16)?).min(file_len.saturating_sub(file_off));
            Some(RawSection {
                rva: u64::from(u32_le(bytes, row + 12)?),
                file_off,
                file_size,
            })
        })
        .collect()
}

/// Tells whether a PE's section table is sound enough to trust a row the
/// end of the file cuts short.
///
/// A truncated download ends inside a section, and its row states more
/// bytes than the file holds; the rows themselves are intact, so the code
/// before the cut is worth keeping. A damaged section count runs the table
/// into whatever follows it, where a row is garbage that may fit the file
/// by chance: `NumberOfSections = 0xfff` on kernel32 named 763 such rows,
/// and clamping them all sent discovery through them for minutes. A table
/// that ends inside the headers and maps its sections in ascending,
/// non-overlapping order is the one a linker wrote; garbage holds neither.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `rows` - The section table as parsed, one entry per row the count states.
/// * `size_of_headers` - `SizeOfHeaders` from the optional header: where
///   the headers, and so the table, must end.
///
/// # Returns
///
/// `true` when the table ends within the headers and the file, and each
/// section's memory extent (its virtual size, or its raw size when that is
/// zero) ends at or before the next one's address.
pub(super) fn sound_section_table(
    bytes: &[u8],
    rows: &[goblin::pe::section_table::SectionTable],
    size_of_headers: u32,
) -> bool {
    let Some(pe) = pe_signature(bytes) else {
        return false;
    };
    let Some(optional) = u16_le(bytes, pe + 20) else {
        return false;
    };
    let table_end = rows
        .len()
        .checked_mul(SECTION_ROW)
        .and_then(|len| len.checked_add(pe + 24 + usize::from(optional)));
    let headers = usize::try_from(size_of_headers).unwrap_or(usize::MAX);
    let extent = |s: &goblin::pe::section_table::SectionTable| {
        u64::from(s.virtual_address)
            + u64::from(if s.virtual_size == 0 {
                s.size_of_raw_data
            } else {
                s.virtual_size
            })
    };
    table_end.is_some_and(|end| end <= headers.min(bytes.len()))
        && rows
            .windows(2)
            .all(|w| extent(&w[0]) <= u64::from(w[1].virtual_address))
}

/// Maps an RVA to the file offset of its byte.
///
/// # Arguments
///
/// * `sections` - The section table rows.
/// * `rva` - An address relative to the image base.
///
/// # Returns
///
/// The offset, or `None` when no row's file bytes cover `rva`.
fn file_offset(sections: &[RawSection], rva: u64) -> Option<usize> {
    sections.iter().find_map(|s| {
        let delta = rva.checked_sub(s.rva)?;
        (delta < s.file_size).then(|| usize::try_from(s.file_off + delta).ok())?
    })
}

/// The entries a PE's import directory reaches before it is refused.
///
/// The parser synthesizes one import per non-zero word of each descriptor's
/// lookup table and, parsing permissively, walks every descriptor the
/// directory reaches: with `.rdata` moved one byte in the file, kernel32's
/// directory named 6.8 million imports of its 844 KB, a gigabyte of them
/// before the analysis began. The descriptors are walked here first, the way
/// the parser walks them, counting the words each table holds until the
/// count passes what the file can hold (one word per import) or
/// [`IMPORTS_MAX`], whichever is less; a sound table ends long before
/// either, so its count is exact and nothing changes for it.
///
/// # Arguments
///
/// * `bytes` - The whole file.
///
/// # Returns
///
/// The count reached when it passed the limit, or `None` when the table
/// is plausible or absent.
pub(super) fn implausible_imports(bytes: &[u8]) -> Option<u64> {
    /// Bytes of one import descriptor.
    const DESCRIPTOR: usize = 20;
    let (entry, plus) = directory_entry(bytes, 1)?;
    let word = if plus { 8 } else { 4 };
    let sections = raw_sections(bytes)?;
    let mut at = file_offset(&sections, u64::from(u32_le(bytes, entry)?))?;
    let limit = from_usize(bytes.len() / word).min(IMPORTS_MAX);
    let mut total = 0u64;
    while let Some(descriptor) = bytes.get(at..at + DESCRIPTOR) {
        let field = |k: usize| u32_le(descriptor, k).unwrap_or(0);
        if field(12) == 0 || field(16) == 0 {
            break;
        }
        let table = file_offset(&sections, u64::from(field(0)))
            .or_else(|| file_offset(&sections, u64::from(field(16))));
        if let Some(off) = table
            && let Some(words) = bytes.get(off..)
        {
            let room = usize::try_from(limit + 1 - total).unwrap_or(usize::MAX);
            total += from_usize(
                words
                    .chunks_exact(word)
                    .take_while(|w| w.iter().any(|b| *b != 0))
                    .take(room)
                    .count(),
            );
            if total > limit {
                return Some(total);
            }
        }
        at += DESCRIPTOR;
    }
    None
}

/// Reads a NUL-terminated name at a file offset.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `at` - The offset of the name's first byte.
///
/// # Returns
///
/// The name, at most 512 bytes, invalid UTF-8 replaced; `None`
/// when the offset is past the end of the file or the name is empty.
pub(super) fn c_name(bytes: &[u8], at: usize) -> Option<String> {
    /// Longest name read.
    const NAME_MAX: usize = 512;
    let rest = bytes.get(at..)?;
    let len = rest
        .iter()
        .take(NAME_MAX)
        .position(|&b| b == 0)
        .unwrap_or(rest.len().min(NAME_MAX));
    (len > 0).then(|| String::from_utf8_lossy(&rest[..len]).into_owned())
}

/// Reads a PE's delay-load import table as imports.
///
/// A DLL linked `/DELAYLOAD` is named in its own directory, not the import
/// directory: its descriptors give the module name, the address table the
/// code calls through and the name table, the same shape as an import
/// descriptor's. Each slot of the address table becomes an import
/// `module!name` (or `module!ORDINAL n`, the import table's spelling) at
/// the slot's address, so a call through it is named as a call through an
/// import slot is. The walk stops at a zeroed descriptor and holds the
/// same total bound the import table does, [`IMPORTS_MAX`].
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `image_base` - The preferred load base: an old descriptor states
///   virtual addresses, a current one relative ones.
/// * `is_64` - Whether the image is PE32+ (eight-byte slots).
///
/// # Returns
///
/// The imports in table order; empty when the image has no delay-load
/// directory or it maps nowhere.
pub(super) fn delay_imports(bytes: &[u8], image_base: u64, is_64: bool) -> Vec<Symbol> {
    /// Bytes of one `ImgDelayDescr`.
    const DESCRIPTOR: usize = 32;
    /// `dlattrRva`: the descriptor's addresses are relative to the base.
    const RVA_ATTR: u32 = 1;
    /// The delay-load directory's slot.
    const DELAY_DIR: usize = 13;
    let mut out = Vec::new();
    let Some((entry, _)) = directory_entry(bytes, DELAY_DIR) else {
        return out;
    };
    let (Some(rva), Some(sections)) = (u32_le(bytes, entry), raw_sections(bytes)) else {
        return out;
    };
    let Some(mut at) = file_offset(&sections, u64::from(rva)).filter(|_| rva != 0) else {
        return out;
    };
    let (word, ordinal_bit) = if is_64 {
        (8u64, 1u64 << 63)
    } else {
        (4, 1 << 31)
    };
    let limit = from_usize(bytes.len() / 4).min(IMPORTS_MAX);
    while let Some(descriptor) = bytes.get(at..at + DESCRIPTOR) {
        let field = |k: usize| u32_le(descriptor, k).unwrap_or(0);
        let (attrs, name, iat, names) = (field(0), field(4), field(12), field(16));
        if name == 0 || iat == 0 {
            break;
        }
        let rva_of = |v: u64| {
            if attrs & RVA_ATTR != 0 {
                Some(v)
            } else {
                v.checked_sub(image_base)
            }
        };
        let module = rva_of(u64::from(name))
            .and_then(|r| file_offset(&sections, r))
            .and_then(|o| c_name(bytes, o))
            .unwrap_or_else(|| "(unnamed)".to_owned());
        let table = rva_of(u64::from(names)).and_then(|r| file_offset(&sections, r));
        if let (Some(iat), Some(table)) = (rva_of(u64::from(iat)), table) {
            for i in 0u64.. {
                if from_usize(out.len()) >= limit {
                    return out;
                }
                let Some(thunk) = usize::try_from(i * word)
                    .ok()
                    .and_then(|k| table.checked_add(k))
                    .and_then(|k| {
                        if is_64 {
                            let b = bytes.get(k..k + 8)?;
                            Some(u64::from_le_bytes(b.try_into().ok()?))
                        } else {
                            u32_le(bytes, k).map(u64::from)
                        }
                    })
                    .filter(|&t| t != 0)
                else {
                    break;
                };
                let import = if thunk & ordinal_bit != 0 {
                    format!("ORDINAL {}", thunk & 0xffff)
                } else {
                    rva_of(u64::from(crate::num::lo32(thunk)))
                        .and_then(|r| file_offset(&sections, r))
                        .and_then(|o| c_name(bytes, o.saturating_add(2)))
                        .unwrap_or_else(|| "(unnamed)".to_owned())
                };
                out.push(Symbol {
                    name: format!("{module}!{import}"),
                    addr: image_base.wrapping_add(iat).wrapping_add(i * word),
                    kind: SymbolKind::Import,
                });
            }
        }
        at += DESCRIPTOR;
    }
    out
}

/// Names a PE's imports by ordinal, which the import table spells
/// `module!ORDINAL n`.
///
/// Each takes the name of the export it is where a table of the system
/// DLLs' exports lists it, else `<module>_ord<n>`
/// ([`crate::hashing::import_ordinal_name`]), so a call to one reads as a
/// C call to a function (`ldap_initW(..)`, `certcli_ord359(..)`).
///
/// # Arguments
///
/// * `symbols` - The program's symbols; its ordinal imports are renamed.
///
/// # Returns
///
/// Each renamed import's slot and ordinal, sorted by slot, for the import
/// hash, which names an import by its ordinal.
pub(super) fn name_ordinal_imports(symbols: &mut [Symbol]) -> Vec<(u64, u16)> {
    let mut out = Vec::new();
    for s in symbols.iter_mut().filter(|s| s.kind == SymbolKind::Import) {
        let Some((dll, func)) = s.name.rsplit_once('!') else {
            continue;
        };
        let Some(n) = func
            .strip_prefix("ORDINAL ")
            .and_then(|n| n.parse::<u16>().ok())
        else {
            continue;
        };
        s.name = format!("{dll}!{}", crate::hashing::import_ordinal_name(dll, n));
        out.push((s.addr, n));
    }
    out.sort_unstable();
    out.dedup_by_key(|(slot, _)| *slot);
    out
}

/// The exports a PE names by ordinal alone, which the parser leaves out.
///
/// The parser reads the exports through the name table, so an
/// address-table entry no name points at, a `NONAME` export reached only
/// by its ordinal, was never listed: a DLL exporting by ordinal showed no
/// exports at all. Each such entry is an export named `Ordinal_<n>` with
/// `n` its ordinal (the address-table index plus the ordinal base), a
/// forwarder when its address holds the forwarding text. Empty slots
/// (address zero) are not exports.
///
/// # Arguments
///
/// * `pe` - The parsed image.
///
/// # Returns
///
/// The ordinal-only exports, in ordinal order.
pub(super) fn ordinal_exports(pe: &goblin::pe::PE<'_>) -> Vec<Symbol> {
    use goblin::pe::export::ExportAddressTableEntry::{ExportRVA, ForwarderRVA};
    let Some(data) = &pe.export_data else {
        return Vec::new();
    };
    let named: BTreeSet<u16> = data.export_ordinal_table.iter().copied().collect();
    let base = u64::from(data.export_directory_table.ordinal_base);
    (0u16..=u16::MAX)
        .zip(&data.export_address_table)
        .filter(|(index, _)| !named.contains(index))
        .filter_map(|(index, entry)| {
            let (rva, kind) = match *entry {
                ExportRVA(rva) => (rva, SymbolKind::Export),
                ForwarderRVA(rva) => (rva, SymbolKind::Forwarder),
            };
            (rva != 0).then(|| Symbol {
                name: format!("Ordinal_{}", base + u64::from(index)),
                addr: pe.image_base.wrapping_add(u64::from(rva)),
                kind,
            })
        })
        .collect()
}

/// A data directory entry zeroed for the length of a parse.
#[derive(Debug, Clone, Copy)]
pub(super) struct Disarmed {
    /// File offset of the entry.
    pub(super) at: usize,
    /// What the entry held.
    pub(super) saved: [u8; DIRECTORY_ENTRY],
    /// The larger of the counts that condemned it.
    pub(super) count: u32,
}

/// Zeroes the export directory entry of a PE whose export table claims more
/// entries than an ordinal can reach, so the parser skips the table.
///
/// The parser sizes the name, ordinal and address tables by the counts the
/// export directory states, each up to the file's own length, and reads
/// the entries one by one until one fails: thirty times the file in
/// transient memory for a directory that lands on garbage. An export is
/// reached by a sixteen-bit ordinal, so a count past [`EXPORTS_MAX`] is a
/// damaged header and the table it describes is not read. The entry goes
/// back once the parse is done ([`Disarmed`]); the computed checksum in
/// [`Headers`](crate::headers::Headers) is taken over the zeroed bytes meanwhile, and the directory
/// list it renders lacks `export`.
///
/// # Arguments
///
/// * `bytes` - The whole file, patched in place.
///
/// # Returns
///
/// What was zeroed, or `None` when the table is plausible or absent.
pub(super) fn disarm_exports(bytes: &mut [u8]) -> Option<Disarmed> {
    let (at, _) = directory_entry(bytes, 0)?;
    let table = file_offset(&raw_sections(bytes)?, u64::from(u32_le(bytes, at)?))?;
    let count = u32_le(bytes, table + 20)?.max(u32_le(bytes, table + 24)?);
    if count <= EXPORTS_MAX {
        return None;
    }
    let slot = bytes.get_mut(at..at + DIRECTORY_ENTRY)?;
    let saved: [u8; DIRECTORY_ENTRY] = slot.try_into().ok()?;
    slot.fill(0);
    Some(Disarmed { at, saved, count })
}

/// `(start, end)` virtual addresses of the code extents an unwind table
/// states, `end` exclusive.
pub(super) type Extents = Vec<(u64, u64)>;

/// Reads an ARM64 image's exception directory (`.pdata`): the extent of
/// every function it declares, and of every fragment.
///
/// An entry states the function's start and either packs its unwind data,
/// length included, into its second word, or points at an `.xdata` record
/// whose header states the length. A packed entry flagged as a fragment
/// describes code with no prologue, a function's separated chunk, which
/// is no function start; an entry with the reserved flag, or whose
/// `.xdata` record does not parse, states no length and is skipped, since a
/// guessed extent would misplace the function's end.
///
/// # Arguments
///
/// * `ex` - The exception directory goblin parsed.
/// * `sections` - The section table, to map an `.xdata` record's address.
/// * `base` - The image base the addresses are relative to.
///
/// # Returns
///
/// `(functions, fragments)`: `(start, end)` virtual addresses, the
/// fragments sorted. Reading the directory can panic in goblin on a
/// damaged file, so the caller runs this under [`caught`].
pub(super) fn arm64_pdata(
    ex: &goblin::pe::exception::ExceptionData<'_>,
    sections: &[goblin::pe::section_table::SectionTable],
    base: u64,
) -> (Extents, Extents) {
    use goblin::pe::exception::{
        ARM64_PDATA_PACKED_UNWIND_FRAGMENT, ARM64_PDATA_PACKED_UNWIND_FUNCTION,
        ARM64_PDATA_REF_TO_FULL_XDATA,
    };
    let mut functions = Vec::new();
    let mut fragments = Vec::new();
    for rf in ex.functions_arm64().flatten() {
        let (len, fragment) = match rf.flag() {
            ARM64_PDATA_PACKED_UNWIND_FUNCTION => (rf.function_length(), false),
            ARM64_PDATA_PACKED_UNWIND_FRAGMENT => (rf.function_length(), true),
            ARM64_PDATA_REF_TO_FULL_XDATA => match ex.get_unwind_info_arm64(rf, sections) {
                Some(Ok(info)) => (info.header.function_length(), false),
                Some(Err(_)) | None => continue,
            },
            _ => continue,
        };
        let Some(start) = base.checked_add(u64::from(rf.begin_address)) else {
            continue;
        };
        let Some(end) = start.checked_add(u64::from(len)).filter(|&end| end > start) else {
            continue;
        };
        let extent = (start, end);
        if fragment {
            fragments.push(extent);
        } else {
            functions.push(extent);
        }
    }
    fragments.sort_unstable();
    (functions, fragments)
}
