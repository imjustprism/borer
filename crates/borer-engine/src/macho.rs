//! Mach-O loading: what one image says about itself, out of a thin file
//! or one slice of a fat one.
//!
//! The image's segments give its sections, its symbol table the exports
//! and locals, the indirect symbols the import slots, the linker's
//! function starts and compact unwind table the function ranges, and the
//! load commands the header facts.
//!
//! A Mach-O says more about its code than an ELF does: ld64 writes
//! `LC_FUNCTION_STARTS`, every function's entry as a ULEB128 delta from
//! the one before, and a stripped image keeps it, so the function starts
//! are a fact the way an x64 PE's exception table is. Import slots come
//! from the indirect symbol table: a `__got` or `__la_symbol_ptr` section
//! names, pointer by pointer, the symbol the loader binds there, and a
//! stub that jumps through the pointer takes that name as a PE's import
//! thunk does. A fat file holds one image per architecture; the x86-64
//! slice is the one analyzed, the arm64 one when there is no other. The
//! image's fixups ([`crate::dyld`]) relocate its pointers and name every
//! slot a bind fills after its import, data words as well as `__got`.

use std::collections::{BTreeMap, BTreeSet};

use goblin::mach::load_command::CommandVariant;
use goblin::mach::{Mach, MachO};

use crate::headers::Headers;
use crate::num::{from_usize, u16_le, u32_le, u64_le};
use crate::program::{Arch, FileOff, Fit, Section, Symbol, SymbolKind, Va, fit_sections};

/// `CPU_TYPE_X86`.
const CPU_X86: u32 = 7;
/// `CPU_TYPE_X86_64`.
const CPU_X86_64: u32 = 7 | 0x0100_0000;
/// `CPU_TYPE_ARM64`.
const CPU_ARM64: u32 = 12 | 0x0100_0000;
/// `CPU_TYPE_ARM`: 32-bit ARM (armv7).
const CPU_ARM: u32 = 12;
/// `N_ARM_THUMB_DEF`: the symbol names T32 code.
const N_ARM_THUMB_DEF: u16 = 0x0008;
/// `MH_PIE`: the image loads at a random base.
const MH_PIE: u32 = 0x0020_0000;
/// `MH_NO_HEAP_EXECUTION`: the heap is mapped non-executable.
const MH_NO_HEAP_EXECUTION: u32 = 0x0100_0000;
/// The section type in a section's flags.
const SECTION_TYPE: u32 = 0xff;
/// Section types the file holds no bytes for.
const ZEROFILL: [u32; 3] = [0x1, 0xc, 0x12];
/// `S_NON_LAZY_SYMBOL_POINTERS`: a `__got`.
const NON_LAZY_POINTERS: u32 = 0x6;
/// `S_LAZY_SYMBOL_POINTERS`: a `__la_symbol_ptr`.
const LAZY_POINTERS: u32 = 0x7;
/// Section attributes that say the section holds instructions.
const INSTRUCTIONS: u32 = 0x8000_0000 | 0x0000_0400;
/// `VM_PROT_READ`, `VM_PROT_WRITE`, `VM_PROT_EXECUTE`.
const PROT: (u32, u32, u32) = (1, 2, 4);
/// Indirect symbol entries that name no symbol.
const INDIRECT_NONE: u32 = 0xc000_0000;
/// `N_STAB`: a debugger symbol.
const N_STAB: u8 = 0xe0;
/// `N_TYPE`: the symbol's kind.
const N_TYPE: u8 = 0x0e;
/// `N_SECT`: defined in a section.
const N_SECT: u8 = 0x0e;
/// `N_EXT`: external.
const N_EXT: u8 = 0x01;
/// Most function starts read.
const STARTS_MAX: usize = 1 << 22;
/// `UNWIND_SECTION_VERSION`: the one `__unwind_info` layout there is.
const UNWIND_VERSION: u32 = 1;
/// `UNWIND_SECOND_LEVEL_REGULAR`: a page of `(function offset, encoding)`
/// pairs, eight bytes each.
const UNWIND_REGULAR: u32 = 2;
/// `UNWIND_SECOND_LEVEL_COMPRESSED`: a page of four-byte entries, each a
/// function's offset from the page's first function in its low 24 bits.
const UNWIND_COMPRESSED: u32 = 3;
/// The offset bits of a compressed second-level entry.
const UNWIND_OFFSET_MASK: u32 = 0x00ff_ffff;
/// Bytes of one first-level index entry: the first function's offset, the
/// page's offset and the LSDA array's offset.
const UNWIND_INDEX_ENTRY: usize = 12;
/// Most slots one import is named at through its binds: a `__got` slot
/// and a few data words are real, a table of thousands names nothing new.
const SLOTS_PER_IMPORT: usize = 16;

/// What one Mach-O image says about itself.
pub(crate) struct Loaded {
    /// The machine.
    pub arch: Arch,
    /// Whether it is a 64-bit image.
    pub is_64: bool,
    /// The entry point, when the image has one.
    pub entry: Option<u64>,
    /// Where `__TEXT` is mapped.
    pub image_base: u64,
    /// The sections, named `__TEXT,__text`.
    pub sections: Vec<Section>,
    /// The symbols: exports, locals and the import slots.
    pub symbols: Vec<Symbol>,
    /// `[start, next start)` for each function start the linker recorded.
    pub function_ranges: Vec<(u64, u64)>,
    /// The header facts.
    pub headers: Headers,
    /// What fitting the sections to the file dropped or cut short.
    pub fit: Fit,
    /// What the strict parse of a fat file's slice said when only the
    /// lossy parse read it.
    pub lenient: Option<String>,
    /// The image as its fixups leave it ([`crate::dyld`]).
    pub relocs: crate::reloc::Relocs,
}

/// A section's raw header, read from its segment command.
struct RawSection {
    /// `segname,sectname`.
    name: String,
    /// Where it is mapped.
    addr: u64,
    /// Its size.
    size: u64,
    /// Its file offset in the whole file.
    offset: u64,
    /// Its flags.
    flags: u32,
    /// `reserved1`: for a pointer section, its first indirect symbol.
    reserved1: u32,
    /// The segment's protection.
    prot: u32,
}

/// Loads the image a file holds, or the slice of a fat file worth
/// analyzing.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `mach` - The file parsed.
///
/// # Returns
///
/// The image.
///
/// # Errors
///
/// When a fat file's architecture table names no slice, the chosen slice
/// runs past the end of the file, or it does not parse even lossily, each
/// said in words: a slice past the end loaded as an image of no
/// architecture, with nothing to say why.
pub(crate) fn load(file: &[u8], mach: &Mach<'_>) -> anyhow::Result<Loaded> {
    match mach {
        Mach::Binary(m) => Ok(image(file, m, 0)),
        Mach::Fat(multi) => {
            let arches: Vec<goblin::mach::fat::FatArch> =
                multi.iter_arches().map_while(Result::ok).collect();
            let pick = arches
                .iter()
                .position(|a| a.cputype == CPU_X86_64)
                .or_else(|| arches.iter().position(|a| a.cputype == CPU_ARM64))
                .or_else(|| arches.iter().position(|a| a.cputype == CPU_X86))
                .unwrap_or(0);
            let arch = arches.get(pick).ok_or_else(|| {
                anyhow::anyhow!(
                    "a fat Mach-O file whose architecture table names no slice it can read: it is truncated or damaged"
                )
            })?;
            let name = match arch.cputype {
                CPU_X86_64 => "x86-64",
                CPU_ARM64 => "arm64",
                CPU_X86 => "x86",
                _ => "first",
            };
            let start = u64::from(arch.offset);
            let end = start.saturating_add(u64::from(arch.size));
            let slice = usize::try_from(start)
                .ok()
                .zip(usize::try_from(end).ok())
                .and_then(|(s, e)| file.get(s..e))
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "the fat file's {name} slice at {start:#x} runs to {end:#x}, past the end of the file at {:#x}: it is truncated",
                        file.len()
                    )
                })?;
            let (m, lenient) = match MachO::parse(slice, 0) {
                Ok(m) => (m, None),
                Err(strict) => {
                    let m = MachO::parse_lossy(slice, 0).map_err(|lossy| {
                        anyhow::anyhow!(
                            "the fat file's {name} slice at {start:#x} does not parse ({strict}; lossy: {lossy})"
                        )
                    })?;
                    (
                        m,
                        Some(format!(
                            "the {name} slice's headers do not all parse ({strict}); read leniently, what does not parse is skipped"
                        )),
                    )
                }
            };
            let mut loaded = image(file, &m, crate::num::saturating_usize(start));
            loaded.lenient = lenient;
            Ok(loaded)
        }
    }
}

/// A NUL-padded 16-byte name.
///
/// # Arguments
///
/// * `raw` - The bytes.
fn name16(raw: &[u8]) -> String {
    let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

/// Reads the section headers of every segment command.
///
/// A segment's section headers follow it inside its own load command, so
/// the command's size bounds how many there are, whatever `nsects` says: a
/// count past that read the next load commands as sections, phantoms with
/// sizes of gigabytes that became fake code.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `m` - The image.
/// * `base` - Where the image begins in the file.
fn raw_sections(file: &[u8], m: &MachO<'_>, base: usize) -> Vec<RawSection> {
    let mut out = Vec::new();
    for lc in &m.load_commands {
        let (nsects, prot, cmdsize, header, entry, wide) = match &lc.command {
            CommandVariant::Segment64(s) => {
                (s.nsects, s.initprot, s.cmdsize, 72usize, 80usize, true)
            }
            CommandVariant::Segment32(s) => {
                (s.nsects, s.initprot, s.cmdsize, 56usize, 68usize, false)
            }
            _ => continue,
        };
        let room = usize::try_from(cmdsize).unwrap_or(0).saturating_sub(header) / entry;
        let Some(first) = base
            .checked_add(lc.offset)
            .and_then(|o| o.checked_add(header))
        else {
            continue;
        };
        for k in 0..usize::try_from(nsects).unwrap_or(0).min(room).min(4096) {
            let Some(at) = first.checked_add(k * entry) else {
                break;
            };
            let Some(raw) = at.checked_add(entry).and_then(|end| file.get(at..end)) else {
                break;
            };
            let sect = name16(&raw[..16]);
            let segment = name16(&raw[16..32]);
            let (addr, size, offset, flags, reserved1) = if wide {
                (
                    u64_le(raw, 32),
                    u64_le(raw, 40),
                    u32_le(raw, 48).map(u64::from),
                    u32_le(raw, 64),
                    u32_le(raw, 68),
                )
            } else {
                (
                    u32_le(raw, 32).map(u64::from),
                    u32_le(raw, 36).map(u64::from),
                    u32_le(raw, 40).map(u64::from),
                    u32_le(raw, 56),
                    u32_le(raw, 60),
                )
            };
            let (Some(addr), Some(size), Some(offset), Some(flags), Some(reserved1)) =
                (addr, size, offset, flags, reserved1)
            else {
                break;
            };
            out.push(RawSection {
                name: format!("{segment},{sect}"),
                addr,
                size,
                offset: offset.saturating_add(from_usize(base)),
                flags,
                reserved1,
                prot,
            });
        }
    }
    out
}

/// Where the `__TEXT` segment is mapped: the image base.
///
/// # Arguments
///
/// * `m` - The image.
fn text_base(m: &MachO<'_>) -> u64 {
    let mut lowest: Option<u64> = None;
    for lc in &m.load_commands {
        let (name, vmaddr, filesize) = match &lc.command {
            CommandVariant::Segment64(s) => (name16(&s.segname), s.vmaddr, s.filesize),
            CommandVariant::Segment32(s) => (
                name16(&s.segname),
                u64::from(s.vmaddr),
                u64::from(s.filesize),
            ),
            _ => continue,
        };
        if name == "__TEXT" {
            return vmaddr;
        }
        if filesize > 0 {
            lowest = Some(lowest.map_or(vmaddr, |l: u64| l.min(vmaddr)));
        }
    }
    lowest.unwrap_or(0)
}

/// Reads the ULEB128 at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset, moved past the value.
pub(crate) fn uleb(data: &[u8], at: &mut usize) -> Option<u64> {
    let mut value: u64 = 0;
    let mut shift = 0u32;
    loop {
        let b = *data.get(*at)?;
        *at += 1;
        if shift < 64 {
            value |= u64::from(b & 0x7f) << shift;
        }
        shift += 7;
        if b & 0x80 == 0 {
            return Some(value);
        }
    }
}

/// The function starts the linker recorded, as addresses.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `m` - The image.
/// * `base` - Where the image begins in the file.
/// * `text` - Where `__TEXT` is mapped, which the first delta counts from.
fn function_starts(file: &[u8], m: &MachO<'_>, base: usize, text: u64) -> Vec<u64> {
    let mut out = Vec::new();
    for lc in &m.load_commands {
        let CommandVariant::FunctionStarts(l) = &lc.command else {
            continue;
        };
        let Some(start) = base.checked_add(usize::try_from(l.dataoff).unwrap_or(usize::MAX)) else {
            continue;
        };
        let Some(data) = file
            .get(start..start.saturating_add(usize::try_from(l.datasize).unwrap_or(usize::MAX)))
        else {
            continue;
        };
        let mut at = 0;
        let mut addr = text;
        while let Some(delta) = uleb(data, &mut at) {
            if delta == 0 || out.len() >= STARTS_MAX {
                break;
            }
            addr = addr.wrapping_add(delta);
            out.push(addr);
        }
    }
    out
}

/// The function starts an image's `__unwind_info` section lists.
///
/// ld64's compact unwind table is a first-level index of pages, each entry
/// naming the first function its page covers, and second-level pages,
/// regular or compressed, naming every function's offset from `__TEXT`.
/// The linker folds a run of functions that share one encoding into the
/// first of them, so the table names a subset of the starts
/// `LC_FUNCTION_STARTS` lists, but each one it names is a function start,
/// and it is there when that command is not. The index's last entry is a
/// sentinel saying where the last function ends; it names no page.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `raw` - The image's section headers.
/// * `text` - Where `__TEXT` is mapped, which every offset counts from.
///
/// # Returns
///
/// The starts in table order, at most [`STARTS_MAX`]; none without a
/// table of the one version there is.
fn unwind_starts(file: &[u8], raw: &[RawSection], text: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let Some(data) = raw
        .iter()
        .find(|s| s.name == "__TEXT,__unwind_info")
        .and_then(|s| {
            let at = usize::try_from(s.offset).ok()?;
            file.get(at..at.checked_add(usize::try_from(s.size).ok()?)?)
        })
    else {
        return out;
    };
    let wide = |v: u32| usize::try_from(v).unwrap_or(usize::MAX);
    let (Some(UNWIND_VERSION), Some(index), Some(count)) =
        (u32_le(data, 0), u32_le(data, 20), u32_le(data, 24))
    else {
        return out;
    };
    for i in 0..wide(count) {
        if out.len() >= STARTS_MAX {
            break;
        }
        let Some(entry) = i
            .checked_mul(UNWIND_INDEX_ENTRY)
            .and_then(|o| o.checked_add(wide(index)))
        else {
            break;
        };
        let (Some(first), Some(page)) = (
            u32_le(data, entry),
            entry.checked_add(4).and_then(|at| u32_le(data, at)),
        ) else {
            break;
        };
        if page == 0 {
            continue;
        }
        out.push(text.wrapping_add(u64::from(first)));
        let page = wide(page);
        let (Some(kind), Some(entries), Some(n)) = (
            u32_le(data, page),
            page.checked_add(4).and_then(|at| u16_le(data, at)),
            page.checked_add(6).and_then(|at| u16_le(data, at)),
        ) else {
            continue;
        };
        let entries = page.saturating_add(usize::from(entries));
        for k in 0..usize::from(n) {
            let offset = match kind {
                UNWIND_REGULAR => u32_le(data, entries.saturating_add(k * 8)),
                UNWIND_COMPRESSED => u32_le(data, entries.saturating_add(k * 4))
                    .map(|w| first.wrapping_add(w & UNWIND_OFFSET_MASK)),
                _ => None,
            };
            let Some(offset) = offset else {
                break;
            };
            out.push(text.wrapping_add(u64::from(offset)));
            if out.len() >= STARTS_MAX {
                break;
            }
        }
    }
    out
}

/// A symbol's name as borer shows it: the C underscore dropped, which
/// leaves a C++ name demanglable.
///
/// # Arguments
///
/// * `name` - The name as the table has it.
fn plain(name: &str) -> &str {
    name.strip_prefix('_').unwrap_or(name)
}

/// Bytes of the smallest symbol table entry (a 32-bit `nlist`): a file
/// of `n` bytes holds at most `n / NLIST_MIN` symbols, whatever count its
/// header states.
const NLIST_MIN: usize = 12;

/// Reads one image.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `m` - The image.
/// * `base` - Where the image begins in the file: zero for a thin file.
fn image(file: &[u8], m: &MachO<'_>, base: usize) -> Loaded {
    let arch = match m.header.cputype {
        CPU_X86_64 => Arch::X86_64,
        CPU_X86 => Arch::X86,
        CPU_ARM64 => Arch::Arm64,
        CPU_ARM => Arch::Arm,
        _ => Arch::Unknown,
    };
    let is_64 = m.is_64;
    let word: u64 = if is_64 { 8 } else { 4 };
    let text = text_base(m);
    let raw = raw_sections(file, m, base);
    let mut sections = Vec::new();
    for s in &raw {
        let kind = s.flags & SECTION_TYPE;
        let holds_bytes = !ZEROFILL.contains(&kind);
        sections.push(Section {
            name: s.name.clone(),
            va: Va(s.addr),
            vsize: s.size,
            file_off: FileOff(if holds_bytes { s.offset } else { 0 }),
            file_size: if holds_bytes { s.size } else { 0 },
            readable: s.prot & PROT.0 != 0,
            writable: s.prot & PROT.1 != 0,
            executable: s.prot & PROT.2 != 0 && s.flags & INSTRUCTIONS != 0,
        });
    }
    let fit = fit_sections(&mut sections, from_usize(file.len()));

    let mut symbols: Vec<Symbol> = Vec::new();
    let mut seen: BTreeSet<(u64, String)> = BTreeSet::new();
    let mut named = 0usize;
    if let Some(table) = &m.symbols {
        for (name, nlist) in table
            .iter()
            .take(file.len() / NLIST_MIN)
            .filter_map(Result::ok)
        {
            if nlist.n_type & N_STAB != 0 || name.is_empty() {
                continue;
            }
            named += 1;
            if nlist.n_type & N_TYPE != N_SECT || nlist.n_value == 0 {
                continue;
            }
            let kind = if nlist.n_type & N_EXT != 0 {
                SymbolKind::Export
            } else {
                SymbolKind::Local
            };
            if seen.insert((nlist.n_value, plain(name).to_owned())) {
                let thumb = arch == Arch::Arm && nlist.n_desc & N_ARM_THUMB_DEF != 0;
                symbols.push(Symbol {
                    name: plain(name).to_owned(),
                    addr: nlist.n_value | u64::from(thumb),
                    kind,
                });
            }
        }
        let indirect = m.load_commands.iter().find_map(|lc| match &lc.command {
            CommandVariant::Dysymtab(d) => Some((
                usize::try_from(d.indirectsymoff).unwrap_or(usize::MAX),
                usize::try_from(d.nindirectsyms).unwrap_or(usize::MAX),
            )),
            _ => None,
        });
        if let Some((off, count)) = indirect {
            let at = |i: usize| -> Option<u32> {
                (i < count)
                    .then(|| u32_le(file, base.checked_add(off)?.checked_add(i.checked_mul(4)?)?))?
            };
            for s in raw
                .iter()
                .filter(|s| matches!(s.flags & SECTION_TYPE, NON_LAZY_POINTERS | LAZY_POINTERS))
            {
                let slots = usize::try_from(s.size / word).unwrap_or(0).min(1 << 20);
                for i in 0..slots {
                    let Some(index) = usize::try_from(s.reserved1)
                        .unwrap_or(usize::MAX)
                        .checked_add(i)
                        .and_then(at)
                    else {
                        break;
                    };
                    if index & INDIRECT_NONE != 0 {
                        continue;
                    }
                    let Ok((name, _)) = table.get(usize::try_from(index).unwrap_or(usize::MAX))
                    else {
                        continue;
                    };
                    let slot = s.addr.wrapping_add(from_usize(i) * word);
                    if !name.is_empty() && seen.insert((slot, plain(name).to_owned())) {
                        symbols.push(Symbol {
                            name: plain(name).to_owned(),
                            addr: slot,
                            kind: SymbolKind::Import,
                        });
                    }
                }
            }
        }
    }

    let chain_starts = raw
        .iter()
        .find(|s| s.name == "__TEXT,__chain_starts")
        .and_then(|s| {
            let at = usize::try_from(s.offset).ok()?;
            file.get(at..at.checked_add(usize::try_from(s.size).ok()?)?)
        });
    let relocs = crate::dyld::read(
        file,
        m,
        base,
        text,
        &sections,
        chain_starts,
        m.libs.len().saturating_sub(1),
    );
    let mut named_slots: BTreeMap<usize, usize> = BTreeMap::new();
    for b in &relocs.binds {
        let (Some(import), slots) = (
            relocs.imports.get(b.import),
            named_slots.entry(b.import).or_default(),
        ) else {
            continue;
        };
        let name = plain(&import.name);
        if *slots < SLOTS_PER_IMPORT && seen.insert((b.slot, name.to_owned())) {
            *slots += 1;
            symbols.push(Symbol {
                name: name.to_owned(),
                addr: b.slot,
                kind: SymbolKind::Import,
            });
        }
    }

    let code = |va: u64| {
        sections
            .iter()
            .find(|s| s.executable && va >= s.va.0 && va < s.va.0.saturating_add(s.vsize))
    };
    let mut starts: Vec<u64> = function_starts(file, m, base, text)
        .into_iter()
        .chain(unwind_starts(file, &raw, text))
        .filter(|&va| code(va).is_some())
        .collect();
    starts.sort_unstable();
    starts.dedup();
    let function_ranges: Vec<(u64, u64)> = starts
        .iter()
        .enumerate()
        .filter_map(|(i, &va)| {
            let section = code(va)?;
            let end = starts
                .get(i + 1)
                .copied()
                .filter(|&n| n < section.va.0.saturating_add(section.vsize))
                .unwrap_or(section.va.0.saturating_add(section.vsize));
            Some((va, end))
        })
        .collect();

    let entry = m
        .load_commands
        .iter()
        .find_map(|lc| match &lc.command {
            CommandVariant::Main(e) => Some(text.wrapping_add(e.entryoff)),
            _ => None,
        })
        .or_else(|| (m.entry != 0).then_some(m.entry));

    let kind = match m.header.filetype {
        0x1 => "object",
        0x2 => "executable",
        0x6 => "dylib",
        0x7 => "dylinker",
        0x8 => "bundle",
        0x9 => "dylib stub",
        0xb => "kext bundle",
        _ => "other",
    };
    let mut headers = Headers {
        kind: Some(kind),
        ..Headers::default()
    };
    if m.header.flags & MH_PIE != 0 {
        headers.mitigations.push("pie");
    } else if m.header.filetype == 0x2 {
        headers.missing.push("no-pie");
    }
    if m.header.flags & MH_NO_HEAP_EXECUTION != 0 {
        headers.mitigations.push("nx");
    }
    headers.libraries = m.libs.iter().skip(1).map(|l| (*l).to_owned()).collect();
    headers.stripped = Some(named == 0);
    headers.unwind_functions = function_ranges.len();
    for lc in &m.load_commands {
        match &lc.command {
            CommandVariant::Uuid(u) => {
                let g = u.uuid;
                let hex = |r: std::ops::Range<usize>| {
                    g[r].iter().map(|b| format!("{b:02X}")).collect::<String>()
                };
                headers.debug_id = Some(format!(
                    "uuid {}-{}-{}-{}-{}",
                    hex(0..4),
                    hex(4..6),
                    hex(6..8),
                    hex(8..10),
                    hex(10..16)
                ));
            }
            CommandVariant::CodeSignature(_) => headers.signed = Some(true),
            CommandVariant::EncryptionInfo32(e) => headers.fairplay = Some(e.cryptid != 0),
            CommandVariant::EncryptionInfo64(e) => headers.fairplay = Some(e.cryptid != 0),
            CommandVariant::LoadDylinker(d) => {
                let at = base
                    .saturating_add(lc.offset)
                    .saturating_add(usize::try_from(d.name).unwrap_or(usize::MAX));
                if let Some(rest) = file.get(at..) {
                    let end = rest.iter().position(|&b| b == 0).unwrap_or(rest.len());
                    headers.interpreter =
                        Some(String::from_utf8_lossy(&rest[..end.min(256)]).into_owned());
                }
            }
            CommandVariant::BuildVersion(b) => {
                headers.subsystem = Some(match b.platform {
                    1 => "macOS",
                    2 => "iOS",
                    3 => "tvOS",
                    4 => "watchOS",
                    5 => "bridgeOS",
                    6 => "Mac Catalyst",
                    7 => "iOS simulator",
                    8 => "tvOS simulator",
                    9 => "watchOS simulator",
                    10 => "DriverKit",
                    11 => "visionOS",
                    12 => "visionOS simulator",
                    _ => "other",
                });
                let first = base.saturating_add(lc.offset).saturating_add(24);
                for k in 0..usize::try_from(b.ntools).unwrap_or(0).min(16) {
                    let at = first.saturating_add(k * 8);
                    if u32_le(file, at) == Some(3)
                        && let Some(v) = at.checked_add(4).and_then(|a| u32_le(file, a))
                    {
                        headers.linker =
                            Some(format!("ld {}.{}.{}", v >> 16, (v >> 8) & 0xff, v & 0xff));
                    }
                }
            }
            _ => {}
        }
    }
    Loaded {
        arch,
        is_64,
        entry,
        image_base: text,
        sections,
        symbols,
        function_ranges,
        headers,
        fit,
        lenient: None,
        relocs,
    }
}

#[cfg(test)]
mod tests {
    use goblin::mach::MachO;

    use super::{SymbolKind, image};

    /// Builds a 64-bit Mach-O image whose one `__DATA,__got` section sits
    /// at the top of the address space and names its slots through the
    /// indirect symbol table, or fills it past the image's parts.
    ///
    /// # Arguments
    ///
    /// * `addr` - The `__got` section's address.
    ///
    /// # Panics
    ///
    /// When `addr` does not fit the header's field.
    fn got_image(addr: u64) -> Vec<u8> {
        let str_at = 0x130usize;
        let ind_at = 0x138usize;
        let got_at = 0x140usize;
        let mut f = Vec::new();
        f.extend_from_slice(&0xfeed_facf_u32.to_le_bytes());
        f.extend_from_slice(&0x0100_0007_u32.to_le_bytes());
        f.extend_from_slice(&3u32.to_le_bytes());
        f.extend_from_slice(&6u32.to_le_bytes());
        f.extend_from_slice(&3u32.to_le_bytes());
        f.extend_from_slice(&256u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 8]);
        f.extend_from_slice(&0x19u32.to_le_bytes());
        f.extend_from_slice(&152u32.to_le_bytes());
        let mut segname = [0u8; 16];
        segname[..6].copy_from_slice(b"__DATA");
        f.extend_from_slice(&segname);
        f.extend_from_slice(&0u64.to_le_bytes());
        f.extend_from_slice(&0x1000u64.to_le_bytes());
        f.extend_from_slice(&u64::try_from(got_at).unwrap().to_le_bytes());
        f.extend_from_slice(&16u64.to_le_bytes());
        f.extend_from_slice(&1u32.to_le_bytes());
        f.extend_from_slice(&3u32.to_le_bytes());
        f.extend_from_slice(&1u32.to_le_bytes());
        f.extend_from_slice(&0u32.to_le_bytes());
        let mut sectname = [0u8; 16];
        sectname[..5].copy_from_slice(b"__got");
        f.extend_from_slice(&sectname);
        f.extend_from_slice(&segname);
        f.extend_from_slice(&addr.to_le_bytes());
        f.extend_from_slice(&16u64.to_le_bytes());
        f.extend_from_slice(&u32::try_from(got_at).unwrap().to_le_bytes());
        f.extend_from_slice(&3u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 8]);
        f.extend_from_slice(&6u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 12]);
        f.extend_from_slice(&2u32.to_le_bytes());
        f.extend_from_slice(&24u32.to_le_bytes());
        f.extend_from_slice(&0x120u32.to_le_bytes());
        f.extend_from_slice(&1u32.to_le_bytes());
        f.extend_from_slice(&u32::try_from(str_at).unwrap().to_le_bytes());
        f.extend_from_slice(&6u32.to_le_bytes());
        f.extend_from_slice(&0xbu32.to_le_bytes());
        f.extend_from_slice(&80u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 48]);
        f.extend_from_slice(&u32::try_from(ind_at).unwrap().to_le_bytes());
        f.extend_from_slice(&2u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 16]);
        f.extend_from_slice(&1u32.to_le_bytes());
        f.push(0x01);
        f.push(0);
        f.extend_from_slice(&0u16.to_le_bytes());
        f.extend_from_slice(&0u64.to_le_bytes());
        f.extend_from_slice(b"\0_imp\0");
        f.extend_from_slice(&[0u8; 2]);
        f.extend_from_slice(&0u32.to_le_bytes());
        f.extend_from_slice(&0u32.to_le_bytes());
        f.extend_from_slice(&[0u8; 16]);
        f
    }

    /// A `__got` at the top of the address space names both its slots: the
    /// second slot's address is the section's address plus the word width,
    /// which leaves the 64-bit space rather than overflowing the sum.
    ///
    /// # Panics
    ///
    /// When the image does not parse or a slot goes unnamed.
    #[test]
    fn a_got_at_the_top_of_the_space_names_its_slots() {
        let file = got_image(u64::MAX);
        let m = MachO::parse(&file, 0).expect("the image parses");
        let loaded = image(&file, &m, 0);
        let slots: Vec<u64> = loaded
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import)
            .map(|s| s.addr)
            .collect();
        assert_eq!(slots, vec![u64::MAX, 7], "both slots are named");
    }

    /// A `__got` anywhere else still names its slots, unwrapped.
    ///
    /// # Panics
    ///
    /// When the image does not parse or a slot goes unnamed.
    #[test]
    fn a_got_away_from_the_top_names_its_slots() {
        let file = got_image(0x1000);
        let m = MachO::parse(&file, 0).expect("the image parses");
        let loaded = image(&file, &m, 0);
        let slots: Vec<u64> = loaded
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import)
            .map(|s| s.addr)
            .collect();
        assert_eq!(slots, vec![0x1000, 0x1008], "both slots are named");
    }
}
