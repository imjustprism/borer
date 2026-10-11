//! Mach-O loading: what one image says about itself, out of a thin file
//! or one slice of a fat one.
//!
//! The image's segments give its sections, its symbol table the exports
//! and locals, the indirect symbols the import slots, the linker's
//! function starts the function ranges, and the load commands the header
//! facts.
//!
//! A Mach-O says more about its code than an ELF does: ld64 writes
//! `LC_FUNCTION_STARTS`, every function's entry as a ULEB128 delta from
//! the one before, and a stripped image keeps it, so the function starts
//! are a fact the way an x64 PE's exception table is. Import slots come
//! from the indirect symbol table: a `__got` or `__la_symbol_ptr` section
//! names, pointer by pointer, the symbol the loader binds there, and a
//! stub that jumps through the pointer takes that name as a PE's import
//! thunk does. A fat file holds one image per architecture; the x86-64
//! slice is the one analyzed, the arm64 one when there is no other.

use std::collections::BTreeSet;

use goblin::mach::load_command::CommandVariant;
use goblin::mach::{Mach, MachO};

use crate::headers::Headers;
use crate::program::{Arch, Fit, Section, Symbol, SymbolKind, fit_sections};

/// `CPU_TYPE_X86`.
const CPU_X86: u32 = 7;
/// `CPU_TYPE_X86_64`.
const CPU_X86_64: u32 = 7 | 0x0100_0000;
/// `CPU_TYPE_ARM64`.
const CPU_ARM64: u32 = 12 | 0x0100_0000;
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
                multi.iter_arches().filter_map(Result::ok).collect();
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

/// Reads a little-endian `u32` at `at` in `file`.
///
/// # Arguments
///
/// * `file` - The file.
/// * `at` - The offset.
fn u32_at(file: &[u8], at: usize) -> Option<u32> {
    let b = file.get(at..at.checked_add(4)?)?;
    Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

/// Reads a little-endian `u64` at `at` in `file`.
///
/// # Arguments
///
/// * `file` - The file.
/// * `at` - The offset.
fn u64_at(file: &[u8], at: usize) -> Option<u64> {
    let b = file.get(at..at.checked_add(8)?)?;
    Some(u64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
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
            let Some(raw) = file.get(at..at + entry) else {
                break;
            };
            let sect = name16(&raw[..16]);
            let segment = name16(&raw[16..32]);
            let (addr, size, offset, flags, reserved1) = if wide {
                (
                    u64_at(raw, 32),
                    u64_at(raw, 40),
                    u32_at(raw, 48).map(u64::from),
                    u32_at(raw, 64),
                    u32_at(raw, 68),
                )
            } else {
                (
                    u32_at(raw, 32).map(u64::from),
                    u32_at(raw, 36).map(u64::from),
                    u32_at(raw, 40).map(u64::from),
                    u32_at(raw, 56),
                    u32_at(raw, 60),
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
                offset: offset.saturating_add(base as u64),
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
fn uleb(data: &[u8], at: &mut usize) -> Option<u64> {
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
        let Some(start) = base.checked_add(l.dataoff as usize) else {
            continue;
        };
        let Some(data) = file.get(start..start.saturating_add(l.datasize as usize)) else {
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

/// A symbol's name as borer shows it: the C underscore dropped, which
/// leaves a C++ name demanglable.
///
/// # Arguments
///
/// * `name` - The name as the table has it.
fn plain(name: &str) -> &str {
    name.strip_prefix('_').unwrap_or(name)
}

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
            va: s.addr,
            vsize: s.size,
            file_off: if holds_bytes { s.offset } else { 0 },
            file_size: if holds_bytes { s.size } else { 0 },
            readable: s.prot & PROT.0 != 0,
            writable: s.prot & PROT.1 != 0,
            executable: s.prot & PROT.2 != 0 && s.flags & INSTRUCTIONS != 0,
        });
    }
    let fit = fit_sections(&mut sections, crate::num::from_usize(file.len()));

    let mut symbols: Vec<Symbol> = Vec::new();
    let mut seen: BTreeSet<(u64, String)> = BTreeSet::new();
    let mut named = 0usize;
    if let Some(table) = &m.symbols {
        for (name, nlist) in table.iter().filter_map(Result::ok) {
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
                symbols.push(Symbol {
                    name: plain(name).to_owned(),
                    addr: nlist.n_value,
                    kind,
                });
            }
        }
        // The pointer sections: each slot's symbol is in the indirect table.
        let indirect = m.load_commands.iter().find_map(|lc| match &lc.command {
            CommandVariant::Dysymtab(d) => {
                Some((d.indirectsymoff as usize, d.nindirectsyms as usize))
            }
            _ => None,
        });
        if let Some((off, count)) = indirect {
            let at = |i: usize| -> Option<u32> {
                (i < count).then(|| u32_at(file, base.checked_add(off)?.checked_add(i * 4)?))?
            };
            for s in raw
                .iter()
                .filter(|s| matches!(s.flags & SECTION_TYPE, NON_LAZY_POINTERS | LAZY_POINTERS))
            {
                let slots = usize::try_from(s.size / word).unwrap_or(0).min(1 << 20);
                for i in 0..slots {
                    let Some(index) = at(s.reserved1 as usize + i) else {
                        break;
                    };
                    if index & INDIRECT_NONE != 0 {
                        continue;
                    }
                    let Ok((name, _)) = table.get(index as usize) else {
                        continue;
                    };
                    let slot = s.addr + i as u64 * word;
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

    let code = |va: u64| {
        sections
            .iter()
            .find(|s| s.executable && va >= s.va && va < s.va.saturating_add(s.vsize))
    };
    let mut starts: Vec<u64> = function_starts(file, m, base, text)
        .into_iter()
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
                .filter(|&n| n < section.va.saturating_add(section.vsize))
                .unwrap_or(section.va.saturating_add(section.vsize));
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
    // INVARIANT: goblin seeds `libs` with the image itself ("self", or
    // its `LC_ID_DYLIB` install name) at index 0, so the linked
    // libraries begin at the second entry.
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
                    .saturating_add(d.name as usize);
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
                // The tools follow the command: `{tool, version}` pairs,
                // the linker being tool 3, its version packed 16.8.8.
                let first = base.saturating_add(lc.offset).saturating_add(24);
                for k in 0..usize::try_from(b.ntools).unwrap_or(0).min(16) {
                    let at = first.saturating_add(k * 8);
                    if u32_at(file, at) == Some(3)
                        && let Some(v) = u32_at(file, at + 4)
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
    }
}
