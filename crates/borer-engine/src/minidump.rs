//! Minidump (`.dmp`) loading: the memory a crash or a snapshot caught,
//! mapped as a program.
//!
//! A minidump holds no image - it holds address ranges. Every memory
//! range the writer captured becomes one section whose file extent is
//! where the dump holds its bytes, so reading, disassembly, emulation and
//! analysis work on the crashed process's memory exactly as they do on a
//! file image, purely and on any platform. The module list names each
//! image's base, the system-info stream states the architecture, and the
//! exception stream's thread context supplies the address the crash
//! stopped at as the program's entry.
//!
//! Everything reads the dump defensively: a count that runs past the
//! file, or a range the file does not hold, is skipped or clamped, the
//! way a half-written dump still answers for the pages it did write.

use crate::num::{u16_le, u32_le, u64_le};
use crate::program::{Arch, Program, Section, Symbol, SymbolKind};

/// The stream directory entry size: type, size, rva.
const DIR_ENTRY: usize = 12;
/// `ThreadListStream`: the threads the dump holds, with their stacks.
const THREADS: u32 = 3;
/// `ModuleListStream`: the images the process had loaded.
const MODULES: u32 = 4;
/// `MemoryListStream`: memory ranges, each at its own file offset.
const MEMORY: u32 = 5;
/// `ExceptionStream`: the crash, with the context of its thread.
const EXCEPTION: u32 = 6;
/// `SystemInfoStream`: the machine the process ran on.
const SYSTEM: u32 = 7;
/// `Memory64ListStream`: memory ranges packed after the directory.
const MEMORY64: u32 = 9;
/// `MemoryInfoListStream`: what the OS said about each page.
const MEMORY_INFO: u32 = 16;
/// `PROCESSOR_ARCHITECTURE_INTEL`: x86.
const ARCH_X86: u16 = 0;
/// `PROCESSOR_ARCHITECTURE_AMD64`: x86-64.
const ARCH_X64: u16 = 9;
/// `PROCESSOR_ARCHITECTURE_ARM64`.
const ARCH_ARM64: u16 = 12;
/// The x64 `CONTEXT` offset of `Rip`.
const X64_RIP: usize = 0xf8;
/// The x86 `CONTEXT` offset of `Eip`.
const X86_EIP: usize = 0xb8;

/// One memory range the dump holds.
#[derive(Debug, Clone, Copy)]
struct Range {
    /// Where the bytes sit in memory.
    start: u64,
    /// How many.
    size: u64,
    /// Where they sit in the file.
    at: u64,
}

/// The minidump's streams: the first directory entry of each type.
struct Streams<'a> {
    /// The whole dump.
    bytes: &'a [u8],
    /// Each entry's `(type, size, rva)`.
    dir: Vec<(u32, u32, u32)>,
}

impl<'a> Streams<'a> {
    /// Reads the dump's stream directory, or `None` when the header or
    /// the directory does not sit in the file.
    fn read(bytes: &'a [u8]) -> Option<Streams<'a>> {
        let count = u32_le(bytes, 8)?;
        let rva = u32_le(bytes, 12)?;
        let mut dir = Vec::new();
        for k in 0..usize::try_from(count).ok()? {
            let at = usize::try_from(rva).ok()?.checked_add(k * DIR_ENTRY)?;
            dir.push((
                u32_le(bytes, at)?,
                u32_le(bytes, at.checked_add(4)?)?,
                u32_le(bytes, at.checked_add(8)?)?,
            ));
        }
        Some(Streams { bytes, dir })
    }

    /// The first stream of `want`, as `(size, rva)`.
    fn first(&self, want: u32) -> Option<(u32, u32)> {
        self.dir
            .iter()
            .find(|(t, ..)| *t == want)
            .map(|&(_, size, rva)| (size, rva))
    }

    /// Reads the memory ranges of the `MemoryListStream`: a count, then
    /// each range's start, size and file offset.
    fn memory(&self) -> Vec<Range> {
        let Some((_, at)) = self.first(MEMORY) else {
            return Vec::new();
        };
        let bytes = self.bytes;
        let Some(count) = u32_le(bytes, usize::try_from(at).ok().unwrap_or(usize::MAX))
            .and_then(|c| usize::try_from(c).ok())
        else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for k in 0..count {
            let entry = usize::try_from(at)
                .ok()
                .and_then(|a| a.checked_add(4 + k * 16));
            let (Some(entry), true) = (entry, k < 0x1_0000) else {
                break;
            };
            let (Some(start), Some(size), Some(at)) = (
                u64_le(bytes, entry),
                u32_le(bytes, entry + 8).map(u64::from),
                u32_le(bytes, entry + 12).map(u64::from),
            ) else {
                break;
            };
            out.push(Range { start, size, at });
        }
        out
    }

    /// Reads the memory ranges of the `Memory64ListStream`: a file offset
    /// the ranges are packed at from, a count, then each range's start
    /// and size.
    fn memory64(&self) -> Vec<Range> {
        let Some((_, at)) = self.first(MEMORY64) else {
            return Vec::new();
        };
        let bytes = self.bytes;
        let at = usize::try_from(at).ok().unwrap_or(usize::MAX);
        let (Some(base), Some(count)) = (u64_le(bytes, at), u64_le(bytes, at + 8)) else {
            return Vec::new();
        };
        let count = usize::try_from(count)
            .ok()
            .unwrap_or(usize::MAX)
            .min(0x1_0000);
        let mut out = Vec::new();
        let mut cursor = base;
        for k in 0..count {
            let entry = at.checked_add(16).and_then(|e| e.checked_add(k * 16));
            let Some(entry) = entry else {
                break;
            };
            let (Some(start), Some(size)) = (u64_le(bytes, entry), u64_le(bytes, entry + 8)) else {
                break;
            };
            out.push(Range {
                start,
                size,
                at: cursor,
            });
            cursor = cursor.saturating_add(size);
        }
        out
    }

    /// Reads the thread stacks of the `ThreadListStream`, which a dump
    /// without the memory lists still holds.
    fn stacks(&self) -> Vec<Range> {
        let Some((_, at)) = self.first(THREADS) else {
            return Vec::new();
        };
        let bytes = self.bytes;
        let Some(count) = u32_le(bytes, usize::try_from(at).ok().unwrap_or(usize::MAX))
            .and_then(|c| usize::try_from(c).ok())
        else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for k in 0..count.min(0x1_0000) {
            // ASM: MINIDUMP_THREAD: ThreadId, Suspend, PriorityClass,
            // Priority, Teb (24 bytes in), then the stack's descriptor.
            let Some(entry) = usize::try_from(at)
                .ok()
                .and_then(|a| a.checked_add(4 + k * 48))
            else {
                break;
            };
            let (Some(start), Some(size), Some(at)) = (
                u64_le(bytes, entry + 24),
                u32_le(bytes, entry + 32).map(u64::from),
                u32_le(bytes, entry + 36).map(u64::from),
            ) else {
                break;
            };
            out.push(Range { start, size, at });
        }
        out
    }

    /// Reads the loaded images of the `ModuleListStream`: each module's
    /// base, size and name.
    fn modules(&self) -> Vec<(u64, u64, String)> {
        let Some((_, at)) = self.first(MODULES) else {
            return Vec::new();
        };
        let bytes = self.bytes;
        let Some(count) = u32_le(bytes, usize::try_from(at).ok().unwrap_or(usize::MAX))
            .and_then(|c| usize::try_from(c).ok())
        else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for k in 0..count.min(0x1_0000) {
            // ASM: MINIDUMP_MODULE: BaseOfImage, SizeOfImage, CheckSum,
            // TimeDateStamp, ModuleNameRva, then the versions.
            let Some(entry) = usize::try_from(at)
                .ok()
                .and_then(|a| a.checked_add(4 + k * 108))
            else {
                break;
            };
            let (Some(base), Some(size), Some(name_at)) = (
                u64_le(bytes, entry),
                u32_le(bytes, entry + 8).map(u64::from),
                u32_le(bytes, entry + 20).map(u64::from),
            ) else {
                break;
            };
            let name = usize::try_from(name_at)
                .ok()
                .and_then(|n| string_at(bytes, n))
                .unwrap_or_default();
            out.push((base, size, name));
        }
        out
    }

    /// The architecture the `SystemInfoStream` states.
    fn arch(&self) -> Arch {
        let Some((_, at)) = self.first(SYSTEM) else {
            return Arch::Unknown;
        };
        match u16_le(self.bytes, usize::try_from(at).unwrap_or(usize::MAX)) {
            Some(ARCH_X86) => Arch::X86,
            Some(ARCH_X64) => Arch::X86_64,
            Some(ARCH_ARM64) => Arch::Arm64,
            _ => Arch::Unknown,
        }
    }

    /// The address the `ExceptionStream`'s context stopped at, as the
    /// program's entry.
    ///
    /// A context too small to hold the architecture's stop register, or
    /// one whose bytes do not sit in the file, states nothing.
    fn stopped_at(&self, arch: Arch) -> Option<u64> {
        let (_, at) = self.first(EXCEPTION)?;
        let bytes = self.bytes;
        let at = usize::try_from(at).ok()?;
        // ASM: MINIDUMP_EXCEPTION_STREAM: ThreadId, alignment, the
        // exception record, then the context location.
        let (size, rva) = (u32_le(bytes, at + 160)?, u32_le(bytes, at + 164)?);
        let rva = usize::try_from(rva).ok()?;
        let rip = match arch {
            Arch::X86_64 => X64_RIP,
            Arch::X86 => X86_EIP,
            _ => return None,
        };
        let size = usize::try_from(size).ok()?;
        if size < rip + 8 {
            return None;
        }
        let end = rva.checked_add(rip)?.checked_add(8)?;
        (end <= bytes.len())
            .then(|| u64_le(bytes, rva + rip))
            .flatten()
    }

    /// The protection the `MemoryInfoListStream` states for the address,
    /// as `(executable, writable)`.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address a memory range starts at.
    fn protects(&self, addr: u64) -> Option<(bool, bool)> {
        let (_, at) = self.first(MEMORY_INFO)?;
        let bytes = self.bytes;
        let at = usize::try_from(at).ok()?;
        let (header, entry, count) = (
            u32_le(bytes, at)?,
            u32_le(bytes, at + 4)?,
            u64_le(bytes, at + 8)?,
        );
        let entry = usize::try_from(entry).ok()?;
        if entry == 0 || entry > 64 {
            return None;
        }
        let count = usize::try_from(count).ok()?.min(0x1_0000);
        let header = usize::try_from(header).ok()?;
        for k in 0..count {
            let Some(e) = at
                .checked_add(header)
                .and_then(|h| h.checked_add(k * entry))
            else {
                break;
            };
            let (base, size, protect) = (
                u64_le(bytes, e)?,
                u64_le(bytes, e + 24)?,
                u32_le(bytes, e + 36)?,
            );
            if base <= addr && addr < base.saturating_add(size) {
                // ASM: the execute protections run 0x10..0x80 with no low
                // bits; the writable ones are 0x04, 0x08, 0x40 and 0x80.
                let exec = protect & 0xf0 != 0 && protect & 0x0f == 0;
                let write = protect & (0x04 | 0x08 | 0x40 | 0x80) != 0;
                return Some((exec, write));
            }
        }
        None
    }
}

/// Reads a `MINIDUMP_STRING`: a byte length and UTF-16 code units.
///
/// # Arguments
///
/// * `bytes` - The whole dump.
/// * `at` - The string's file offset.
///
/// # Returns
///
/// The name, lossily decoded, cut at 260 characters.
fn string_at(bytes: &[u8], at: usize) -> Option<String> {
    let len = usize::try_from(u32_le(bytes, at)?).ok()?;
    if len > 0x1000 || len % 2 != 0 {
        return None;
    }
    let units: Vec<u16> = (0..len / 2)
        .map(|k| u16_le(bytes, at + 4 + k * 2))
        .collect::<Option<Vec<u16>>>()?
        .into_iter()
        .take_while(|&u| u != 0)
        .collect();
    Some(
        char::decode_utf16(units)
            .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
            .take(260)
            .collect(),
    )
}

/// Builds a program out of a minidump: every captured range a section,
/// every module base a data symbol.
///
/// The first module the list names is the image base - a dump of one
/// process names the executable first - and the exception stream's
/// context supplies the entry. A range the file does not hold is clamped
/// to what it does; the memory-info stream's protections set the section
/// flags where it states them, and a range it does not stays readable,
/// writable and executable, the way a snapshot answers for every page it
/// caught.
///
/// # Arguments
///
/// * `path` - The dump's path, recorded.
/// * `bytes` - The whole dump, moved into the program.
///
/// # Returns
///
/// The program, or `None` when the header or the stream directory does
/// not sit in the file.
#[must_use]
pub(crate) fn program(path: std::path::PathBuf, bytes: Vec<u8>) -> Option<Program> {
    let streams = Streams::read(&bytes)?;
    let arch = streams.arch();
    let mut ranges = streams.memory();
    ranges.extend(streams.memory64());
    for stack in streams.stacks() {
        let covered = ranges.iter().any(|r| {
            r.start <= stack.start
                && r.start.saturating_add(r.size) >= stack.start.saturating_add(stack.size)
        });
        if !covered {
            ranges.push(stack);
        }
    }
    ranges.sort_unstable_by_key(|r| r.start);
    let file_len = crate::num::from_usize(bytes.len());
    let mut sections: Vec<Section> = Vec::new();
    for (k, r) in ranges.iter().enumerate() {
        if r.size == 0 || r.at >= file_len {
            continue;
        }
        let held = r.size.min(file_len - r.at);
        let (exec, write) = streams.protects(r.start).unwrap_or((true, true));
        sections.push(Section {
            name: format!("mem{k}"),
            va: crate::program::Va(r.start),
            vsize: r.size,
            file_off: crate::program::FileOff(r.at),
            file_size: held,
            readable: true,
            writable: write,
            executable: exec,
        });
    }
    let modules = streams.modules();
    let symbols: Vec<Symbol> = modules
        .iter()
        .filter(|(base, ..)| *base != 0)
        .map(|&(base, _, ref name)| Symbol {
            name: name.clone(),
            addr: base,
            kind: SymbolKind::Data,
        })
        .collect();
    let entry = streams.stopped_at(arch);
    let image_base = modules.first().map_or(0, |&(base, ..)| base);
    let mut p = Program::raw(bytes, arch, image_base, entry, sections);
    p.path = path;
    p.symbols = symbols;
    p.headers.kind = Some("minidump");
    p.headers.machine = Some(match arch {
        Arch::X86 => "x86".to_owned(),
        Arch::X86_64 => "x86-64".to_owned(),
        Arch::Arm64 => "arm64".to_owned(),
        Arch::Arm => "arm".to_owned(),
        Arch::Unknown => "unknown".to_owned(),
    });
    Some(p)
}
